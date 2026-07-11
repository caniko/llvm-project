//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implements the BTF type deduplication algorithm, a port of the algorithm
// from libbpf (btf_dedup.c, BSD-licensed).
//
// The algorithm runs in 6 passes:
//   1. String deduplication
//   2. Primitive type dedup (INT, FLOAT, ENUM, ENUM64, FWD)
//   3. Composite type dedup (STRUCT, UNION)
//   4. Resolve unambiguous FWD -> STRUCT/UNION mappings
//   5. Reference type dedup (PTR, TYPEDEF, VOLATILE, etc.)
//   6. Type compaction and ID remapping
//
// For struct/union types, a DFS-based type graph equivalence check is used
// with a "hypothetical map" to handle recursive/cyclic types.
//
//===----------------------------------------------------------------------===//

#include "llvm/DebugInfo/BTF/BTFDedup.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/DebugInfo/BTF/BTF.h"
#include "llvm/DebugInfo/BTF/BTFBuilder.h"

#define DEBUG_TYPE "btf-dedup"

using namespace llvm;

namespace {

// Sentinel value: type has not been processed yet.
constexpr uint32_t BTF_UNPROCESSED = UINT32_MAX;

/// State for the BTF deduplication algorithm.
class BTFDedupState {
  BTFBuilder &Builder;

  enum class RefDedupState : uint8_t {
    Unprocessed,
    InProgress,
    Done,
  };

  // Equivalence map: Map[i] = canonical type ID for type i.
  // Initially Map[i] = i (each type is its own canonical).
  // After dedup, Map[i] = j means type i is equivalent to canonical type j.
  std::vector<uint32_t> Map;

  // Hypothetical map for recursive type comparison.
  // HypotMap[i] = j means "we hypothesize type i is equivalent to type j".
  // Reset between each top-level comparison.
  std::vector<uint32_t> HypotMap;

  // List of types currently in the hypothetical map (for fast reset).
  SmallVector<uint32_t, 0> HypotList;

  // String dedup: maps string content to canonical offset.
  StringMap<uint32_t> StringDedup;

  // New string offsets: NewStrOff[old_offset] = new_offset after dedup.
  DenseMap<uint32_t, uint32_t> NewStrOff;

  // Hash for each type, used for bucketing candidates.
  std::vector<uint64_t> TypeHash;

  // Buckets: hash -> list of canonical type IDs with that hash.
  DenseMap<uint64_t, SmallVector<uint32_t, 4>> HashBuckets;

  // After compaction: OldToNew[old_id] = new_id.
  std::vector<uint32_t> OldToNew;

  // Reference-type dedup status used by the recursive ref pass.
  std::vector<RefDedupState> RefState;

  // FWD -> STRUCT/UNION mappings discovered while proving type graph
  // equivalence. These are committed only if the full top-level comparison
  // succeeds.
  SmallVector<std::pair<uint32_t, uint32_t>, 0> PendingFwdResolutions;

  static bool isPrimitiveKind(uint32_t Kind) {
    switch (Kind) {
    case BTF::BTF_KIND_INT:
    case BTF::BTF_KIND_FLOAT:
    case BTF::BTF_KIND_ENUM:
    case BTF::BTF_KIND_ENUM64:
    case BTF::BTF_KIND_FWD:
      return true;
    default:
      return false;
    }
  }

  // Returns true if this is a composite kind that needs DFS comparison.
  static bool isCompositeKind(uint32_t Kind) {
    return Kind == BTF::BTF_KIND_STRUCT || Kind == BTF::BTF_KIND_UNION;
  }

  bool isFwdCompatibleWithComposite(const BTF::CommonType *Fwd,
                                    const BTF::CommonType *Composite) const {
    if (!Fwd || !Composite || Fwd->getKind() != BTF::BTF_KIND_FWD ||
        !isCompositeKind(Composite->getKind()))
      return false;

    uint32_t FwdKind =
        (Fwd->Info & BTF::FWD_UNION_FLAG) ? BTF::BTF_KIND_UNION
                                          : BTF::BTF_KIND_STRUCT;
    return FwdKind == Composite->getKind() &&
           dedupStrOff(Fwd->NameOff) == dedupStrOff(Composite->NameOff);
  }

  // Get the canonical representative for a type ID.
  uint32_t resolve(uint32_t Id) const {
    while (Id < Map.size() && Map[Id] != Id)
      Id = Map[Id];
    return Id;
  }

  // Hash a type for bucketing. Only considers local structure, not
  // referenced type IDs (those are checked in equivalence comparison).
  uint64_t hashType(uint32_t Id);

  // Hash helpers for specific kinds.
  uint64_t hashCommon(const BTF::CommonType *T);
  uint64_t hashStruct(const BTF::CommonType *T);
  uint64_t hashEnum(const BTF::CommonType *T);
  uint64_t hashEnum64(const BTF::CommonType *T);
  uint64_t hashFuncProto(const BTF::CommonType *T);
  uint64_t hashArray(const BTF::CommonType *T);
  uint64_t hashDataSec(const BTF::CommonType *T);
  uint64_t hashDeclTag(uint32_t Id);

  // Check if two types are structurally equivalent.
  // Uses the hypothetical map for cycle handling.
  bool isEquiv(uint32_t CandId, uint32_t CanonId);

  // Deep comparison helpers.
  bool isEquivCommon(const BTF::CommonType *Cand, const BTF::CommonType *Canon);
  bool isEquivStruct(uint32_t CandId, uint32_t CanonId);
  bool isEquivEnum(const BTF::CommonType *Cand, const BTF::CommonType *Canon);
  bool isEquivEnum64(const BTF::CommonType *Cand, const BTF::CommonType *Canon);
  bool isEquivFuncProto(uint32_t CandId, uint32_t CanonId);
  bool isEquivArray(uint32_t CandId, uint32_t CanonId);
  bool isEquivDataSec(uint32_t CandId, uint32_t CanonId);

  // Reset the hypothetical map.
  void clearHypot() {
    for (uint32_t Id : HypotList)
      HypotMap[Id] = BTF_UNPROCESSED;
    HypotList.clear();
    PendingFwdResolutions.clear();
  }

  uint32_t dedupStrOff(uint32_t Offset) const {
    auto It = NewStrOff.find(Offset);
    return It != NewStrOff.end() ? It->second : Offset;
  }

  // The six passes.
  Error dedupStrings();
  Error dedupPrimitives();
  Error dedupComposites();
  Error resolveFwds();
  Error dedupRefs();
  Error compact();
  Expected<uint32_t> dedupRefType(uint32_t Id);

public:
  BTFDedupState(BTFBuilder &B) : Builder(B) {}
  Error run();
};

//===----------------------------------------------------------------------===//
// Hashing
//===----------------------------------------------------------------------===//

uint64_t BTFDedupState::hashCommon(const BTF::CommonType *T) {
  return hash_combine(T->getKind(), dedupStrOff(T->NameOff), T->Size);
}

uint64_t BTFDedupState::hashStruct(const BTF::CommonType *T) {
  // Hash name + size + member names (NOT member types — those are checked
  // during equivalence comparison).
  uint64_t H = hash_combine(T->getKind(), dedupStrOff(T->NameOff), T->Size,
                            T->getVlen());
  auto *Members = reinterpret_cast<const BTF::BTFMember *>(
      reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType));
  for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
    H = hash_combine(H, dedupStrOff(Members[I].NameOff), Members[I].Offset);
  return H;
}

uint64_t BTFDedupState::hashEnum(const BTF::CommonType *T) {
  uint64_t H = hashCommon(T);
  auto *Values = reinterpret_cast<const BTF::BTFEnum *>(
      reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType));
  for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
    H = hash_combine(H, dedupStrOff(Values[I].NameOff), Values[I].Val);
  return H;
}

uint64_t BTFDedupState::hashEnum64(const BTF::CommonType *T) {
  uint64_t H = hashCommon(T);
  auto *Values = reinterpret_cast<const BTF::BTFEnum64 *>(
      reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType));
  for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
    H = hash_combine(H, dedupStrOff(Values[I].NameOff), Values[I].Val_Lo32,
                     Values[I].Val_Hi32);
  return H;
}

uint64_t BTFDedupState::hashFuncProto(const BTF::CommonType *T) {
  uint64_t H = hash_combine(T->getKind(), T->Type, T->getVlen());
  auto *Params = reinterpret_cast<const BTF::BTFParam *>(
      reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType));
  for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
    H = hash_combine(H, dedupStrOff(Params[I].NameOff), Params[I].Type);
  return H;
}

uint64_t BTFDedupState::hashArray(const BTF::CommonType *T) {
  auto *Arr = reinterpret_cast<const BTF::BTFArray *>(
      reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType));
  return hash_combine(T->getKind(), Arr->ElemType, Arr->IndexType,
                      Arr->Nelems);
}

uint64_t BTFDedupState::hashDataSec(const BTF::CommonType *T) {
  uint64_t H = hash_combine(T->getKind(), dedupStrOff(T->NameOff), T->Size,
                            T->getVlen());
  auto *Vars = reinterpret_cast<const BTF::BTFDataSec *>(
      reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType));
  for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
    H = hash_combine(H, Vars[I].Type, Vars[I].Offset, Vars[I].Size);
  return H;
}

uint64_t BTFDedupState::hashDeclTag(uint32_t Id) {
  const BTF::CommonType *T = Builder.findType(Id);
  if (!T)
    return 0;

  auto Bytes = Builder.getTypeBytes(Id);
  if (Bytes.size() < sizeof(BTF::CommonType) + 4)
    return hashCommon(T);

  uint32_t ComponentIdx = 0;
  memcpy(&ComponentIdx, Bytes.data() + sizeof(BTF::CommonType), 4);
  return hash_combine(hashCommon(T), ComponentIdx);
}

uint64_t BTFDedupState::hashType(uint32_t Id) {
  const BTF::CommonType *T = Builder.findType(Id);
  if (!T)
    return 0;

  switch (T->getKind()) {
  case BTF::BTF_KIND_INT:
  case BTF::BTF_KIND_FLOAT:
  case BTF::BTF_KIND_FWD:
    return hashCommon(T);
  case BTF::BTF_KIND_ENUM:
    return hashEnum(T);
  case BTF::BTF_KIND_ENUM64:
    return hashEnum64(T);
  case BTF::BTF_KIND_STRUCT:
  case BTF::BTF_KIND_UNION:
    return hashStruct(T);
  case BTF::BTF_KIND_PTR:
  case BTF::BTF_KIND_TYPEDEF:
  case BTF::BTF_KIND_VOLATILE:
  case BTF::BTF_KIND_CONST:
  case BTF::BTF_KIND_RESTRICT:
  case BTF::BTF_KIND_FUNC:
  case BTF::BTF_KIND_VAR:
  case BTF::BTF_KIND_TYPE_TAG:
    return hashCommon(T);
  case BTF::BTF_KIND_FUNC_PROTO:
    return hashFuncProto(T);
  case BTF::BTF_KIND_ARRAY:
    return hashArray(T);
  case BTF::BTF_KIND_DATASEC:
    return hashDataSec(T);
  case BTF::BTF_KIND_DECL_TAG:
    return hashDeclTag(Id);
  default:
    // Reference types: hash by kind only (real comparison uses resolved refs).
    return hash_combine(T->getKind());
  }
}

//===----------------------------------------------------------------------===//
// Equivalence checking
//===----------------------------------------------------------------------===//

bool BTFDedupState::isEquivCommon(const BTF::CommonType *Cand,
                                  const BTF::CommonType *Canon) {
  return Cand->getKind() == Canon->getKind() &&
         dedupStrOff(Cand->NameOff) == dedupStrOff(Canon->NameOff) &&
         Cand->Size == Canon->Size && Cand->getVlen() == Canon->getVlen();
}

bool BTFDedupState::isEquivEnum(const BTF::CommonType *Cand,
                                const BTF::CommonType *Canon) {
  if (!isEquivCommon(Cand, Canon))
    return false;

  auto *CandVals = reinterpret_cast<const BTF::BTFEnum *>(
      reinterpret_cast<const uint8_t *>(Cand) + sizeof(BTF::CommonType));
  auto *CanonVals = reinterpret_cast<const BTF::BTFEnum *>(
      reinterpret_cast<const uint8_t *>(Canon) + sizeof(BTF::CommonType));

  for (unsigned I = 0, N = Cand->getVlen(); I < N; ++I) {
    if (dedupStrOff(CandVals[I].NameOff) != dedupStrOff(CanonVals[I].NameOff) ||
        CandVals[I].Val != CanonVals[I].Val)
      return false;
  }
  return true;
}

bool BTFDedupState::isEquivEnum64(const BTF::CommonType *Cand,
                                  const BTF::CommonType *Canon) {
  if (!isEquivCommon(Cand, Canon))
    return false;

  auto *CandVals = reinterpret_cast<const BTF::BTFEnum64 *>(
      reinterpret_cast<const uint8_t *>(Cand) + sizeof(BTF::CommonType));
  auto *CanonVals = reinterpret_cast<const BTF::BTFEnum64 *>(
      reinterpret_cast<const uint8_t *>(Canon) + sizeof(BTF::CommonType));

  for (unsigned I = 0, N = Cand->getVlen(); I < N; ++I) {
    if (dedupStrOff(CandVals[I].NameOff) != dedupStrOff(CanonVals[I].NameOff) ||
        CandVals[I].Val_Lo32 != CanonVals[I].Val_Lo32 ||
        CandVals[I].Val_Hi32 != CanonVals[I].Val_Hi32)
      return false;
  }
  return true;
}

bool BTFDedupState::isEquivStruct(uint32_t CandId, uint32_t CanonId) {
  const BTF::CommonType *Cand = Builder.findType(CandId);
  const BTF::CommonType *Canon = Builder.findType(CanonId);
  if (!Cand || !Canon || !isEquivCommon(Cand, Canon))
    return false;

  auto *CandMembers = reinterpret_cast<const BTF::BTFMember *>(
      reinterpret_cast<const uint8_t *>(Cand) + sizeof(BTF::CommonType));
  auto *CanonMembers = reinterpret_cast<const BTF::BTFMember *>(
      reinterpret_cast<const uint8_t *>(Canon) + sizeof(BTF::CommonType));

  for (unsigned I = 0, N = Cand->getVlen(); I < N; ++I) {
    if (dedupStrOff(CandMembers[I].NameOff) !=
            dedupStrOff(CanonMembers[I].NameOff) ||
        CandMembers[I].Offset != CanonMembers[I].Offset)
      return false;
    if (!isEquiv(CandMembers[I].Type, CanonMembers[I].Type))
      return false;
  }
  return true;
}

bool BTFDedupState::isEquivFuncProto(uint32_t CandId, uint32_t CanonId) {
  const BTF::CommonType *Cand = Builder.findType(CandId);
  const BTF::CommonType *Canon = Builder.findType(CanonId);
  if (!Cand || !Canon)
    return false;
  if (Cand->getKind() != Canon->getKind() ||
      Cand->getVlen() != Canon->getVlen())
    return false;

  if (!isEquiv(Cand->Type, Canon->Type))
    return false;

  auto *CandParams = reinterpret_cast<const BTF::BTFParam *>(
      reinterpret_cast<const uint8_t *>(Cand) + sizeof(BTF::CommonType));
  auto *CanonParams = reinterpret_cast<const BTF::BTFParam *>(
      reinterpret_cast<const uint8_t *>(Canon) + sizeof(BTF::CommonType));

  for (unsigned I = 0, N = Cand->getVlen(); I < N; ++I) {
    if (dedupStrOff(CandParams[I].NameOff) !=
        dedupStrOff(CanonParams[I].NameOff))
      return false;
    if (!isEquiv(CandParams[I].Type, CanonParams[I].Type))
      return false;
  }
  return true;
}

bool BTFDedupState::isEquivArray(uint32_t CandId, uint32_t CanonId) {
  const BTF::CommonType *Cand = Builder.findType(CandId);
  const BTF::CommonType *Canon = Builder.findType(CanonId);
  if (!Cand || !Canon || Cand->getKind() != Canon->getKind())
    return false;

  auto *CandArr = reinterpret_cast<const BTF::BTFArray *>(
      reinterpret_cast<const uint8_t *>(Cand) + sizeof(BTF::CommonType));
  auto *CanonArr = reinterpret_cast<const BTF::BTFArray *>(
      reinterpret_cast<const uint8_t *>(Canon) + sizeof(BTF::CommonType));

  if (CandArr->Nelems != CanonArr->Nelems)
    return false;
  return isEquiv(CandArr->ElemType, CanonArr->ElemType) &&
         isEquiv(CandArr->IndexType, CanonArr->IndexType);
}

bool BTFDedupState::isEquivDataSec(uint32_t CandId, uint32_t CanonId) {
  const BTF::CommonType *Cand = Builder.findType(CandId);
  const BTF::CommonType *Canon = Builder.findType(CanonId);
  if (!Cand || !Canon || !isEquivCommon(Cand, Canon))
    return false;

  auto *CandVars = reinterpret_cast<const BTF::BTFDataSec *>(
      reinterpret_cast<const uint8_t *>(Cand) + sizeof(BTF::CommonType));
  auto *CanonVars = reinterpret_cast<const BTF::BTFDataSec *>(
      reinterpret_cast<const uint8_t *>(Canon) + sizeof(BTF::CommonType));

  for (unsigned I = 0, N = Cand->getVlen(); I < N; ++I) {
    if (CandVars[I].Offset != CanonVars[I].Offset ||
        CandVars[I].Size != CanonVars[I].Size)
      return false;
    if (CandVars[I].Type != 0 && CanonVars[I].Type != 0) {
      if (!isEquiv(CandVars[I].Type, CanonVars[I].Type))
        return false;
    } else if (CandVars[I].Type != CanonVars[I].Type) {
      return false;
    }
  }
  return true;
}

bool BTFDedupState::isEquiv(uint32_t CandId, uint32_t CanonId) {
  CandId = resolve(CandId);
  CanonId = resolve(CanonId);

  if (CandId == 0 && CanonId == 0)
    return true;
  if (CandId == 0 || CanonId == 0)
    return false;
  if (CandId == CanonId)
    return true;

  const BTF::CommonType *Cand = Builder.findType(CandId);
  const BTF::CommonType *Canon = Builder.findType(CanonId);
  if (!Cand || !Canon)
    return false;

  if (Cand->getKind() != Canon->getKind()) {
    if (isFwdCompatibleWithComposite(Cand, Canon)) {
      PendingFwdResolutions.push_back({CandId, CanonId});
      return true;
    }
    if (isFwdCompatibleWithComposite(Canon, Cand)) {
      PendingFwdResolutions.push_back({CanonId, CandId});
      return true;
    }
    return false;
  }

  // Cycle detection: check if we already have a hypothesis for CandId.
  if (HypotMap[CandId] != BTF_UNPROCESSED)
    return HypotMap[CandId] == CanonId;

  HypotMap[CandId] = CanonId;
  HypotList.push_back(CandId);

  switch (Cand->getKind()) {
  case BTF::BTF_KIND_INT:
  case BTF::BTF_KIND_FLOAT:
  case BTF::BTF_KIND_FWD:
    return isEquivCommon(Cand, Canon);

  case BTF::BTF_KIND_ENUM:
    return isEquivEnum(Cand, Canon);

  case BTF::BTF_KIND_ENUM64:
    return isEquivEnum64(Cand, Canon);

  case BTF::BTF_KIND_STRUCT:
  case BTF::BTF_KIND_UNION:
    return isEquivStruct(CandId, CanonId);

  case BTF::BTF_KIND_FUNC_PROTO:
    return isEquivFuncProto(CandId, CanonId);

  case BTF::BTF_KIND_ARRAY:
    return isEquivArray(CandId, CanonId);

  case BTF::BTF_KIND_PTR:
  case BTF::BTF_KIND_TYPEDEF:
  case BTF::BTF_KIND_VOLATILE:
  case BTF::BTF_KIND_CONST:
  case BTF::BTF_KIND_RESTRICT:
  case BTF::BTF_KIND_TYPE_TAG:
    if (dedupStrOff(Cand->NameOff) != dedupStrOff(Canon->NameOff))
      return false;
    return isEquiv(Cand->Type, Canon->Type);

  case BTF::BTF_KIND_FUNC:
    if (dedupStrOff(Cand->NameOff) != dedupStrOff(Canon->NameOff))
      return false;
    return isEquiv(Cand->Type, Canon->Type);

  case BTF::BTF_KIND_VAR:
    if (dedupStrOff(Cand->NameOff) != dedupStrOff(Canon->NameOff))
      return false;
    if (Cand->Type != 0 && Canon->Type != 0)
      return isEquiv(Cand->Type, Canon->Type);
    return Cand->Type == Canon->Type;

  case BTF::BTF_KIND_DATASEC:
    return isEquivDataSec(CandId, CanonId);

  case BTF::BTF_KIND_DECL_TAG:
    if (dedupStrOff(Cand->NameOff) != dedupStrOff(Canon->NameOff))
      return false;
    {
      auto CandBytes = Builder.getTypeBytes(CandId);
      auto CanonBytes = Builder.getTypeBytes(CanonId);
      if (CandBytes.size() < sizeof(BTF::CommonType) + 4 ||
          CanonBytes.size() < sizeof(BTF::CommonType) + 4)
        return false;
      uint32_t CandIdx, CanonIdx;
      memcpy(&CandIdx, CandBytes.data() + sizeof(BTF::CommonType), 4);
      memcpy(&CanonIdx, CanonBytes.data() + sizeof(BTF::CommonType), 4);
      if (CandIdx != CanonIdx)
        return false;
    }
    return isEquiv(Cand->Type, Canon->Type);

  default:
    return false;
  }
}

//===----------------------------------------------------------------------===//
// Pass 1: String deduplication
//===----------------------------------------------------------------------===//

Error BTFDedupState::dedupStrings() {
  StringDedup[""] = 0;

  for (uint32_t Id = 1; Id <= Builder.typesCount(); ++Id) {
    const BTF::CommonType *T = Builder.findType(Id);
    if (!T)
      continue;

    auto DedupStr = [&](uint32_t Off) {
      if (NewStrOff.count(Off))
        return;
      StringRef S = Builder.findString(Off);
      auto It = StringDedup.find(S);
      if (It != StringDedup.end()) {
        NewStrOff[Off] = It->second;
      } else {
        StringDedup[S] = Off;
        NewStrOff[Off] = Off;
      }
    };

    DedupStr(T->NameOff);

    const uint8_t *TailPtr =
        reinterpret_cast<const uint8_t *>(T) + sizeof(BTF::CommonType);
    switch (T->getKind()) {
    case BTF::BTF_KIND_STRUCT:
    case BTF::BTF_KIND_UNION: {
      auto *M = reinterpret_cast<const BTF::BTFMember *>(TailPtr);
      for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
        DedupStr(M[I].NameOff);
      break;
    }
    case BTF::BTF_KIND_ENUM: {
      auto *E = reinterpret_cast<const BTF::BTFEnum *>(TailPtr);
      for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
        DedupStr(E[I].NameOff);
      break;
    }
    case BTF::BTF_KIND_ENUM64: {
      auto *E = reinterpret_cast<const BTF::BTFEnum64 *>(TailPtr);
      for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
        DedupStr(E[I].NameOff);
      break;
    }
    case BTF::BTF_KIND_FUNC_PROTO: {
      auto *P = reinterpret_cast<const BTF::BTFParam *>(TailPtr);
      for (unsigned I = 0, N = T->getVlen(); I < N; ++I)
        DedupStr(P[I].NameOff);
      break;
    }
    default:
      break;
    }
  }

  return Error::success();
}

//===----------------------------------------------------------------------===//
// Pass 2: Primitive and composite type dedup
//===----------------------------------------------------------------------===//

Error BTFDedupState::dedupPrimitives() {
  uint32_t N = Builder.typesCount();
  for (uint32_t Id = 1; Id <= N; ++Id) {
    const BTF::CommonType *T = Builder.findType(Id);
    if (!T || !isPrimitiveKind(T->getKind()))
      continue;

    uint64_t H = TypeHash[Id];
    auto &Bucket = HashBuckets[H];

    bool Found = false;
    for (uint32_t CanonId : Bucket) {
      clearHypot();
      if (isEquiv(Id, CanonId)) {
        Map[Id] = CanonId;
        Found = true;
        break;
      }
    }
    if (!Found)
      Bucket.push_back(Id);
  }

  return Error::success();
}

Error BTFDedupState::dedupComposites() {
  uint32_t N = Builder.typesCount();
  for (uint32_t Id = 1; Id <= N; ++Id) {
    if (Map[Id] != Id)
      continue;

    const BTF::CommonType *T = Builder.findType(Id);
    if (!T || !isCompositeKind(T->getKind()))
      continue;

    uint64_t H = TypeHash[Id];
    auto &Bucket = HashBuckets[H];

    bool Found = false;
    for (uint32_t CanonId : Bucket) {
      if (CanonId == Id)
        continue;

      clearHypot();
      if (isEquiv(Id, CanonId)) {
        // Commit hypothetical mappings.
        for (uint32_t HId : HypotList)
          Map[HId] = HypotMap[HId];
        for (const auto &[FwdId, CompositeId] : PendingFwdResolutions)
          Map[FwdId] = CompositeId;
        Found = true;
        break;
      }
    }

    clearHypot();
    if (!Found)
      Bucket.push_back(Id);
  }

  return Error::success();
}

//===----------------------------------------------------------------------===//
// Pass 4: Resolve unambiguous forward declarations
//===----------------------------------------------------------------------===//

Error BTFDedupState::resolveFwds() {
  DenseMap<uint32_t, uint32_t> UniqueCompositesByName;
  uint32_t N = Builder.typesCount();

  for (uint32_t Id = 1; Id <= N; ++Id) {
    if (Map[Id] != Id)
      continue;

    const BTF::CommonType *T = Builder.findType(Id);
    if (!T || !isCompositeKind(T->getKind()))
      continue;

    uint32_t NameOff = dedupStrOff(T->NameOff);
    auto [It, Inserted] = UniqueCompositesByName.try_emplace(NameOff, Id);
    if (!Inserted)
      It->second = 0;
  }

  for (uint32_t Id = 1; Id <= N; ++Id) {
    if (Map[Id] != Id)
      continue;

    const BTF::CommonType *T = Builder.findType(Id);
    if (!T || T->getKind() != BTF::BTF_KIND_FWD)
      continue;

    auto It = UniqueCompositesByName.find(dedupStrOff(T->NameOff));
    if (It == UniqueCompositesByName.end() || It->second == 0)
      continue;

    const BTF::CommonType *Composite = Builder.findType(It->second);
    if (!isFwdCompatibleWithComposite(T, Composite))
      continue;

    Map[Id] = It->second;
  }

  return Error::success();
}

//===----------------------------------------------------------------------===//
// Pass 3: Reference type dedup
//===----------------------------------------------------------------------===//

Error BTFDedupState::dedupRefs() {
  uint32_t N = Builder.typesCount();
  RefState.assign(N + 1, RefDedupState::Unprocessed);

  for (uint32_t Id = 1; Id <= N; ++Id) {
    const BTF::CommonType *T = Builder.findType(Id);
    if (!T)
      continue;

    uint32_t Kind = T->getKind();
    if (isPrimitiveKind(Kind) || isCompositeKind(Kind))
      continue;
    if (Error E = dedupRefType(Id).takeError())
      return E;
  }

  return Error::success();
}

Expected<uint32_t> BTFDedupState::dedupRefType(uint32_t Id) {
  Id = resolve(Id);
  if (Id == 0)
    return 0u;

  const BTF::CommonType *T = Builder.findType(Id);
  if (!T)
    return createStringError(inconvertibleErrorCode(),
                             "invalid BTF type id %u", Id);

  uint32_t Kind = T->getKind();
  if (isPrimitiveKind(Kind) || isCompositeKind(Kind))
    return Id;

  if (RefState[Id] == RefDedupState::Done)
    return Id;
  if (RefState[Id] == RefDedupState::InProgress)
    return createStringError(inconvertibleErrorCode(),
                             "cycle detected in BTF reference dedup at type %u",
                             Id);

  RefState[Id] = RefDedupState::InProgress;

  auto Fail = [&](Error E) -> Expected<uint32_t> {
    RefState[Id] = RefDedupState::Unprocessed;
    return std::move(E);
  };

  MutableArrayRef<uint8_t> Bytes = Builder.getMutableTypeBytes(Id);
  if (Bytes.size() < sizeof(BTF::CommonType))
    return Fail(createStringError(inconvertibleErrorCode(),
                                  "truncated BTF type record %u", Id));

  auto *MutT = reinterpret_cast<BTF::CommonType *>(Bytes.data());
  uint8_t *TailPtr = Bytes.data() + sizeof(BTF::CommonType);

  auto DedupTypeRef = [&](uint32_t &TypeRef) -> Error {
    if (TypeRef == 0)
      return Error::success();
    Expected<uint32_t> NewType = dedupRefType(TypeRef);
    if (!NewType)
      return NewType.takeError();
    TypeRef = *NewType;
    return Error::success();
  };

  switch (Kind) {
  case BTF::BTF_KIND_PTR:
  case BTF::BTF_KIND_TYPEDEF:
  case BTF::BTF_KIND_VOLATILE:
  case BTF::BTF_KIND_CONST:
  case BTF::BTF_KIND_RESTRICT:
  case BTF::BTF_KIND_FUNC:
  case BTF::BTF_KIND_VAR:
  case BTF::BTF_KIND_DECL_TAG:
  case BTF::BTF_KIND_TYPE_TAG:
    if (Error E = DedupTypeRef(MutT->Type))
      return Fail(std::move(E));
    break;
  case BTF::BTF_KIND_ARRAY: {
    auto *Arr = reinterpret_cast<BTF::BTFArray *>(TailPtr);
    if (Error E = DedupTypeRef(Arr->ElemType))
      return Fail(std::move(E));
    if (Error E = DedupTypeRef(Arr->IndexType))
      return Fail(std::move(E));
    break;
  }
  case BTF::BTF_KIND_FUNC_PROTO: {
    auto *Params = reinterpret_cast<BTF::BTFParam *>(TailPtr);
    if (Error E = DedupTypeRef(MutT->Type))
      return Fail(std::move(E));
    for (unsigned I = 0, N = MutT->getVlen(); I < N; ++I)
      if (Error E = DedupTypeRef(Params[I].Type))
        return Fail(std::move(E));
    break;
  }
  case BTF::BTF_KIND_DATASEC: {
    auto *Vars = reinterpret_cast<BTF::BTFDataSec *>(TailPtr);
    for (unsigned I = 0, N = MutT->getVlen(); I < N; ++I)
      if (Error E = DedupTypeRef(Vars[I].Type))
        return Fail(std::move(E));
    break;
  }
  default:
    RefState[Id] = RefDedupState::Done;
    return Id;
  }

  uint64_t H = hashType(Id);
  auto &Bucket = HashBuckets[H];

  uint32_t CanonId = Id;
  for (uint32_t CandidateId : Bucket) {
    clearHypot();
    if (isEquiv(Id, CandidateId)) {
      CanonId = CandidateId;
      break;
    }
  }

  clearHypot();
  Map[Id] = CanonId;
  if (CanonId == Id)
    Bucket.push_back(Id);

  RefState[Id] = RefDedupState::Done;
  return CanonId;
}

//===----------------------------------------------------------------------===//
// Pass 4-5: Compaction and remapping
//===----------------------------------------------------------------------===//

Error BTFDedupState::compact() {
  uint32_t N = Builder.typesCount();
  BTFBuilder NewBuilder;
  DenseMap<uint32_t, uint32_t> StrMap;
  auto MapStr = [&](uint32_t OldOff) -> uint32_t {
    uint32_t DedupOff = dedupStrOff(OldOff);
    auto It = StrMap.find(DedupOff);
    if (It != StrMap.end())
      return It->second;
    StringRef S = Builder.findString(DedupOff);
    uint32_t NewOff = NewBuilder.addString(S);
    StrMap[DedupOff] = NewOff;
    return NewOff;
  };

  StrMap[0] = 0;
  OldToNew.assign(N + 1, 0);
  for (uint32_t Id = 1; Id <= N; ++Id) {
    if (Map[Id] != Id)
      continue;

    const BTF::CommonType *T = Builder.findType(Id);
    if (!T)
      continue;

    BTF::CommonType NewHeader = *T;
    NewHeader.NameOff = MapStr(T->NameOff);
    uint32_t NewId = NewBuilder.addType(NewHeader);
    OldToNew[Id] = NewId;

    ArrayRef<uint8_t> TypeBytes = Builder.getTypeBytes(Id);
    if (TypeBytes.size() > sizeof(BTF::CommonType)) {
      ArrayRef<uint8_t> Tail = TypeBytes.slice(sizeof(BTF::CommonType));
      SmallVector<uint8_t, 64> TailCopy(Tail.begin(), Tail.end());
      uint8_t *TailPtr = TailCopy.data();

      switch (T->getKind()) {
      case BTF::BTF_KIND_STRUCT:
      case BTF::BTF_KIND_UNION: {
        auto *M = reinterpret_cast<BTF::BTFMember *>(TailPtr);
        for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
          M[I].NameOff = MapStr(M[I].NameOff);
        break;
      }
      case BTF::BTF_KIND_ENUM: {
        auto *E = reinterpret_cast<BTF::BTFEnum *>(TailPtr);
        for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
          E[I].NameOff = MapStr(E[I].NameOff);
        break;
      }
      case BTF::BTF_KIND_ENUM64: {
        auto *E = reinterpret_cast<BTF::BTFEnum64 *>(TailPtr);
        for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
          E[I].NameOff = MapStr(E[I].NameOff);
        break;
      }
      case BTF::BTF_KIND_FUNC_PROTO: {
        auto *P = reinterpret_cast<BTF::BTFParam *>(TailPtr);
        for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
          P[I].NameOff = MapStr(P[I].NameOff);
        break;
      }
      default:
        break;
      }

      for (uint8_t B : TailCopy)
        NewBuilder.addTail(B);
    }
  }

  for (uint32_t Id = 1; Id <= N; ++Id) {
    if (OldToNew[Id] != 0)
      continue;
    uint32_t CanonId = resolve(Id);
    OldToNew[Id] = OldToNew[CanonId];
  }

  for (uint32_t NewId = 1; NewId <= NewBuilder.typesCount(); ++NewId) {
    MutableArrayRef<uint8_t> Bytes = NewBuilder.getMutableTypeBytes(NewId);
    if (Bytes.empty())
      continue;

    auto *T = reinterpret_cast<BTF::CommonType *>(Bytes.data());
    uint8_t *TailPtr = Bytes.data() + sizeof(BTF::CommonType);

    if (BTFBuilder::hasTypeRef(T->getKind()) && T->Type != 0) {
      if (T->Type < OldToNew.size())
        T->Type = OldToNew[T->Type];
    }

    switch (T->getKind()) {
    case BTF::BTF_KIND_ARRAY: {
      auto *A = reinterpret_cast<BTF::BTFArray *>(TailPtr);
      if (A->ElemType != 0 && A->ElemType < OldToNew.size())
        A->ElemType = OldToNew[A->ElemType];
      if (A->IndexType != 0 && A->IndexType < OldToNew.size())
        A->IndexType = OldToNew[A->IndexType];
      break;
    }
    case BTF::BTF_KIND_STRUCT:
    case BTF::BTF_KIND_UNION: {
      auto *M = reinterpret_cast<BTF::BTFMember *>(TailPtr);
      for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
        if (M[I].Type != 0 && M[I].Type < OldToNew.size())
          M[I].Type = OldToNew[M[I].Type];
      break;
    }
    case BTF::BTF_KIND_FUNC_PROTO: {
      auto *P = reinterpret_cast<BTF::BTFParam *>(TailPtr);
      for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
        if (P[I].Type != 0 && P[I].Type < OldToNew.size())
          P[I].Type = OldToNew[P[I].Type];
      break;
    }
    case BTF::BTF_KIND_DATASEC: {
      auto *D = reinterpret_cast<BTF::BTFDataSec *>(TailPtr);
      for (unsigned I = 0, VN = T->getVlen(); I < VN; ++I)
        if (D[I].Type != 0 && D[I].Type < OldToNew.size())
          D[I].Type = OldToNew[D[I].Type];
      break;
    }
    default:
      break;
    }
  }

  Builder = std::move(NewBuilder);
  return Error::success();
}

//===----------------------------------------------------------------------===//
// Main entry point
//===----------------------------------------------------------------------===//

Error BTFDedupState::run() {
  uint32_t N = Builder.typesCount();
  if (N == 0)
    return Error::success();

  Map.resize(N + 1);
  for (uint32_t I = 0; I <= N; ++I)
    Map[I] = I;
  HypotMap.assign(N + 1, BTF_UNPROCESSED);

  if (Error E = dedupStrings())
    return E;

  TypeHash.resize(N + 1, 0);
  for (uint32_t Id = 1; Id <= N; ++Id)
    TypeHash[Id] = hashType(Id);

  if (Error E = dedupPrimitives())
    return E;
  if (Error E = dedupComposites())
    return E;
  if (Error E = resolveFwds())
    return E;
  if (Error E = dedupRefs())
    return E;
  if (Error E = compact())
    return E;

  return Error::success();
}

} // anonymous namespace

Error llvm::BTF::dedup(BTFBuilder &Builder) {
  BTFDedupState State(Builder);
  return State.run();
}
