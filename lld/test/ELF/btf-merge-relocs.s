# REQUIRES: x86
## Verify that --btf-merge relocates .BTF before deduplication.

# RUN: rm -rf %t && split-file %s %t && cd %t
# RUN: llvm-mc -filetype=obj -triple=x86_64 a.s -o a.o
# RUN: llvm-mc -filetype=obj -triple=x86_64 b.s -o b.o
# RUN: ld.lld --btf-merge --image-base=0x0 --section-start=.data=0x1000 a.o b.o -o merged
# RUN: ld.lld -r a.o b.o -o reloc.o
# RUN: ld.lld --btf-merge --image-base=0x0 --section-start=.data=0x1000 reloc.o -o merged-from-reloc
# RUN: llvm-objdump -h merged | FileCheck %s --check-prefix=SECTIONS
# RUN: llvm-objdump -s -j .BTF merged | FileCheck %s --check-prefix=BTF
# RUN: llvm-objdump -s -j .BTF merged-from-reloc | FileCheck %s --check-prefix=BTF

# SECTIONS: .BTF
# SECTIONS-NOT: .rela.BTF

# BTF: Contents of section .BTF:
# BTF: 00000000 04000000
# BTF: 04000000 04000000

#--- a.s
.text
.globl _start
_start:
  ret

.data
.globl a_data
a_data:
  .long 0

.section .BTF,"",@progbits
.short 0xeb9f           # magic
.byte 1                 # version
.byte 0                 # flags
.long 24                # hdr_len
.long 0                 # type_off
.long 56                # type_len
.long 56                # str_off
.long 13                # str_len
## Type 1: INT "int" size=4
.long 1                 # name_off
.long 0x01000000        # info: kind=INT(1), vlen=0
.long 4                 # size
.long 0x00000020        # encoding: bits=32
## Type 2: VAR "a" type=int linkage=static
.long 5                 # name_off
.long 0x0e000000        # info: kind=VAR(14), vlen=0
.long 1                 # type=int
.long 0                 # linkage=VAR_STATIC
## Type 3: DATASEC ".data" with one VAR entry relocated to a_data.
.long 7                 # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 4                 # size
.long 2                 # var type id
.long a_data            # offset
.long 4                 # size
## String table: "\0int\0a\0.data\0"
.byte 0
.ascii "int"
.byte 0
.ascii "a"
.byte 0
.ascii ".data"
.byte 0

#--- b.s
.text
.globl b_fn
b_fn:
  ret

.data
.globl b_data
b_data:
  .long 0

.section .BTF,"",@progbits
.short 0xeb9f           # magic
.byte 1                 # version
.byte 0                 # flags
.long 24                # hdr_len
.long 0                 # type_off
.long 56                # type_len
.long 56                # str_off
.long 13                # str_len
## Type 1: INT "int" size=4
.long 1                 # name_off
.long 0x01000000        # info: kind=INT(1), vlen=0
.long 4                 # size
.long 0x00000020        # encoding: bits=32
## Type 2: VAR "b" type=int linkage=static
.long 5                 # name_off
.long 0x0e000000        # info: kind=VAR(14), vlen=0
.long 1                 # type=int
.long 0                 # linkage=VAR_STATIC
## Type 3: DATASEC ".data" with one VAR entry relocated to b_data.
.long 7                 # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 4                 # size
.long 2                 # var type id
.long b_data            # offset
.long 4                 # size
## String table: "\0int\0b\0.data\0"
.byte 0
.ascii "int"
.byte 0
.ascii "b"
.byte 0
.ascii ".data"
.byte 0
