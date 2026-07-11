# REQUIRES: x86
## Verify that final-link native BTF keeps ordinary DATASECs alone, but when a
## .data..percpu DATASEC is present it rebuilds the final native layout without
## dropping unrelated VAR types.

# RUN: rm -rf %t && split-file %s %t && cd %t
# RUN: llvm-mc -filetype=obj -triple=x86_64 nopercpu.s -o nopercpu.o
# RUN: ld.lld --btf-merge --image-base=0x0 --section-start=.data=0x1000 nopercpu.o -o nopercpu
# RUN: llvm-objcopy --dump-section .BTF=nopercpu.btf nopercpu
# RUN: %python %S/../../../llvm/test/CodeGen/BPF/BTF/print_btf.py nopercpu.btf | FileCheck %s --check-prefix=NO-PERCPU

# RUN: llvm-mc -filetype=obj -triple=x86_64 mixed.s -o mixed.o
# RUN: ld.lld --btf-merge --image-base=0x0 --section-start=.data=0x1000 --section-start=.data..percpu=0x2000 mixed.o -o mixed
# RUN: llvm-objcopy --dump-section .BTF=mixed.btf mixed
# RUN: %python %S/../../../llvm/test/CodeGen/BPF/BTF/print_btf.py mixed.btf | FileCheck %s --check-prefix=WITH-PERCPU

# NO-PERCPU: [1] INT 'int' size=4 bits_offset=0 nr_bits=32 encoding=(none)
# NO-PERCPU: [2] VAR 'regular' type_id=1, linkage=static
# NO-PERCPU: [3] DATASEC '.data' size=4 vlen=1
# NO-PERCPU-NEXT: type_id=2 offset=0 size=4

# WITH-PERCPU: [1] INT 'int' size=4 bits_offset=0 nr_bits=32 encoding=(none)
# WITH-PERCPU: [2] VAR 'regular' type_id=1, linkage=static
# WITH-PERCPU: [3] VAR 'percpu' type_id=1, linkage=static
# WITH-PERCPU: FUNC_PROTO
# WITH-PERCPU: FUNC '__x64_sys_fork' type_id={{[0-9]+}} linkage=global
# WITH-PERCPU: DATASEC '.data..percpu' size={{[0-9]+}} vlen=1
# WITH-PERCPU-NEXT: type_id=3 offset={{[0-9]+}} size=4
# WITH-PERCPU-NOT: DATASEC '.data'
# WITH-PERCPU-NOT: DATASEC '.apicdrivers'
# WITH-PERCPU-NOT: DATASEC '.bss'

#--- nopercpu.s
.text
.globl _start
_start:
  ret
.type __x64_sys_fork,@function
.globl __x64_sys_fork
__x64_sys_fork:
  ret

.data
.globl regular
regular:
  .long 0

.section .BTF,"",@progbits
.short 0xeb9f           # magic
.byte 1                 # version
.byte 0                 # flags
.long 24                # hdr_len
.long 0                 # type_off
.long 56                # type_len
.long 56                # str_off
.long 19                # str_len
## Type 1: INT "int" size=4
.long 1                 # name_off
.long 0x01000000        # info: kind=INT(1), vlen=0
.long 4                 # size
.long 0x00000020        # encoding: bits=32
## Type 2: VAR "regular" type=int linkage=static
.long 5                 # name_off
.long 0x0e000000        # info: kind=VAR(14), vlen=0
.long 1                 # type=int
.long 0                 # linkage=VAR_STATIC
## Type 3: DATASEC ".data" with one VAR entry relocated to regular.
.long 13                # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 4                 # size
.long 2                 # var type id
.long regular           # offset
.long 4                 # size
## String table: "\0int\0regular\0.data\0"
.byte 0
.ascii "int"
.byte 0
.ascii "regular"
.byte 0
.ascii ".data"
.byte 0

#--- mixed.s
.text
.globl _start
_start:
  ret
.type __x64_sys_fork,@function
.globl __x64_sys_fork
__x64_sys_fork:
  ret

.data
.globl regular
regular:
  .long 0

.section .data..percpu,"aw",@progbits
.globl percpu
percpu:
  .long 0

.section .BTF,"",@progbits
.short 0xeb9f           # magic
.byte 1                 # version
.byte 0                 # flags
.long 24                # hdr_len
.long 0                 # type_off
.long 168               # type_len
.long 168               # str_off
.long 73                # str_len
## Type 1: INT "int" size=4
.long 1                 # name_off
.long 0x01000000        # info: kind=INT(1), vlen=0
.long 4                 # size
.long 0x00000020        # encoding: bits=32
## Type 2: VAR "regular" type=int linkage=static
.long 5                 # name_off
.long 0x0e000000        # info: kind=VAR(14), vlen=0
.long 1                 # type=int
.long 0                 # linkage=VAR_STATIC
## Type 3: VAR "percpu" type=int linkage=static
.long 13                # name_off
.long 0x0e000000        # info: kind=VAR(14), vlen=0
.long 1                 # type=int
.long 0                 # linkage=VAR_STATIC
## Type 4: FUNC_PROTO "() -> int".
.long 0                 # name_off
.long 0x0d000000        # info: kind=FUNC_PROTO(13), vlen=0
.long 1                 # ret_type=int
## Type 5: extern FUNC "__x64_sys_fork" that should become global after the
## final native link finds the defined STT_FUNC symbol.
.long 20                # name_off
.long 0x0c000002        # info: kind=FUNC(12), linkage=extern
.long 4                 # type=FUNC_PROTO
## Type 6: DATASEC ".data" with one VAR entry relocated to regular.
.long 35                # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 4                 # size
.long 2                 # var type id
.long regular           # offset
.long 4                 # size
## Type 7: DATASEC ".data..percpu" with one VAR entry relocated to percpu.
.long 41                # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 4                 # size
.long 3                 # var type id
.long percpu            # offset
.long 4                 # size
## Type 8: zero-sized DATASEC ".apicdrivers" from input-object native BTF.
.long 55                # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 0                 # size
.long 2                 # var type id
.long regular           # offset
.long 4                 # size
## Type 9: zero-sized DATASEC ".bss" from input-object native BTF.
.long 68                # name_off
.long 0x0f000001        # info: kind=DATASEC(15), vlen=1
.long 0                 # size
.long 2                 # var type id
.long regular           # offset
.long 4                 # size
## String table: "\0int\0regular\0percpu\0__x64_sys_fork\0.data\0.data..percpu\0.apicdrivers\0.bss\0"
.byte 0
.ascii "int"
.byte 0
.ascii "regular"
.byte 0
.ascii "percpu"
.byte 0
.ascii "__x64_sys_fork"
.byte 0
.ascii ".data"
.byte 0
.ascii ".data..percpu"
.byte 0
.ascii ".apicdrivers"
.byte 0
.ascii ".bss"
.byte 0
