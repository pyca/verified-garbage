module

public import VerifiedGarbage.Impl.Md5.RISCV64
public import VerifiedGarbage.Impl.MdStream.RISCV64

/-!
# Streaming MD5: RISC-V implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`). `init(state = a0)` stores the
initial MD buffer (`initWords`); `update` and `finalize` are the generic
streaming code (`Impl/MdStream/RISCV64.lean`) calling `vg_md5_compress`,
with MD5's little-endian length field and digest, also stored a byte at a
time.
-/

@[expose] public section

namespace VG.Impl.Md5.RISCV64.Stream

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Impl.MdStream.RISCV64 (Params)

def init : Prog isa := MdStream.RISCV64.initWords Spec.Md5.H0.toList

/-- The message length in bits (`8 * count`), little-endian, at the end of
the buffer: its low word, then its high word. -/
def lenStore : List Instr :=
  .shift .sll .d .t1 .s4 3 :: storeLE32 .t1 .t3 .s1 72 ++
    .shift .srl .d .t1 .t1 32 :: storeLE32 .t1 .t3 .s1 76

/-- Word `k` of the final MD buffer to `out`, little-endian. -/
def outW (k : Nat) : List Instr := loadLE32 .t1 .t2 .s1 (4 * k) ++ storeLE32 .t1 .t2 .s3 (4 * k)

def params : Params where
  N := 16
  len := lenStore
  out := (List.range 4).flatMap outW

def update : Prog isa := MdStream.RISCV64.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.RISCV64.finalize params "vg_md5_compress" compress

end VG.Impl.Md5.RISCV64.Stream
