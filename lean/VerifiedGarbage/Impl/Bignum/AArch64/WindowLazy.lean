module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core


/-! One-pass final reduction for internal Montgomery squares. The enclosing
window restores a canonical residue with its last multiplication. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def word (i : Nat) : List Instr :=
 [ld .x3 .x16 (8*i), ld .x4 .x17 (8*i), .logic .and .x .x4 .x4 .x15,
  .sbcs .x .x3 .x3 .x4, st .x3 .x5 (8*i)]
def words : List Instr := (List.range 4).flatMap word

def code : Prog isa :=
 .seq (.block [mov .x16 .x8, mov .x17 .x10,
  .lsl .x .x14 .x12 3, .add .x .x14 .x8 .x14, ld .x15 .x14,
  .sub .x .x15 .x7 .x15, .lsr .x .x14 .x12 2, .subs .x .x3 .x7 .x7])
 (countLoop .x14 (words ++
  [.addImm .x .x16 .x16 32, .addImm .x .x17 .x17 32, .addImm .x .x5 .x5 32]))

end VG.Impl.Bignum.AArch64.WindowLazy
