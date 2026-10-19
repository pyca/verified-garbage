module

public import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-! # ML-KEM CBD2 in sixteen byte lanes

Each lane computes the two signed differences plus two, in separate nibbles.
The nibbles are interleaved and widened before canonical reduction modulo q.

`code16` (`vg_mlkem16_cbd2`) writes 16-bit coefficients instead: the
coefficient of a nibble `f ≤ 4` is `(f - 2) mod q`, whose low and high bytes
two TBLs look up (`tables`), and ZIP1 and ZIP2 interleave into
halfwords.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Cbd16
open VG.AArch64

def constant (v : VReg) (a : VArr) (n : Nat) : List Instr :=
 [.movz .x .x9 (BitVec.ofNat 16 n) 0,.vop (.dup a v .x9)]
def out (off : Nat) (part : VPermOp) : List Instr :=
 [.vop (.perm part .h8 .v6 .v5 .v22),.vop (.add .s4 .v6 .v6 .v17),
 .vop (.sub .s4 .v7 .v6 .v16),.vop (.umin .v6 .v6 .v7),.strq .v6 .x1 off]
def words (off : Nat) (part : VPermOp) : List Instr :=
 [.vop (.perm part .b16 .v5 .v4 .v22)] ++ out off .zip1 ++ out (off+16) .zip2
def half (off : Nat) (part : VPermOp) : List Instr :=
 [.vop (.perm part .b16 .v4 .v2 .v3)] ++ words off .zip1 ++ words (off+32) .zip2
def prepare : List Instr :=
 [.vop (.shift .ushr .b16 .v1 .v0 1),
 .vop (.logic .and .v0 .v0 .v18),.vop (.logic .and .v1 .v1 .v18),.vop (.add .b16 .v0 .v0 .v1),
 .vop (.shift .ushr .b16 .v1 .v0 2),.vop (.logic .and .v0 .v0 .v19),
 .vop (.logic .and .v1 .v1 .v19),.vop (.add .b16 .v0 .v0 .v20),.vop (.sub .b16 .v0 .v0 .v1),
 .vop (.logic .and .v2 .v0 .v21),.vop (.shift .ushr .b16 .v3 .v0 4)]
def body : List Instr :=
 [.ldrq .v0 .x0 0] ++ prepare ++
 half 0 .zip1 ++ half 64 .zip2 ++
 [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 128,.subImm .x .x10 .x10 1]
def code : Prog isa :=
 .seq (.block (constant .v16 .s4 3329 ++ constant .v17 .s4 3327 ++
 constant .v18 .b16 0x55 ++ constant .v19 .b16 0x33 ++ constant .v20 .b16 0x22 ++ constant .v21 .b16 0x0f ++
 [.vop (.movi0 .v22),.movz .x .x10 8 0])) (.loop (.block body) (.nonzero .x .x10))

/-- The tables of `code16`: in bytes `f ≤ 4` of each doubleword, the low (`v16`) and high
(`v17`) bytes of `(f - 2) mod q`, which are `3327, 3328, 0, 1, 2`. -/
def tables : List Instr :=
 [.movz .x .x9 0x00FF 0,.movk .x .x9 0x0100 1,.movk .x .x9 0x0002 2,.vop (.dup .d2 .v16 .x9),
 .movz .x .x9 0x0D0C 0,.vop (.dup .d2 .v17 .x9)]
def grp16 (off : Nat) : List Instr :=
 [.vop (.tbl .v5 .v16 .v4),.vop (.tbl .v6 .v17 .v4),.vop (.perm .zip1 .b16 .v7 .v5 .v6),
 .vop (.perm .zip2 .b16 .v5 .v5 .v6),.strq .v7 .x1 off,.strq .v5 .x1 (off+16)]
def half16 (off : Nat) (part : VPermOp) : List Instr :=
 [.vop (.perm part .b16 .v4 .v2 .v3)] ++ grp16 off
def body16 : List Instr :=
 [.ldrq .v0 .x0 0] ++ prepare ++
 half16 0 .zip1 ++ half16 32 .zip2 ++
 [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 64,.subImm .x .x10 .x10 1]
def code16 : Prog isa :=
 .seq (.block (tables ++
 constant .v18 .b16 0x55 ++ constant .v19 .b16 0x33 ++ constant .v20 .b16 0x22 ++ constant .v21 .b16 0x0f ++
 [.movz .x .x10 8 0])) (.loop (.block body16) (.nonzero .x .x10))

end VG.Impl.MlKem.AArch64.Cbd16
