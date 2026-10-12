module

public import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase

/-!
# X25519 of the base point on x86 (32-bit)

`X25519(k, 9)` as `u = (Z + Y) / (Z - Y)` of `[k] B` on edwards25519
(`Proof/X25519/Edwards/Ladder.lean`), with Ed25519's fixed-base comb
(`Impl/Ed25519/X86/Comb.lean`): the scalar's bits are expanded one per byte
at byte 7168 of the workspace, as for `vg_ed25519_scalar_base` (after the
address of the comb's tables at byte `combTbl`), then clamped
as RFC 7748 §5 decodes the scalar (bits 0–2 and 255 cleared, bit 254 set);
the comb leaves `[k] B` in slots 0–3, and one inversion gives `u`, which is
reduced and written out.
-/

@[expose] public section

namespace VG.Impl.X25519.X86.Base
open VG VG.X86
open VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (sc freeze)

/-- Bit `q` of the scalar (byte `7168 + q` of the workspace) set to `v`. -/
def storeBit (q v : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 v)), .store8 (sc (7168 + q)) .al]

/-- RFC 7748 §5's clamping of the expanded scalar. -/
def clampBits : List Instr :=
  storeBit 0 0 ++ storeBit 1 0 ++ storeBit 2 0 ++ storeBit 255 0 ++ storeBit 254 1

/-- `Z + Y` in slot 0 and `Z - Y` in slot 2, which `invert` inverts into slot 15. -/
def uOps : List FieldOp := [.add 0 2 1, .sub 2 2 1]

def uMulOps : List FieldOp := [.mul 0 0 15]

/-- `u = (Z + Y) / (Z - Y)`, reduced, in slot 0 (bytes 64–95). -/
def uEncode : Prog isa :=
  .seq (.block (fieldCode uOps))
    (.seq Impl.Ed25519.X86.invert (.seq (.block (fieldCode uMulOps)) (.block (freeze 64))))

/-- The callee-saved registers saved, the clamped scalar's bits expanded, and `d` in slot 16. -/
def x25519BaseStart : List Instr := abiSave 2 ++ inputBits 1 32 ++ clampBits ++ fieldCode baseSetupOps

/-- After the comb's tables' address (`combAddr`). -/
def x25519BaseBody : Prog isa :=
  .seq (.block x25519BaseStart)
    (.seq combMultiply (.seq uEncode (.block (finishWords 64))))

def x25519Base : Code Instr Cond := .seq (combAddr 2) x25519BaseBody

end VG.Impl.X25519.X86.Base
