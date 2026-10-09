import VerifiedGarbage.Impl.Ed25519.Arm.Word
import VerifiedGarbage.Proof.X25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Field16.Call

/-!
# Ed25519 on ARMv7: field elements in the working space

The field arithmetic is X25519's (`Proof/X25519/Arm/Field`, `AddSub`, `Mul`,
`Cswap`, `Slots`), in a working space of 8192 bytes (`Ctx`); a product is a
call of `vg_gf25519_r16_mul`, whose own working space is `ACC` and the 32
bytes after it.
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm

/-- `r0` holds the working space `b`, 8192 writable bytes. -/
abbrev Ctx := Proof.X25519.Arm.CtxN 4096

theorem ACC_eq : ACC = 1472 := rfl

/-- The field area `[64, 1632)` of the working space: the elements and the
product's own working space. -/
abbrev FA (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, 1568⟩

/-- The registers field code changes: the inlined operations' and a call's
(`r12` and `lr`). -/
abbrev fclob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .lr]

end VG.Proof.Ed25519.Arm
