module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Returning the DSA acceptance bit in the AAPCS64 result register -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem result_ok {s : State} {B : Addr} {Z : Nat} {valid : Bool}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block SignVerify.result) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 valid.toNat ∧ t.mem = s.mem ∧ Keep [.x0, .x3] s t := by
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t =>
    t.gpr .x0 = BitVec.ofNat 64 valid.toNat ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  unfold SignVerify.result
  brun [Core.field, h0, field_enc .mask, fieldAddress,
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ), hm]
  cases valid <;> rfl

end VG.Proof.Dsa.AArch64
