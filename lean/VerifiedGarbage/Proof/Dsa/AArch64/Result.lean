module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
public import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Returning the DSA acceptance bit -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem result_ok {s : State} {B : Addr} {Z : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block SignVerify.result) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 valid.toNat ∧ t.mem = s.mem ∧ Keep [.x0, .x3, .x4] s t := by
  refine WP.mono (WP.keep [.x0, .x3, .x4] (Q := fun t =>
    t.gpr .x0 = BitVec.ofNat 64 valid.toNat ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨ht, hmem⟩, hk⟩ => ⟨ht, hmem, hk⟩
  unfold SignVerify.result Core.field
  brun [hdi, field_enc, hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ), hm]
  cases valid <;> decide

end VG.Proof.Dsa.AArch64
