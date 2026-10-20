module
public import VerifiedGarbage.Impl.Bignum.Arm.Select
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasState

import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Termination and exact value of an in-place selection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem selectAliasRow_ok (s : State) {base : BitVec 32} {size o a b n : Nat}
    (ctx : SelectCtx s base size o a b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa selectRow s (SelectInv s base o a b n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectInv s base o a b n i t
  unfold selectRow
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (selectAliasBody_ok ctx hi (by omega) hc) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp0
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp10
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp12
    · simpa only [Nat.sub_zero] using hcount
    · simp only [val32, ite_self]

end VG.Proof.Bignum.Arm
