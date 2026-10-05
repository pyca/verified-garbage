import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.Octets

/-!
# `vg_rsa_private_checked` on x86-64: the outcome

What the CRT returns and writes, followed by what the check returns and
releases (`check_ok`), is `privateChecked`'s outcome (`outcome_eq`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64

/-- The CRT's result `mB` (returning `rc`), and the check's of it (returning
`r` and writing `outB`), are the checked private operation's. -/
theorem outcome_eq {m m' : Mem} {M out : Addr} {k : Nat} {rc r : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (rc.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hr : r = checkResult rc nB eB xB (Spec.Rsa.bytesAt m M k))
    (hout : Spec.Rsa.bytesAt m' out k =
      if released rc nB eB xB (Spec.Rsa.bytesAt m M k) then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' out k (r.setWidth 32) (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  rw [Proof.Rsa.privateChecked_of_crt (hx.trans hn.symm)]
  cases hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB with
  | none =>
    rw [hc] at hcrt
    have h1 := and1_of_setWidth_zero hcrt.1
    have hrel : ¬ released rc nB eB xB (Spec.Rsa.bytesAt m M k) := fun h => h1 h.1
    simp only [checkResult, h1, false_and, ↓reduceIte] at hr
    simp only [hrel, ↓reduceIte] at hout
    exact ⟨by rw [hr]; rfl, hout⟩
  | some y =>
    rw [hc] at hcrt
    obtain ⟨hr1, hy⟩ := hcrt
    obtain ⟨hm, hs⟩ := Proof.Rsa.privateCrt_some hc
    have h1 := and1_of_setWidth_one hr1
    rw [hy] at hr hout
    by_cases he : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eB) = true
    · have hsome := hs eB he
      by_cases hp : Spec.Rsa.publicOpChecked nB eB y = some xB
      · have hrel : released rc nB eB xB y := ⟨h1, hm, hp⟩
        simp only [checkResult, h1, hm, hp, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
      · have hrel : ¬ released rc nB eB xB y := fun h => hp h.2.2
        simp only [checkResult, h1, hm, hsome, hp, and_self, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
    · have hnone : Spec.Rsa.publicOpChecked nB eB y = none := by
        simp only [Spec.Rsa.publicOpChecked, he]; rfl
      have hrel : ¬ released rc nB eB xB y := fun h => by
        have := h.2.2; rw [hnone] at this; cases this
      simp only [checkResult, hnone, Option.isSome_none, Bool.false_eq_true, and_false, ↓reduceIte] at hr
      simp only [hrel, ↓reduceIte] at hout
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by rw [hr]; rfl, hout⟩

end VG.Proof.Rsa.X86_64
