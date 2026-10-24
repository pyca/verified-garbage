module

public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.Octets

/-!
# `vg_rsa_private_checked` on PPC64LE: the outcome

The outcome from what the calls returned and wrote (`final_ok`): the check's
logic on every target (`Proof.Rsa.check_logic`, `Proof.Rsa.outcome_eq`),
without the status of `vg_rsa_public_precompute`, which this check does not
read: `n`'s values are invalid only when `n` is, and then so is the CRT's
result.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.Proof.Rsa

theorem final_ok {m m' : Mem} {O M : Addr} {k : Nat} {cs es acc : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (cs.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hpub : ∀ ws, Spec.Rsa.publicPrecompute nB = some ws →
      Spec.Rsa.written m O k (es.setWidth 32) (Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k)))
    (heq : acc = 0#64 ↔ Spec.Rsa.bytesAt m O k = xB)
    (hout : Spec.Rsa.bytesAt m' O k =
      if cs &&& es &&& 1 = 1 ∧ decide (acc = 0#64) = true then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' O k ((result (cs &&& es &&& 1) (decide (acc = 0#64))).setWidth 32)
      (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  let r₃ : BitVec 64 := if (Spec.Rsa.publicPrecompute nB).isSome then 1 else 0
  have hv : cs &&& es &&& 1 = gOf es cs r₃ := by
    by_cases hp : (Spec.Rsa.publicPrecompute nB).isSome
    · simp only [gOf, r₃, hp, ↓reduceIte]
      rw [BitVec.and_assoc (es &&& cs) 1 1, BitVec.and_self, BitVec.and_comm cs es]
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length = false := by
        rw [← precompute_isSome]; simpa using hp
      have hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB = none := by
        simp only [Spec.Rsa.privateCrt, hm]; rfl
      rw [hc] at hcrt
      have h1 : cs &&& 1 = 0 := by
        rcases gOf_cases cs cs 1 with h | h <;> simp only [gOf] at h
        all_goals
          have := and1_of_setWidth_zero hcrt.1
          have e : cs &&& cs &&& 1 &&& 1 = cs &&& 1 := by
            rw [BitVec.and_self, BitVec.and_assoc, BitVec.and_self]
          rw [e] at h
          first | exact h | exact absurd h this
      simp only [gOf, r₃, hp, Bool.false_eq_true, ↓reduceIte]
      rw [show cs &&& es &&& 1 = (cs &&& 1) &&& es by ac_rfl, h1]
      rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_and, BitVec.and_zero, BitVec.zero_and]
  have h3 : match Spec.Rsa.publicPrecompute nB with
      | some _ => r₃.setWidth 32 = 1
      | none => r₃.setWidth 32 = 0 := by
    cases hpc : Spec.Rsa.publicPrecompute nB <;> simp [r₃, hpc]
  have h2 : (Spec.Rsa.publicPrecompute nB).isSome = true →
      match Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k) with
      | some y => es.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m O k = y
      | none => es.setWidth 32 = 0 := by
    intro hs
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hs
    have := hpub ws hws
    cases hpo : Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k) <;>
      simp only [hpo, Spec.Rsa.written] at this ⊢
    · exact this.1
    · exact this
  have hL := check_logic (r₁ := cs) (xB := xB) h3 h2
  have hd : decide (acc = 0#64) = decide (Spec.Rsa.bytesAt m O k = xB) := decide_eq_decide.mpr heq
  refine outcome_eq hn hx hcrt (by rw [hv, hd]; exact hL.1) ?_
  have hc : (gOf es cs r₃ = 1 ∧ decide (Spec.Rsa.bytesAt m O k = xB) = true) ↔
      released cs nB eB xB (Spec.Rsa.bytesAt m M k) := by
    rw [decide_eq_true_eq]; exact hL.2
  rw [hout, hv, hd]
  by_cases hr : released cs nB eB xB (Spec.Rsa.bytesAt m M k)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hc.mpr hr)), ite_eq_left_of_eq_true _ _ (eq_true hr)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hr (hc.mp h)), ite_eq_right_of_eq_false _ _ (eq_false hr)]

end VG.Proof.Rsa.PPC64LE.Priv
