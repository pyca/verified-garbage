module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCT1
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCT1
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCorrect
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverExp
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCorrect
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvRest
meta import VerifiedGarbage.Proof.Rsa.RecoverExp
meta import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots

/-!
# `vg_rsa_recover_primes` on PPC64LE: constant time of the candidates

`cand_ct`: the candidates, as many as `recoverPrimes` tries, which is
public; each one is checked by the taint analysis from the registers that
hold the lengths, the pointers and the candidate.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Spec.Rsa (recoverPrimes recoverTries primesKey)
open VG.Impl.Rsa.PPC64LE.Recover (candLoop candBody)

theorem tries_eq (s0 : State) : (primesKey (nB s0) (eB s0) (dB s0)).2 =
    if Spec.Rsa.modulusValid (nV s0) (kK s0) then (recoverPrimes (nV s0) (eV s0) (dV s0)).2 else 0 := by
  rw [pk_eq]
  split
  · generalize recoverPrimes (nV s0) (eV s0) (dV s0) = R
    obtain ⟨o, t⟩ := R
    cases o with
    | none => rfl
    | some pq => obtain ⟨p, q⟩ := pq; rfl
  · rfl

/-- With `n` valid and `d e` odd and above 1, the tries are `recoverPrimes.go`'s. -/
theorem nt_eq {s0 : State} (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true)
    (odd : dV s0 * eV s0 % 2 = 1) (two : 2 ≤ dV s0 * eV s0) : (primesKey (nB s0) (eB s0) (dB s0)).2 = nt s0 := by
  have h1 : ¬(dV s0 * eV s0 < 2 ∨ (dV s0 * eV s0 - 1) % 2 = 1) := by omega
  rw [tries_eq, ite_eq_left hmv, VG.Proof.Rsa.recoverPrimes_go h1, ← mV_eq odd]

/-- Before the candidate `j`. -/
def CI (d : RvD) (j : Nat) (u : State) : Prop :=
  ∃ s0, R0 d s0 ∧ NOk s0 ∧ Par s0 ∧ (primesKey (nB s0) (eB s0) (dB s0)).2 = nt s0 ∧ CF s0 u ∧
    u.gpr .r24 = BitVec.ofNat 64 j ∧ j < nt s0 ∧ gos s0 recoverTries = gos s0 (recoverTries - j)

/-- After the last candidate. -/
def CE (d : RvD) (u : State) : Prop :=
  ∃ s0, R0 d s0 ∧ NOk s0 ∧ CP s0 (jL s0) u ∧ gos s0 recoverTries = gos s0 (recoverTries - jL s0)

theorem pins_CI {j : Nat} : Pins (fun d => CI d j) [.r21, .r23, .r24, .r25, .r26, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, -, -, -, c₁, j₁, -⟩ ⟨b, hb, -, -, -, c₂, j₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [c₁.r21, c₂.r21]; exact ha.reg hb (by decide)
  · rw [c₁.r23, c₂.r23]; exact ha.reg hb (by decide)
  · rw [j₁, j₂]
  · rw [c₁.r25, c₂.r25]; exact ha.reg hb (by decide)
  · rw [c₁.r26, c₂.r26, ha.cB hb]
  · rw [c₁.ws.r29, c₂.ws.r29, ha.k hb]
  · rw [c₁.ws.r30, c₂.ws.r30, ha.k hb]
  · rw [c₁.ws.r31, c₂.ws.r31]; exact ha.arg hb (by decide)

theorem candBody_ct {j : Nat} : RelCT isa (Two fun d => CI d j) candBody fun _ _ => True :=
  two_taint _ pins_CI (by taint_decide)

/-- Before the candidates. -/
def CL0 (d : RvD) (u : State) : Prop :=
  ∃ s0, R0 d s0 ∧ NOk s0 ∧ Par s0 ∧ (primesKey (nB s0) (eB s0) (dB s0)).2 = nt s0 ∧ CF s0 u

theorem pins_CL0 : Pins CL0 [.r21, .r23, .r25, .r26, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, -, -, -, c₁⟩ ⟨b, hb, -, -, -, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [c₁.r21, c₂.r21]; exact ha.reg hb (by decide)
  · rw [c₁.r23, c₂.r23]; exact ha.reg hb (by decide)
  · rw [c₁.r25, c₂.r25]; exact ha.reg hb (by decide)
  · rw [c₁.r26, c₂.r26, ha.cB hb]
  · rw [c₁.ws.r29, c₂.ws.r29, ha.k hb]
  · rw [c₁.ws.r30, c₂.ws.r30, ha.k hb]
  · rw [c₁.ws.r31, c₂.ws.r31]; exact ha.arg hb (by decide)

theorem CI0_of {d : RvD} {u : State} (h : CL0 d u) : WP isa (.block [.li .r24 0]) u (CI d 0) := by
  obtain ⟨s0, hs, hn, hp, ht, c⟩ := h
  refine WP.mono (WP.keep [.r24] (Q := fun x => x.gpr .r24 = BitVec.ofNat 64 0 ∧ x.mem = u.mem) (by prun)
    (by decide)) fun u1 ⟨⟨a24, m1⟩, k1⟩ => ?_
  have c1 := c.of_keep (show KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u.mem u1.mem by
    rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _) (by simp) (by simp) k1 (c.ws.of_keep k1)
  exact ⟨s0, hs, hn, hp, ht, c1, a24, nt_pos s0, rfl⟩

/-- After the candidate `j`, with the loop's condition. -/
def CG (j : Nat) (d : RvD) (t : State) : Prop :=
  ∃ s0, R0 d s0 ∧ NOk s0 ∧ Par s0 ∧ (primesKey (nB s0) (eB s0) (dB s0)).2 = nt s0 ∧ j < nt s0 ∧
    gos s0 recoverTries = gos s0 (recoverTries - j) ∧ CP s0 j t ∧
    t.gpr .r0 = b64 (decide (j + 1 < 100) && !(fres s0 j).isSome)

theorem CG_of {d : RvD} {j : Nat} {u : State} (h : CI d j u) : WP isa candBody u (CG j d) := by
  obtain ⟨s0, hs, hn, hp, ht, c, h24, hj, hg⟩ := h
  have n2 := nt_le s0
  exact WP.mono (candBody_ok hn hp (by omega) c h24) fun t ⟨cp, r0⟩ => ⟨s0, hs, hn, hp, ht, hj, hg, cp, r0⟩

/-- The loop's condition after the candidate `j`: whether `j + 1` are fewer than the tries. -/
theorem CG.cond {d : RvD} {j : Nat} {t : State} (h : CG j d t) :
    isa.eval (.nonzero .d .r0) t = some (decide (j + 1 < d.tries)) := by
  obtain ⟨s0, hs, hn, hp, ht, hj, hg, -, r0⟩ := h
  have cc := VG.Proof.Rsa.cand_cond (nV s0) (tT s0) (rR s0) (j := j) hj hg
  rw [← ok_eq hn hp] at cc
  rw [eval_nonzero_ofNat' t .r0 (by have := b2n_le (decide (j + 1 < 100) && !(fres s0 j).isSome); omega) r0]
  rw [show d.tries = nt s0 by rw [← ht, ← hs.2]; rfl]
  rw [← cc, Bool.not_not]
  cases (decide (j + 1 < 100) && !(fres s0 j).isSome) <;> rfl

theorem CG.next {d : RvD} {j : Nat} {t : State} (h : CG j d t) (hl : j + 1 < d.tries) : CI d (j + 1) t := by
  obtain ⟨s0, hs, hn, hp, ht, hj, hg, cp, r0⟩ := h
  have dt : d.tries = nt s0 := by rw [← ht, ← hs.2]; rfl
  have hl' : j + 1 < nt s0 := dt ▸ hl
  have cc := VG.Proof.Rsa.cand_cond (nV s0) (tT s0) (rR s0) (j := j) hj hg
  rw [← ok_eq hn hp] at cc
  refine ⟨s0, hs, hn, hp, ht, cp.cf, cp.r24, hl', ?_⟩
  have hok : (fres s0 j).isSome = false := by
    have : (decide (j + 1 < 100) && !(fres s0 j).isSome) = true := by
      rw [← Bool.not_not (decide _ && _), cc]; simpa using hl'
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this.2
  have hs' : Spec.Rsa.recoverStep (nV s0) (tT s0) (rR s0) (j + 2) = none := by
    rw [ok_eq hn hp] at hok
    exact Option.not_isSome_iff_eq_none.mp (by rw [hok]; decide)
  have n2 := nt_le s0
  rw [hg]; show recoverPrimes.go _ _ _ _ = recoverPrimes.go _ _ _ _
  rw [VG.Proof.Rsa.go_eq _ _ _ (show j < recoverTries by unfold recoverTries; omega), hs']

theorem CG.last {d : RvD} {j : Nat} {t : State} (h : CG j d t) (hl : ¬ j + 1 < d.tries) : CE d t := by
  obtain ⟨s0, hs, hn, hp, ht, hj, hg, cp, r0⟩ := h
  have e : j = jL s0 := by
    have : d.tries = nt s0 := by rw [← ht, ← hs.2]; rfl
    simp only [jL]; omega
  subst e
  exact ⟨s0, hs, hn, cp, hg⟩

/-- The loop's invariant: before the candidate `j`, `tries - 1 - j` left. -/
def LI (m : Nat) (s₁ s₂ : State) : Prop := ∃ j, Two (fun d s => CI d j s ∧ m = d.tries - 1 - j) s₁ s₂

theorem loop_step (n : Nat) : RelCT isa (LI n) candBody fun s₁ s₂ =>
    isa.eval (.nonzero .d .r0) s₁ = isa.eval (.nonzero .d .r0) s₂ ∧
      (isa.eval (.nonzero .d .r0) s₁ = some false → Two CE s₁ s₂) ∧
      (isa.eval (.nonzero .d .r0) s₁ = some true → ∃ m < n, LI m s₁ s₂) := by
  refine RelCT.exists_ fun j => ?_
  have hct : RelCT isa (Two fun d s => CI d j s ∧ n = d.tries - 1 - j) candBody fun _ _ => True :=
    candBody_ct.mono (fun _ _ ⟨d, ⟨a, _⟩, ⟨b, _⟩, sp⟩ => ⟨d, a, b, sp⟩) fun _ _ h => h
  refine (two_post (Ψ := fun d t => CG j d t ∧ n = d.tries - 1 - j) hct fun _ _ ⟨h, e⟩ =>
    WP.mono (CG_of h) fun _ g => ⟨g, e⟩).mono (fun _ _ h => h) fun s₁ s₂ ⟨d, ⟨g₁, e⟩, ⟨g₂, _⟩, sp⟩ => ?_
  rw [g₁.cond, g₂.cond]
  refine ⟨rfl, fun hf => ⟨d, g₁.last ?_, g₂.last ?_, sp⟩, fun ht => ?_⟩
  · simpa using hf
  · simpa using hf
  · have hl : j + 1 < d.tries := by simpa using ht
    exact ⟨d.tries - 1 - (j + 1), by omega, j + 1, d, ⟨g₁.next hl, rfl⟩, ⟨g₂.next hl, rfl⟩, sp⟩

/-- The candidates. -/
theorem cand_ct : RelCT isa (Two CL0) candLoop (Two CE) := by
  unfold candLoop
  refine RelCT.seq (two_post (two_taint _ pins_CL0 (by taint_decide)) fun _ _ h => CI0_of h) ?_
  refine RelCT.mono (RelCT.exists_ (P := LI) fun m => RelCT.loop (M := isa) (body := candBody) (c := .nonzero .d .r0) (Q := Two CE) LI loop_step m)
    (fun s₁ s₂ ⟨d, h₁, h₂, hsp⟩ => ⟨d.tries - 1 - 0, 0, d, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩, hsp⟩) fun _ _ h => h

end VG.Proof.Rsa.PPC64LE.Recover
