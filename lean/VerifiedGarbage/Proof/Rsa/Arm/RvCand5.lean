module

public import VerifiedGarbage.Proof.Rsa.Arm.RvCand4
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2

/-! # `vg_rsa_recover_primes` on ARMv7: the candidates (`candLoop_vp`)

The loop runs as many times as `recoverPrimes` tries candidates, which the
contract makes public (`P.nt`): before the candidate `j`, those before it
failed (`gos 100 = gos (100 - j)`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n sqIter sqStep sqStart sqRes)
open VG.Spec.Rsa (recoverPrimes recoverStep recoverTries)

/-- `recoverPrimes`'s candidates from the `k`-th last. -/
abbrev gos (P : RP) (σ : State) (k : Nat) : Option (Nat × Nat) × Nat := recoverPrimes.go P.n (tv P σ) (rv P σ) k

/-- The stage before the candidate `j`, those before having failed. -/
abbrev Ej (P : RP) (E : State → Prop) (j : Nat) : State → Prop := fun σ => E σ ∧ gos P σ 100 = gos P σ (100 - j)

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- No candidate tried. -/
theorem St.pcandZero :
    VP (St P E A L AW LW V LS P.w nArr) (.block candZero)
      (St P E A L AW LW (fun σ => upd (V σ) sCand 0) (sCand :: LS) P.w nArr) := by
  refine VP.ctx candZero_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  obtain ⟨g1, hw1⟩ := h.reg hw (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine g1.strSlot_m (hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem) hw1 (d := sCand) (r := .r1) (by decide)
    fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [u1.gpr] at ht; exact ht

theorem St.monoE {E' : State → Prop} {A' : State → Nat → Nat} {L' : List Nat} {AW' : State → Nat → Nat}
    {LW' : List Nat} {V' : State → Nat → Nat} {LS' : List Nat} {v N : Nat} {σ s : State}
    (h : St P E A L AW LW V LS v N σ s) (he : E' σ)
    (hl : ∀ j ∈ L', j ∈ L ∧ A σ j = A' σ j) (hlW : ∀ j ∈ LW', j ∈ LW ∧ AW σ j = AW' σ j)
    (hls : ∀ d ∈ LS', d ∈ LS ∧ V σ d = V' σ d) : St P E' A' L' AW' LW' V' LS' v N σ s :=
  ⟨he, h.2.1.mono hl hlW hls, h.2.2⟩

end

section
variable {P : RP}

theorem ok_eq (σ : State) (j : Nat) (ht1 : 1 ≤ tv P σ) (htc : tv P σ ≤ P.c) :
    (sqst P σ j P.c).2.2 = (recoverStep P.n (tv P σ) (rv P σ) (j + 2)).isSome := by
  rw [← VG.Proof.Rsa.sq_result (n := P.n) (r := rv P σ) (g := j + 2) ht1 htc]
  show _ = (sqRes (sqst P σ j P.c)).isSome
  simp only [sqRes]
  cases (sqst P σ j P.c).2.2 <;> rfl

/-- The candidates. -/
theorem candLoop_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (h101 : 101 < P.n) (hcl : P.c < 2 ^ 31) (hc0 : 0 < P.c)
    (hnt : 1 ≤ P.nt) (hnt' : P.nt ≤ 100) {E : State → Prop}
    (hE : ∀ σ, E σ → 1 ≤ tv P σ ∧ tv P σ ≤ P.c ∧ rv P σ < 2 ^ P.c ∧ (gos P σ 100).2 = P.nt) :
    VP (fun σ s => E σ ∧ KM P σ (AWh P σ P.c) [wR] (Vh P σ P.c) [sTc] s) candLoop
      (Cf P (Ej P E (P.nt - 1)) (P.nt - 1)) := by
  refine VP.seq (St.pcandZero (P := P) (E := E) (A := fun _ => AM P) (L := liveM) (AW := fun σ => AWh P σ P.c)
    (LW := [wR]) (V := fun σ => Vh P σ P.c) (LS := [sTc])) ?_
  have hl := VP.loop (I := fun m σ s => m ≤ P.nt ∧ Cs P (Ej P E (P.nt - m)) (P.nt - m) σ s) (body := candBody)
    (c := .ne) (Q := Cf P (Ej P E (P.nt - 1)) (P.nt - 1)) (fun n => VP.pure fun hle => ?_) (P.nt - 1)
  · refine hl.mono (fun σ s h => ⟨by omega, ?_⟩) fun _ _ h => h
    rw [show P.nt - (P.nt - 1 + 1) = 0 by omega]
    refine St.monoE h ⟨h.1, rfl⟩ (fun x hx => ⟨hx, rfl⟩) (fun x hx => ⟨hx, rfl⟩) ?_
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simp, by simp [upd, Vc]⟩
    · exact ⟨by simp, by simp [upd, Vc, Vh, sTc, sCand, sCnt]⟩
  · have hj : P.nt - (n + 1) < 100 := by omega
    refine (candBody_vp hn h101 hcl hc0 hj fun σ e => ⟨(hE σ e.1).2.1, (hE σ e.1).2.2.1⟩).mono (fun _ _ h => h)
      fun σ s ⟨hc, z⟩ => ?_
    obtain ⟨ht1, htc, _, hnt⟩ := hE σ hc.1.1
    have hgo := hc.1.2
    have hnt2 : (recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries).2 = P.nt := hnt
    have hgo2 : recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries =
        recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - (n + 1))) := hgo
    have cc := VG.Proof.Rsa.cand_cond P.n (tv P σ) (rv P σ) (j := P.nt - (n + 1)) (by rw [hnt2]; omega) hgo2
    rw [hnt2, ← ok_eq σ _ ht1 htc] at cc
    have ev : isa.eval .ne s = some (decide (0 < n)) := by
      show some (!s.z) = some (decide (0 < n))
      rw [z, cc]
      congr 1
      simp only [decide_eq_decide]
      omega
    refine ⟨ev, fun h0 => ?_, fun hp => ⟨by omega, ?_⟩⟩
    · subst h0; exact hc
    · -- The candidate failed: `ok` is false, and the next one is tried.
      have hok : (sqst P σ (P.nt - (n + 1)) P.c).2.2 = false := by
        have : (decide (P.nt - (n + 1) + 1 < 100) && !(sqst P σ (P.nt - (n + 1)) P.c).2.2) = true := by
          rw [← Bool.not_not (decide _ && _), cc]; simp only [decide_eq_true_eq]; omega
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
        exact this.2
      have hs : recoverStep P.n (tv P σ) (rv P σ) (P.nt - (n + 1) + 2) = none := by
        rw [ok_eq σ _ ht1 htc] at hok
        exact Option.not_isSome_iff_eq_none.mp (by rw [hok]; decide)
      have hj100 : P.nt - (n + 1) < recoverTries := by unfold recoverTries; omega
      have g : recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - (n + 1))) =
          recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - (n + 1) + 1)) := by
        rw [VG.Proof.Rsa.go_eq _ _ _ hj100, hs]
      refine St.monoE hc ⟨hc.1.1, ?_⟩ ?_ (fun x hx => ⟨hx, rfl⟩) ?_
      · show recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries =
          recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - n))
        rw [hgo2, g, show P.nt - (n + 1) + 1 = P.nt - n by omega]
      · intro x hx
        refine ⟨List.mem_cons_of_mem _ hx, ?_⟩
        simp only [liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Aq, upd, mY, aNg, aO, mR2, aOne, aZ, aN]
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨by simp, by simp [upd, Vc, sCand, sCnt]; omega⟩
        · exact ⟨by simp, by simp [upd, Vc, Vq, sTc, sCand, sCnt, sK, sDone, sOk]⟩

end

end VG.Proof.Rsa.Arm.Recover
