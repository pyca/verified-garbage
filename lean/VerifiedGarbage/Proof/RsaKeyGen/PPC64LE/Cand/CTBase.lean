module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Tail
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: what two runs share

Two runs from states the contract relates agree on `pubOf`: the argument
registers, the arguments on the stack, the table's address, `e`'s octets and
what the candidate leaks (`candidateLeak`). With enough random octets for a
candidate, they then take the same branches (`schedOf_eq`): the candidate is
too close to `p` in both or neither (`close_agree`), and so on; a candidate
rejected in both was read from the same octets (`rej_take`), so the branches
that follow a rejection agree too (`gcd_agree`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont
open VG.Spec.RsaKeyGen (Candidate)
open VG.Proof.RsaKeyGen (schedOf leakOf seg afterDraw)

/-- What two runs share. -/
structure CD where
  regs : List (BitVec 64)
  stk : List (BitVec 64)
  sym : Addr
  e : List Byte
  lk : List Nat

/-- The public data of the call from `s0`. -/
def pubOf (s0 : State) : CD :=
  ⟨argRegs.map s0.gpr, (List.range 3).map (PPC64LE.stackArg s0), s0.syms VG.Impl.RsaKeyGen.TrialTable32.symbol,
    eB s0, Spec.RsaKeyGen.candidateLeak (oL s0) (eB s0) (pB s0) (rB s0)⟩

/-- A call the contract allows, with the public data `a`. -/
def KRel (a : CD) (s0 : State) : Prop := CIn s0 ∧ TabOk s0 ∧ pubOf s0 = a

theorem KRel.reg {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) {r : Reg} (hr : r ∈ argRegs) :
    s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp ((congrArg CD.regs h₁.2.2).trans (congrArg CD.regs h₂.2.2).symm) r hr

theorem KRel.arg {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) {i : Nat} (hi : i < 3) :
    PPC64LE.stackArg s₁ i = PPC64LE.stackArg s₂ i :=
  List.map_inj_left.mp ((congrArg CD.stk h₁.2.2).trans (congrArg CD.stk h₂.2.2).symm) i (List.mem_range.mpr hi)

theorem KRel.sym {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) :
    s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s₂.syms VG.Impl.RsaKeyGen.TrialTable32.symbol :=
  (congrArg CD.sym h₁.2.2).trans (congrArg CD.sym h₂.2.2).symm

theorem KRel.e {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) : eB s₁ = eB s₂ :=
  (congrArg CD.e h₁.2.2).trans (congrArg CD.e h₂.2.2).symm

theorem KRel.lk {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) :
    Spec.RsaKeyGen.candidateLeak (oL s₁) (eB s₁) (pB s₁) (rB s₁) =
      Spec.RsaKeyGen.candidateLeak (oL s₂) (eB s₂) (pB s₂) (rB s₂) :=
  (congrArg CD.lk h₁.2.2).trans (congrArg CD.lk h₂.2.2).symm

theorem KRel.oL_eq {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) : oL s₁ = oL s₂ := by
  show (s₁.gpr .r4).toNat = (s₂.gpr .r4).toNat
  rw [h₁.reg h₂ (r := .r4) (by decide)]

theorem KRel.rL_eq {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) : rL s₁ = rL s₂ := by
  show (PPC64LE.stackArg s₁ 0).toNat = (PPC64LE.stackArg s₂ 0).toNat
  rw [h₁.arg h₂ (i := 0) (by decide)]

/-- The branches of the call from `s0`. -/
def schedS (s0 : State) : VG.Proof.RsaKeyGen.Sched :=
  schedOf (oL s0) (Spec.Rsa.os2ip (eB s0)) (Spec.RsaKeyGen.otherPrime (pB s0)) (rB s0)

theorem KRel.sched {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁) :
    schedS s₁ = schedS s₂ := by
  have hp := h₁.1
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have eo := h₁.oL_eq h₂
  have er := h₁.rL_eq h₂
  have hl := h₁.lk h₂
  rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq, h₁.e h₂, eo] at hl
  unfold Spec.RsaKeyGen.candidateOp at hl
  unfold schedS
  rw [h₁.e h₂, eo]
  have h0 : 0 < oL s₂ := by rw [← eo]; simp only [oL]; omega
  exact VG.Proof.RsaKeyGen.schedOf_eq h0 (by rw [bytesAt_length, bytesAt_length, er])
    (by rw [bytesAt_length, ← eo]; exact hk) hl

/-- A rejected candidate was read from at least its own octets. -/
theorem rej_take {L e : Nat} {p : Option Nat} {r rest : Spec.RsaKeyGen.Rand} (hL : 0 < L)
    (h : Spec.RsaKeyGen.candidateStep (8 * L) e p r = some (.rejected, rest)) : L ≤ r.length - rest.length := by
  rw [VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ hL] at h
  split at h
  · rename_i hk
    unfold afterDraw at h
    split at h
    · cases h
    · split at h
      · rename_i _ _
        rcases hp : Spec.RsaKeyGen.primalityTest (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (seg r 0 L)))
            (r.drop L) with _ | ⟨b, rest'⟩
        · rw [hp] at h; cases h
        · rw [hp] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          have := VG.Proof.RsaKeyGen.primalityTest_rest hp
          rw [← h.2]
          simp only [List.length_drop] at this
          omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, List.length_drop]
        omega
  · cases h

/-- Two candidates rejected with the same leak were read from the same
octets. -/
theorem rej_same {L e : Nat} {p₁ p₂ : Option Nat} {r₁ r₂ rest₁ rest₂ : Spec.RsaKeyGen.Rand} (hL : 0 < L)
    (h₁ : Spec.RsaKeyGen.candidateStep (8 * L) e p₁ r₁ = some (.rejected, rest₁))
    (h₂ : Spec.RsaKeyGen.candidateStep (8 * L) e p₂ r₂ = some (.rejected, rest₂))
    (h : leakOf r₁ (Spec.RsaKeyGen.candidateStep (8 * L) e p₁ r₁) =
      leakOf r₂ (Spec.RsaKeyGen.candidateStep (8 * L) e p₂ r₂)) :
    r₁.take L = r₂.take L := by
  have t₁ := rej_take hL h₁
  have t₂ := rej_take hL h₂
  rw [h₁, h₂] at h
  simp only [leakOf, List.cons.injEq, true_and] at h
  obtain ⟨hu, he⟩ := VG.Proof.RsaKeyGen.take_eq_of_map (by omega) (by omega) h
  have := congrArg (List.take L) he
  rw [VG.Proof.RsaKeyGen.take_take_of_le t₁, VG.Proof.RsaKeyGen.take_take_of_le (hu ▸ t₁)] at this
  exact this

/-- The candidate, as `schedOf` reads it. -/
abbrev candS (s0 : State) : Nat :=
  Spec.RsaKeyGen.candidate (8 * oL s0) (Spec.Rsa.os2ip ((rB s0).take (oL s0)))

theorem leak_step {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) :
    leakOf (rB s₁) (Spec.RsaKeyGen.candidateStep (8 * oL s₁) (Spec.Rsa.os2ip (eB s₁))
        (Spec.RsaKeyGen.otherPrime (pB s₁)) (rB s₁)) =
      leakOf (rB s₂) (Spec.RsaKeyGen.candidateStep (8 * oL s₂) (Spec.Rsa.os2ip (eB s₂))
        (Spec.RsaKeyGen.otherPrime (pB s₂)) (rB s₂)) := by
  have hl := h₁.lk h₂
  rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl
  exact hl

theorem close_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁) :
    Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) =
      Spec.RsaKeyGen.tooClose (8 * oL s₂) (Spec.RsaKeyGen.otherPrime (pB s₂)) (candS s₂) := by
  have e := congrArg VG.Proof.RsaKeyGen.Sched.close (h₁.sched h₂ hk)
  unfold schedS at e
  rwa [VG.Proof.RsaKeyGen.sched_close, VG.Proof.RsaKeyGen.sched_close] at e

theorem comp_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false) :
    Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁) =
      Spec.RsaKeyGen.obviouslyComposite (8 * oL s₂) (candS s₂) := by
  have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
  have e := congrArg VG.Proof.RsaKeyGen.Sched.comp (h₁.sched h₂ hk)
  unfold schedS at e
  rwa [VG.Proof.RsaKeyGen.sched_comp hc, VG.Proof.RsaKeyGen.sched_comp hc₂] at e

/-- A candidate trial division rejects is rejected. -/
theorem step_comp {L e : Nat} {p : Option Nat} {r : Spec.RsaKeyGen.Rand} (hL : 0 < L) (hk : L ≤ r.length)
    (hc : Spec.RsaKeyGen.tooClose (8 * L) p
      (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false)
    (ho : Spec.RsaKeyGen.obviouslyComposite (8 * L)
      (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = true) :
    Spec.RsaKeyGen.candidateStep (8 * L) e p r = some (.rejected, r.drop L) := by
  rw [VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ hL, VG.Proof.RsaKeyGen.ite_t hk]
  unfold afterDraw seg
  rw [List.drop_zero, hc, ho]
  rfl

/-- Candidates trial division rejects are the same. -/
theorem comp_same {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false)
    (ho : Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁) = true) : candS s₁ = candS s₂ := by
  have hp := h₁.1
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have eo := h₁.oL_eq h₂
  have er := h₁.rL_eq h₂
  have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
  have ho₂ := (comp_agree h₁ h₂ hk hc).symm.trans ho
  have h0 : 0 < oL s₁ := by simp only [oL]; omega
  have t := rej_same (L := oL s₁) h0
    (step_comp h0 (by rw [bytesAt_length]; exact hk) hc ho)
    (eo ▸ step_comp (eo ▸ h0) (by rw [bytesAt_length, ← eo, ← er]; exact hk) hc₂ ho₂)
    (by have := leak_step h₁ h₂; rw [← eo, ← h₁.e h₂] at this; exact this)
  unfold candS
  rw [← eo, t]

theorem gcd_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false) :
    Nat.gcd (candS s₁ - 1) (Spec.Rsa.os2ip (eB s₁)) = 1 ↔ Nat.gcd (candS s₂ - 1) (Spec.Rsa.os2ip (eB s₂)) = 1 := by
  rw [h₁.e h₂]
  cases ho : Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁)
  · have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
    have ho₂ := (comp_agree h₁ h₂ hk hc).symm.trans ho
    have e := congrArg VG.Proof.RsaKeyGen.Sched.gbad (h₁.sched h₂ hk)
    unfold schedS at e
    rw [VG.Proof.RsaKeyGen.sched_gbad hc ho, VG.Proof.RsaKeyGen.sched_gbad hc₂ ho₂, h₁.e h₂] at e
    constructor
    · intro hg; simp [hg] at e; simpa using e
    · intro hg; simp [hg] at e; simpa using e
  · rw [comp_same h₁ h₂ hk hc ho]

theorem shape_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false)
    (ho : Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁) = false)
    (hg : Nat.gcd (candS s₁ - 1) (Spec.Rsa.os2ip (eB s₁)) = 1) :
    VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candS s₁) ((rB s₁).drop (oL s₁))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candS s₂) ((rB s₂).drop (oL s₂))) := by
  have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
  have ho₂ := (comp_agree h₁ h₂ hk hc).symm.trans ho
  have hg₂ := (gcd_agree h₁ h₂ hk hc).mp hg
  have e := congrArg VG.Proof.RsaKeyGen.Sched.mr (h₁.sched h₂ hk)
  unfold schedS at e
  rwa [VG.Proof.RsaKeyGen.sched_mr hc ho (by simp [hg]), VG.Proof.RsaKeyGen.sched_mr hc₂ ho₂ (by simp [hg₂])] at e

end VG.Proof.RsaKeyGen.PPC64LE.Cand
