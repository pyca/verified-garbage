module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp1

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint5
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2
import VerifiedGarbage.Proof.Rsa.Arm.RvHalving

/-! # A candidate on ARMv7: the halvings (`halving_vp`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n halveStep)
open VG.Impl.RsaKeyGen.Arm.Key (notS)

section
variable {P : CP}

theorem halfBit_eq : halfBit = bitOf sBit aHm ++ (notS sBit sBit ++ ([.ldr .r2 .r8 sTc,
    .dp .add .r2 .r2 (.reg .r1), .str .r2 .r8 sTc] : List Instr)) := rfl

/-- Whether `m` is even, after `k` halvings. -/
def evb (P : CP) (k : Nat) (σ : State) : Bool := decide ((hv P σ k).1 % 2 = 0)

def AB (P : CP) (k : Nat) (σ : State) : Nat → Nat :=
  upd (upd (AH P k σ) aH1 (hv P σ k).1) aH2 ((hv P σ k).1 / 2)
abbrev LB : List Nat := aH2 :: aH1 :: LH

def VB (P : CP) (k : Nat) (σ : State) : Nat → Nat :=
  upd (upd (VH P k σ) sBit (b2n (evb P k σ))) sTc ((hv P σ k).2 + b2n (evb P k σ))
abbrev LSB : List Nat := sTc :: sBit :: LSH

theorem not_odd (x : Nat) : 1 - b2n (decide (x % 2 = 1)) = b2n (decide (x % 2 = 0)) := by
  by_cases h : x % 2 = 0
  · simp [h, VG.Proof.Rsa.b2n]
  · have : x % 2 = 1 := by omega
    simp [this, VG.Proof.Rsa.b2n]

theorem halfBody_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ) {k : Nat} (hk : k < 8 * P.L) :
    VP (HS P E k) halfBody (fun σ s => HS P E (k + 1) σ s ∧ s.z = decide (8 * P.L - (k + 1) = 0)) := by
  simp only [halfBody, seqs]
  have eA : ∀ σ, AH P k σ aHm = (hv P σ k).1 := fun σ => by simp only [AH, upd_self]
  -- `aH1 := m`, `aH2 := m / 2`.
  refine VP.seq (St.pcopy copyH1_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.pcopy copyH2_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.pmov11 mov11_taint) ?_
  refine VP.seq ((St.phalf halfH2_taint (by simp)).mono (fun _ _ h => h) fun σ s h =>
    (h.mono (A' := AB P k) (L' := LB) (V' := VH P k) (LS' := LSH) (fun j hj => ⟨by mem_sub, ?_⟩)
      fun j hj => ⟨hj, rfl⟩ : St P E (AB P k) LB (VH P k) LSH σ s)) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [AB, upd, ↓reduceIte, eA]
  -- `sBit := m` even, `t +=` it.
  rw [halfBit_eq]
  refine VP.seq ((VP.block_append (St.pbitOf bitHm_taint (by simp) (by decide))
    (St.pnotAdd notAdd_taint (by simp) (by simp) (fun σ _ => by
      simp only [upd_self]; exact VG.Proof.Rsa.b2n_le _) (fun σ e => ?_))).mono (fun _ _ h => h) fun σ s h =>
    (h.mono (A' := AB P k) (L' := LB) (V' := VB P k) (LS' := LSB) (fun j hj => ⟨hj, rfl⟩)
      fun j hj => ⟨by mem_sub, ?_⟩ : St P E (AB P k) LB (VB P k) LSB σ s)) ?_
  · have pre := hE σ e
    have := hv_le (P := P) σ k
    have := pre.k2
    simp (config := {decide := true}) only [VH, upd, ↓reduceIte]
    omega
  · have hm : AB P k σ aHm = (hv P σ k).1 := by simp (config := {decide := true}) only [AB, upd, ↓reduceIte, eA]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [upd, ↓reduceIte, VB, VH, hm, evb, not_odd]
  -- `m` selected.
  refine VP.seq ((St.psel selHm_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    (fun σ _ => by simp (config := {decide := true}) only [VB, upd, ↓reduceIte]; exact VG.Proof.Rsa.b2n_le _)).mono
    (fun _ _ h => h) fun σ s h =>
    (h.mono (A' := fun σ => upd (AB P k σ) aHm (hv P σ (k + 1)).1) (L' := aHm :: LB) (V' := VB P k) (LS' := LSB)
      (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨hj, rfl⟩ :
      St P E (fun σ => upd (AB P k σ) aHm (hv P σ (k + 1)).1) (aHm :: LB) (VB P k) LSB σ s)) ?_
  · have key : (if VB P k σ sBit = 0 then AB P k σ aH1 else AB P k σ aH2) = (hv P σ (k + 1)).1 := by
      rw [hv_succ]
      simp (config := {decide := true}) only [VB, upd, ↓reduceIte, AB, evb, halveStep]
      by_cases h2 : (hv P σ k).1 % 2 = 0 <;> simp [h2, VG.Proof.Rsa.b2n]
    rw [key]
  -- The count.
  refine (St.pcntNext cntNext_taint (by simp) (fun σ e => ?_)).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ⟨?_, ?_⟩
  · have := (hE σ e).k2
    simp (config := {decide := true}) only [VB, VH, upd, ↓reduceIte]
    omega
  · refine h.mono (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) only [AH, AB, upd, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · simp (config := {decide := true}) only [VB, VH, upd, ↓reduceIte]; omega
      · simp (config := {decide := true}) only [VB, VH, upd, ↓reduceIte, hv_succ, halveStep, evb]
        by_cases h2 : (hv P σ k).1 % 2 = 0 <;> simp [h2, VG.Proof.Rsa.b2n]
      all_goals simp (config := {decide := true}) only [VB, VH, upd, ↓reduceIte]
  · rw [z]
    have := (hE σ h.1).k2
    simp (config := {decide := true}) only [VB, VH, upd, ↓reduceIte]
    simp only [decide_eq_decide]; omega

theorem halving_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (S3 P E) halving (HS P E (8 * P.L)) := by
  refine halfInit_vp.seq ?_
  let I := fun n σ s => n ≤ 8 * P.L ∧ HS P E (8 * P.L - n) σ s
  have hl := VP.loop (I := I) (body := halfBody) (c := .ne) (Q := HS P E (8 * P.L)) (fun n => ?_)
  · refine VP.ofImp (p := 0 < P.L) (fun σ s h => by have := (hE σ h.1).k1; omega) fun hL => ?_
    refine (hl (8 * P.L - 1)).mono (fun σ s h => ⟨by omega, ?_⟩) fun _ _ h => h
    rw [show 8 * P.L - (8 * P.L - 1 + 1) = 0 by omega]; exact h
  · refine VP.ofImp (p := n + 1 ≤ 8 * P.L) (fun σ s h => h.1) fun hn => ?_
    refine (halfBody_vp hE (k := 8 * P.L - (n + 1)) (by omega)).mono (fun σ s h => h.2)
      fun σ s ⟨h, z⟩ => ⟨?_, fun h0 => ?_, fun hp => ⟨by omega, ?_⟩⟩
    · show some (!s.z) = some (decide (0 < n))
      rw [z, show 8 * P.L - (8 * P.L - (n + 1) + 1) = n by omega]
      by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero]
    · subst h0; rwa [show 8 * P.L - (0 + 1) + 1 = 8 * P.L by omega] at h
    · rwa [show 8 * P.L - (n + 1) + 1 = 8 * P.L - n by omega] at h

end

end VG.Proof.Dsa.Arm.Prime
