module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr10
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.MillerRabin.Arm.Body

/-! # A candidate on ARMv7: Miller–Rabin (`millerRabin_vp`)

An iteration (`body_vp`): Z iff it goes on, which the branches decide; and
the loop of iterations from `mrInit`, to the stage `QS`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.RsaKeyGen (goS shapeOf itersOf)
open VG.Proof.Dsa.Generation (DMrAt dmrS dwit dres)
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {P : CP} {E : State → Prop}

/-- The comparison ending an iteration: Z iff it goes on. -/
theorem cmp4_vp {n : Nat} : VP (GQ P E n) (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 4)])
    (fun σ s => isa.eval .eq s = some (decide (0 < n)) ∧ (n = 0 → QS P E σ s) ∧ (0 < n → MRI P E n σ s)) :=
  VP.kv cmp4_taint (fun _ _ h => by rcases h with ⟨_, h⟩ | ⟨_, h⟩; exacts [h.2.2, h.2.2.2.1.2.2]) fun σ s h => by
    rcases h with ⟨h0, e, k, hw⟩ | ⟨hp, h1, h2, mr, ⟨e, k, hw⟩, m⟩
    · refine k.ldr hw (d := sStat) (by simp) (r := .r1) (by decide) fun s1 k1 hw1 u1 => ?_
      refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨?_, fun _ => ⟨e, k1.of_rest (f.rest []) f.mem,
        hw1.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩, fun h => absurd h (by omega)⟩
      rw [isa_eq, z, u1.gpr, h0]
      simp only [upd_self]
      unfold statQ
      split <;> decide
    · refine k.ldr hw (d := sStat) (by simp) (r := .r1) (by decide) fun s1 k1 hw1 u1 => ?_
      refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨?_, fun h => absurd h (by omega),
        fun _ => ⟨h1, h2, mr, ⟨e, (k1.of_rest (f.rest []) f.mem).mono (fun j hj => ⟨hj, rfl⟩)
          (fun d hd => ⟨List.mem_cons_of_mem _ hd, upd_ne _ _ (by revert hd; revert d; decide)⟩),
          hw1.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩,
          (m.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem).of_rest (f.rest []) f.mem⟩⟩
      rw [isa_eq, z, u1.gpr]
      simp only [upd_self, decide_eq_true hp]
      rfl

/-- An iteration of Miller–Rabin, `n + 1` of them left. -/
theorem body_vp (v : RoundImpl) (hE : ∀ σ, E σ → In P σ ∧ EM P σ) (n : Nat) :
    VP (MRI P E (n + 1)) (Impl.Dsa.Arm.ProbablePrime.mrBody v.name v.code)
      (fun σ s => isa.eval .eq s = some (decide (0 < n)) ∧ (n = 0 → QS P E σ s) ∧ (0 < n → MRI P E n σ s)) := by
  refine VP.ofImp (p := n ≤ Nt P) (fun σ s h => by have := h.2.1; omega) fun hn => ?_
  have hk : Nt P + 1 - (n + 1) = Nt P - n := by omega
  simp only [Impl.Dsa.Arm.ProbablePrime.mrBody, seqs]
  refine (VP.seq (avFlag_vp (E := fun σ => E σ ∧ DMrAt (cv P σ) (chP P) (taP P σ) (tmP P σ) P.D (rB P σ) (Nt P - n) n)
    (k := Nt P - n) (fun σ e => by have := e.2.used; rwa [rB_length] at this))
    (VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2]) ?_ ?_) cmp4_vp)).mono
    (fun σ s ⟨_, _, mr, st, m⟩ => by
      rw [hk, Nat.add_sub_cancel] at mr
      rw [hk] at st
      exact ⟨⟨⟨st.1, mr⟩, st.2.1, st.2.2⟩, m⟩) (fun _ _ h => h)
  · refine VP.ofImp (p := ¬ P.D * (Nt P - n) + P.D ≤ P.rl) (fun σ s h => by
      have := h.2; rw [isa_eq, h.1.2] at this; simpa using this) fun hna => ?_
    refine (St.psetSM stat0_taint (by decide) (by decide) (by decide)).mono (fun σ s h => h.1.1)
      fun σ s ⟨⟨⟨e, mr⟩, h, hw⟩, m⟩ => ?_
    obtain ⟨pre, hm⟩ := hE σ e
    obtain ⟨-, hwb, -⟩ := mr_facts pre hm
    obtain ⟨hn0, hres⟩ := VG.Proof.Dsa.Generation.dmrAt_short mr hwb (by have := pre.sizes; omega)
      (by rw [rB_length]; exact hna)
    have hres' : resP P σ = none := hres
    refine .inl ⟨hn0, e, h.mono (fun j hj => ⟨hj, rfl⟩) fun d hd => ⟨by revert hd; revert d; decide, ?_⟩, hw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · simp (config := {decide := true}) only [upd, ↓reduceIte]
      unfold statQ; rw [hres']
    · simp (config := {decide := true}) only [upd, ↓reduceIte, VI]
      unfold usedQ; rw [hres', hn0, Nat.sub_zero]
  · refine VP.ofImp (p := P.D * (Nt P - n) + P.D ≤ P.rl) (fun σ s h => by
      have := h.2; rw [isa_eq, h.1.2] at this; simpa using this) fun hav => ?_
    rw [List.append_assoc, List.append_assoc]
    exact (VP.seqs_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (witnessLoad_vp (E := EK P E (Nt P - n) n) (k := Nt P - n) fun σ e => ⟨(hE σ e.1).1, e.2.2⟩)
      (VP.seqs_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (witnessFix_vp fun σ e => e.2.2)
        (VP.seqs_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (mrCall_vp v) (tail_vp hE hn)))).mono
      (fun σ s ⟨⟨⟨⟨⟨e, mr⟩, h, hw⟩, m⟩, _⟩, _⟩ => ⟨⟨⟨e, mr, hav⟩, h, hw⟩, m⟩) (fun _ _ h => h)

/-- Miller–Rabin on the candidate, from its Montgomery forms of 1 and −1. -/
theorem millerRabin_vp (v : RoundImpl) (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (SM P E) (Impl.Dsa.Arm.ProbablePrime.millerRabin v.name v.code) (QS P E) :=
  (mrInit_vp hE).seq (VP.loop (I := MRI P E) (body_vp v hE) (Nt P))

end

end VG.Proof.Dsa.Arm.Prime
