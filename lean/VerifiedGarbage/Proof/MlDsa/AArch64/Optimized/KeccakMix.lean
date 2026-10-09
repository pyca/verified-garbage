import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.MlDsa.AArch64.Optimized.KeccakMix
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Neon.Hw

/-- The measured schedule preserves every output bit in either lane. -/
theorem chi_eq (σ : Low) : ∀ i < 25,
    runLow Impl.MlDsa.AArch64.Optimized.KeccakMix.chi σ (vreg i) = runLow chi σ (vreg i) := by
  refine forall_lt_25 ?_
  simp only [runLow, Impl.MlDsa.AArch64.Optimized.KeccakMix.chi, chi, List.foldl_cons, List.foldl_nil,
    opLow, put, vreg, List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false, and_self]

theorem core_math (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) :
    CLanes (runLow (theta ++ rhoPi ++ Impl.MlDsa.AArch64.Optimized.KeccakMix.chi) σ) A := by
  have hc := Hw.core_math σ A h
  intro i hi
  simp only [runLow, List.foldl_append] at hc ⊢
  exact (chi_eq _ i hi).trans (hc i hi)

theorem core2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block ((theta ++ rhoPi ++ Impl.MlDsa.AArch64.Optimized.KeccakMix.chi).map Op.instr)) s
      fun t => Keep s t ∧ CPairs t A B := by
  refine WP.mono (ops_lanes _ s) fun t ⟨ht, hl⟩ => ⟨ht, ?_⟩
  have ha : ALanes (lane s 0) A := by
    intro i hi
    change vdword (s.v (vreg i)) 0 = _
    rw [hp i hi, vdword_ofVDwords_0, Proof.Sha3.getElem!_eq A hi]
  have hb : ALanes (lane s 1) B := by
    intro i hi
    change vdword (s.v (vreg i)) 1 = _
    rw [hp i hi, vdword_ofVDwords_1, Proof.Sha3.getElem!_eq B hi]
  intro i hi
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    change lane t 0 (vreg i) = _
    rw [hl 0 (by decide)]
    exact core_math (lane s 0) A ha i hi
  · rw [vdword_ofVDwords_1]
    change lane t 1 (vreg i) = _
    rw [hl 1 (by decide)]
    exact core_math (lane s 1) B hb i hi

theorem round2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.KeccakMix.round r)) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold Impl.MlDsa.AArch64.Optimized.KeccakMix.round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++ Impl.MlDsa.AArch64.Optimized.KeccakMix.chi.map Op.instr ++ iota =
    constant (Spec.Sha3.RC r) ++ (theta++rhoPi++Impl.MlDsa.AArch64.Optimized.KeccakMix.chi).map Op.instr ++ iota by
      simp only [List.map_append,List.append_assoc]]
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s1 ⟨h1,hv1,hrc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (core2_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s2 ⟨h2,hp2⟩ => ?_
  refine WP.mono (iota2_ok hp2 (Spec.Sha3.RC r) (by rw [h2.gpr,hrc,constantLow_RC r hr]))
    fun t ⟨h3,hpt⟩ => ⟨h1.trans (h2.core.trans (vchg_core h3)),?_⟩
  simpa only [Proof.Sha3.outState_eq] using hpt

theorem rounds2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.KeccakMix.rounds) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold Impl.MlDsa.AArch64.Optimized.KeccakMix.rounds
  refine wp_range_flatMap (M := isa)
    (fun k t => CoreKeep s t ∧ Pairs t
      ((List.range k).foldl Spec.Sha3.rnd A) ((List.range k).foldl Spec.Sha3.rnd B))
    (fun k t hk ⟨ht,hpt⟩ => ?_) 24 (Nat.le_refl _) s ⟨CoreKeep.refl _,hp⟩
  refine WP.mono (round2_ok hpt hk) fun u ⟨hu,hpu⟩ => ⟨ht.trans hu,?_⟩
  simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpu

/-- Neither SIMD lane is public; the fixed unrolled rounds have no data-dependent trace. -/
theorem rounds_ct :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
      (.block Impl.MlDsa.AArch64.Optimized.KeccakMix.rounds) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.KeccakMix
