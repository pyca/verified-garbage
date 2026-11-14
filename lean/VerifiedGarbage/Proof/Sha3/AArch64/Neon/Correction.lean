module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Vector
public import VerifiedGarbage.Proof.Sha3.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate

/-! ### `Sha3.AArch64.Neon.Column`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

def columnRegs (x : Nat) : List VReg := (List.range 5).map fun y => vreg (x+5*y)

/-- Apply a theta correction to the five words in one column. -/
theorem column_ok (x : Nat) (hx : x < 5) (s : State) :
    WP isa (.block ((List.range 5).map fun y =>
      .vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30))) s fun s' =>
      VChg (columnRegs x) s s' ∧ s'.v .v30 = s.v .v30 ∧
      ∀ i < 25, s'.v (vreg i) = if i%5 = x then s.v (vreg i) ^^^ s.v .v30 else s.v (vreg i) := by
  have h30 (y : Nat) (hy : y < 5) : VReg.v30 ≠ vreg (x+5*y) := by
    change vreg 30 ≠ vreg (x+5*y)
    rw [ne_eq,vreg_inj 30 (by decide) (x+5*y) (by omega_using [hx, hy])]; omega_using [hx, hy]
  have hm : ∀ y < 5, vreg (x+5*y) ∈ columnRegs x := by
    intro y hy
    exact List.mem_map.mpr ⟨y,List.mem_range.mpr hy,rfl⟩
  have heq : ∀ i < 25, ∀ y < 5, i = x+5*y ↔ i%5 = x ∧ i/5 = y := by
    intro i hi y hy
    omega_using [hx]
  have hcode : (List.range 5).map (fun y =>
      Instr.vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)) =
      (List.range 5).flatMap (fun y => [Instr.vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)]) := by
    rfl
  rw [hcode]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg (columnRegs x) s s' ∧ s'.v .v30 = s.v .v30 ∧
      ∀ i < 25, s'.v (vreg i) =
        if i%5 = x ∧ i/5 < k then s.v (vreg i) ^^^ s.v .v30 else s.v (vreg i))
    (fun y s' hy ⟨hchg,hv30,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,rfl,by intro i hi; rw [ite_eq_right (by omega_using [])]⟩)
    fun s' ⟨hchg,hv30,hvals⟩ => ⟨hchg,hv30,fun i hi => by
      rw [hvals i hi]
      have hdiv : i/5 < 5 := by omega_using [hi]
      simp only [hdiv,and_true]⟩
  refine wp_vop (d := vreg (x+5*y)) rfl fun s'' h => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact (hchg.trans h.chg).mono (by
      intro r hr
      rw [List.mem_append,List.mem_singleton] at hr
      rcases hr with hh | rfl
      · exact hh
      · exact hm y hy)
  · rw [h.get .v30 (h30 y hy),hv30]
  · intro i hi
    by_cases hid : i = x+5*y
    · subst i
      rw [h.v,hvals _ (by omega_using [hx, hy]),hv30,ite_eq_right (by
        have := (heq (x+5*y) (by omega_using [hx, hy]) y hy).mp rfl; omega_using []),ite_eq_left (by
        have := (heq (x+5*y) (by omega_using [hx, hy]) y hy).mp rfl; omega_using [hx])]
    · rw [h.get (vreg i) (by rw [ne_eq,vreg_inj i (by omega_using [hi]) (x+5*y) (by omega_using [hx, hy])]; exact hid),hvals i hi]
      have hi' : ¬ (i%5 = x ∧ i/5 = y) := by rw [← heq i hi y hy]; exact hid
      by_cases hc : i%5 = x ∧ i/5 < y <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
end VG.Proof.Sha3.AArch64.Neon

end

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3 (C D)
set_option linter.unusedSimpArgs false

/-- Compute and apply a theta correction without disturbing any column parity. -/
theorem correction_ok {s : State} {A B : Spec.Sha3.State} {x : Nat} (hx : x < 5)
    (hc : ∀ c < 5, s.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) :
    WP isa (.block (correction x)) s fun s' =>
      VChg (.v30 :: columnRegs x) s s' ∧
      (∀ c < 5, s'.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) ∧
      ∀ i < 25, s'.v (vreg i) =
        if i%5 = x then s.v (vreg i) ^^^ ofVDwords (D A x) (D B x) else s.v (vreg i) := by
  have h30 (j : Nat) (hj : j < 30) : vreg j ≠ VReg.v30 := by
    change vreg j ≠ vreg 30
    rw [ne_eq,vreg_inj j (by omega_using [hj]) 30 (by decide)]; omega_using [hj]
  unfold correction
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rol_ok (d := .v30) (n := vreg (25+(x+1)%5))
    (Ne.symm (h30 _ (by omega_using []))) (by decide) (by decide)) fun s₁ ⟨h1,v1⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v30) rfl fun s₂ h2 => ?_
  have v2 : s₂.v .v30 = ofVDwords (D A x) (D B x) := by
    rw [h2.v,h1.get (vreg (25+(x+4)%5)) (by simp only [List.mem_singleton]; exact h30 _ (by omega_using [])),
      hc _ (by omega_using []),v1,hc _ (by omega_using []),vdword_ofVDwords_0,vdword_ofVDwords_1,pair_xor]
    rw [VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide),
      VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide)]
    simp only [D]; rw [BitVec.xor_comm (C A _),BitVec.xor_comm (C B _)]
  refine WP.mono (column_ok x hx s₂) fun s₃ ⟨h3,_,vals⟩ => ⟨?_,?_,?_⟩
  · exact ((h1.trans h2.chg).trans h3).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with (rfl | rfl) | h
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr h)
  · intro c hcc
    have hn : vreg (25+c) ∉ columnRegs x := by
      intro hh
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hh
      rw [List.mem_range] at hy
      have hh := (vreg_inj (x+5*y) (by omega_using [hx, hy]) (25+c) (by omega_using [hcc])).mp he
      omega_using [hx, hy, hh]
    rw [h3.get _ hn,h2.get _ (h30 _ (by omega_using [hcc])),h1.get _ (by
      simp only [List.mem_singleton]; exact h30 _ (by omega_using [hcc]))]
    exact hc c hcc
  · intro i hi
    rw [vals i hi,v2,h2.get _ (h30 _ (by omega_using [hi])),h1.get _ (by
      simp only [List.mem_singleton]; exact h30 _ (by omega_using [hi]))]
end VG.Proof.Sha3.AArch64.Neon
