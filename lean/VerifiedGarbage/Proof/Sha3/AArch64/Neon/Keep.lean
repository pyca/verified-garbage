import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Vector
import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Sha3.Compl
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Sha3.AArch64.Permute

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
set_option linter.unusedSimpArgs false

theorem sli_rotate (x : BitVec 64) {k : Nat} (hk : k < 64) :
    VShiftOp.sli.eval k 64 (x >>> (64-k)) x = x.rotateLeft k := by
  rw [VShiftOp.eval,BitVec.rotateLeft_def,Nat.mod_eq_of_lt hk,BitVec.or_comm (x <<< k)]
  apply congrArg (· ||| (x <<< k))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes,BitVec.getLsbD_ushiftRight]
  by_cases h : i < k
  · simp only [hi,h,decide_true,decide_false,Bool.true_and,Bool.false_and,
      Bool.and_true,Bool.not_true,Bool.not_false,Bool.and_false]
  · rw [BitVec.getLsbD_of_ge x (64-k+i) (by omega : 64 ≤ 64-k+i)]
    simp only [Bool.false_and]

theorem rol_ok {s : State} {d n : VReg} (hdn : d ≠ n) {k : Nat} (hk0 : 0 < k) (hk : k < 64) :
    WP isa (.block (rol d n k)) s fun s' => VChg [d] s s' ∧
      s'.v d = ofVDwords ((vdword (s.v n) 0).rotateLeft k) ((vdword (s.v n) 1).rotateLeft k) := by
  unfold rol
  refine wp_vop (op := .shift .ushr .d2 d n (64-k)) (d := d)
    (x := VArr.d2.map2 (fun w a b => VShiftOp.ushr.eval (64-k) w a b) (s.v d) (s.v n))
    (by simp [VOp.eval,VShiftOp.ok,show 1 ≤ 64-k by omega,show 64-k ≤ 64 by omega]) fun s₁ h1 => ?_
  refine wp_vop (op := .shift .sli .d2 d n k) (d := d)
    (x := VArr.d2.map2 (fun w a b => VShiftOp.sli.eval k w a b) (s₁.v d) (s₁.v n))
    (by simp [VOp.eval,VShiftOp.ok,hk]) fun s₂ h2 => WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (by intro r hr; simpa using hr),?_⟩
  rw [h2.v,h1.v,h1.get n (Ne.symm hdn)]
  simp only [VArr.map2,vdword_ofVDwords_0,vdword_ofVDwords_1,VShiftOp.eval]
  change ofVDwords (VShiftOp.sli.eval k 64 ((vdword (s.v n) 0) >>> (64-k)) (vdword (s.v n) 0))
    (VShiftOp.sli.eval k 64 ((vdword (s.v n) 1) >>> (64-k)) (vdword (s.v n) 1)) = _
  rw [VG.Proof.Sha3.AArch64.Neon.sli_rotate _ hk,VG.Proof.Sha3.AArch64.Neon.sli_rotate _ hk]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3 (C)

def Pairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, s.v (vreg i) = ofVDwords A[i]! B[i]!

theorem vreg_inj : ∀ i < 32, ∀ j < 32, vreg i = vreg j ↔ i = j := by decide

theorem pair_xor (a b c d : BitVec 64) :
    ofVDwords a b ^^^ ofVDwords c d = ofVDwords (a ^^^ c) (b ^^^ d) := by
  apply vec64_ext <;> simp only [vdword,BitVec.extractLsb'_xor]
  · change vdword (ofVDwords a b) 0 ^^^ vdword (ofVDwords c d) 0 = vdword (ofVDwords (a ^^^ c) (b ^^^ d)) 0
    rw [vdword_ofVDwords_0,vdword_ofVDwords_0,vdword_ofVDwords_0]
  · change vdword (ofVDwords a b) 1 ^^^ vdword (ofVDwords c d) 1 = vdword (ofVDwords (a ^^^ c) (b ^^^ d)) 1
    rw [vdword_ofVDwords_1,vdword_ofVDwords_1,vdword_ofVDwords_1]

/-- The parity of each column is computed independently for both SHAKE streams. -/
theorem parity_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) {x : Nat} (hx : x < 5) :
    WP isa (.block (parity x)) s fun s' => VChg [vreg (25+x)] s s' ∧
      s'.v (vreg (25+x)) = ofVDwords (C A x) (C B x) := by
  have hn (j : Nat) (hj : j < 25) : vreg j ≠ vreg (25+x) := by
    rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj j (by omega) (25+x) (by omega)]; omega
  unfold parity
  refine wp_vop (d := vreg (25+x)) rfl fun s₁ h1 =>
    wp_vop (d := vreg (25+x)) rfl fun s₂ h2 =>
    wp_vop (d := vreg (25+x)) rfl fun s₃ h3 =>
    wp_vop (d := vreg (25+x)) rfl fun s₄ h4 =>
      WP.block_nil_iff.mpr ⟨(((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono
        (by intro r hr; simpa using hr),?_⟩
  rw [h4.v,h3.v,h2.v,h1.v,
    h3.get (vreg (x+20)) (hn _ (by omega)),h2.get (vreg (x+20)) (hn _ (by omega)),
    h1.get (vreg (x+20)) (hn _ (by omega)),h2.get (vreg (x+15)) (hn _ (by omega)),
    h1.get (vreg (x+15)) (hn _ (by omega)),h1.get (vreg (x+10)) (hn _ (by omega)),
    hp x (by omega),hp (x+5) (by omega),hp (x+10) (by omega),hp (x+15) (by omega),hp (x+20) (by omega)]
  simp only [VG.Proof.Sha3.AArch64.Neon.pair_xor,C]
/-- All five column parities are ready before any state lane changes. -/
theorem parityAll_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block ((List.range 5).flatMap parity)) s fun s' =>
      VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' A B ∧
      ∀ x < 5, s'.v (vreg (25+x)) = ofVDwords (C A x) (C B x) := by
  have hmem : ∀ x < 5, vreg (25+x) ∈ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  refine wp_range_flatMap (M := isa)
    (fun k s' => VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' A B ∧
      ∀ x < k, s'.v (vreg (25+x)) = ofVDwords (C A x) (C B x))
    (fun k s' hk ⟨hkeep,hpairs,hcols⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,hp,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.parity_ok hpairs hk) fun s'' ⟨hchg,hcol⟩ => ⟨?_,?_,?_⟩
  · exact (hkeep.trans hchg).mono (by
      intro r hr
      rw [List.mem_append,List.mem_singleton] at hr
      rcases hr with h | rfl
      · exact h
      · exact hmem k hk)
  · intro i hi
    rw [hchg.get (vreg i) (by
      simp only [List.mem_singleton]
      rw [VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) (25+k) (by omega)]; omega)]
    exact hpairs i hi
  · intro x hx
    by_cases he : x = k
    · subst x; exact hcol
    · rw [hchg.get (vreg (25+x)) (by
        simp only [List.mem_singleton]
        rw [VG.Proof.Sha3.AArch64.Neon.vreg_inj (25+x) (by omega) (25+k) (by omega)]; omega)]
      exact hcols x (by omega)
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Column`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

def columnRegs (x : Nat) : List VReg := (List.range 5).map fun y => vreg (x+5*y)

/-- Apply a theta correction to the five words in one column. -/
theorem column_ok (x : Nat) (hx : x < 5) (s : State) :
    WP isa (.block ((List.range 5).map fun y =>
      .vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30))) s fun s' =>
      VChg (VG.Proof.Sha3.AArch64.Neon.columnRegs x) s s' ∧ s'.v .v30 = s.v .v30 ∧
      ∀ i < 25, s'.v (vreg i) = if i%5 = x then s.v (vreg i) ^^^ s.v .v30 else s.v (vreg i) := by
  have h30 (y : Nat) (hy : y < 5) : VReg.v30 ≠ vreg (x+5*y) := by
    change vreg 30 ≠ vreg (x+5*y)
    rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj 30 (by decide) (x+5*y) (by omega)]; omega
  have hm : ∀ y < 5, vreg (x+5*y) ∈ VG.Proof.Sha3.AArch64.Neon.columnRegs x := by
    intro y hy
    exact List.mem_map.mpr ⟨y,List.mem_range.mpr hy,rfl⟩
  have heq : ∀ i < 25, ∀ y < 5, i = x+5*y ↔ i%5 = x ∧ i/5 = y := by
    intro i hi y hy
    omega
  have hcode : (List.range 5).map (fun y =>
      Instr.vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)) =
      (List.range 5).flatMap (fun y => [Instr.vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)]) := by
    rfl
  rw [hcode]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg (VG.Proof.Sha3.AArch64.Neon.columnRegs x) s s' ∧ s'.v .v30 = s.v .v30 ∧
      ∀ i < 25, s'.v (vreg i) =
        if i%5 = x ∧ i/5 < k then s.v (vreg i) ^^^ s.v .v30 else s.v (vreg i))
    (fun y s' hy ⟨hchg,hv30,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,rfl,by intro i hi; rw [ite_eq_right (by omega)]⟩)
    fun s' ⟨hchg,hv30,hvals⟩ => ⟨hchg,hv30,fun i hi => by
      rw [hvals i hi]
      have hdiv : i/5 < 5 := by omega
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
      rw [h.v,hvals _ (by omega),hv30,ite_eq_right (by
        have := (heq (x+5*y) (by omega) y hy).mp rfl; omega),ite_eq_left (by
        have := (heq (x+5*y) (by omega) y hy).mp rfl; omega)]
    · rw [h.get (vreg i) (by rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) (x+5*y) (by omega)]; exact hid),hvals i hi]
      have hi' : ¬ (i%5 = x ∧ i/5 = y) := by rw [← heq i hi y hy]; exact hid
      by_cases hc : i%5 = x ∧ i/5 < y <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction`. -/
section

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
      VChg (.v30 :: VG.Proof.Sha3.AArch64.Neon.columnRegs x) s s' ∧
      (∀ c < 5, s'.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) ∧
      ∀ i < 25, s'.v (vreg i) =
        if i%5 = x then s.v (vreg i) ^^^ ofVDwords (D A x) (D B x) else s.v (vreg i) := by
  have h30 (j : Nat) (hj : j < 30) : vreg j ≠ VReg.v30 := by
    change vreg j ≠ vreg 30
    rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj j (by omega) 30 (by decide)]; omega
  unfold correction
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.rol_ok (d := .v30) (n := vreg (25+(x+1)%5))
    (Ne.symm (h30 _ (by omega))) (by decide) (by decide)) fun s₁ ⟨h1,v1⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v30) rfl fun s₂ h2 => ?_
  have v2 : s₂.v .v30 = ofVDwords (D A x) (D B x) := by
    rw [h2.v,h1.get (vreg (25+(x+4)%5)) (by simp only [List.mem_singleton]; exact h30 _ (by omega)),
      hc _ (by omega),v1,hc _ (by omega),vdword_ofVDwords_0,vdword_ofVDwords_1,VG.Proof.Sha3.AArch64.Neon.pair_xor]
    rw [VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide),
      VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide)]
    simp only [D]; rw [BitVec.xor_comm (C A _),BitVec.xor_comm (C B _)]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.column_ok x hx s₂) fun s₃ ⟨h3,_,vals⟩ => ⟨?_,?_,?_⟩
  · exact ((h1.trans h2.chg).trans h3).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with (rfl | rfl) | h
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr h)
  · intro c hcc
    have hn : vreg (25+c) ∉ VG.Proof.Sha3.AArch64.Neon.columnRegs x := by
      intro hh
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hh
      rw [List.mem_range] at hy
      have hh := (VG.Proof.Sha3.AArch64.Neon.vreg_inj (x+5*y) (by omega) (25+c) (by omega)).mp he
      omega
    rw [h3.get _ hn,h2.get _ (h30 _ (by omega)),h1.get _ (by
      simp only [List.mem_singleton]; exact h30 _ (by omega))]
    exact hc c hcc
  · intro i hi
    rw [vals i hi,v2,h2.get _ (h30 _ (by omega)),h1.get _ (by
      simp only [List.mem_singleton]; exact h30 _ (by omega))]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Theta`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.Sha3 (C D)

/-- Internal kernels may use every vector register; their boundaries save the ABI-preserved lanes. -/
def allV : List VReg := (List.range 32).map vreg

theorem allV_mem : ∀ r : VReg, r ∈ VG.Proof.Sha3.AArch64.Neon.allV := by intro r; cases r <;> decide

/-- Theta acts independently on the two states held in NEON lanes. -/
theorem theta_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block theta) s fun s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' (Spec.Sha3.theta A) (Spec.Sha3.theta B) := by
  unfold theta
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.parityAll_ok hp) fun s₁ ⟨h1,hp1,cols1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s₁ s' ∧
      (∀ c < 5, s'.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) ∧
      ∀ i < 25, s'.v (vreg i) = if i%5 < k then
        ofVDwords (A[i]! ^^^ D A (i%5)) (B[i]! ^^^ D B (i%5)) else ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hkeep,hcols,hvals⟩ => ?_) 5 (Nat.le_refl _) s₁
    ⟨VChg.refl _ _,cols1,by intro i hi; rw [ite_eq_right (Nat.not_lt_zero _)]; exact hp1 i hi⟩)
    fun s₂ ⟨hkeep,_,hvals⟩ => ⟨(h1.trans hkeep).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),?_⟩
  · refine WP.mono (VG.Proof.Sha3.AArch64.Neon.correction_ok hk hcols) fun s'' ⟨hchg,hcols',vals⟩ =>
      ⟨(hkeep.trans hchg).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),hcols',?_⟩
    intro i hi
    rw [vals i hi,hvals i hi]
    by_cases he : i%5 = k
    · rw [ite_eq_left he,ite_eq_right (by omega),ite_eq_left (by omega),VG.Proof.Sha3.AArch64.Neon.pair_xor,he]
    · rw [ite_eq_right he]
      by_cases hlt : i%5 < k <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
  · intro i hi
    rw [hvals i hi,ite_eq_left (by omega)]
    have hta := VG.Proof.Sha3.theta_get A hi
    have htb := VG.Proof.Sha3.theta_get B hi
    rw [VG.Proof.Sha3.getElem!_eq A hi,VG.Proof.Sha3.getElem!_eq B hi,
      ← hta,← htb,VG.Proof.Sha3.getElem!_eq (Spec.Sha3.theta A) hi,
      VG.Proof.Sha3.getElem!_eq (Spec.Sha3.theta B) hi]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

/-- Install a rotated predecessor while saving the displaced state word. -/
theorem rhoPiStep_ok {s : State} {j k : Nat} (hj : j < 25) (hk0 : 0 < k) (hk : k < 64) :
    WP isa (.block (rhoPiStep (j,k))) s fun s' => VChg [vreg j,.v25,.v26] s s' ∧
      s'.v (vreg j) = ofVDwords ((vdword (s.v .v25) 0).rotateLeft k)
        ((vdword (s.v .v25) 1).rotateLeft k) ∧ s'.v .v25 = s.v (vreg j) := by
  have h25 : vreg j ≠ VReg.v25 := by
    change vreg j ≠ vreg 25
    rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj j (by omega) 25 (by decide)]; omega
  have h26 : vreg j ≠ VReg.v26 := by
    change vreg j ≠ vreg 26
    rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj j (by omega) 26 (by decide)]; omega
  unfold rhoPiStep
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v26) rfl fun s₁ h1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.rol_ok h25 hk0 hk) fun s₂ ⟨h2,v2⟩ => ?_
  refine wp_vop (d := .v25) rfl fun s₃ h3 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((h1.chg.trans h2).trans h3.chg).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_singleton] at hr
      rcases hr with (rfl | rfl) | rfl <;> simp)
  · rw [h3.get _ h25,v2,h1.get .v25]
  · rw [h3.v,h2.get .v26 (by simp only [List.mem_singleton]; exact Ne.symm h26),h1.v]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3 (piSrc rhoOff)

def dest (k : Nat) : Nat := cycle[k]!.1
def rotation (k : Nat) : Nat := cycle[k]!.2
def source (k : Nat) : Nat := if k = 0 then 1 else VG.Proof.Sha3.AArch64.Neon.dest (k-1)
def Done (k i : Nat) : Prop := i ∈ (List.range k).map VG.Proof.Sha3.AArch64.Neon.dest
instance (k i : Nat) : Decidable (VG.Proof.Sha3.AArch64.Neon.Done k i) := inferInstanceAs (Decidable (i ∈ (List.range k).map VG.Proof.Sha3.AArch64.Neon.dest))

theorem cycle_facts : ∀ k < 24,
    VG.Proof.Sha3.AArch64.Neon.dest k < 25 ∧ VG.Proof.Sha3.AArch64.Neon.source k < 25 ∧ 0 < VG.Proof.Sha3.AArch64.Neon.rotation k ∧ VG.Proof.Sha3.AArch64.Neon.rotation k < 64 ∧
    ¬ VG.Proof.Sha3.AArch64.Neon.Done k (VG.Proof.Sha3.AArch64.Neon.dest k) ∧ VG.Proof.Sha3.AArch64.Neon.source (k+1) = VG.Proof.Sha3.AArch64.Neon.dest k ∧
    piSrc (VG.Proof.Sha3.AArch64.Neon.dest k%5) (VG.Proof.Sha3.AArch64.Neon.dest k/5) = VG.Proof.Sha3.AArch64.Neon.source k ∧ rhoOff (VG.Proof.Sha3.AArch64.Neon.source k) = VG.Proof.Sha3.AArch64.Neon.rotation k := by decide

theorem done_next (k i : Nat) : VG.Proof.Sha3.AArch64.Neon.Done (k+1) i ↔ VG.Proof.Sha3.AArch64.Neon.Done k i ∨ i = VG.Proof.Sha3.AArch64.Neon.dest k := by
  simp only [VG.Proof.Sha3.AArch64.Neon.Done,List.range_succ,List.map_append,List.map_singleton,List.mem_append,List.mem_singleton]

theorem done_all : ∀ i < 25, VG.Proof.Sha3.AArch64.Neon.Done 24 i ↔ i ≠ 0 := by decide

/-- The cycle's destination and rotation are exactly pi and rho's coordinates. -/
theorem cycle_word (A : Spec.Sha3.State) {k : Nat} (hk : k < 24) :
    (Spec.Sha3.pi (Spec.Sha3.rho A))[VG.Proof.Sha3.AArch64.Neon.dest k]! = (A[VG.Proof.Sha3.AArch64.Neon.source k]!).rotateLeft (VG.Proof.Sha3.AArch64.Neon.rotation k) := by
  obtain ⟨hd,hs,_,_,_,_,hp,hr⟩ := VG.Proof.Sha3.AArch64.Neon.cycle_facts k hk
  have hpi := VG.Proof.Sha3.pi_get (Spec.Sha3.rho A)
    (x := VG.Proof.Sha3.AArch64.Neon.dest k%5) (y := VG.Proof.Sha3.AArch64.Neon.dest k/5) (by omega) (by omega)
  have hpiBang : (Spec.Sha3.pi (Spec.Sha3.rho A))[VG.Proof.Sha3.AArch64.Neon.dest k%5+5*(VG.Proof.Sha3.AArch64.Neon.dest k/5)]! =
      (Spec.Sha3.rho A)[piSrc (VG.Proof.Sha3.AArch64.Neon.dest k%5) (VG.Proof.Sha3.AArch64.Neon.dest k/5)]! := by
    rw [VG.Proof.Sha3.getElem!_eq _ (by omega),VG.Proof.Sha3.getElem!_eq _ (by simp only [piSrc]; omega)]
    exact hpi
  rw [show VG.Proof.Sha3.AArch64.Neon.dest k%5+5*(VG.Proof.Sha3.AArch64.Neon.dest k/5) = VG.Proof.Sha3.AArch64.Neon.dest k by omega,hp] at hpiBang
  rw [hpiBang,VG.Proof.Sha3.getElem!_eq _ hs,VG.Proof.Sha3.rho_get A hs,
    hr,VG.Proof.Sha3.getElem!_eq A hs]

theorem cycle_zero (A : Spec.Sha3.State) :
    (Spec.Sha3.pi (Spec.Sha3.rho A))[0]! = A[0]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ (by decide),VG.Proof.Sha3.pi_get _ (x := 0) (y := 0) (by decide) (by decide),
    VG.Proof.Sha3.rho_get A (by decide),VG.Proof.Sha3.getElem!_eq A (by decide)]
  exact VG.Proof.Sha3.rotateLeft_zero _
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
set_option linter.unusedSimpArgs false

/-- The in-place cycle implements rho and pi for both independent states. -/
theorem rhoPi_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block rhoPi) s fun s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧
      VG.Proof.Sha3.AArch64.Neon.Pairs s' (Spec.Sha3.pi (Spec.Sha3.rho A)) (Spec.Sha3.pi (Spec.Sha3.rho B)) := by
  unfold rhoPi
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v25) rfl fun s₁ h1 => ?_
  have hcode : cycle.flatMap rhoPiStep = (List.range 24).flatMap
      (fun k => rhoPiStep (VG.Proof.Sha3.AArch64.Neon.dest k,VG.Proof.Sha3.AArch64.Neon.rotation k)) := by rfl
  rw [hcode]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s₁ s' ∧ s'.v .v25 = ofVDwords A[VG.Proof.Sha3.AArch64.Neon.source k]! B[VG.Proof.Sha3.AArch64.Neon.source k]! ∧
      ∀ i < 25, s'.v (vreg i) = if VG.Proof.Sha3.AArch64.Neon.Done k i then
        ofVDwords (Spec.Sha3.pi (Spec.Sha3.rho A))[i]! (Spec.Sha3.pi (Spec.Sha3.rho B))[i]!
        else ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hchg,h25,hvals⟩ => ?_) 24 (Nat.le_refl _) s₁
    ⟨VChg.refl _ _,by rw [h1.v]; exact hp 1 (by decide),
      by intro i hi; rw [ite_eq_right (by simp [VG.Proof.Sha3.AArch64.Neon.Done])];
         rw [h1.get (vreg i) (by
           change vreg i ≠ vreg 25; rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) 25 (by decide)]; omega)]
         exact hp i hi⟩)
    fun s₂ ⟨hchg,_,vals⟩ => ⟨(h1.chg.trans hchg).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),?_⟩
  · obtain ⟨hd,hs,hk0,hkr,hfresh,hnext,_,_⟩ := VG.Proof.Sha3.AArch64.Neon.cycle_facts k hk
    refine WP.mono (VG.Proof.Sha3.AArch64.Neon.rhoPiStep_ok hd hk0 hkr) fun s'' ⟨hstep,hnew,htemp⟩ =>
      ⟨(hchg.trans hstep).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),?_,?_⟩
    · rw [htemp,hvals _ hd,ite_eq_right hfresh,hnext]
    · intro i hi
      by_cases he : i = VG.Proof.Sha3.AArch64.Neon.dest k
      · subst i
        rw [hnew,h25,vdword_ofVDwords_0,vdword_ofVDwords_1,
          ← VG.Proof.Sha3.AArch64.Neon.cycle_word A hk,← VG.Proof.Sha3.AArch64.Neon.cycle_word B hk,ite_eq_left ((VG.Proof.Sha3.AArch64.Neon.done_next k _).mpr (Or.inr rfl))]
      · have h25n : vreg i ≠ VReg.v25 := by
          change vreg i ≠ vreg 25
          rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) 25 (by decide)]; omega
        have h26n : vreg i ≠ VReg.v26 := by
          change vreg i ≠ vreg 26
          rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) 26 (by decide)]; omega
        rw [hstep.get (vreg i) (by
          simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or]
          exact ⟨by rw [VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) (VG.Proof.Sha3.AArch64.Neon.dest k) (by omega)]; exact he,h25n,h26n⟩),hvals i hi]
        have hiff : VG.Proof.Sha3.AArch64.Neon.Done (k+1) i ↔ VG.Proof.Sha3.AArch64.Neon.Done k i := by rw [VG.Proof.Sha3.AArch64.Neon.done_next,or_iff_left he]
        by_cases hd : VG.Proof.Sha3.AArch64.Neon.Done k i
        · rw [ite_eq_left hd,ite_eq_left (hiff.mpr hd)]
        · rw [ite_eq_right hd,ite_eq_right (fun h => hd (hiff.mp h))]
  · intro i hi
    rw [vals i hi]
    by_cases he : i = 0
    · subst i
      rw [ite_eq_right (by rw [VG.Proof.Sha3.AArch64.Neon.done_all 0 (by decide)]; simp),VG.Proof.Sha3.AArch64.Neon.cycle_zero A,VG.Proof.Sha3.AArch64.Neon.cycle_zero B]
    · rw [ite_eq_left ((VG.Proof.Sha3.AArch64.Neon.done_all i hi).mpr he)]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

theorem saveRow_ok {s : State} {y : Nat} (hy : y < 5) :
    WP isa (.block (saveRow y)) s fun s' => VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧
      ∀ x < 5, s'.v (vreg (25+x)) = s.v (vreg (x+5*y)) := by
  have hm : ∀ x < 5, vreg (25+x) ∈ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  have hs : ∀ i < 25, vreg i ∉ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  unfold saveRow
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k s' => VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧
      ∀ x < k, s'.v (vreg (25+x)) = s.v (vreg (x+5*y)))
    (fun k s' hk ⟨hchg,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_vop (d := vreg (25+k)) rfl fun s'' h => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (hchg.trans h.chg).mono (by
      intro r hr
      rw [List.mem_append,List.mem_singleton] at hr
      rcases hr with hh | rfl
      · exact hh
      · exact hm k hk)
  · intro x hx
    by_cases he : x = k
    · subst x
      rw [h.v,hchg.get _ (hs _ (by omega))]
    · rw [h.get _ (by
        rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj (25+x) (by omega) (25+k) (by omega)]; omega)]
      exact hvals x (by omega)
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

theorem pair_bic (a b c d : BitVec 64) :
    ofVDwords a b &&& ~~~(ofVDwords c d) = ofVDwords (a &&& ~~~c) (b &&& ~~~d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp only [h,hi,decide_true,Bool.true_and,ite_true]
  · simp only [h,hi,show i-64 < 64 by omega,decide_true,Bool.true_and,ite_false]

/-- One chi word, with all five row inputs still preserved in temporaries. -/
theorem chiWord_ok {s : State} {x y : Nat} (hx : x < 5) (_hy : y < 5)
    {F G : Nat → BitVec 64}
    (hp : ∀ z < 5, s.v (vreg (25+z)) = ofVDwords (F z) (G z)) :
    WP isa (.block (VG.Impl.Sha3.AArch64.Neon.Vector.chiWord x y)) s fun s' => VChg [.v30,vreg (x+5*y)] s s' ∧
      s'.v (vreg (x+5*y)) = ofVDwords
        (F x ^^^ (F ((x+2)%5) &&& ~~~(F ((x+1)%5))))
        (G x ^^^ (G ((x+2)%5) &&& ~~~(G ((x+1)%5)))) := by
  have hn : ∀ z < 5, vreg (25+z) ≠ VReg.v30 := by decide
  unfold VG.Impl.Sha3.AArch64.Neon.Vector.chiWord
  refine wp_vop (d := .v30) rfl fun s₁ h1 =>
    wp_vop (d := vreg (x+5*y)) rfl fun s₂ h2 =>
      WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (by intro r hr; simpa using hr),?_⟩
  rw [h2.v,h1.get _ (hn x hx),h1.v,hp x hx,hp ((x+2)%5) (by omega),hp ((x+1)%5) (by omega)]
  change ofVDwords (F x) (G x) ^^^
    (ofVDwords (F ((x+2)%5)) (G ((x+2)%5)) &&& ~~~(ofVDwords (F ((x+1)%5)) (G ((x+1)%5)))) = _
  rw [VG.Proof.Sha3.AArch64.Neon.pair_bic,VG.Proof.Sha3.AArch64.Neon.pair_xor]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg)

/-- The canonical chi word, expressed in the operand order used by BIC. -/
theorem chi_word (A : Spec.Sha3.State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (Spec.Sha3.chi A)[x+5*y]! = A[x+5*y]! ^^^
      (A[(x+2)%5+5*y]! &&& ~~~(A[(x+1)%5+5*y]!)) := by
  rw [VG.Proof.Sha3.getElem!_eq _ (by omega),VG.Proof.Sha3.chi_get A hx hy,
    VG.Proof.Sha3.getElem!_eq A (by omega),VG.Proof.Sha3.getElem!_eq A (by omega),
    VG.Proof.Sha3.getElem!_eq A (by omega),BitVec.and_comm]

/-- Preserve and transform one complete chi row for two states. -/
theorem row_ok {s : State} {A B : Spec.Sha3.State} {y : Nat} (hy : y < 5)
    (hp : ∀ x < 5, s.v (vreg (x+5*y)) = ofVDwords A[x+5*y]! B[x+5*y]!) :
    WP isa (.block (row y)) s fun s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧
      ∀ i < 25, s'.v (vreg i) = if i/5 = y then
        ofVDwords (Spec.Sha3.chi A)[i]! (Spec.Sha3.chi B)[i]! else s.v (vreg i) := by
  have hn : ∀ i < 25, vreg i ∉ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  have ht30 : ∀ z < 5, vreg (25+z) ≠ VReg.v30 := by decide
  have htstate : ∀ z < 5, ∀ i < 25, vreg (25+z) ≠ vreg i := by decide
  have hi30 : ∀ i < 25, vreg i ≠ VReg.v30 := by decide
  unfold row
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.saveRow_ok hy) fun s₁ ⟨h1,vals1⟩ => ?_
  have cols1 : ∀ z < 5, s₁.v (vreg (25+z)) = ofVDwords A[z+5*y]! B[z+5*y]! := by
    intro z hz; rw [vals1 z hz]; exact hp z hz
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s₁ s' ∧
      (∀ z < 5, s'.v (vreg (25+z)) = ofVDwords A[z+5*y]! B[z+5*y]!) ∧
      ∀ i < 25, s'.v (vreg i) = if i/5 = y ∧ i%5 < k then
        ofVDwords (Spec.Sha3.chi A)[i]! (Spec.Sha3.chi B)[i]! else s₁.v (vreg i))
    (fun k s' hk ⟨hchg,hcols,hvals⟩ => ?_) 5 (Nat.le_refl _) s₁
    ⟨VChg.refl _ _,cols1,by intro i hi; rw [ite_eq_right (by omega)]⟩)
    fun s₂ ⟨hchg,_,vals⟩ => ⟨(h1.trans hchg).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),?_⟩
  · refine WP.mono (VG.Proof.Sha3.AArch64.Neon.chiWord_ok hk hy hcols) fun s'' ⟨hstep,hnew⟩ =>
      ⟨(hchg.trans hstep).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),?_,?_⟩
    · intro z hz
      rw [hstep.get _ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨ht30 z hz,htstate z hz _ (by omega)⟩)]
      exact hcols z hz
    · intro i hi
      by_cases he : i = k+5*y
      · subst i
        rw [hnew,← VG.Proof.Sha3.AArch64.Neon.chi_word A hk hy,← VG.Proof.Sha3.AArch64.Neon.chi_word B hk hy,ite_eq_left (by omega)]
      · rw [hstep.get _ (by
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hi30 i hi,by rw [VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) (k+5*y) (by omega)]; exact he⟩),hvals i hi]
        have hne : ¬ (i/5 = y ∧ i%5 = k) := by intro h; omega
        by_cases h : i/5 = y ∧ i%5 < k <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
  · intro i hi
    rw [vals i hi,h1.get _ (hn i hi)]
    have hmod : i%5 < 5 := by omega
    simp only [hmod,and_true]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg)

/-- Chi's nonlinear layer acts independently on the paired states. -/
theorem chi_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block VG.Impl.Sha3.AArch64.Neon.Vector.chi) s fun s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' (Spec.Sha3.chi A) (Spec.Sha3.chi B) := by
  unfold VG.Impl.Sha3.AArch64.Neon.Vector.chi
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun y s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧ ∀ i < 25, s'.v (vreg i) = if i/5 < y then
      ofVDwords (Spec.Sha3.chi A)[i]! (Spec.Sha3.chi B)[i]! else ofVDwords A[i]! B[i]!)
    (fun y s' hy ⟨hchg,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,by intro i hi; rw [ite_eq_right (Nat.not_lt_zero _)]; exact hp i hi⟩)
    fun s' ⟨hchg,hvals⟩ => ⟨hchg,fun i hi => by rw [hvals i hi,ite_eq_left (by omega)]⟩
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.row_ok hy (A := A) (B := B) (by
    intro x hx
    rw [hvals _ (by omega),ite_eq_right (by omega)])) fun s'' ⟨hrow,vals⟩ =>
      ⟨(hchg.trans hrow).mono (fun r _ => VG.Proof.Sha3.AArch64.Neon.allV_mem r),?_⟩
  intro i hi
  rw [vals i hi,hvals i hi]
  by_cases he : i/5 = y
  · rw [ite_eq_left he,ite_eq_left (by omega)]
  · rw [ite_eq_right he]
    by_cases hlt : i/5 < y <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep constant_ok constantLow_RC)

theorem iota_word (A : Spec.Sha3.State) (r : Nat) {i : Nat} (hi : i < 25) :
    (Spec.Sha3.iota A r)[i]! = if i = 0 then A[0]! ^^^ Spec.Sha3.RC r else A[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi]
  unfold Spec.Sha3.iota
  rw [Vector.getElem_set]
  by_cases he : i = 0
  · subst i
    rw [ite_eq_left rfl,ite_eq_left rfl,VG.Proof.Sha3.getElem!_eq A (by decide)]
  · rw [ite_eq_right (Ne.symm he),ite_eq_right he,VG.Proof.Sha3.getElem!_eq A hi]

/-- Broadcast the round constant into both independent states. -/
theorem iota_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) (r : Nat)
    (hr : s.gpr .x16 = Spec.Sha3.RC r) :
    WP isa (.block iota) s fun s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' (Spec.Sha3.iota A r) (Spec.Sha3.iota B r) := by
  unfold iota
  refine wp_vop (d := .v25) rfl fun s₁ h1 => wp_vop (d := .v0) rfl fun s₂ h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => VG.Proof.Sha3.AArch64.Neon.allV_mem v),?_⟩
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Neon.iota_word A r hi,VG.Proof.Sha3.AArch64.Neon.iota_word B r hi]
  by_cases he : i = 0
  · subst i
    rw [ite_eq_left rfl,ite_eq_left rfl]
    change s₂.v .v0 = _
    rw [h2.v,h1.get .v0,h1.v,hr]
    have hp0 : s.v .v0 = ofVDwords A[0]! B[0]! := hp 0 (by decide)
    change s.v .v0 ^^^ ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) = _
    rw [hp0,VG.Proof.Sha3.AArch64.Neon.pair_xor]
  · have h0 : vreg i ≠ VReg.v0 := by
      change vreg i ≠ vreg 0
      rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) 0 (by decide)]; exact he
    have h25 : vreg i ≠ VReg.v25 := by
      change vreg i ≠ vreg 25
      rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) 25 (by decide)]; omega
    rw [ite_eq_right he,ite_eq_right he,h2.get _ h0,h1.get _ h25]
    exact hp i hi

theorem vchg_core {s s' : State} {rs : List VReg} (h : VChg rs s s') : CoreKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r,h.mem,h.rd,h.wr,h.sp⟩

/-- One portable NEON round of Keccak, on two independent states. -/
theorem round_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (round r)) s fun s' => CoreKeep s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold round
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s₁ ⟨h1,hv1,hc1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.theta_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s₂ ⟨h2,hp2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.rhoPi_ok hp2) fun s₃ ⟨h3,hp3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.chi_ok hp3) fun s₄ ⟨h4,hp4⟩ => ?_
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.iota_ok hp4 r (by rw [h4.gpr,h3.gpr,h2.gpr,hc1,constantLow_RC r hr]))
    fun s₅ ⟨h5,hp5⟩ => ⟨h1.trans ((VG.Proof.Sha3.AArch64.Neon.vchg_core h2).trans ((VG.Proof.Sha3.AArch64.Neon.vchg_core h3).trans ((VG.Proof.Sha3.AArch64.Neon.vchg_core h4).trans (VG.Proof.Sha3.AArch64.Neon.vchg_core h5)))),hp5⟩
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- All 24 rounds of Keccak-f[1600] on two independent NEON states. -/
theorem rounds_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block rounds) s fun s' => CoreKeep s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold rounds
  refine wp_range_flatMap (M := isa)
    (fun k s' => CoreKeep s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s'
      ((List.range k).foldl Spec.Sha3.rnd A) ((List.range k).foldl Spec.Sha3.rnd B))
    (fun k s' hk ⟨hc,hp'⟩ => ?_) 24 (Nat.le_refl _) s ⟨CoreKeep.refl _,hp⟩
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.round_ok hp' hk) fun s'' ⟨hc',hp''⟩ => ⟨hc.trans hc',?_⟩
  simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hp''
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)

def pairR (p : Addr) : Region := ⟨p,400⟩
def wordAddr (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (16*i)

def PairAt (m : Mem) (p : Addr) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, m.read (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16 = ofVDwords A[i]! B[i]!

theorem pair_contains (p : Addr) {i : Nat} (hi : i < 25) :
    (VG.Proof.Sha3.AArch64.Neon.pairR p).Contains (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16 := Offset.contains_base p (by omega) (by omega)

/-- Load two packed states into the same register layout used by the verified rounds. -/
theorem load_ok {s : State} {p : Addr} {r : Reg} {A B : Spec.Sha3.State}
    (hr : s.gpr r = p) (hp : VG.Proof.Sha3.AArch64.Neon.PairAt s.mem p A B) (hin : ∀ i < 25, InRegions (s.rd++s.wr) (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.load r)) s fun s' =>
      VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧ VG.Proof.Sha3.AArch64.Neon.Pairs s' A B := by
  unfold Impl.Sha3.AArch64.Neon.Pair.load
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k s' => VChg VG.Proof.Sha3.AArch64.Neon.allV s s' ∧ ∀ i < k, s'.v (vreg i) = ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hchg,hvals⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨VChg.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_ldrq (t := vreg k) (a := VG.Proof.Sha3.AArch64.Neon.wordAddr p k) (by omega)
    (by rw [hchg.gpr,hr]; rfl)
    (by rw [hchg.rd,hchg.wr]; exact hin k hk)
    fun s'' h => WP.block_nil_iff.mpr ⟨(hchg.trans h.chg).mono (fun v _ => VG.Proof.Sha3.AArch64.Neon.allV_mem v),?_⟩
  intro i hi
  by_cases he : i = k
  · subst i
    rw [h.v,hchg.mem,hp k hk]
  · rw [h.get (vreg i) (by rw [ne_eq,VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) k (by omega)]; exact he)]
    exact hvals i (by omega)
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VMem wp_strq)

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v := by
  have h := Mem.readW_writeW_self m p 16 v (by decide)
  exact h

/-- Store paired states while framing the rest of the sampler's scratch space. -/
theorem store_ok {s : State} {p : Addr} {r : Reg} {A B : Spec.Sha3.State}
    (hr : s.gpr r = p) (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B)
    (hw : ∀ i < 25, InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.store r)) s fun s' =>
      VMem s s' s'.mem ∧ VG.Proof.Sha3.AArch64.Neon.PairAt s'.mem p A B ∧ Frame [VG.Proof.Sha3.AArch64.Neon.pairR p] s.mem s'.mem := by
  unfold Impl.Sha3.AArch64.Neon.Pair.store
  rw [List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VMem s s' s'.mem ∧ Frame [VG.Proof.Sha3.AArch64.Neon.pairR p] s.mem s'.mem ∧
      ∀ i < k, s'.mem.read (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16 = ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hmem,hframe,hvals⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun s' ⟨hmem,hframe,hvals⟩ => ⟨hmem,hvals,hframe⟩
  refine wp_strq (t := vreg k) (a := VG.Proof.Sha3.AArch64.Neon.wordAddr p k) (by omega)
    (by rw [hmem.gpr,hr]; rfl) (by rw [hmem.wr]; exact hw k hk)
    fun s'' h => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨h.gpr.trans hmem.gpr,h.v.trans hmem.v,rfl,h.rd.trans hmem.rd,h.wr.trans hmem.wr,h.sp.trans hmem.sp⟩
  · rw [h.mem]
    exact hframe.write (List.mem_singleton_self _) _ (VG.Proof.Sha3.AArch64.Neon.pair_contains p hk)
  · intro i hi
    rw [h.mem]
    by_cases he : i = k
    · subst i
      rw [VG.Proof.Sha3.AArch64.Neon.read_write16,hmem.v,hp k hk]
    · have hsep : Mem.Sep (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16 (VG.Proof.Sha3.AArch64.Neon.wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega)
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64 (Upd Mupd wp_str)

structure OutKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem OutKeep.refl (s : State) : VG.Proof.Sha3.AArch64.Neon.OutKeep s s := ⟨fun _ _ _ => rfl,rfl,rfl,rfl,rfl⟩
theorem OutKeep.trans {s t u : State} (h : VG.Proof.Sha3.AArch64.Neon.OutKeep s t) (k : VG.Proof.Sha3.AArch64.Neon.OutKeep t u) : VG.Proof.Sha3.AArch64.Neon.OutKeep s u :=
  ⟨fun r h6 h7 => (k.gpr r h6 h7).trans (h.gpr r h6 h7), k.vec.trans h.vec,
    k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem OutKeep.upd {s t : State} {r : Reg} {v : BitVec 64}
    (h : Upd s t r v) (hr : r = .x6 ∨ r = .x7) : VG.Proof.Sha3.AArch64.Neon.OutKeep s t :=
  ⟨fun q h6 h7 => h.other q (by rcases hr with h | h <;> subst r <;> with_reducible assumption),h.vec,h.rd,h.wr,h.sp⟩
theorem OutKeep.mem {s t : State} {m : Mem} (h : Mupd s t m) : VG.Proof.Sha3.AArch64.Neon.OutKeep s t :=
  ⟨fun _ _ _ => congrFun h.gpr _,h.vec,h.rd,h.wr,h.sp⟩

def outAddr (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (8*i)
def outR (p : Addr) : Region := ⟨p,168⟩
def RateAt (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 21, m.readW (VG.Proof.Sha3.AArch64.Neon.outAddr p i) 64 = A[i]!

theorem out_contains (p : Addr) {i : Nat} (hi : i < 21) :
    (VG.Proof.Sha3.AArch64.Neon.outR p).Contains (VG.Proof.Sha3.AArch64.Neon.outAddr p i) 8 := Offset.contains_base p (by omega) (by omega)

theorem squeeze_step {s : State} {a b : Addr} {ra rb : Reg} {i : Nat} (hi : i < 21)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hwa : InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr a i) 8) (hwb : InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr b i) 8) :
    WP isa (.block ([.umov .x .x6 (vreg i) 0,.umov .x .x7 (vreg i) 1,
      .str .x .x6 ra (8*i),.str .x .x7 rb (8*i)] : List Instr)) s fun t =>
      VG.Proof.Sha3.AArch64.Neon.OutKeep s t ∧ t.mem = (s.mem.writeW (VG.Proof.Sha3.AArch64.Neon.outAddr a i) (vdword (s.v (vreg i)) 0)).writeW
        (VG.Proof.Sha3.AArch64.Neon.outAddr b i) (vdword (s.v (vreg i)) 1) := by
  refine WP.cons (s' := s.write .x .x6 (vdword (s.v (vreg i)) 0)) (by rfl) ?_
  have h1 := Upd.write64 s .x6 (vdword (s.v (vreg i)) 0)
  let s1 := s.write .x .x6 (vdword (s.v (vreg i)) 0)
  refine WP.cons (s' := s1.write .x .x7 (vdword (s1.v (vreg i)) 1)) (by rfl) ?_
  have h2 := Upd.write64 s1 .x7 (vdword (s1.v (vreg i)) 1)
  refine wp_str ⟨by omega,by omega⟩
    (by rw [h2.other ra ha7,h1.other ra ha6,ha])
    (by rw [h2.wr,h1.wr]; exact hwa) fun s3 h3 => ?_
  refine wp_str ⟨by omega,by omega⟩
    (by rw [h3.gpr,h2.other rb hb7,h1.other rb hb6,hb])
    (by rw [h3.wr,h2.wr,h1.wr]; exact hwb) fun s4 h4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((OutKeep.upd h1 (Or.inl rfl)).trans (OutKeep.upd h2 (Or.inr rfl))).trans
      ((OutKeep.mem h3).trans (OutKeep.mem h4))
  · rw [h4.mem,h3.mem,h3.gpr,h2.gpr,h2.other .x6 (by decide),h1.gpr,h2.mem,h1.mem,h1.vec]
    rfl

/-- Copy a complete rate block for each state without changing the packed states. -/
theorem squeeze_ok {s : State} {a b : Addr} {ra rb : Reg} {A B : Spec.Sha3.State}
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) (hd : (VG.Proof.Sha3.AArch64.Neon.outR a).Disjoint (VG.Proof.Sha3.AArch64.Neon.outR b))
    (hwa : ∀ i < 21, InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr a i) 8)
    (hwb : ∀ i < 21, InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr b i) 8) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.squeeze ra rb)) s fun t =>
      VG.Proof.Sha3.AArch64.Neon.OutKeep s t ∧ VG.Proof.Sha3.AArch64.Neon.RateAt t.mem a A ∧ VG.Proof.Sha3.AArch64.Neon.RateAt t.mem b B ∧ Frame [VG.Proof.Sha3.AArch64.Neon.outR a,VG.Proof.Sha3.AArch64.Neon.outR b] s.mem t.mem := by
  unfold Impl.Sha3.AArch64.Neon.Pair.squeeze
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => VG.Proof.Sha3.AArch64.Neon.OutKeep s t ∧ Frame [VG.Proof.Sha3.AArch64.Neon.outR a,VG.Proof.Sha3.AArch64.Neon.outR b] s.mem t.mem ∧
      (∀ i < k, t.mem.readW (VG.Proof.Sha3.AArch64.Neon.outAddr a i) 64 = A[i]!) ∧
      (∀ i < k, t.mem.readW (VG.Proof.Sha3.AArch64.Neon.outAddr b i) 64 = B[i]!))
    (fun k t hk ⟨ht,hf,hva,hvb⟩ => ?_) 21 (Nat.le_refl _) s
    ⟨OutKeep.refl _,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h),
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,hf,hva,hvb⟩ => ⟨ht,hva,hvb,hf⟩
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.squeeze_step hk ((ht.gpr ra ha6 ha7).trans ha) ((ht.gpr rb hb6 hb7).trans hb)
    ha6 ha7 hb6 hb7 (by rw [ht.wr]; exact hwa k hk) (by rw [ht.wr]; exact hwb k hk))
    fun u ⟨hu,hm⟩ => ⟨ht.trans hu,?_,?_,?_⟩
  · rw [hm]
    exact (hf.writeW (by simp) _ (VG.Proof.Sha3.AArch64.Neon.out_contains a hk)).writeW (by simp) _ (VG.Proof.Sha3.AArch64.Neon.out_contains b hk)
  · intro i hi
    rw [hm,Mem.readW_writeW_sep (hd.sep (VG.Proof.Sha3.AArch64.Neon.out_contains a (by omega)) (VG.Proof.Sha3.AArch64.Neon.out_contains b hk)) (by decide)]
    by_cases he : i = k
    · subst i
      rw [Mem.readW_writeW_self64,ht.vec,hp k (by omega),vdword_ofVDwords_0]
    · rw [Mem.readW_writeW_sep (Offset.sep a (d := 8*i) (n := 8) (e := 8*k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hva i (by omega)
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      rw [Mem.readW_writeW_self64,ht.vec,hp k (by omega),vdword_ofVDwords_1]
    · rw [Mem.readW_writeW_sep (Offset.sep b (d := 8*i) (n := 8) (e := 8*k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (hd.symm.sep (VG.Proof.Sha3.AArch64.Neon.out_contains b (by omega)) (VG.Proof.Sha3.AArch64.Neon.out_contains a hk)) (by decide)]
      exact hvb i (by omega)

/-- Word-wise output is the SHA-3 specification's byte serialization. -/
theorem RateAt.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : VG.Proof.Sha3.AArch64.Neon.RateAt m p A)
    {j : Nat} (hj : j < 168) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (VG.Proof.Sha3.AArch64.Neon.outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [VG.Proof.Sha3.AArch64.Neon.outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega] at he
  exact he
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector

def lane (s : State) (e : Nat) : Low := fun r => vdword (s.v r) e

theorem lane_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword,BitVec.extractLsb'_xor]
theorem lane_and (a b : BitVec 128) (e : Nat) : vdword (a &&& b) e = vdword a e &&& vdword b e := by
  simp only [vdword,BitVec.extractLsb'_and]
theorem lane_not (a : BitVec 128) {e : Nat} (he : e < 2) : vdword (~~~a) e = ~~~vdword a e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_not,hi,decide_true,Bool.true_and,
    show 64*e+i < 128 by omega]

theorem lane_setV (s : State) (d : VReg) (v : BitVec 128) (e : Nat) :
    VG.Proof.Sha3.AArch64.Neon.Hw.lane (s.setV d v) e = put (VG.Proof.Sha3.AArch64.Neon.Hw.lane s e) d (vdword v e) := by
  funext r
  simp only [VG.Proof.Sha3.AArch64.Neon.Hw.lane,put,RegUpd.v_setV]
  split <;> rfl

theorem op_lane (s : State) (op : Op) {e : Nat} (he : e < 2) :
    VG.Proof.Sha3.AArch64.Neon.Hw.lane (opState s op) e = opLow (VG.Proof.Sha3.AArch64.Neon.Hw.lane s e) op := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact op_low s op
  · cases op <;> simp only [opState,VG.Proof.Sha3.AArch64.Neon.Hw.lane_setV,opLow,VG.Proof.Sha3.AArch64.Neon.Hw.lane_xor,VG.Proof.Sha3.AArch64.Neon.Hw.lane_and,VG.Proof.Sha3.AArch64.Neon.Hw.lane_not _ (by decide : 1 < 2),
      VArr.map2,vdword_ofVDwords_1,VG.Proof.Sha3.AArch64.Neon.Hw.lane]

/-- The SHA3 instructions operate independently on both 64-bit lanes. -/
theorem ops_lanes (ops : List Op) (s : State) :
    WP isa (.block (ops.map Op.instr)) s fun t => Keep s t ∧
      ∀ e < 2,VG.Proof.Sha3.AArch64.Neon.Hw.lane t e = runLow ops (VG.Proof.Sha3.AArch64.Neon.Hw.lane s e) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨Keep.refl _,fun _ _ => rfl⟩
  | cons op ops ih =>
    refine VG.Proof.Sha3.AArch64.WP.cons (op_exec s op)
      (WP.mono (ih (opState s op)) fun t ⟨ht,hl⟩ => ⟨(op_keep s op).trans ht,?_⟩)
    intro e he
    rw [hl e he,VG.Proof.Sha3.AArch64.Neon.Hw.op_lane s op he]
    rfl

/-- The existing register schedule's pure mathematics applies to either lane. -/
theorem core_math (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) :
    CLanes (runLow (theta++rhoPi++chi) σ) A := by
  have ht := theta_lanes σ A h
  have hd : DLanes (runLow theta σ) A := theta_d σ A h
  have hr := rho_lanes (runLow theta σ) A ht hd
  have hc := chi_lanes (runLow rhoPi (runLow theta σ)) A hr
  simpa only [runLow,List.foldl_append] using hc
end VG.Proof.Sha3.AArch64.Neon.Hw

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def CPairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25,s.v (vreg i) = ofVDwords (chiWord A i) (chiWord B i)

theorem core2_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block ((theta++rhoPi++chi).map Op.instr)) s fun t => Keep s t ∧ VG.Proof.Sha3.AArch64.Neon.Hw.CPairs t A B := by
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.ops_lanes (theta++rhoPi++chi) s) fun t ⟨ht,hl⟩ => ⟨ht,?_⟩
  have ha : ALanes (VG.Proof.Sha3.AArch64.Neon.Hw.lane s 0) A := by
    intro i hi
    change vdword (s.v (vreg i)) 0 = _
    rw [hp i hi,vdword_ofVDwords_0,Proof.Sha3.getElem!_eq A hi]
  have hb : ALanes (VG.Proof.Sha3.AArch64.Neon.Hw.lane s 1) B := by
    intro i hi
    change vdword (s.v (vreg i)) 1 = _
    rw [hp i hi,vdword_ofVDwords_1,Proof.Sha3.getElem!_eq B hi]
  have hca := VG.Proof.Sha3.AArch64.Neon.Hw.core_math (VG.Proof.Sha3.AArch64.Neon.Hw.lane s 0) A ha
  have hcb := VG.Proof.Sha3.AArch64.Neon.Hw.core_math (VG.Proof.Sha3.AArch64.Neon.Hw.lane s 1) B hb
  intro i hi
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    change VG.Proof.Sha3.AArch64.Neon.Hw.lane t 0 (vreg i) = _
    rw [hl 0 (by decide)]
    exact hca i hi
  · rw [vdword_ofVDwords_1]
    change VG.Proof.Sha3.AArch64.Neon.Hw.lane t 1 (vreg i) = _
    rw [hl 1 (by decide)]
    exact hcb i hi

theorem out_word (A : Spec.Sha3.State) (rc : BitVec 64) {i : Nat} (hi : i < 25) :
    (Proof.Sha3.outState A rc)[i]! = if i = 0 then chiWord A i ^^^ rc else chiWord A i := by
  rw [Proof.Sha3.getElem!_eq _ hi,chiWord_out A rc i hi]

theorem iota2_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Hw.CPairs s A B) (rc : BitVec 64)
    (hc : s.gpr .x16 = rc) :
    WP isa (.block iota) s fun t => VChg VG.Proof.Sha3.AArch64.Neon.allV s t ∧
      VG.Proof.Sha3.AArch64.Neon.Pairs t (Proof.Sha3.outState A rc) (Proof.Sha3.outState B rc) := by
  unfold iota
  refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun t h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => VG.Proof.Sha3.AArch64.Neon.allV_mem v),?_⟩
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Neon.Hw.out_word A rc hi,VG.Proof.Sha3.AArch64.Neon.Hw.out_word B rc hi]
  by_cases h0 : i = 0
  · subst i
    change t.v .v0 = ofVDwords (chiWord A 0 ^^^ rc) (chiWord B 0 ^^^ rc)
    rw [h2.v,h1.get .v0,h1.v,hc]
    change s.v .v0 ^^^ ofVDwords rc rc = _
    have hp0 : s.v .v0 = ofVDwords (chiWord A 0) (chiWord B 0) := hp 0 (by decide)
    rw [hp0,VG.Proof.Sha3.AArch64.Neon.pair_xor]
  · rw [ite_eq_right h0,ite_eq_right h0,h2.get (vreg i) (by
      change ¬ vreg i = vreg 0
      rw [VG.Proof.Sha3.AArch64.Neon.vreg_inj i (by omega) 0 (by decide)]; exact h0),h1.get (vreg i)
      ((show ∀ i < 25,vreg i ≠ .v26 by decide) i hi)]
    exact hp i hi

theorem round2_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (round r)) s fun t => CoreKeep s t ∧ VG.Proof.Sha3.AArch64.Neon.Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++ chi.map Op.instr ++ iota =
    constant (Spec.Sha3.RC r) ++ (theta++rhoPi++chi).map Op.instr ++ iota by
      simp only [List.map_append,List.append_assoc]]
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s1 ⟨h1,hv1,hrc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.core2_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s2 ⟨h2,hp2⟩ => ?_
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.iota2_ok hp2 (Spec.Sha3.RC r) (by rw [h2.gpr,hrc,constantLow_RC r hr]))
    fun t ⟨h3,hpt⟩ => ⟨h1.trans (h2.core.trans (VG.Proof.Sha3.AArch64.Neon.vchg_core h3)),?_⟩
  simpa only [Proof.Sha3.outState_eq] using hpt
end VG.Proof.Sha3.AArch64.Neon.Hw

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

theorem rounds2_ok {s : State} {A B : Spec.Sha3.State} (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    WP isa (.block rounds) s fun t => CoreKeep s t ∧ VG.Proof.Sha3.AArch64.Neon.Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold rounds
  refine wp_range_flatMap (M := isa)
    (fun k t => CoreKeep s t ∧ VG.Proof.Sha3.AArch64.Neon.Pairs t
      ((List.range k).foldl Spec.Sha3.rnd A) ((List.range k).foldl Spec.Sha3.rnd B))
    (fun k t hk ⟨ht,hpt⟩ => ?_) 24 (Nat.le_refl _) s ⟨CoreKeep.refl _,hp⟩
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.round2_ok hpt hk) fun u ⟨hu,hpu⟩ => ⟨ht.trans hu,?_⟩
  simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpu
end VG.Proof.Sha3.AArch64.Neon.Hw

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

structure BlockKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem roundsProg_ok (sha3 : Bool) {n : Nat} (hn : n ≤ 24) {s : State} {A B : Spec.Sha3.State}
    (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) : WP isa (Impl.Sha3.AArch64.Neon.Pair.roundsProg sha3 n) s fun t =>
      CoreKeep s t ∧ VG.Proof.Sha3.AArch64.Neon.Pairs t ((List.range n).foldl Spec.Sha3.rnd A) ((List.range n).foldl Spec.Sha3.rnd B) := by
  induction n generalizing s A B with
  | zero => exact WP.block_nil_iff.mpr ⟨CoreKeep.refl _,hp⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega) hp) fun u ⟨hu,hpu⟩ => ?_)
    have hr : WP isa (.block (if sha3 then Impl.Sha3.AArch64.Sha3.Vector.round n else
        Impl.Sha3.AArch64.Neon.Vector.round n)) u fun t => CoreKeep u t ∧
          VG.Proof.Sha3.AArch64.Neon.Pairs t (Spec.Sha3.rnd ((List.range n).foldl Spec.Sha3.rnd A) n)
            (Spec.Sha3.rnd ((List.range n).foldl Spec.Sha3.rnd B) n) := by
      cases sha3
      · exact VG.Proof.Sha3.AArch64.Neon.round_ok hpu (by omega)
      · exact Hw.round2_ok hpu (by omega)
    refine WP.mono hr fun t ⟨ht,hpt⟩ => ⟨hu.trans ht,?_⟩
    simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpt

/-- One permutation and one output block for two independent SHAKE128 streams. -/
theorem prog_okWith (sha3 : Bool) {s : State} {p a b : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hp16 : rp ≠ .x16)
    (hpair : VG.Proof.Sha3.AArch64.Neon.PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16)
    (hwp : ∀ i < 25, InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.wordAddr p i) 16)
    (hwa : ∀ i < 21, InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr a i) 8)
    (hwb : ∀ i < 21, InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr b i) 8)
    (hd : (VG.Proof.Sha3.AArch64.Neon.outR a).Disjoint (VG.Proof.Sha3.AArch64.Neon.outR b))
    (hpa : (VG.Proof.Sha3.AArch64.Neon.pairR p).Disjoint (VG.Proof.Sha3.AArch64.Neon.outR a)) (hpb : (VG.Proof.Sha3.AArch64.Neon.pairR p).Disjoint (VG.Proof.Sha3.AArch64.Neon.outR b)) :
    WP isa (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 rp ra rb) s fun t =>
      VG.Proof.Sha3.AArch64.Neon.BlockKeep s t ∧ VG.Proof.Sha3.AArch64.Neon.PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      VG.Proof.Sha3.AArch64.Neon.RateAt t.mem a (Spec.Sha3.keccakF A) ∧ VG.Proof.Sha3.AArch64.Neon.RateAt t.mem b (Spec.Sha3.keccakF B) ∧
      Frame [VG.Proof.Sha3.AArch64.Neon.pairR p,VG.Proof.Sha3.AArch64.Neon.outR a,VG.Proof.Sha3.AArch64.Neon.outR b] s.mem t.mem := by
  unfold Impl.Sha3.AArch64.Neon.Pair.progWith
  refine WP.seq (WP.mono (VG.Proof.Sha3.AArch64.Neon.load_ok hp hpair hin) fun s1 ⟨h1,hpair1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Sha3.AArch64.Neon.roundsProg_ok sha3 (by decide : 24 ≤ 24) hpair1) fun s2 ⟨h2,hpair2⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Sha3.AArch64.Neon.store_ok ((h2.gpr rp hp16).trans ((congrFun h1.gpr rp).trans hp)) hpair2
    (fun i hi => by rw [h2.wr,h1.wr]; exact hwp i hi)) fun s3 ⟨h3,hpair3,hf3⟩ => ?_)
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.squeeze_ok (A := Spec.Sha3.keccakF A) (B := Spec.Sha3.keccakF B)
    (by rw [h3.gpr,h2.gpr ra ha16,h1.gpr,ha])
    (by rw [h3.gpr,h2.gpr rb hb16,h1.gpr,hb]) ha6 ha7 hb6 hb7
    (by intro i hi; rw [h3.v]; exact hpair2 i hi) hd
    (fun i hi => by rw [h3.wr,h2.wr,h1.wr]; exact hwa i hi)
    (fun i hi => by rw [h3.wr,h2.wr,h1.wr]; exact hwb i hi)) fun t ⟨h4,hra,hrb,hf4⟩ => ?_
  refine ⟨⟨fun r h6 h7 h16 => by rw [h4.gpr r h6 h7,h3.gpr,h2.gpr r h16,h1.gpr],
    h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd)),
    h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr)),
    h4.sp.trans (h3.sp.trans (h2.sp.trans h1.sp))⟩,?_,hra,hrb,?_⟩
  · intro i hi
    rw [hf4.read (VG.Proof.Sha3.AArch64.Neon.pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl; exact hpa; exact hpb) (by decide)]
    exact hpair3 i hi
  · have hf3' : Frame [VG.Proof.Sha3.AArch64.Neon.pairR p,VG.Proof.Sha3.AArch64.Neon.outR a,VG.Proof.Sha3.AArch64.Neon.outR b] s.mem s3.mem := by
      rw [← h1.mem,← h2.mem]
      exact hf3.sub (fun r hr => ⟨r,by simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self,fun _ h => h⟩)
    exact hf3'.trans (hf4.sub (fun r hr => ⟨r,List.mem_cons_of_mem _ hr,fun _ h => h⟩))
end VG.Proof.Sha3.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep`. -/
section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only VUpd VMem)
open VG.Proof.Sha3.AArch64 (Upd Mupd)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- Scalar fields preserved by a kernel that may use every vector register. -/
structure RegKeep (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem RegKeep.refl (rs : List Reg) (s : State) : VG.Proof.Sha3.AArch64.Neon.RegKeep rs s s := ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
theorem RegKeep.trans {rs ts : List Reg} {s t u : State} (h : VG.Proof.Sha3.AArch64.Neon.RegKeep rs s t) (k : VG.Proof.Sha3.AArch64.Neon.RegKeep ts t u) :
    VG.Proof.Sha3.AArch64.Neon.RegKeep (rs++ts) s u :=
  ⟨fun r hr => (k.gpr r (fun ht => hr (List.mem_append.mpr (.inr ht)))).trans
    (h.gpr r (fun hs => hr (List.mem_append.mpr (.inl hs)))),k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem RegKeep.mono {rs ts : List Reg} {s t : State} (h : VG.Proof.Sha3.AArch64.Neon.RegKeep rs s t) (hm : ∀ r ∈ rs,r ∈ ts) :
    VG.Proof.Sha3.AArch64.Neon.RegKeep ts s t := ⟨fun r hr => h.gpr r (fun hs => hr (hm r hs)),h.rd,h.wr,h.sp⟩
theorem RegKeep.upd {s t : State} {r : Reg} {v : BitVec 64} (h : Upd s t r v) : VG.Proof.Sha3.AArch64.Neon.RegKeep [r] s t :=
  ⟨fun q hq => h.other q (by simpa using hq),h.rd,h.wr,h.sp⟩
theorem RegKeep.only {rs : List Reg} {s t : State} (h : Only rs s t) : VG.Proof.Sha3.AArch64.Neon.RegKeep rs s t :=
  ⟨h.gpr,h.rd,h.wr,h.sp⟩
theorem RegKeep.vupd {s t : State} {r : VReg} {v : BitVec 128} (h : VUpd s t r v) : VG.Proof.Sha3.AArch64.Neon.RegKeep [] s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp⟩
theorem RegKeep.vmem {s t : State} {m : Mem} (h : VMem s t m) : VG.Proof.Sha3.AArch64.Neon.RegKeep [] s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp⟩
theorem RegKeep.mupd {s t : State} {m : Mem} (h : Mupd s t m) : VG.Proof.Sha3.AArch64.Neon.RegKeep [] s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp⟩
end VG.Proof.Sha3.AArch64.Neon

end
