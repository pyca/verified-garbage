module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Chi
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Theta
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Sha3.AArch64.Neon.HwLanes`, which only this module used -/

section

@[expose] public section

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
    show 64*e+i < 128 by omega_using [he, hi]]

theorem lane_setV (s : State) (d : VReg) (v : BitVec 128) (e : Nat) :
    lane (s.setV d v) e = put (lane s e) d (vdword v e) := by
  funext r
  simp only [lane,put,RegUpd.v_setV]
  split <;> rfl

theorem op_lane (s : State) (op : Op) {e : Nat} (he : e < 2) :
    lane (opState s op) e = opLow (lane s e) op := by
  rcases (show e = 0 ∨ e = 1 by omega_using [he]) with rfl | rfl
  · exact op_low s op
  · cases op <;> simp only [opState,lane_setV,opLow,lane_xor,lane_and,lane_not _ (by decide : 1 < 2),
      VArr.map2,vdword_ofVDwords_1,lane]

/-- The SHA3 instructions operate independently on both 64-bit lanes. -/
theorem ops_lanes (ops : List Op) (s : State) :
    WP isa (.block (ops.map Op.instr)) s fun t => Keep s t ∧
      ∀ e < 2,lane t e = runLow ops (lane s e) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨Keep.refl _,fun _ _ => rfl⟩
  | cons op ops ih =>
    refine VG.Proof.Sha3.AArch64.WP.cons (op_exec s op)
      (WP.mono (ih (opState s op)) fun t ⟨ht,hl⟩ => ⟨(op_keep s op).trans ht,?_⟩)
    intro e he
    rw [hl e he,op_lane s op he]
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

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def CPairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25,s.v (vreg i) = ofVDwords (chiWord A i) (chiWord B i)

theorem core2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block ((theta++rhoPi++chi).map Op.instr)) s fun t => Keep s t ∧ CPairs t A B := by
  refine WP.mono (ops_lanes (theta++rhoPi++chi) s) fun t ⟨ht,hl⟩ => ⟨ht,?_⟩
  have ha : ALanes (lane s 0) A := by
    intro i hi
    change vdword (s.v (vreg i)) 0 = _
    rw [hp i hi,vdword_ofVDwords_0,Proof.Sha3.getElem!_eq A hi]
  have hb : ALanes (lane s 1) B := by
    intro i hi
    change vdword (s.v (vreg i)) 1 = _
    rw [hp i hi,vdword_ofVDwords_1,Proof.Sha3.getElem!_eq B hi]
  have hca := core_math (lane s 0) A ha
  have hcb := core_math (lane s 1) B hb
  intro i hi
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    change lane t 0 (vreg i) = _
    rw [hl 0 (by decide)]
    exact hca i hi
  · rw [vdword_ofVDwords_1]
    change lane t 1 (vreg i) = _
    rw [hl 1 (by decide)]
    exact hcb i hi

theorem out_word (A : Spec.Sha3.State) (rc : BitVec 64) {i : Nat} (hi : i < 25) :
    (Proof.Sha3.outState A rc)[i]! = if i = 0 then chiWord A i ^^^ rc else chiWord A i := by
  rw [Proof.Sha3.getElem!_eq _ hi,chiWord_out A rc i hi]

theorem iota2_ok {s : State} {A B : Spec.Sha3.State} (hp : CPairs s A B) (rc : BitVec 64)
    (hc : s.gpr .x16 = rc) :
    WP isa (.block iota) s fun t => VChg allV s t ∧
      Pairs t (Proof.Sha3.outState A rc) (Proof.Sha3.outState B rc) := by
  unfold iota
  refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun t h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => allV_mem v),?_⟩
  intro i hi
  rw [out_word A rc hi,out_word B rc hi]
  by_cases h0 : i = 0
  · subst i
    change t.v .v0 = ofVDwords (chiWord A 0 ^^^ rc) (chiWord B 0 ^^^ rc)
    rw [h2.v,h1.get .v0,h1.v,hc]
    change s.v .v0 ^^^ ofVDwords rc rc = _
    have hp0 : s.v .v0 = ofVDwords (chiWord A 0) (chiWord B 0) := hp 0 (by decide)
    rw [hp0,pair_xor]
  · rw [ite_eq_right h0,ite_eq_right h0,h2.get (vreg i) (by
      change ¬ vreg i = vreg 0
      rw [vreg_inj i (by omega_using [hi]) 0 (by decide)]; exact h0),h1.get (vreg i)
      ((show ∀ i < 25,vreg i ≠ .v26 by decide) i hi)]
    exact hp i hi

theorem round2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (round r)) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++ chi.map Op.instr ++ iota =
    constant (Spec.Sha3.RC r) ++ (theta++rhoPi++chi).map Op.instr ++ iota by
      simp only [List.map_append,List.append_assoc]]
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s1 ⟨h1,hv1,hrc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (core2_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s2 ⟨h2,hp2⟩ => ?_
  refine WP.mono (iota2_ok hp2 (Spec.Sha3.RC r) (by rw [h2.gpr,hrc,constantLow_RC r hr]))
    fun t ⟨h3,hpt⟩ => ⟨h1.trans (h2.core.trans (vchg_core h3)),?_⟩
  simpa only [Proof.Sha3.outState_eq] using hpt
end VG.Proof.Sha3.AArch64.Neon.Hw
