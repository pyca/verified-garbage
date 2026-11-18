module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! ### `MlDsa.AArch64.Optimized.ResponseFlags`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

/-- The per-lane accumulator records whether any processed group failed. -/
def flagBad (bad : Nat → Nat → Bool) : Nat → Nat → Bool
  | 0,_ => false
  | j+1,e => flagBad bad j e || bad j e

theorem maskWord_or (a b : Bool) : maskWord a ||| maskWord b=maskWord (a||b) := by
  cases a <;> cases b <;> rfl

theorem flagBad_false (bad : Nat → Nat → Bool) (j e : Nat) :
    flagBad bad j e=false ↔ ∀i<j,bad i e=false := by
  induction j with
  | zero => simp [flagBad]
  | succ j ih =>
    simp only [flagBad,Bool.or_eq_false_iff,ih]
    constructor
    · rintro ⟨h,hj⟩ i hi
      by_cases he : i=j
      · simpa only [he] using hj
      · exact h i (by omega_using [hi, he])
    · intro h
      exact ⟨fun i hi => h i (by omega_using [hi]),h j (by omega_using [])⟩

theorem finishValue_flags {v : BitVec 128} {bad : Nat → Nat → Bool} {j : Nat}
    (h : ∀e<4,vword v e=maskWord (flagBad bad j e)) :
    finishValue v=1 ↔ (∀i<j,∀e<4,bad i e=false) := by
  have hv : v=ofVWords (maskWord (flagBad bad j 0)) (maskWord (flagBad bad j 1))
      (maskWord (flagBad bad j 2)) (maskWord (flagBad bad j 3)) := by
    apply vec_ext
    intro e he
    rw [h e he,vword_ofVWords _ _ _ _ he]
    rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl <;> rfl
  rw [hv,finishValue_masks]
  have he : (flagBad bad j 0 || flagBad bad j 1 || flagBad bad j 2 || flagBad bad j 3)=false ↔
      ∀i<j,∀e<4,bad i e=false := by
    simp only [Bool.or_eq_false_iff,flagBad_false]
    constructor
    · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ i hi e he
      rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl
      · exact h0 i hi
      · exact h1 i hi
      · exact h2 i hi
      · exact h3 i hi
    · intro h
      exact ⟨⟨⟨fun i hi=>h i hi 0 (by decide),fun i hi=>h i hi 1 (by decide)⟩,
        fun i hi=>h i hi 2 (by decide)⟩,fun i hi=>h i hi 3 (by decide)⟩
  rw [← he]
  cases hbad : (flagBad bad j 0 || flagBad bad j 1 || flagBad bad j 2 || flagBad bad j 3) <;> simp

theorem finishValue_flags_range {v : BitVec 128} {bad : Nat → Nat → Bool} {j : Nat}
    (h : ∀e<4,vword v e=maskWord (flagBad bad j e)) :
    finishValue v=0 ∨ finishValue v=1 := by
  have hv : v=ofVWords (maskWord (flagBad bad j 0)) (maskWord (flagBad bad j 1))
      (maskWord (flagBad bad j 2)) (maskWord (flagBad bad j 3)) := by
    apply vec_ext
    intro e he
    rw [h e he,vword_ofVWords _ _ _ _ he]
    rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl <;> rfl
  rw [hv,finishValue_masks]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

structure ZReady (B : BitVec 32) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v16) e=8380417#32
  c : ∀e<4,vword (s.v .v25) e=4194304#32
  lo : ∀e<4,vword (s.v .v27) e=B-1
  width : ∀e<4,vword (s.v .v24) e=B+(B-1)

theorem ZReady.frame {B : BitVec 32} {s t : State} {rs : List VReg}
    (h : ZReady B s) (hv : ∀r∈[VReg.v16,.v25,.v27,.v24],r∉rs)
    (hf : ∀r,r∉rs → t.v r=s.v r) : ZReady B t := by
  constructor
  · intro e he; rw [hf .v16 (hv _ (by simp))]; exact h.q e he
  · intro e he; rw [hf .v25 (hv _ (by simp))]; exact h.c e he
  · intro e he; rw [hf .v27 (hv _ (by simp))]; exact h.lo e he
  · intro e he; rw [hf .v24 (hv _ (by simp))]; exact h.width e he

def addInit : List Instr :=
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v16 8380417 ++
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v25 4194304 ++
  [.vop (.dup .s4 .v24 .x2),.vop (.movi0 .v31)] ++
  VG.Impl.MlDsa.AArch64.Optimized.Response.normConstants

theorem addInit_ok (s : State) : WP isa (.block addInit) s fun t =>
    SetupKeep [.v16,.v25,.v24,.v31,.v27] s t ∧
    ZReady ((s.gpr .x2).setWidth 32) t ∧ t.v .v31=0 := by
  unfold addInit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v25 4194304) fun b hb => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v24) rfl fun c hc => wp_vop (d := .v31) rfl fun d hd => ?_
  refine WP.mono (normConstants_ok d) fun t ⟨ht,hlo,hw⟩ => ?_
  have hsc : SetupKeep [.v16,.v25,.v24,.v31] s d := setup_mono
    (((SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst hb.1)).trans (setup_ofChg (hc.chg.trans hd.chg))) (by decide)
  have hbound : ∀e<4,vword (d.v .v24) e=(s.gpr .x2).setWidth 32 := by
    intro e he
    rw [hd.other .v24 (by decide),hc.v,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he,
      hb.1.gpr .x2 (by decide),ha.1.gpr .x2 (by decide)]
    have heq : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
    rcases heq with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨setup_mono (hsc.trans ht) (by decide),⟨?_,?_,?_,?_⟩,?_⟩
  · intro e he
    rw [ht.vec .v16 (by decide),hd.other .v16 (by decide),hc.other .v16 (by decide),
      hb.1.vec .v16 (by decide),ha.2,HighPack.repeatedWord_lane _ he]
  · intro e he
    rw [ht.vec .v25 (by decide),hd.other .v25 (by decide),hc.other .v25 (by decide),
      hb.2,HighPack.repeatedWord_lane _ he]
  · intro e he; rw [hlo e he,hbound e he]
  · intro e he; rw [hw e he,hbound e he]
  · rw [ht.vec .v31 (by decide),hd.v]

end VG.Proof.MlDsa.AArch64.Optimized.Response
