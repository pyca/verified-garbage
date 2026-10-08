import VerifiedGarbage.Proof.P256.EcdhInverse.Step
import VerifiedGarbage.Proof.P256.EcdhInverse.Bounds

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

structure RowState (t : MSt) (s : State) : Prop where
  d : s.gpr .x1=BitVec.ofInt 64 t.d
  f : s.gpr .x4=BitVec.ofInt 64 t.f
  g : s.gpr .x5=BitVec.ofInt 64 t.g
  zero : s.gpr .x27=0
  parity : s.zf=decide (t.g%2=0)

def numerator (t : MSt) : Int :=
  if 0≤t.d ∧ t.g%2=1 then t.g-t.f else t.g+t.g%2*t.f

theorem updateStep_int {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) :
    WP isa (.block updateStep) s fun a =>
      a.gpr .x1=BitVec.ofInt 64 (mstep t).d ∧
      a.gpr .x4=BitVec.ofInt 64 (mstep t).f ∧
      a.gpr .x5=BitVec.ofInt 64 (numerator t) ∧ Keeps [.x1,.x4,.x5,.x6] s a := by
  have hz : s.zf = !decide (t.g%2=1) := by
    rw [hs.parity]
    rcases Int.emod_two_eq_zero_or_one t.g with h|h <;> simp [h]
  have hn : (s.gpr .x1).msb=decide (t.d<0) := by rw [hs.d]; exact msb_ofInt hd
  refine WP.mono (updateStep_run s hs.zero hz hn) fun a ⟨ad,af,ag,hk⟩ => ?_
  rw [hs.d] at ad
  rw [hs.f,hs.g] at af
  rw [hs.f,hs.g] at ag
  have e2 : BitVec.ofInt 64 2=(2 : BitVec 64) := by decide
  by_cases hg : t.g%2=1
  · by_cases hd0 : 0≤t.d
    · have hn0 : ¬t.d<0 := by omega
      simp only [hg,hn0,decide_true,decide_false,Bool.not_false,
        Bool.and_true,Bool.false_eq_true,↓reduceIte] at ad af ag
      simp only [mstep,numerator,hg,hd0,and_self,↓reduceIte]
      refine ⟨?_,af,?_,hk⟩
      · rw [show (2-t.d:Int)= -t.d+2 by omega,BitVec.ofInt_add,BitVec.ofInt_neg,e2]
        exact ad
      · rw [ofInt_sub']
        simpa only [BitVec.sub_eq_add_neg] using ag
    · have hdn : t.d<0 := by omega
      simp only [hg,hdn,decide_true,Bool.not_true,Bool.and_false,↓reduceIte] at ad af ag
      simp only [mstep,numerator,hg,hd0,false_and,↓reduceIte,one_mul]
      refine ⟨?_,af,?_,hk⟩
      · rw [BitVec.ofInt_add,e2,BitVec.add_comm]; exact ad
      · rw [BitVec.ofInt_add]; exact ag
  · have hg0 : t.g%2=0 := by omega
    simp only [hg,decide_false,Bool.false_and,Bool.false_eq_true,↓reduceIte,add_zero] at ad af ag
    simp only [mstep,numerator,hg0,show ¬(0:Int)=1 by decide,and_false,↓reduceIte,zero_mul,add_zero]
    refine ⟨?_,af,ag,hk⟩
    rw [BitVec.ofInt_add,e2,BitVec.add_comm]; exact ad


theorem numerator_half (t : MSt) : numerator t / 2 = (mstep t).g := by
  unfold numerator mstep
  split <;> rfl

theorem roundStep_ok {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) (hb : rowBounds t) :
    WP isa (.block roundStep) s fun a => RowState (mstep t) a ∧
      Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  have he : roundStep=updateStep++testHalf := by
    simp only [roundStep,testHalf,List.append_assoc]
  rw [he,WP.block_append_iff]
  refine WP.mono (updateStep_int hs hd) fun a ⟨ad,af,ag,ka⟩ => ?_
  have a27 : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hs.zero
  refine WP.mono (testHalf_run a a27) fun b ⟨bg,bz,kb⟩ => ?_
  have bg' : b.gpr .x5=BitVec.ofInt 64 (mstep t).g := by
    have hnum : -(2^63)≤numerator t ∧ numerator t<2^63 := row_numerator_bound hb
    rw [bg,ag,signed_shift_ofInt hnum]
    change BitVec.ofInt 64 (numerator t / 2)=_
    rw [numerator_half]
  refine ⟨⟨?_,?_,bg',?_,?_⟩,(ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide)]; exact ad
  · rw [kb.gpr _ (by decide)]; exact af
  · rw [kb.gpr _ (by decide)]; exact a27
  · rw [bz,bg']
    simp only [ofInt_parity]

end VG.Proof.P256.EcdhInverse
