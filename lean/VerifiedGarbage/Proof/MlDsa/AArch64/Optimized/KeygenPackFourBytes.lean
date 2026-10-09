import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourMath

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64

theorem four_word_byte (x : BitVec 128) {e j : Nat} (hj : j<4) :
    (vword x e).extractLsb' (8*j) 8=vbyte x (4*e+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vword,vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and,
    show 8*j+k<32 by omega]
  congr 1
  omega

theorem fourGather_coeff (v : VReg → BitVec 128) (f : Nat → BitVec 4)
    (h : ∀i<16,tableByte v .v0 (4*i)=(f i).setWidth 8) {e : Nat} (he : e<4) :
    vword (fourGather v fourGatherIndex) e=
      (f (4*e)).setWidth 32 ||| ((f (4*e+1)).setWidth 32 <<< 8) |||
      ((f (4*e+2)).setWidth 32 <<< 16) ||| ((f (4*e+3)).setWidth 32 <<< 24) := by
  have hb (j : Nat) (hj : j<4) :
      (vword (fourGather v fourGatherIndex) e).extractLsb' (8*j) 8=(f (4*e+j)).setWidth 8 := by
    rw [four_word_byte _ hj,fourGather_byte _ (by omega),h _ (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨ k=20 ∨ k=21 ∨ k=22 ∨ k=23 ∨ k=24 ∨ k=25 ∨ k=26 ∨ k=27 ∨ k=28 ∨ k=29 ∨ k=30 ∨ k=31 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 3 (by decide))

theorem four_word_low_byte (x : BitVec 128) {e j : Nat} (hj : j<2) :
    ((vword x e).setWidth 16).extractLsb' (8*j) 8=vbyte x (4*e+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hk,decide_true,Bool.true_and,
    show 8*j+k<16 by omega,vword,vbyte,show 8*j+k<32 by omega]
  congr 1
  omega

theorem four_packed_byte (a b c d : BitVec 4) {j : Nat} (hj : j<2) :
    (a.setWidth 16 ||| (b.setWidth 16 <<< 4) ||| (c.setWidth 16 <<< 8) |||
      (d.setWidth 16 <<< 12)).extractLsb' (8*j) 8 =
      if j=0 then a.setWidth 8 ||| (b.setWidth 8 <<< 4) else c.setWidth 8 ||| (d.setWidth 8 <<< 4) := by
  rcases (show j=0 ∨ j=1 by omega) with rfl|rfl
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro k hk
  all_goals rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem four_output_byte (v : VReg → BitVec 128) (f : Nat → BitVec 4)
    (h : ∀i<16,tableByte v .v0 (4*i)=(f i).setWidth 8)
    (mask : BitVec 128) (hm : ∀e<4,vword mask e=0x00ff00ff) {i : Nat} (hi : i<8) :
    vbyte (fourCompress (fourGather v fourGatherIndex) mask fourPackIndex) i=
      (f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4) := by
  rw [fourCompress_byte _ _ (by omega),ite_eq_left hi,
    ← four_word_low_byte _ (by omega : i%2<2),
    fourWord_low _ (by omega : i/2<4) _ _ _ _ (fourGather_coeff v f h (by omega)) mask (hm _ (by omega)),
    four_packed_byte _ _ _ _ (by omega)]
  rcases (show i%2=0 ∨ i%2=1 by omega) with hz|hz
  · rw [ite_eq_left hz]
    rw [show 4*(i/2)=2*i by omega]
  · rw [ite_eq_right (by omega)]
    rw [show 4*(i/2)+2=2*i by omega,show 4*(i/2)+3=2*i+1 by omega]

theorem fourShuffle_bytes {s : State} {rest : List Instr} {Q : State → Prop}
    (f : Nat → BitVec 4) (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hf : ∀i<16,tableByte s.v .v0 (4*i)=(f i).setWidth 8)
    (k : ∀t,VG.Proof.MlKem.AArch64.VChg [.v0,.v1] s t →
      (∀i<8,vbyte (t.v .v0) i=(f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4)) →
      WP isa (.block rest) t Q) : WP isa (.block (fourShuffle++rest)) s Q := by
  refine fourShuffle_ok fun t ht hout=>k t ht ?_
  intro i hi
  rw [hout,hg,hp]
  exact four_output_byte s.v f hf (s.v .v20) hm hi

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
