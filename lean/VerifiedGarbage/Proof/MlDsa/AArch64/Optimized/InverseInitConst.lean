import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseScale
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_scalar wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep)
open VG.Impl.MlDsa.AArch64.Arith (movW)

def insertWord (d : VReg) (i n : Nat) : List Instr :=
  movW .x9 n ++ [.vop (.ins .s4 d i .x9)]

theorem insertWord_ok (s : State) (d : VReg) (n : Nat) {i : Nat} (hi : i<4) :
    WP isa (.block (insertWord d i n)) s fun t =>
      ConstKeep d s t ∧ t.v d=setLane (s.v d) 32 i (BitVec.ofNat 32 n) := by
  unfold insertWord
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x9 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d := d) (x := setLane (a.v d) 32 i ((a.gpr .x9).setWidth 32)) (by simp [VOp.eval,hi])
    fun t ht => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr => ?_,fun r hr => ?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hk.gpr r (by simpa using hr)]
    · rw [ht.other r hr,hv]
    · rw [ht.mem,hm]
    · rw [ht.rd,hk.rd]
    · rw [ht.wr,hk.wr]
    · rw [ht.sp,hk.sp]
  · rw [ht.v,ha,hv]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq,BitVec.natCast_eq_ofNat]

def cvWords (a b c d : Nat) : BitVec 128 :=
  setLane (setLane (setLane (HighPack.repeatedWord a) 32 1 (BitVec.ofNat 32 b))
    32 2 (BitVec.ofNat 32 c)) 32 3 (BitVec.ofNat 32 d)

theorem cv4_ok (s : State) (r : VReg) (a b c d : Nat) (hb : b≠a) (hc : c≠a) (hd : d≠a) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv r [a,b,c,d])) s fun t =>
      ConstKeep r s t ∧ t.v r=cvWords a b c d := by
  have he : VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv r [a,b,c,d]=
      VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc r a ++
      insertWord r 1 b ++ insertWord r 2 c ++ insertWord r 3 d := by
    simp [VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv,VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc,
      insertWord,hb,hc,hd,List.range_succ,List.append_assoc]
  rw [he]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s r a) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (insertWord_ok s₁ r b (by decide : 1<4)) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (insertWord_ok s₂ r c (by decide : 2<4)) fun s₃ h₃ => ?_
  refine WP.mono (insertWord_ok s₃ r d (by decide : 3<4)) fun t h₄ => ?_
  refine ⟨((h₁.1.trans h₂.1).trans h₃.1).trans h₄.1,?_⟩
  rw [h₄.2,h₃.2,h₂.2,h₁.2]
  rfl

def scaleConst : List Instr := VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv .v30
  [16382,VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar 16382,
   (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417,
   VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar ((VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417)]

def scaleVector : BitVec 128 := cvWords 16382 4197891 8085692 2071960303

theorem folded_value_eq : (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417=8085692 := by decide +kernel

theorem scaleConst_ok (s : State) : WP isa (.block scaleConst) s fun t =>
    ConstKeep .v30 s t ∧ t.v .v30=scaleVector := by
  have he : scaleConst=VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv .v30 [16382,4197891,8085692,2071960303] := by
    simp only [scaleConst,folded_value_eq]
    rfl
  rw [he]
  exact cv4_ok s .v30 _ _ _ _ (by decide) (by decide) (by decide)

theorem scaleVector_ready {s : State} (h : s.v .v30=scaleVector) : ScaleRoots s := by
  rw [ScaleRoots,h]
  decide +kernel

theorem scaleVector_folded {s : State} (h : s.v .v30=scaleVector) :
    vword (s.v .v30) 2=BitVec.ofInt 32 (finalZ 6 0) ∧
    vword (s.v .v30) 3=BitVec.ofInt 32 (reciprocal (finalZ 6 0)) := by
  rw [h]
  simp only [finalZ,finalValue,show ¬(6<4) by decide,show ¬(6<6) by decide,ite_false,folded_value_eq]
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
