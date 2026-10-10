import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeArgs

/-! ## From `BoundedFourMaskGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def maskGroup : List Instr :=
 [.ldrq .v1 .x3 0,.vop (.logic .and .v1 .v1 .v0),.strq .v1 .x3 0]
def maskMem (m : Mem) (p : Addr) (v : BitVec 128) : Mem :=
 m.write p 16 (m.read p 16 &&& v)

theorem maskGroup_ok {s : State}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x3) 16)
    (hw : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.block maskGroup) s fun t=>
      StepKeep [.v1] s t ∧ t.mem=maskMem s.mem (s.gpr .x3) (s.v .v0) := by
  unfold maskGroup
  refine wp_ldrq (by decide) (by simp) hr fun a ha=>?_
  refine wp_vop (d := .v1) rfl fun b hb=>?_
  have hk : VChg [.v1] s b := (ha.chg.trans hb.chg).mono (by decide)
  refine wp_strq (a := s.gpr .x3) (by decide) (by rw [hk.gpr]; simp) (by rw [hk.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem ht)).mono (by decide),?_⟩
  rw [ht.mem,hk.mem,hb.v,ha.v,ha.get .v0]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def maskAdvance : List Instr := [.addImm .x .x3 .x3 16,.subImm .x .x5 .x5 1]
theorem maskAdvance_ok (s : State) :
    WP isa (.block maskAdvance) s fun t=>
      ((t.gpr .x3=s.gpr .x3+16 ∧ t.gpr .x5=s.gpr .x5-1 ∧t.mem=s.mem) ∧
        Keep [.x3,.x5] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskAdvance
  arun
  exact ⟨rfl,rfl⟩

def maskRun (m : Mem) (p : Addr) (v : BitVec 128) : Nat→Mem
 | 0=>m
 | j+1=>maskMem (maskRun m p v j) (p+BitVec.ofNat 64 (16*j)) v

structure MaskInv (σ s : State) (p : Addr) (v : BitVec 128) (j : Nat) : Prop where
 bound : j≤64
 keep : Keep [.x3,.x5] σ s
 vec : ∀r,r≠.v1→s.v r=σ.v r
 mem : s.mem=maskRun σ.mem p v j
 ptr : s.gpr .x3=p+BitVec.ofNat 64 (16*j)
 count : s.gpr .x5=BitVec.ofNat 64 (64-j)
 mask : s.v .v0=v

theorem maskStep_ok {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) (hj : j<64)
    (hr : ∀i<64,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (maskGroup++maskAdvance)) s (fun t=>MaskInv σ t p v (j+1)) := by
  rw [WP.block_append_iff]
  refine WP.mono (maskGroup_ok (s := s) (by rw [hi.keep.rd,hi.keep.wr,hi.ptr]; exact hr j hj)
    (by rw [hi.keep.wr,hi.ptr]; exact hw j hj)) fun a ⟨ha,hm⟩=>?_
  refine WP.mono (maskAdvance_ok a) fun t ⟨⟨⟨hp,hc,hmem⟩,hk⟩,hv⟩=>?_
  refine ⟨by omega,((hi.keep.trans ha.keep).trans hk).mono (by decide),?_,?_,?_,?_,?_⟩
  · intro r hn
    rw [hv,ha.vec r (by simpa using hn),hi.vec r hn]
  · rw [hmem,hm,hi.mem,hi.ptr,hi.mask]
    rfl
  · rw [hp,ha.keep.get .x3,hi.ptr,BitVec.add_assoc]
    change p+(BitVec.ofNat 64 (16*j)+BitVec.ofNat 64 16)=_
    rw [←BitVec.ofNat_add]
    congr 1
  · rw [hc,ha.keep.get .x5,hi.count]
    change BitVec.ofNat 64 (64-j)-BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_sub_ofNat_of_le (64-j) 1 (by decide) (by omega)]
    congr 1
  · rw [hv,ha.vec .v0 (by decide),hi.mask]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
