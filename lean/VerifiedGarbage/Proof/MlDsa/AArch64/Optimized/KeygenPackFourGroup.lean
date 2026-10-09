import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourStore

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def fourGroup (signed : Bool) : List Instr :=
  Impl.MlDsa.AArch64.Optimized.KeygenPack.loadVec signed 16++fourShuffle++
    [.umov .x .x9 .v0 0,.str .x .x9 .x2 0]

theorem fourStored_byte (x : BitVec 128) {i : Nat} (hi : i<8) :
    (x.extractLsb' 0 64).extractLsb' (8*i) 8=vbyte x i := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vbyte,BitVec.getLsbD_extractLsb',hk,show 8*i+k<64 by omega,
    decide_true,Bool.true_and,Nat.zero_add]

theorem fourGroup_ok (signed : Bool) (s : State) (f : Nat → BitVec 4)
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hv : ∀j<4,∀e<4,(if signed then encoded 4 (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)=(f (4*j+e)).setWidth 32)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hout : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block (fourGroup signed)) s fun t=>
      Keep [.x9] s t ∧
      (∀r,r∉[VReg.v0,.v1,.v2,.v3,.v4] → t.v r=s.v r) ∧
      t.mem=s.mem.writeW (s.gpr .x2) (t.gpr .x9) ∧
      ∀i<8,(t.gpr .x9).extractLsb' (8*i) 8=
        (f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4) := by
  unfold fourGroup
  rw [WP.block_append_iff]
  refine WP.mono (fourLoadShuffle_ok signed s f hc hin hv hg hp hm) fun a ⟨ha,hbytes⟩=>?_
  refine WP.mono (fourStore_ok a (by simpa only [ha.wr,ha.gpr] using hout)) fun t ⟨⟨⟨hword,hmem⟩,ht⟩,htv⟩=>?_
  refine ⟨(ha.keep.trans ht).mono,?_,?_,?_⟩
  · intro r hr
    rw [htv,ha.get r hr]
  · rw [hmem,ha.mem,ha.gpr,hword]
  · intro i hi
    rw [hword,fourStored_byte _ hi]
    exact hbytes i hi

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
