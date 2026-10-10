import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoads
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField

/-! ## From `KeygenPackFourInput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

theorem four_low_byte (x : BitVec 128) (e : Nat) :
    vbyte x (4*e)=(vword x e).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [vbyte,vword,hk,show k<32 by omega]
  congr 1
  omega

theorem four_table_word (v : VReg → BitVec 128) {i : Nat} (hi : i<16) :
    tableByte v .v0 (4*i)=(vword (v (regAt (i/4))) (i%4)).setWidth 8 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 by omega) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 3
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 3
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 3
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 3

theorem four_table_nibbles (v : VReg → BitVec 128) (f : Nat → BitVec 4)
    (h : ∀j<4,∀e<4,vword (v (regAt j)) e=(f (4*j+e)).setWidth 32) :
    ∀i<16,tableByte v .v0 (4*i)=(f i).setWidth 8 := by
  intro i hi
  rw [four_table_word v hi,h _ (by omega) _ (by omega),show 4*(i/4)+i%4=i by omega]
  simp

theorem fourLoadShuffle_ok (signed : Bool) (s : State) (f : Nat → BitVec 4)
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hv : ∀j<4,∀e<4,(if signed then encoded 4 (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)=(f (4*j+e)).setWidth 32)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.KeygenPack.loadVec signed 16++fourShuffle)) s fun t=>
      VChg [.v0,.v1,.v2,.v3,.v4] s t ∧
      ∀i<8,vbyte (t.v .v0) i=(f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4) := by
  rw [WP.block_append_iff]
  refine WP.mono (loadCount_ok signed 4 4 (by decide) s hc hin) fun a ⟨ha,_,hwa⟩=>?_
  rw [←List.append_nil fourShuffle]
  refine fourShuffle_bytes f (by rw [ha.get .v18 (by decide)];exact hg)
    (by rw [ha.get .v19 (by decide)];exact hp)
    (by rw [ha.get .v20 (by decide)];exact hm)
    (four_table_nibbles a.v f (fun j hj e he=>(hwa j hj e he).trans (hv j hj e he)))
    fun t ht hb=>WP.block_nil_iff.mpr ⟨(ha.trans ht).mono (by simp),hb⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourStore_ok (s : State) (hw : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block [.umov .x .x9 .v0 0,.str .x .x9 .x2 0]) s fun t=>
      ((t.gpr .x9=(s.v .v0).extractLsb' 0 64 ∧
        t.mem=s.mem.writeW (s.gpr .x2) ((s.v .v0).extractLsb' 0 64)) ∧ Keep [.x9] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=by rfl)
  arun [Option.bind_some,exec,addr,Size.bytes,State.store,State.read,Mem.writeW,hw]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourGroup.lean` -/

section

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

end
