import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourCanonical
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackInput

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)
open VG.Proof.MlKem.AArch64 (Keep)

theorem four_input (signed : Bool) (s : State) (V : Nat → Nat) (hV : ∀j<16,V j<16)
    (hvalues : ∀j<16,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j))
    {j e : Nat} (hj : j<4) (he : e<4) :
    (if signed then encoded 4 (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)=
      (BitVec.ofNat 4 (V (4*j+e))).setWidth 32 := by
  have h := congrArg (BitVec.setWidth 32) (hvalues (4*j+e) (by omega))
  simp only [inputValue,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq] at h
  have hw := inputWord s.mem (s.gpr .x0) (4*j+e)
  rw [show (4*j+e)/4=j by omega,show (4*j+e)%4=e by omega] at hw
  rw [hw,h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,
    show 2^4=16 by decide]
  have hv := hV (4*j+e) (by omega)
  omega

theorem fourGroup_written (signed : Bool) (s : State) (V : Nat → Nat) (hV : ∀j<16,V j<16)
    (hvalues : ∀j<16,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j))
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hout : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block (fourGroup signed)) s fun t=>
      Keep [.x9] s t ∧ (∀r,r∉[VReg.v0,.v1,.v2,.v3,.v4] → t.v r=s.v r) ∧
      Written s.mem t.mem (s.gpr .x2) 8 (byteOf (digits 4 ((List.range 16).map V))) := by
  refine WP.mono (fourGroup_ok signed s (fun j=>BitVec.ofNat 4 (V j)) hc hin
    (fun j hj e he=>four_input signed s V hV hvalues hj he) hg hp hm hout) fun t ⟨hk,hv,hmem,hbytes⟩=>?_
  refine ⟨hk,hv,?_⟩
  rw [hmem]
  exact (written_word s.mem (s.gpr .x2) 8 (t.gpr .x9)).congr fun i hi=>
    (hbytes i hi).trans (four_byte V hV hi).symm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
