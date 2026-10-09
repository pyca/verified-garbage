import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourWritten
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourAdvance
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackBody

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlKem (digits)

def fourBody (signed : Bool) : List Instr := fourGroup signed ++ advance 4 16

theorem fourBody_ok (signed : Bool) (s : State) (V : Nat → Nat) (hV : ∀j<16,V j<16)
    (hvalues : ∀j<16,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j))
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hout : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block (fourBody signed)) s fun t=>
      Written s.mem t.mem (s.gpr .x2) 8 (byteOf (digits 4 ((List.range 16).map V))) ∧
      t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x2=s.gpr .x2+8 ∧
      t.gpr .x15=s.gpr .x15-1 ∧ Keep widthRegs s t ∧
      (signed=true → Constants 4 t) ∧ t.v .v18=fourGatherIndex ∧
      t.v .v19=fourPackIndex ∧ (∀e<4,vword (t.v .v20) e=0x00ff00ff) := by
  rw [fourBody,WP.block_append_iff]
  refine WP.mono (fourGroup_written signed s V hV hvalues hc hin hg hp hm hout) fun a ⟨hk,hv,hw⟩=>?_
  refine WP.mono (fourAdvance_ok a) fun t ⟨⟨⟨h0,h2,h15,htm⟩,kt⟩,vt⟩=>?_
  refine ⟨by rw [htm];exact hw,?_,?_,?_,(hk.trans kt).mono,?_,?_,?_,?_⟩
  · rw [h0,hk.get .x0]
  · rw [h2,hk.get .x2]
  · rw [h15,hk.get .x15]
  · intro hh
    exact ⟨by rw [vt,hv .v16 (by decide)];exact (hc hh).bias,
      by rw [vt,hv .v17 (by decide)];exact (hc hh).modulus⟩
  · rw [vt,hv .v18 (by decide),hg]
  · rw [vt,hv .v19 (by decide),hp]
  · rw [vt,hv .v20 (by decide)];exact hm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
