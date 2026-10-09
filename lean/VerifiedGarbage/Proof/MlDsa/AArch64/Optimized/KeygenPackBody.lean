import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackAdvance

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlKem (digits)

abbrev widthRegs : List Reg := [.x0,.x2,.x9,.x10,.x11,.x15]
def widthBody (signed : Bool) (b d c : Nat) : List Instr := groupCode signed b d c ++ advance d c

theorem body_ok (signed : Bool) (b d c : Nat) (hd : d≤20) (hc : 0<c) (hc8 : c≤8)
    (hc4 : c%4=0) (halign : d*c%8=0) (ht : TailWidth (d*c/8)) (s : State)
    (hconst : signed=true → Constants b s)
    (hin : ∀off,off+16≤4*c → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hout : ∀off sz,off+sz≤d*c/8 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) sz)
    (V : Nat → Nat) (hV : ∀j<c,V j<2^d)
    (hvalues : ∀j<c,inputValue signed b s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j)) :
    WP isa (.block (widthBody signed b d c)) s fun t=>
      Written s.mem t.mem (s.gpr .x2) (d*c/8) (byteOf (digits d ((List.range c).map V))) ∧
      t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (4*c) ∧
      t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (d*c/8) ∧
      t.gpr .x15=s.gpr .x15-1 ∧ Keep widthRegs s t ∧ (signed=true → Constants b t) := by
  rw [widthBody,WP.block_append_iff]
  refine WP.mono (group_ok signed b d c hd hc hc8 hc4 ht s hconst hin hout) fun a ⟨hk,ha,hm,_⟩=>?_
  refine WP.mono (advance_ok d c hd hc8 a) fun t ⟨⟨⟨h0,h2,h15,htm⟩,kt⟩,hv⟩=>?_
  refine ⟨?_,?_,?_,?_,(hk.trans kt).mono,?_⟩
  · rw [htm,hm]
    exact group_written signed b d c hd hc8 halign ht s.mem (s.gpr .x0) (s.gpr .x2) V hV hvalues
  · rw [h0,hk.get .x0]
  · rw [h2,hk.get .x2]
  · rw [h15,hk.get .x15]
  · intro hh
    have hh' := ha hh
    exact ⟨by rw [hv];exact hh'.bias,by rw [hv];exact hh'.modulus⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
