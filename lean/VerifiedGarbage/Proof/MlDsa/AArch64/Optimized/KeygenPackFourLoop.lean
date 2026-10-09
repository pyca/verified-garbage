import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBody

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Keep ptr_add)
open VG.Proof.MlKem (digits)

structure FourInv (signed : Bool) (m : Mem) (input out : Addr)
    (B : Nat → Byte) (start : State) (i : Nat) (s : State) : Prop where
  input : s.gpr .x0=input+BitVec.ofNat 64 (64*i)
  output : s.gpr .x2=out+BitVec.ofNat 64 (8*i)
  bytes : ∀j<8*i,s.mem (out+BitVec.ofNat 64 j)=B j
  frame : Frame [⟨out,128⟩] m s.mem
  keep : Keep widthRegs start s
  constants : signed=true → Constants 4 s
  gather : s.v .v18=fourGatherIndex
  pack : s.v .v19=fourPackIndex
  mask : ∀e<4,vword (s.v .v20) e=0x00ff00ff

section
variable (signed : Bool) (start : State) (input out : Addr) (V : Nat → Nat) (B : Nat → Byte)
  (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,128⟩:Region)∈start.wr)
  (hsep : (polyRegion input).Disjoint ⟨out,128⟩)
  (hv : ∀j<256,V j<16)
  (hvalues : ∀j<256,inputValue signed 4 start.mem input j=BitVec.ofNat 64 (V j))
  (hbytes : ∀i<16,∀j<8,
    byteOf (digits 4 ((List.range 16).map fun k=>V (16*i+k))) j=B (8*i+j))
include hin hout hsep hv hvalues hbytes

theorem four_step {i : Nat} (hi : i<16) {s : State}
    (h : FourInv signed start.mem input out B start i s) :
    WP isa (.block (fourBody signed)) s fun t=>
      FourInv signed start.mem input out B start (i+1) t ∧ t.gpr .x15=s.gpr .x15-1 := by
  refine WP.mono (fourBody_ok signed s (fun j=>V (16*i+j)) (fun j hj=>hv _ (by omega)) ?_
    h.constants ?_ h.gather h.pack h.mask ?_) fun t ⟨hw,h0,h2,h15,hk,hc,hg,hp,hm⟩=>?_
  · intro j hj
    rw [h.input,show 64*i=4*(16*i) by omega,inputValue_shift,
      inputValue_frame signed 4 h.frame (by intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hsep) (by omega)]
    exact hvalues _ (by omega)
  · intro j hj
    rw [h.input,ptr_add,h.keep.rd,h.keep.wr]
    exact ⟨_,hin,Offset.contains_base input (by omega) (by omega)⟩
  · rw [h.output,h.keep.wr]
    exact ⟨_,hout,Offset.contains_base out (by omega) (by omega)⟩
  · have hw' := hw.congr (hbytes i hi)
    rw [h.output] at hw'
    obtain ⟨hf,hb⟩ := Written.step h.frame h.bytes hw' (by omega) (by decide : 128<2^64)
    refine ⟨⟨?_,?_,?_,hf,(h.keep.trans hk).mono,hc,hg,hp,hm⟩,h15⟩
    · rw [h0,h.input,show (64:BitVec 64)=BitVec.ofNat 64 64 by rfl,ptr_add,Nat.mul_succ]
    · rw [h2,h.output,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
    · simpa only [Nat.mul_succ] using hb

theorem four_loop {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants 4 s) (hg : s.v .v18=fourGatherIndex)
    (hp : s.v .v19=fourPackIndex) (hmask : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (h15 : s.gpr .x15=16) :
    WP isa (.loop (.block (fourBody signed)) (.nonzero .x .x15)) s fun t=>
      (∀j<128,t.mem (out+BitVec.ofNat 64 j)=B j) ∧
      Frame [⟨out,128⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=16) (by decide) (by decide)
    (FourInv signed start.mem input out B start)
    (fun i hi s h _=>four_step signed start input out V B hin hout hsep hv hvalues hbytes hi h)
    (s:=s) ?_ h15) fun t h=>⟨h.bytes,h.frame,h.keep⟩
  exact ⟨by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h0,
    by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h2,
    by intro j hj;simp only [Nat.mul_zero] at hj;omega,
    by rw [hm];exact Frame.refl _ _,hk,hc,hg,hp,hmask⟩

end
end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
