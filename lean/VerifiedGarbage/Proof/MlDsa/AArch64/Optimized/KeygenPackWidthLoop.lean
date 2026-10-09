import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackBody

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape)
open VG.Proof.MlKem.AArch64 (Keep ptr_add)
open VG.Proof.MlKem (digits)

structure WidthInv (signed : Bool) (b d c : Nat) (m : Mem) (input out : Addr)
    (B : Nat → Byte) (start : State) (i : Nat) (s : State) : Prop where
  input : s.gpr .x0=input+BitVec.ofNat 64 (4*c*i)
  output : s.gpr .x2=out+BitVec.ofNat 64 (d*c/8*i)
  bytes : ∀j<d*c/8*i,s.mem (out+BitVec.ofNat 64 j)=B j
  frame : Frame [⟨out,32*d⟩] m s.mem
  keep : Keep widthRegs start s
  constants : signed=true → Constants b s

section
variable (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
  (ht : TailWidth (d*c/8)) (start : State) (input out : Addr) (V : Nat → Nat) (B : Nat → Byte)
  (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,32*d⟩:Region)∈start.wr)
  (hsep : (polyRegion input).Disjoint ⟨out,32*d⟩)
  (hv : ∀j<256,V j<2^d)
  (hvalues : ∀j<256,inputValue signed b start.mem input j=BitVec.ofNat 64 (V j))
  (hbytes : ∀i<256/c,∀j<d*c/8,
    byteOf (digits d ((List.range c).map fun k=>V (c*i+k))) j=B (d*c/8*i+j))
include hs hc4 ht hin hout hsep hv hvalues hbytes

theorem width_step {i : Nat} (hi : i<256/c) {s : State}
    (h : WidthInv signed b d c start.mem input out B start i s) :
    WP isa (.block (widthBody signed b d c)) s fun t=>
      WidthInv signed b d c start.mem input out B start (i+1) t ∧ t.gpr .x15=s.gpr .x15-1 := by
  obtain ⟨hci,hbi⟩ := hs.group hi
  have hpoly : 4*c*i+4*c≤1024 := by simpa only [Nat.mul_add,Nat.mul_assoc] using Nat.mul_le_mul_left 4 hci
  have hn : 32*d<2^64 := by have := hs.d20;omega
  have hg : d*c%8=0 := by have := hs.dc;omega
  refine WP.mono (body_ok signed b d c hs.d20 hs.c0 hs.c8 hc4 hg ht s h.constants ?_ ?_
    (fun j=>V (c*i+j)) (fun j hj=>hv _ (by omega)) ?_) fun t ⟨hw,h0,h2,h15,hk,hc⟩=>?_
  · intro off hoff
    rw [h.input,ptr_add,h.keep.rd,h.keep.wr]
    exact ⟨_,hin,Offset.contains_base input (by omega) (by omega)⟩
  · intro off sz hoff
    rw [h.output,ptr_add,h.keep.wr]
    exact ⟨_,hout,Offset.contains_base out (by omega) (by omega)⟩
  · intro j hj
    have hij : c*i+j<256 := by omega
    rw [h.input,show 4*c*i=4*(c*i) by rw [Nat.mul_assoc],inputValue_shift,
      inputValue_frame signed b h.frame (by intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hsep) hij]
    exact hvalues _ (by omega)
  · have hw' := hw.congr (hbytes i hi)
    rw [h.output] at hw'
    obtain ⟨hf,hb⟩ := Written.step h.frame h.bytes hw' hbi hn
    refine ⟨⟨?_,?_,?_,hf,(h.keep.trans hk).mono,hc⟩,h15⟩
    · rw [h0,h.input,ptr_add,Nat.mul_succ]
    · rw [h2,h.output,ptr_add,Nat.mul_succ]
    · simpa only [Nat.mul_succ] using hb

theorem width_loop {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants b s) (h15 : s.gpr .x15=BitVec.ofNat 64 (256/c)) :
    WP isa (.loop (.block (widthBody signed b d c)) (.nonzero .x .x15)) s fun t=>
      (∀j<32*d,t.mem (out+BitVec.ofNat 64 j)=B j) ∧
      Frame [⟨out,32*d⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  obtain ⟨hN0,hN⟩ := hs.G
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.wp_countdown (by omega) hN0
    (WidthInv signed b d c start.mem input out B start)
    (fun i hi s h _=>width_step signed b d c hs hc4 ht start input out V B hin hout hsep hv hvalues hbytes hi h)
    (s:=s) ?_ h15) fun t h=>?_
  · exact ⟨by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h0,
      by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h2,
      by intro j hj;simp only [Nat.mul_zero] at hj;omega,
      by rw [hm];exact Frame.refl _ _,hk,hc⟩
  · exact ⟨by simpa only [hs.bN] using h.bytes,h.frame,h.keep⟩

end
end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
