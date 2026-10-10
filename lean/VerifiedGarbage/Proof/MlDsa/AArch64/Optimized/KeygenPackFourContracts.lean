import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackAdvance
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackStreamMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackInput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack

/-! ## From `KeygenPackFourAdvance.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourAdvance_ok (s : State) :
    WP isa (.block (advance 4 16)) s fun t =>
      ((t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x2=s.gpr .x2+8 ∧
        t.gpr .x15=s.gpr .x15-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x2,.x15] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  arun [advance]
  exact ⟨rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourCanonical.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)

theorem nibble_pair (a b : Nat) (ha : a<16) (hb : b<16) :
    (BitVec.ofNat 4 a).setWidth 8 ||| ((BitVec.ofNat 4 b).setWidth 8<<<4)=
      BitVec.ofNat 8 (a+16*b) := by
  have hA : (BitVec.ofNat 4 a).setWidth 8=BitVec.ofNat 8 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,show 2^4=16 by decide,Nat.mod_eq_of_lt ha]
  have hB : (BitVec.ofNat 4 b).setWidth 8=BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,show 2^4=16 by decide,Nat.mod_eq_of_lt hb]
  rw [hA,hB]
  have hshift : (BitVec.ofNat 8 b<<<4)=BitVec.ofNat 8 (16*b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]
    rw [Nat.mul_comm b]
  rw [hshift,←BitVec.ofNat_or,Nat.or_comm,←Nat.two_pow_add_eq_or_of_lt (show a<2^4 from ha) b,Nat.add_comm]

theorem four_byte (V : Nat → Nat) (hV : ∀j<16,V j<16) {i : Nat} (hi : i<8) :
    byteOf (digits 4 ((List.range 16).map V)) i=
      (BitVec.ofNat 4 (V (2*i))).setWidth 8 ||| ((BitVec.ofNat 4 (V (2*i+1))).setWidth 8<<<4) := by
  rw [nibble_pair _ _ (hV _ (by omega)) (hV _ (by omega))]
  let G := digits 4 ((List.range 16).map V)
  have h0 := digits_range_get (d:=4) (c:=16) hV (show 2*i<16 by omega)
  have h1 := digits_range_get (d:=4) (c:=16) hV (show 2*i+1<16 by omega)
  change G/2^(4*(2*i))%16=V (2*i) at h0
  change G/2^(4*(2*i+1))%16=V (2*i+1) at h1
  apply BitVec.eq_of_toNat_eq
  change (G/2^(8*i))%256=(V (2*i)+16*V (2*i+1))%256
  have hsum : V (2*i)+16*V (2*i+1)<256 := by have := hV (2*i) (by omega);have := hV (2*i+1) (by omega);omega
  rw [Nat.mod_eq_of_lt hsum,show 256=16*16 by decide,Nat.mod_mul]
  rw [show 8*i=4*(2*i) by omega,h0]
  congr 1
  rw [show 16=2^4 by decide,Nat.div_div_eq_div_mul,←Nat.pow_add,
    show 4*(2*i)+4=4*(2*i+1) by omega]
  exact congrArg (16*·) h1

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourWritten.lean` -/

section

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

end

/-! ## From `KeygenPackFourBody.lean` -/

section

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

end

/-! ## From `KeygenPackFourLoop.lean` -/

section

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

end

/-! ## From `KeygenPackFour.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (vals vals_lt vals_getD)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_eq!)
open VG.Proof.MlKem.AArch64 (Keep)

theorem four_packed_group (F : BitVec 32 → Nat) (m : Mem) (input : Addr)
    (hV : ∀j<256,F (coeffAt m input j)<16) {i j : Nat} (hi : i<16) (hj : j<8) :
    byteOf (digits 4 ((List.range 16).map fun k=>F (coeffAt m input (16*i+k)))) j=
      (bitsToBytes (fieldBits 4 (vals F m input)))[8*i+j]! := by
  rw [pack_group (c:=16) (by decide : 0<4) (by decide : 4*16=8*8) (by simp)
    (vals_lt hV) hj (by omega),take_drop_eq _ 0 (by simp;omega)]
  apply congrArg (fun L=>BitVec.ofNat 8 (digits 4 L/2^(8*j)))
  apply List.map_congr_left
  intro k hk
  symm
  exact vals_getD F m input (by have := List.mem_range.mp hk;omega)

theorem four_ok (signed : Bool) (s : State) (F : BitVec 32 → Nat)
    (hin : polyRegion (s.gpr .x0) ∈ s.rd++s.wr)
    (hout : (⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩:Region)∈s.wr)
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩)
    (hv : ∀j<256,F (coeffAt s.mem (s.gpr .x0) j)<16)
    (hvalues : ∀j<256,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (F (coeffAt s.mem (s.gpr .x0) j))) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four signed) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem (if signed then s.gpr .x3 else s.gpr .x2) 128=
        bitsToBytes (fieldBits 4 (vals F s.mem (s.gpr .x0))) ∧
      Frame [⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩] s.mem t.mem ∧ Keep widthRegs s t := by
  have hcode : Impl.MlDsa.AArch64.Optimized.KeygenPack.four signed=
      .seq (.block (fourSetup signed)) (.loop (.block (fourBody signed)) (.nonzero .x .x15)) := by
    simp [Impl.MlDsa.AArch64.Optimized.KeygenPack.four,fourSetup,fourBody,fourGroup,fourShuffle,advance,List.append_assoc]
  rw [hcode]
  refine WP.seq ?_
  refine WP.mono (fourSetup_ok signed s) fun u ⟨hk,hm,h2,hc,hg,hp,hmask,h15⟩=>?_
  refine WP.mono (four_loop signed s (s.gpr .x0) (if signed then s.gpr .x3 else s.gpr .x2)
    (fun j=>F (coeffAt s.mem (s.gpr .x0) j))
    (fun j=>(bitsToBytes (fieldBits 4 (vals F s.mem (s.gpr .x0))))[j]!) hin hout hsep hv hvalues
    (fun i hi j hj=>four_packed_group F s.mem (s.gpr .x0) hv hi hj)
    (hk.get .x0) h2 hm hk.mono hc hg hp hmask h15) fun t ⟨hb,hf,hk⟩=>?_
  exact ⟨bytesAt_eq! (pack_length 4 _ (by simp)) hb,hf,hk⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourContracts.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only)

theorem simple_four_wp {s₀ s : State} (hp : simpleBitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    (hlen128 : (s₀.gpr .x3).toNat=128) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four false) s
      (fun t=>simpleBitPackK.post s₀ t) := by
  have hcases := sbp_cases hp.2.2.2.1 hp.2.2.2.2.1
  have hd : bitlen (wArg s₀ .x1)=4 := by omega
  obtain ⟨hrd,hwr,hsep,hb,hlen,hle⟩ := hp
  rw [hd] at hlen
  refine WP.mono (four_ok false s BitVec.toNat ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x2,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x2,hlen,Bool.false_eq_true,↓reduceIte] using hsep
  · intro i hi
    change (coeffAt s.mem (s.gpr .x0) i).toNat<2^4
    rw [ho.mem,ho.get .x0,←hd]
    exact lt_bitlen (hle i hi)
  · intro i _
    simp [inputValue]
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat=simpleBitPack _ _
    simp only [Bool.false_eq_true,↓reduceIte,ho.get .x2,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,simpleBitPack_eq,natPolyAt_toList,hd]

theorem signed_four_wp {s₀ s : State} (hp : bitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    (hlen128 : (s₀.gpr .x4).toNat=128) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four true) s
      (fun t=>bitPackK.post s₀ t) := by
  have hcases := bp_cases hp.2.2.2.1 hp.2.2.2.2.1
  have hd : bitlen (wArg s₀ .x1+wArg s₀ .x2)=4 := by omega
  have hB : wArg s₀ .x2=4 := by omega
  obtain ⟨hrd,hwr,hsep,hab,hlen,hred,hbnd⟩ := hp
  have hc := bp_cases hab hlen
  have hq : q=8380417 := rfl
  rw [hd] at hlen
  refine WP.mono (four_ok true s (bpVal 4) ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x3,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x3,hlen,↓reduceIte] using hsep
  · intro i hi
    change bpVal 4 (coeffAt s.mem (s.gpr .x0) i)<2^4
    rw [ho.mem,ho.get .x0]
    obtain ⟨h₁,h₂⟩ := hbnd i hi
    rw [hB] at h₂
    have hx := hred i hi
    rw [bpVal,←BitVec.ofNat_toNat,subModQ_toNat (by omega) hx,
      ←sub_modPm hx (by omega) h₂]
    have hh := lt_bitlen (sub_modPm_le h₁ h₂)
    simpa only [show bitlen (wArg s₀ .x1+4)=4 by simpa only [hB] using hd] using hh
  · intro i hi
    simpa only [fieldValueNat,↓reduceIte] using inputValue_nat true 4 s.mem (s.gpr .x0) i
      (by omega) (by rw [ho.mem,ho.get .x0];exact hred i hi)
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat=bitPack _ _ _
    simp only [↓reduceIte,ho.get .x3,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,bitPack_eq,bitPack_vals hred (by omega) (fun i hi=>(hbnd i hi).2),hd,hB]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end
