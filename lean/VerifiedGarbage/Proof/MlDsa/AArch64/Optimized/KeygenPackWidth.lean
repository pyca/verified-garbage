import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackBody

/-! ## From `KeygenPackSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (Keep wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep repeatedWord repeatedWord_lane)

theorem vc_ok (s : State) (d : VReg) (n : Nat) :
    WP isa (.block (vc d n)) s fun t=>ConstKeep d s t ∧ t.v d=repeatedWord n := by
  rw [vc,WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 (BitVec.ofNat 64 n)) fun a ha=>?_
  refine wp_vop (d:=d) rfl fun t ht=>WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr=>?_,fun r hr=>?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,ha.2.1 r hr]
    · rw [ht.other r hr,ha.2.2]
    · rw [ht.mem,ha.2.2]
    · rw [ht.rd,ha.2.2]
    · rw [ht.wr,ha.2.2]
    · rw [ht.sp,ha.2.2]
  · rw [ht.v,ha.1]
    simp [repeatedWord]

theorem constants_ok (s : State) (b : Nat) :
    WP isa (.block (vc .v16 b ++ vc .v17 8380417)) s fun t=>
      SetupKeep [.v16,.v17] s t ∧ Constants b t := by
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok s .v16 b) fun a ha=>?_
  refine WP.mono (vc_ok a .v17 8380417) fun t ht=>?_
  refine ⟨(SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst ht.1),?_,?_⟩
  · intro e he
    rw [ht.1.vec .v16 (by decide),ha.2,repeatedWord_lane _ he]
  · intro e he
    rw [ht.2,repeatedWord_lane _ he]

theorem setup_ok (signed : Bool) (b : Nat) (s : State) :
    WP isa (.block (setup signed b)) s fun t=>
      Keep [.x2,.x9] s t ∧ t.mem=s.mem ∧
      t.gpr .x2=(if signed then s.gpr .x3 else s.gpr .x2) ∧
      (signed=true → Constants b t) := by
  cases signed
  · exact WP.block_nil_iff.mpr ⟨Keep.refl _ _,rfl,rfl,by simp⟩
  · simp only [setup,↓reduceIte,List.cons_append,List.nil_append]
    refine VG.Proof.MlKem.AArch64.wp_mov fun a ha h2=>?_
    refine WP.mono (constants_ok a b) fun t ⟨ht,hc⟩=>?_
    refine ⟨?_,ht.mem.trans ha.mem,?_,fun _=>hc⟩
    · exact ⟨fun r hr=>by rw [ht.gpr r (by simp_all),ha.gpr r (by simp_all)],
        ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp,fun r hr=>by
          rw [ht.vec r (by rcases r <;> simp_all [preservedV])];exact ha.vcs r hr⟩
    · rw [ht.gpr .x2 (by decide),h2]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackWidthLoop.lean` -/

section

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

end

/-! ## From `KeygenPackWidthBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape vals vals_lt vals_getD)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_eq!)
open VG.Proof.MlKem.AArch64 (Keep)

theorem packed_group (F : BitVec 32 → Nat) (m : Mem) (input : Addr)
    (d c : Nat) (hs : Shape d c (d*c/8)) (hV : ∀j<256,F (coeffAt m input j)<2^d)
    {i j : Nat} (hi : i<256/c) (hj : j<d*c/8) :
    byteOf (digits d ((List.range c).map fun k=>F (coeffAt m input (c*i+k)))) j=
      (bitsToBytes (fieldBits d (vals F m input)))[d*c/8*i+j]! := by
  obtain ⟨hc,hb⟩ := hs.group hi
  rw [pack_group (c:=c) (by have := hs.d1;omega) hs.dc (by simp) (vals_lt hV) hj (by omega),
    take_drop_eq _ 0 (by simp;omega)]
  apply congrArg (fun L=>BitVec.ofNat 8 (digits d L/2^(8*j)))
  apply List.map_congr_left
  intro k hk
  symm
  exact vals_getD F m input (by have := List.mem_range.mp hk;omega)

theorem width_loop_bytes (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
    (ht : TailWidth (d*c/8)) (start : State) (input out : Addr) (F : BitVec 32 → Nat)
    (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,32*d⟩:Region)∈start.wr)
    (hsep : (polyRegion input).Disjoint ⟨out,32*d⟩)
    (hv : ∀j<256,F (coeffAt start.mem input j)<2^d)
    (hvalues : ∀j<256,inputValue signed b start.mem input j=BitVec.ofNat 64 (F (coeffAt start.mem input j)))
    {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants b s) (h15 : s.gpr .x15=BitVec.ofNat 64 (256/c)) :
    WP isa (.loop (.block (widthBody signed b d c)) (.nonzero .x .x15)) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem out (32*d)=bitsToBytes (fieldBits d (vals F start.mem input)) ∧
      Frame [⟨out,32*d⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  refine WP.mono (width_loop signed b d c hs hc4 ht start input out
    (fun j=>F (coeffAt start.mem input j))
    (fun j=>(bitsToBytes (fieldBits d (vals F start.mem input)))[j]!)
    hin hout hsep hv hvalues (fun i hi j hj=>packed_group F start.mem input d c hs hv hi hj)
    h0 h2 hm hk hc h15) fun t ⟨hb,hf,hk⟩=>?_
  exact ⟨bytesAt_eq! (pack_length d _ (by simp)) hb,hf,hk⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackWidth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape vals)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem counter_ok (n : Nat) (hn : n<2^16) (s : State) :
    WP isa (.block [.movz .x .x15 (BitVec.ofNat 16 n) 0]) s fun t=>
      ((t.gpr .x15=BitVec.ofNat 64 n ∧ t.mem=s.mem) ∧ Keep [.x15] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  arun
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]

theorem width_ok (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
    (ht : TailWidth (d*c/8)) (s : State) (F : BitVec 32 → Nat)
    (hin : polyRegion (s.gpr .x0) ∈ s.rd++s.wr)
    (hout : (⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩:Region)∈s.wr)
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩)
    (hv : ∀j<256,F (coeffAt s.mem (s.gpr .x0) j)<2^d)
    (hvalues : ∀j<256,inputValue signed b s.mem (s.gpr .x0) j=BitVec.ofNat 64 (F (coeffAt s.mem (s.gpr .x0) j))) :
    WP isa (width signed b d c) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem (if signed then s.gpr .x3 else s.gpr .x2) (32*d)=
        bitsToBytes (fieldBits d (vals F s.mem (s.gpr .x0))) ∧
      Frame [⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩] s.mem t.mem ∧ Keep widthRegs s t := by
  unfold width
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (setup_ok signed b s) fun a ⟨ka,ma,oa,ca⟩=>?_
  refine WP.mono (counter_ok (256/c) (by have := hs.G;omega) a) fun u ⟨⟨⟨cu,mu⟩,ku⟩,vu⟩=>?_
  have hk : Keep widthRegs s u := (ka.trans ku).mono
  exact width_loop_bytes signed b d c hs hc4 ht s (s.gpr .x0)
    (if signed then s.gpr .x3 else s.gpr .x2) F hin hout hsep hv hvalues
    (by rw [ku.get .x0,ka.get .x0]) (by rw [ku.get .x2,oa]) (mu.trans ma) hk
    (fun h=>⟨by rw [vu];exact (ca h).bias,by rw [vu];exact (ca h).modulus⟩) cu

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end
