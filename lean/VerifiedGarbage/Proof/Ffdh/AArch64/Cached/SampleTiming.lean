module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleMaskTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! Sampling uses the public width and length for every draw, including rejected draws. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure SamplePublic where
 workspace : Ws
 room : slot workspace.w 8≤workspace.Z
 k : Nat
 N : Nat
 xp : Addr
 rp : Addr
 positive : 0<N
 bound : N≤8192

structure SampleReady (p : SamplePublic) (s : State) : Prop where
 good : GoodW p.workspace s
 bits : word s.mem p.workspace.B (8*sBits)=BitVec.ofNat 64 p.N
 bytes : word s.mem p.workspace.B (8*sBytes)=BitVec.ofNat 64 ((p.N+7)/8)
 length : word s.mem p.workspace.B (8*sLen)=BitVec.ofNat 64 p.k
 x : word s.mem p.workspace.B (8*sX)=p.xp
 random : word s.mem p.workspace.B (8*sRand)=p.rp

structure SampleMasked (p : SamplePublic) (s : State) : Prop extends SampleReady p s where
 mask : s.gpr .x12=sampleMask p.N

theorem sample_ct : RelCT isa (Two SampleReady) Generate.sample (fun _ _ =>True) := by
 unfold Generate.sample
 refine RelCT.seq (two_post (Ψ:=SampleMasked) ?_ ?_) ?_
 · exact two_map (fun p =>(⟨p.workspace.B,p.workspace.Z,p.N,by
    have := p.room;dsimp only [slot,hdrBytes] at this;omega,p.positive,p.bound⟩ : MaskPublic))
    (fun _ _ h =>by rcases h.good with ⟨mi,good,_⟩;exact ⟨good.scr,good.x0,h.bits⟩) sampleMask_ct
 · intro p s h
   obtain ⟨mi,good,room⟩ := h.good
   have room256 : 256≤p.workspace.Z := by dsimp only [slot,hdrBytes] at room;omega
   refine WP.mono (sampleMask_ok good.scr room256 good.x0 p.positive p.bound h.bits) ?_
   rintro t ⟨mask,_,_,frame,rest⟩
   have goodT := good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0)
   have same (i : Nat) (hi : i<32) (ne : i≠sMask) := header_other frame (by decide) hi ne
   exact ⟨⟨⟨mi,goodT,room⟩,(same sBits (by decide) (by decide)).trans h.bits,
    (same sBytes (by decide) (by decide)).trans h.bytes,(same sLen (by decide) (by decide)).trans h.length,
    (same sX (by decide) (by decide)).trans h.x,(same sRand (by decide) (by decide)).trans h.random⟩,mask⟩
 · refine RelCT.seq (two_piece (Ψ:=fun p s =>
    s.gpr .x1=p.rp ∧ s.gpr .x2=p.xp ∧ s.gpr .x10=0#64 ∧
    s.gpr .x11=BitVec.ofNat 64 p.k-BitVec.ofNat 64 ((p.N+7)/8) ∧
    s.gpr .x12=sampleMask p.N ∧ s.gpr .x14=BitVec.ofNat 64 p.k)
    [.x0] (fun p s t hs ht r hr =>by
     have eq : r= .x0 := by simpa using hr
     subst r
     obtain ⟨_,gs,_⟩ := hs.good;obtain ⟨_,gt,_⟩ := ht.good
     exact gs.x0.trans gt.x0.symm) (by taint_decide) ?_)
    (two_taint [.x1,.x2,.x10,.x11,.x12,.x14] ?_ (by taint_decide))
   · intro p s h
     obtain ⟨mi,good,room⟩ := h.good
     brun [good.x0,hdr_enc (show sLen<32 by decide),hdr_enc (show sBytes<32 by decide),
      hdr_enc (show sX<32 by decide),hdr_enc (show sRand<32 by decide),
      header_read good room (show sLen<32 by decide),header_read good room (show sBytes<32 by decide),
      header_read good room (show sX<32 by decide),header_read good room (show sRand<32 by decide),
      h.length,h.bytes,h.x,h.random,h.mask]
   · intro p s t hs ht r hr
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
     · exact hs.1.trans ht.1.symm
     · exact hs.2.1.trans ht.2.1.symm
     · exact hs.2.2.1.trans ht.2.2.1.symm
     · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
     · exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
     · exact hs.2.2.2.2.2.trans ht.2.2.2.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached
