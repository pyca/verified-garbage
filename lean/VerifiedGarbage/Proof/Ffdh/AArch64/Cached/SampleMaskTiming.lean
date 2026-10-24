module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleMask
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Mask setup branches only on the reviewed public width, never on entropy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure MaskPublic where
 B : Addr
 Z : Nat
 N : Nat
 room : 256≤Z
 positive : 0<N
 bound : N≤8192

structure MaskReady (p : MaskPublic) (s : State) : Prop where
 scratch : Scr s p.B p.Z
 base : s.gpr .x0=p.B
 bits : word s.mem p.B (8*sBits)=BitVec.ofNat 64 p.N

theorem sampleMask_ct : RelCT isa (Two MaskReady) Generate.mask (fun _ _ => True) := by
 unfold Generate.mask
 refine RelCT.seq (two_piece (Ψ:=fun p s =>s.gpr .x0=p.B ∧ s.gpr .x3=BitVec.ofNat 64 (7-(p.N-1)%8))
  [.x0] ?_ (by taint_decide) ?_) (two_taint [.x0,.x3] ?_ (by taint_decide))
 · intro p s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.base.trans ht.base.symm
 · intro p s h
   refine WP.mono (sampleMaskHead_ok h.scratch p.room h.base p.positive p.bound h.bits) ?_
   rintro t ⟨⟨count,_,_⟩,rest⟩
   exact ⟨(rest.gpr .x0 (by decide)).trans h.base,count⟩
 · intro p s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.trans ht.2.symm

end VG.Proof.Ffdh.AArch64.Cached
