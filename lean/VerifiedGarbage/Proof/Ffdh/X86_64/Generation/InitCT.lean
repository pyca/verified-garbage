module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Initialization only exposes its public pointer, bit count and u32 generator -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation

structure InitPublic where
  ptr : Addr
  bits : BitVec 64
  generator : BitVec 32

def InitInput (p : InitPublic) (s : State) : Prop :=
  s.gpr .rdi = p.ptr ∧ s.gpr .rsi = p.bits ∧ (s.gpr .rdx).setWidth 32 = p.generator

def InitNormalized (p : InitPublic) (s : State) : Prop :=
  s.gpr .rdi = p.ptr ∧ s.gpr .rsi = p.bits ∧ s.gpr .rdx = p.generator.setWidth 64

private theorem normalize_ok (p : InitPublic) (s : State) (h : InitInput p s) :
    WP isa (.block [.mov32 .rdx (.reg .rdx)]) s (InitNormalized p) := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.gpr .rdx = ((s.gpr .rdx).setWidth 32).setWidth 64) (by xrun []) rfl)
    fun _ ⟨hd, k⟩ => ?_
  exact ⟨(k.gpr (by decide)).trans h.1, (k.gpr (by decide)).trans h.2.1,
    hd.trans (congrArg (BitVec.setWidth 64) h.2.2)⟩

theorem init_ct : RelCT isa (Two InitInput) init fun _ _ => True := by
  unfold init
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by cases h)
    (by taint_decide) normalize_ok) ?_
  exact two_taint [.rdi, .rsi, .rdx] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm])
    (by taint_decide)

def initPub (s t : State) : Prop :=
  s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    (s.gpr .rdx).setWidth 32 = (t.gpr .rdx).setWidth 32

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  refine RelCT.constantTime (init_ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hdi, hsi, hg⟩ := h
  exact ⟨⟨s.gpr .rdi, s.gpr .rsi, (s.gpr .rdx).setWidth 32⟩,
    ⟨rfl, rfl, rfl⟩, hdi.symm, hsi.symm, hg.symm⟩

end VG.Proof.Ffdh.X86_64.Generation
