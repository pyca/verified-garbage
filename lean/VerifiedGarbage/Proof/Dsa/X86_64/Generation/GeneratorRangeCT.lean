module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoadsCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DecrementOdd
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoads
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoadsCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DecrementOdd
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoads
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of generator-input and generator-output range filtering -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

def GeneratorRangeBefore (p : GeneratorLoadPublic) (s : State) : Prop :=
  GeneratorLoadBefore p s ∧ Spec.Rsa.os2ip p.modulus.bytes % 2 = 1

def GeneratorRangeLoaded (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 0) p.w % 2 = 1

def GeneratorRangeWorkspace (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Ws s p.B p.Z p.w

theorem generatorRangeWorkspace_ct :
    RelCT isa (Two GeneratorRangeWorkspace) (Impl.Dsa.X86_64.Checks.rangeMask true)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Checks.rangeMask seqs
  let addresses (p : LoadPublic) (s : State) : Prop :=
    s.gpr .r12 = BitVec.ofNat 64 p.w ∧
    s.gpr .rbx = off p.B (slot p.w Public.aX) ∧
    s.gpr .r10 = off p.B (slot p.w Public.aN)
  refine RelCT.seq (two_piece (Ψ := addresses) [.rdi] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.rdi.trans ht.rdi.symm
  · intro p s h
    exact WP.mono (VG.Proof.Dsa.X86_64.rangeHead_ok h.good.1 h.good.2)
      fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  · exact two_taint [.r12, .rbx, .r10] (fun p s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

theorem generatorLoadPair_ready {p : GeneratorLoadPublic} {s : State}
    (h : GeneratorLoadBefore p s) :
    WP isa Impl.Dsa.X86_64.Generation.generatorLoadPair s fun t =>
      VG.Proof.Rsa.X86_64.Ws t p.modulus.B p.modulus.Z p.modulus.w ∧
      wv t.mem p.modulus.B (slot p.modulus.w 0) p.modulus.w = Spec.Rsa.os2ip p.modulus.bytes :=
  WP.mono (generatorLoadPair_ok h.1.ws h.1.pointer h.1.length h.2.pointer h.2.length
    h.1.source h.2.source h.1.positive h.1.fits h.2.positive h.2.fits)
    (fun _ h => ⟨h.1, h.2.1⟩)

theorem generatorDecrement_ct :
    RelCT isa (Two GeneratorRangeLoaded) (.block (decA 0))
      (Two GeneratorRangeWorkspace) := by
  unfold decA
  simp only [List.append_assoc]
  exact ws_block_ct LoadPublic.B LoadPublic.Z LoadPublic.w (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => WP.mono
      (decrementOdd_ok h.1 (by decide : 0 < 16) h.2) fun _ ht => ht.1)

theorem generatorRange_ct :
    RelCT isa (Two GeneratorRangeBefore) Impl.Dsa.X86_64.Generation.generatorRange
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.generatorRange
  refine RelCT.seq (two_post (generatorLoadPair_ct.mono
    (fun _ _ ⟨p, hs, ht⟩ => ⟨p, hs.1, ht.1⟩) (fun _ _ h => h))
    (fun p s h => WP.mono (generatorLoadPair_ready h.1) fun t ht =>
      show GeneratorRangeLoaded p.modulus t from ⟨ht.1, ht.2 ▸ h.2⟩)) ?_
  exact RelCT.seq (two_map GeneratorLoadPublic.modulus (fun _ _ h => h) generatorDecrement_ct)
    generatorRangeWorkspace_ct

theorem generatorResult_ct :
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.X86_64.Generation.generatorResult
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.generatorResult
  refine RelCT.seq (two_post generatorLoadPair_ct
    (fun p s h => WP.mono (generatorLoadPair_ready h) fun _ ht =>
      show GeneratorRangeWorkspace p.modulus _ from ht.1)) ?_
  exact two_map GeneratorLoadPublic.modulus
    (fun _ _ h => h) generatorRangeWorkspace_ct

end VG.Proof.Dsa.X86_64.Generation
