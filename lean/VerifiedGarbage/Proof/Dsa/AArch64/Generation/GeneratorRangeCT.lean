module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoadsCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
public import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoadsCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT

/-! # Timing of generator-input and generator-output range filtering -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

def GeneratorRangeBefore (p : GeneratorLoadPublic) (s : State) : Prop :=
  GeneratorLoadBefore p s ∧ Spec.Rsa.os2ip p.modulus.bytes % 2 = 1

def GeneratorRangeLoaded (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 0) p.w % 2 = 1

def GeneratorRangeWorkspace (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w

theorem generatorRangeWorkspace_ct :
    RelCT isa (Two GeneratorRangeWorkspace) (Impl.Dsa.AArch64.Checks.rangeMask true)
      (fun _ _ => True) := by
  exact two_map (fun p : LoadPublic => (⟨p.B, p.Z, p.w⟩ : VG.Proof.Bignum.AArch64.Ws))
    (fun _ _ h => ⟨⟨_, h.good⟩, h.w1, by dsimp only; have := h.w2; omega⟩)
    (VG.Proof.Dsa.AArch64.rangeMask_ct true)

theorem generatorLoadPair_ready {p : GeneratorLoadPublic} {s : State}
    (h : GeneratorLoadBefore p s) :
    WP isa Impl.Dsa.AArch64.Generation.generatorLoadPair s fun t =>
      VG.Proof.Rsa.AArch64.Ws t p.modulus.B p.modulus.Z p.modulus.w ∧
      wv t.mem p.modulus.B (slot p.modulus.w 0) p.modulus.w = Spec.Rsa.os2ip p.modulus.bytes :=
  WP.mono (generatorLoadPair_ok h.1.ws h.1.pointer h.1.length h.2.pointer h.2.length
    h.1.source h.2.source h.1.positive h.1.fits h.2.positive h.2.fits)
    (fun _ h => ⟨h.1, h.2.1⟩)

theorem generatorDecrement_ct :
    RelCT isa (Two GeneratorRangeLoaded) (.block (decA 0))
      (Two GeneratorRangeWorkspace) := by
  unfold decA
  simp only [List.append_assoc]
  exact ws_block_ct (fun p : LoadPublic => p.B) (fun p : LoadPublic => p.Z) (fun p : LoadPublic => p.w) (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => WP.mono
      (decrementOdd_ok h.1 (by decide : 0 < 16) h.2) fun _ ht => ht.1)

theorem generatorRange_ct :
    RelCT isa (Two GeneratorRangeBefore) Impl.Dsa.AArch64.Generation.generatorRange
      (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.generatorRange
  refine RelCT.seq (two_post (generatorLoadPair_ct.mono
    (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p, hs.1, ht.1, hsp⟩) (fun _ _ h => h))
    (fun p s h => WP.mono (generatorLoadPair_ready h.1) fun t ht =>
      show GeneratorRangeLoaded p.modulus t from ⟨ht.1, ht.2 ▸ h.2⟩)) ?_
  exact RelCT.seq (two_map GeneratorLoadPublic.modulus (fun _ _ h => h) generatorDecrement_ct)
    generatorRangeWorkspace_ct

theorem generatorResult_ct :
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.AArch64.Generation.generatorResult
      (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.generatorResult
  refine RelCT.seq (two_post generatorLoadPair_ct
    (fun p s h => WP.mono (generatorLoadPair_ready h) fun _ ht =>
      show GeneratorRangeWorkspace p.modulus _ from ht.1)) ?_
  exact two_map GeneratorLoadPublic.modulus
    (fun _ _ h => h) generatorRangeWorkspace_ct

end VG.Proof.Dsa.AArch64.Generation
