module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DecompressMain
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP320r1.Config
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP320r1Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP320r1Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec

/-! # Instantiate shared compression with BrainpoolP320r1's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.BrainpoolP320r1Decompress

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.BrainpoolP320r1

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.decompress brainpoolp320r1

materialize_shared baseline := code

 theorem ct : ConstantTime isa (decompressContract Spec.BrainpoolP320r1.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.BrainpoolP320r1.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
  apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
  · intro s₁ s₂ _ _ hp
    obtain ⟨hsp, hout, hpk, hws⟩ := hp
    refine ⟨hsp, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
  · taint_decide

 theorem sat : ∃ s, (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.BrainpoolP320r1.curve.len)

 theorem chain_ok : Proof.Weierstrass.AArch64.ChainOk
    (Impl.EcKey.Compressed.AArch64.rootChain brainpoolp320r1 ((brainpoolp320r1.C.p + 1) / 4)) ((brainpoolp320r1.C.p + 1) / 4) := by
  apply Proof.Weierstrass.AArch64.ChainOk.of_check
  decide +kernel

/-- brainpoolP320r1's `p` takes the general form of the multiplication
function, which the root's power calls (`rootMod`). -/
theorem brainpoolp320r1p_ok : Proof.Weierstrass.AArch64.Mont.ModOk 5 Spec.BrainpoolP320r1.p := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

theorem rootCall : RootCall brainpoolp320r1 := by
  intro f m h
  have e : (Impl.Weierstrass.AArch64.Mont.rootCallOf (Impl.EcKey.Compressed.AArch64.rootMod brainpoolp320r1)).map
      Prod.snd = some Spec.BrainpoolP320r1.p := by decide +kernel
  rw [h] at e
  obtain rfl := Option.some.inj e
  exact ⟨rfl, brainpoolp320r1p_ok⟩

 theorem verified (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract abi 0) := by
  have hc := (brainpoolp320r1_ok hI)
  exact Verified.of_correct (decompress_correct brainpoolp320r1 hc _
    (candidateThree_correct hc rootCall (by decide +kernel) chain_ok)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct
    (decompress_implies Spec.EcKey.BrainpoolP320r1.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat)

/-- `vg_ec_brainpoolp320r1_decompress_public_key` as it is emitted, its cleanup included
(`Impl.EcKey.AArch64.Fn.decompressBrainpoolP320r1`), meets its contract in constant time and
returns without secret residue. -/
theorem scrubbed (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.EcKey.AArch64.Fn.decompressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract abi 0) 32 :=
  AArch64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi)
    { code := code, verified := verified hL hI } _
    (Proof.EcKey.AArch64.Scrub.decompressOk _) (by dsimp only; lit_decide)

end VG.Proof.EcKey.Compressed.AArch64.BrainpoolP320r1Decompress
