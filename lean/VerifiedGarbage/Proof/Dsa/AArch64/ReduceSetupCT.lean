module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByteCT
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByteCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of streaming-reduction setup -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReduceContext (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus

def ReduceSetupPre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ p.bytes.x.wx ≤ 48

theorem reduceSetup_ct (M : Mont) : RelCT isa (Two ReduceSetupPre)
    (Arithmetic.reduceSetup M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceSetup seqs
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2, h.2, p.greater, p.odd⟩) (constants_ct M)) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hw⟩
    exact WP.mono (prepare_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
      fun t ⟨hct, hmt, _, hr, _⟩ => ⟨⟨hct, hmt⟩, hr ▸ Nat.mod_lt _ (by have := p.greater; omega)⟩
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product.layout)
      (fun _ _ h => ⟨h.1.1.good, Nat.le_refl _⟩)
      (small256_ct (by decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hr⟩
    refine WP.mono (small_ok hc.good (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega) (by decide) (value := 256) (by decide))
      fun t ⟨hg, _, hf, hk⟩ => ?_
    have ht := arrays_context hc hf (by decide) hk
    have hz := hc.good.scr.nowrap
    refine ⟨⟨ht, ⟨hg, (hf.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩⟩, ?_⟩
    · rw [hf.word0_of_not_mem (by decide) (by decide) hz (by have := p.lower; omega)]
      exact hm.inverse
    · rw [hf.wv_of_not_mem (by decide) (by decide) hz]
      exact hr
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.1.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hr⟩
    exact WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega) (by unfold MmUse; decide) hr)
      fun t ⟨ht, _, _, hf, hk⟩ => ⟨arrays_context hc hf (by decide) hk, ht⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
      (zeroArr_ct (by decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, hm⟩
    exact WP.mono (clear_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega)
      (by decide) (by decide)) fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
  exact two_map (fun p : ReducePublic => p.bytes.x.ws)
    (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
    (zeroArr_ct (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64
