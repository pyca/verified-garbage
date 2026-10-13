module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByteCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByteCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

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

def ReduceDoublePre (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx < p.modulus

theorem reduceSetup_ct (M : Mont) : RelCT isa (Two ReduceSetupPre)
    (Arithmetic.reduceSetup M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceSetup seqs
  refine RelCT.seq (two_post (Ψ := fun p s => ReduceContext p s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aOne) p.bytes.x.wx = 1)
    (two_map (fun p : ReducePublic => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2, h.2, p.greater, p.odd⟩) (constants_ct M)) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hw⟩
    exact WP.mono (prepare_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
      fun t ⟨hct, hmt, hone, _⟩ => ⟨⟨hct, hmt⟩, hone⟩
  refine RelCT.seq (two_post (Ψ := ReduceDoublePre)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.1.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hone⟩
    exact WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega) (by unfold MmUse; decide)
      (by rw [hone]; exact p.greater)) fun t ⟨hmt, hlt, _, hf, hk⟩ =>
        ⟨⟨arrays_context hc hf (by decide) hk, hmt⟩, hlt⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => ReduceDoublePre p s ∧ s.gpr .x13 = BitVec.ofNat 64 8) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_) ?_
  · intro p s ⟨⟨hc, hm⟩, hlt⟩
    refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 8 ∧ t.mem = s.mem)
      (by brun) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hcx, hmem⟩, hk⟩ => ?_
    have hct := hc.of_keep hmem hk (by decide)
    exact ⟨⟨⟨hct, ⟨hct.good, hmem ▸ hm.modulus, hmem ▸ hm.inverse⟩⟩, hmem ▸ hlt⟩, hcx⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => (⟨p.toPowerPublic.product.layout, 8⟩ : DblPub)) ?_
      ((doubles_ct (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (sl := sCnt) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)).mono
          (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_) ?_
  · intro p s ⟨⟨⟨hc, hm⟩, hlt⟩, hcx⟩
    exact ⟨⟨hc.good, Nat.le_refl _⟩, p.lower,
      by change p.bytes.x.wx < 2 ^ 31; have := p.fits; have := p.upper; omega,
      by change 1 ≤ 8; decide, by change 8 < 2 ^ 31; decide, hcx, by
        change wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx <
          wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aN) p.bytes.x.wx
        rw [hm.modulus]; exact hlt⟩
  · intro p s ⟨⟨⟨hc, hm⟩, hlt⟩, hcx⟩
    exact WP.mono (double_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega)
      (by decide) (by decide) (c := 8) hcx hlt) fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
  refine RelCT.seq (two_post (Ψ := ReduceContext)
    (two_map (fun p : ReducePublic => p.bytes.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
      (copyArr_ct (o := aXm) (a := aR2) (by decide) (by decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, hm⟩
    exact WP.mono (copy_mod_ok hc hm p.lower (by have := p.fits; have := p.upper; omega))
      fun t ⟨hct, hmt, _⟩ => ⟨hct, hmt⟩
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
