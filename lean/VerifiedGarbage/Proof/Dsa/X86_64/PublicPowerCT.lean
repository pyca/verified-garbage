module
public import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower

import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponentCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPower
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponentCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of public exponentiation with secret bases -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

def EncodedPre (p : PowerPublic × List Byte) (s : State) : Prop :=
  ∃ x : Nat, PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx Crt.aXc) p.1.bytes.x.wx =
      x * 2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aY) p.1.bytes.x.wx =
      2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus

/-- Exponentiation and decoding together have a secret-independent trace. -/
theorem encodedPower_ct (M : Mont) (Sq : MontS) : RelCT isa (Two EncodedPre)
    (VG.Impl.Dsa.X86_64.PublicPower.encodedPower Sq.mm M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.encodedPower
  refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.1.bytes.x.ws s)
    (two_map (fun p : PowerPublic × List Byte => (p.1.bytes, p.2)) ?_ (crtExpLoop_ct M Sq (by taint_decide))) ?_)
    (two_map (fun p : PowerPublic × List Byte => p.1.bytes.x.ws) (fun _ _ h => h)
      (M.ct (by unfold MmUse; decide)))
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, hlen, h1, h2, hs⟩, hx, hy⟩
    refine ⟨p.1.minv, p.1.modulus, x, 1, hc, p.1.lower, p.1.fits, p.1.upper,
      hm.modulus, hm.inverse, p.1.odd, ?_, ?_, ?_, ?_, by decide, by decide,
      hp, hl, hlen, h1, h2, hs⟩
    · rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega)
    · rw [hx, Nat.mod_mod]
    · rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega)
    · rw [hy, Nat.mod_mod, Nat.one_mul]
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, _, h1, h2, hs⟩, hx, hy⟩
    refine WP.mono (expLoop_ok M Sq (x := x) hc p.1.lower p.1.fits p.1.upper hm.modulus hm.inverse p.1.odd
      (by rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega))
      (by rw [hx, Nat.mod_mod])
      (by rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega))
      (by rw [hy, Nat.mod_mod]) (by decide) (by decide) hp hl h1 h2 hs)
      fun t ⟨ht, _⟩ => ⟨p.1.minv, ht.good, Nat.le_refl _⟩

/-- Prepared ordinary bases for the complete encode/exponentiate/decode core. -/
def PowerCorePre (p : PowerPublic × List Byte) (s : State) : Prop :=
  PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aR2) p.1.bytes.x.wx =
      2 ^ (128 * p.1.bytes.x.wx) % p.1.modulus

/-- The whole power core is constant time for secret bases and fixed public exponents. -/
theorem powerCore_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCorePre)
    (VG.Impl.Dsa.X86_64.PublicPower.powerCore Sq.mm M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.powerCore
  refine RelCT.seq (two_post (Ψ := EncodedPre)
    (two_map (fun p : PowerPublic × List Byte => p.1.product) ?_ (encodePower_ct M)) ?_)
    (encodedPower_ct M Sq)
  · intro p s ⟨⟨_, hm, hone, _⟩, hr2⟩
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]; exact Nat.mod_lt _ (by have := p.1.greater; omega)
    · dsimp only [PowerPublic.product]
      rw [hone]; exact p.1.greater
  · intro p s ⟨⟨hc, hm, hone, hp, hl, hlen, h1, h2, hs⟩, hr2⟩
    rw [show 128 * p.1.bytes.x.wx = 64 * p.1.bytes.x.wx + 64 * p.1.bytes.x.wx by omega, Nat.pow_add] at hr2
    refine WP.mono (encodePower_ok M hm (Nat.le_refl _) p.1.lower
      (by have := p.1.fits; have := p.1.upper; omega) p.1.greater p.1.odd rfl hr2 hone)
      fun t ⟨hmt, hx, hy, htone, hf, hk⟩ => ?_
    have hct := arrays_context hc hf (by decide) hk
    have hfw := arrays_work hf (by decide)
    exact ⟨_, ⟨hct, hmt, htone, (work_parent hc hfw (by decide)).trans hp,
      (work_parent hc hfw (by decide)).trans hl, hlen, h1, h2, work_source hc hfw hk hs⟩, hx, hy⟩


end VG.Proof.Dsa.X86_64.PublicPower
