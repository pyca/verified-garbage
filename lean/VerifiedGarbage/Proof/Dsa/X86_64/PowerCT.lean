module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time components of DSA exponentiation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

/-- Encoding the base does not branch on or address memory by its value. -/
theorem encodePower_ct (M : Mont) :
    RelCT isa (Two (Reduced [aR2, aOne])) (Arithmetic.encodePower M.mm) (fun _ _ => True) := by
  unfold Arithmetic.encodePower
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aR2, aOne] (by decide) (by decide))
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aY, aR2, aOne] (by decide) (by decide))
  exact two_map (fun p : ProductPublic => p.layout.ws)
    (fun p _ h => ⟨_, h.1.good, p.fits⟩)
    (copyArr_ct (o := Crt.aXc) (a := aXm) (by decide) (by decide) (by taint_decide))

/-- The shared secret-exponent loop with DSA's parent-header argument slots.
The byte values are secret; the pointer, length and workspace layout are public. -/
theorem exponent_ct (M : Mont) (Sq : MontS) :
    ExpCTS M Sq CrtSel.sse VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len :=
  crtExpLoopS_ct M Sq CrtSel.sse CrtSel.sse_ct (by taint_decide)

/-- The caller fixes addresses, widths and modulus; exponent and base values
remain existential in the relational preconditions. -/
structure PowerPublic where
  bytes : BPub
  minv : BitVec 64
  modulus : Nat
  lower : 2 ≤ bytes.x.wx
  fits : bytes.x.wx ≤ bytes.x.w
  upper : bytes.x.w < 2 ^ 30
  greater : 1 < modulus
  odd : modulus % 2 = 1

def PowerPublic.product (p : PowerPublic) : ProductPublic :=
  ⟨⟨off p.bytes.x.B p.bytes.x.o, slot p.bytes.x.wx 8, p.bytes.x.wx, p.minv⟩,
    p.modulus, Nat.le_refl _, p.lower, by change p.bytes.x.wx < 2 ^ 31; have := p.fits; have := p.upper; omega⟩

/-- Common buffer and modulus facts for the power core. -/
def PowerInputs (p : PowerPublic) (eb : List Byte) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aOne) p.bytes.x.wx = 1 ∧
  word s.mem p.bytes.x.B (8 * VG.Impl.Dsa.Layout.arg2) = p.bytes.ptr ∧
  word s.mem p.bytes.x.B (8 * VG.Impl.Dsa.Layout.arg2Len) = BitVec.ofNat 64 eb.length ∧
  eb.length = p.bytes.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧
  Src s p.bytes.x.B p.bytes.x.Z p.bytes.ptr eb

def EncodedPre (p : PowerPublic) (s : State) : Prop :=
  ∃ (x : Nat) (eb : List Byte), PowerInputs p eb s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx Crt.aXc) p.bytes.x.wx =
      x * 2 ^ (64 * p.bytes.x.wx) % p.modulus ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx =
      2 ^ (64 * p.bytes.x.wx) % p.modulus

/-- Exponentiation and decoding together have a secret-independent trace. -/
theorem encodedPower_ct (M : Mont) (Sq : MontS) : RelCT isa (Two EncodedPre)
    (Arithmetic.encodedPower Sq.mm M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold Arithmetic.encodedPower
  refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.bytes.x.ws s)
    (two_map (fun p : PowerPublic => p.bytes) ?_ (exponent_ct M Sq)) ?_)
    (two_map (fun p : PowerPublic => p.bytes.x.ws) (fun _ _ h => h)
      (M.ct (by unfold MmUse; decide)))
  · intro p s ⟨x, eb, ⟨hc, hm, _, hp, hl, hlen, h1, h2, hs⟩, hx, hy⟩
    refine ⟨p.minv, p.modulus, x, 1, eb, hc, p.lower, p.fits, p.upper,
      hm.modulus, hm.inverse, p.odd, ?_, ?_, ?_, ?_, by decide, by decide,
      hp, hl, hlen, h1, h2, hs⟩
    · rw [hx]; exact Nat.mod_lt _ (by have := p.greater; omega)
    · rw [hx, Nat.mod_mod]
    · rw [hy]; exact Nat.mod_lt _ (by have := p.greater; omega)
    · rw [hy, Nat.mod_mod, Nat.one_mul]
  · intro p s ⟨x, eb, ⟨hc, hm, _, hp, hl, _, h1, h2, hs⟩, hx, hy⟩
    refine WP.mono (expLoop_ok M Sq (x := x) hc p.lower p.fits p.upper hm.modulus hm.inverse p.odd
      (by rw [hx]; exact Nat.mod_lt _ (by have := p.greater; omega))
      (by rw [hx, Nat.mod_mod])
      (by rw [hy]; exact Nat.mod_lt _ (by have := p.greater; omega))
      (by rw [hy, Nat.mod_mod]) (by decide) (by decide) hp hl h1 h2 hs)
      fun t ⟨ht, _⟩ => ⟨p.minv, ht.good, Nat.le_refl _⟩

/-- Prepared ordinary bases for the complete encode/exponentiate/decode core. -/
def PowerCorePre (p : PowerPublic) (s : State) : Prop :=
  ∃ eb : List Byte, PowerInputs p eb s ∧
    wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aR2) p.bytes.x.wx =
      2 ^ (128 * p.bytes.x.wx) % p.modulus

/-- The whole power core is constant time for secret bases and exponents. -/
theorem powerCore_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCorePre)
    (Arithmetic.powerCore Sq.mm M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold Arithmetic.powerCore
  refine RelCT.seq (two_post (Ψ := EncodedPre)
    (two_map (fun p : PowerPublic => p.product) ?_ (encodePower_ct M)) ?_)
    (encodedPower_ct M Sq)
  · intro p s ⟨eb, ⟨_, hm, hone, _⟩, hr2⟩
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]; exact Nat.mod_lt _ (by have := p.greater; omega)
    · dsimp only [PowerPublic.product]
      rw [hone]; exact p.greater
  · intro p s ⟨eb, ⟨hc, hm, hone, hp, hl, hlen, h1, h2, hs⟩, hr2⟩
    rw [show 128 * p.bytes.x.wx = 64 * p.bytes.x.wx + 64 * p.bytes.x.wx by omega, Nat.pow_add] at hr2
    refine WP.mono (encodePower_ok M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega) p.greater p.odd rfl hr2 hone)
      fun t ⟨hmt, hx, hy, htone, hf, hk⟩ => ?_
    have hct := arrays_context hc hf (by decide) hk
    have hfw := arrays_work hf (by decide)
    exact ⟨_, eb, ⟨hct, hmt, htone, (work_parent hc hfw (by decide)).trans hp,
      (work_parent hc hfw (by decide)).trans hl, hlen, h1, h2, work_source hc hfw hk hs⟩, hx, hy⟩

end VG.Proof.Dsa.X86_64
