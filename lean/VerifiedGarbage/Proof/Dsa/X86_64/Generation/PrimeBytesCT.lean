module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrimeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PaddedLoadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TrialCT
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrimeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytes
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PaddedLoadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TrialCT
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of primality testing directly from the saved candidate bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

structure PrimeBytesPublic where
  call : PrimeCallPublic
  source : Addr
  bytes : List Byte
  length : bytes.length = call.draw.prime.len
  value : Spec.Rsa.os2ip bytes = call.draw.prime.N

def PrimeBytesBefore (len drawBytes : Nat) (p : PrimeBytesPublic) (s : State) : Prop :=
  (∃ mi, PrimeArguments p.call.draw.prime mi p.call.draw.used s) ∧
    word s.mem p.call.draw.prime.B 160 = p.source ∧ Src s p.call.draw.prime.B p.call.draw.prime.Z p.source p.bytes ∧
    s.wr = p.call.wr ∧ p.call.draw.used ≤ p.call.draw.prime.rand.length ∧
    p.call.draw.prime.len = len ∧ p.call.draw.prime.drawBytes = drawBytes

def PrimeBytesPublic.padded (p : PrimeBytesPublic) : PaddedPublic :=
  ⟨p.call.draw.prime.B, p.call.draw.prime.Z, p.call.draw.prime.w, p.source, p.call.draw.prime.len⟩

theorem primeBytesLoad_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeBytesBefore len drawBytes))
    (Impl.Dsa.X86_64.Generation.loadPadded 0 20 18) (fun _ _ => True) := by
  refine two_map PrimeBytesPublic.padded (fun p s h => ?_)
    (loadPadded_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))
  obtain ⟨mi, hs⟩ := h.1
  exact ⟨⟨mi, hs.good⟩, p.call.draw.prime.dims.z,
    by change 1 ≤ p.call.draw.prime.w; have := p.call.draw.prime.dims.w4; omega,
    by change p.call.draw.prime.w < 2 ^ 31; have := p.call.draw.prime.dims.w128; omega,
    h.2.1, hs.len⟩

theorem primeBytesLoad_ready {len drawBytes : Nat} {p : PrimeBytesPublic} {s : State}
    (h : PrimeBytesBefore len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded 0 20 18) s (PrimeCallBefore len drawBytes p.call) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (loadPrimeBytes_ok hs h.2.1 p.length p.value h.2.2.1) fun _ ⟨ht, _, hk⟩ =>
    ⟨⟨mi, ht⟩, hk.2.2.trans h.2.2.2.1, h.2.2.2.2⟩

theorem primeBytes_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) :
    RelCT isa (Two (PrimeBytesBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeBytes
  exact RelCT.seq (two_post (primeBytesLoad_ct len drawBytes) (fun _ _ h => primeBytesLoad_ready h))
    (two_map PrimeBytesPublic.call (fun _ _ h => h) (probablePrime_ct M K len drawBytes))

end VG.Proof.Dsa.X86_64.Generation
