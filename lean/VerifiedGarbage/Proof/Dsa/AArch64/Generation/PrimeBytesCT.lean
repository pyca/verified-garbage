module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ProbablePrimeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ProbablePrimeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytes

/-! Test saved candidate bytes using the shared native primality operation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate

structure PrimeBytesPublic where
  call : PrimeCallPublic
  source : Addr
  bytes : List Byte
  length : bytes.length = call.draw.prime.len
  value : Spec.Rsa.os2ip bytes = call.draw.prime.N

def PrimeBytesBefore (len drawBytes : Nat) (p : PrimeBytesPublic) (s : State) : Prop :=
  PrimeArguments p.call.draw.prime p.call.draw.used s ∧
    word s.mem p.call.draw.prime.B 160 = p.source ∧ Src s p.call.draw.prime.B p.call.draw.prime.Z p.source p.bytes ∧
    p.call.draw.used ≤ p.call.draw.prime.rand.length ∧ p.call.draw.prime.len = len ∧ p.call.draw.prime.drawBytes = drawBytes

theorem primeBytesLoad_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeBytesBefore len drawBytes))
    (seqs (Impl.Rsa.AArch64.Keys.loadA 0 20 kUsedP)) (fun _ _ => True) :=
  VG.Proof.RsaKeyGen.AArch64.loadA_ct0 (fun p : PrimeBytesPublic => p.call.draw.prime.B)
    (fun p => p.call.draw.prime.Z) (fun p => p.call.draw.prime.w)
    (by decide) (by decide) (by decide) PrimeBytesPublic.source (fun p => p.call.draw.prime.len)
    (fun _ _ h => ⟨h.1.ws, h.2.1, h.1.len⟩) (by taint_decide) (by taint_decide) (by taint_decide)

theorem primeBytesLoad_ready {len drawBytes : Nat} {p : PrimeBytesPublic} {s : State}
    (h : PrimeBytesBefore len drawBytes p s) :
    WP isa (seqs (Impl.Rsa.AArch64.Keys.loadA 0 20 kUsedP)) s (PrimeCallBefore len drawBytes p.call) :=
  WP.mono (loadPrimeBytes_ok h.1 h.2.1 p.length p.value h.2.2.1) (fun _ ⟨ht, _, _⟩ => ⟨ht, h.2.2.2⟩)

theorem primeBytes_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc₂).isSome = true) :
    RelCT isa (Two (PrimeBytesBefore len drawBytes)) (Impl.Dsa.AArch64.Generation.primeBytes M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeBytes
  exact RelCT.seq (two_post (primeBytesLoad_ct len drawBytes) (fun _ _ h => primeBytesLoad_ready h))
    (two_map PrimeBytesPublic.call (fun _ _ h => h) (probablePrime_ct M K len drawBytes ht₁ ht₂))

end VG.Proof.Dsa.AArch64.Generation
