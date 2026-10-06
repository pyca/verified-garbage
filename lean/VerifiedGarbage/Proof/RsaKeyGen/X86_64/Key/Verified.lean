import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Implies

/-!
# An RSA key from its primes on x86-64: verified against the shared contract

With correctness (`keyCode_wp`), constant time (`keyCode_constantTime`) and
the shared contract's implication (`key_implies`), `code` is verified
(`key_verified`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem keyCode_correct (hmx : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : keyCtr.pre s) :
    ∃ t s', Exec isa VG.Impl.RsaKeyGen.X86_64.Key.code s t s' ∧ abiPreserved s s' ∧ keyCtr.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := keyCode_wp s h
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩

/-- `vg_rsa_keygen_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem key_verified (hmx : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target VG.Impl.RsaKeyGen.X86_64.Key.code (Spec.RsaKeyGen.keyContract abi) :=
  Verified.of_correct (keyCode_correct hmx) keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.X86_64.Key
