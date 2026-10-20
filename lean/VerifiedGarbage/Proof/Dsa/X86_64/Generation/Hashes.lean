module
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Spec.Mgf1

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Hash implementations shared by the complete parameter-generation phases -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Pbkdf2.Md.X86_64

structure GenerationHashes where
  sha1 : Impl.Pbkdf2.Md.X86_64.Stream
  sha256 : Impl.Pbkdf2.Md.X86_64.Stream
  h1 : Calls.StreamOK sha1
  h256 : Calls.StreamOK sha256
  hash1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x
  hash256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x
  size1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = sha1.D
  size256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = sha256.D
  width1 : sha1.D = 20
  width256 : sha256.D = 32

end VG.Proof.Dsa.X86_64.Generation
