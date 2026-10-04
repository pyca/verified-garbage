import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Impl.Ecdsa.P256.Arm
import VerifiedGarbage.Proof.Ecdsa.Arm.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on AArch64 (`Proof/Ecdsa/Rfc6979/AArch64/Hash.lean`): the instance of the
contract it implements (P-256, the hash function's HMAC, its output length,
8 candidates), the functions PBKDF2's code calls and what its proofs know of
them (`FnsOK`: HMAC's `init` and `finalize` and the streaming `update`,
verified), what is proven of `vg_ecdsa_p256_sign`, which each candidate calls
(`coreX`, `coreCT`: its proof's heavy algebra stays out of the modules
generic over the hash function), and the sizes the frame and `scratch` are
laid out for: the output and block sizes of SHA-256, SHA-384 or SHA-512, and
states and working space no larger than SHA-512's.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Whole.Arm (FnsOK)

/-- A hash function, for RFC 6979 over P-256 on 32-bit ARM. -/
structure RfcHash where
  /-- The instance of the contract. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The functions PBKDF2's code calls, of the hash function. -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  ok : FnsOK F
  /-- The instance is of P-256, with this hash function's HMAC, its output
  length and 8 candidates. -/
  ecdsa : I.ecdsa = Spec.Ecdsa.P256.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  tries : I.tries = 8
  /-- The sizes the frame and `scratch` hold: the output and block sizes of
  SHA-256, SHA-384 or SHA-512. -/
  hDB : (F.H.D = 32 ∧ F.H.B = 64) ∨ (F.H.D = 48 ∧ F.H.B = 128) ∨ (F.H.D = 64 ∧ F.H.B = 128)
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872
  hWb : ok.hH.Wb ≤ 1872
  /-- `vg_ecdsa_p256_sign` is correct and constant time. -/
  coreX : ∀ s, Proof.Ecdsa.Arm.signArm.pre s → ∃ t s', Exec isa Impl.Ecdsa.Arm.signP256 s t s' ∧
    abiPreserved s s' ∧ Proof.Ecdsa.Arm.signArm.post s s'
  coreCT : ConstantTime isa Proof.Ecdsa.Arm.signArm.pre Proof.Ecdsa.Arm.signArm.pub Impl.Ecdsa.Arm.signP256

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    32 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 8 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧
    P.ok.hH.SH.stateBytes = P.F.H.S ∧ P.ok.hH.SH.digestBytes = P.F.H.D ∧
    P.ok.hH.SH.H.blockSize = P.F.H.B := by
  refine ⟨P.hS, P.hWi, P.hWf, P.hWb, ?_, ?_, ?_, ?_, ?_, P.ok.hH.hS, P.ok.hH.hD, P.ok.hH.hB⟩ <;>
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> omega

/-- The digest is at least 32 bytes. -/
theorem len32 : 32 ≤ P.I.hashLen := by
  rw [P.len]; rcases P.hDB with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  F := P.F
  n := Spec.P256.n
  tries := 8
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.Arm.signP256

end VG.Proof.Ecdsa.Rfc6979.Arm
