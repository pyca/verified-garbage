import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common
import VerifiedGarbage.Impl.Ecdsa.P256.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Contract

/-!
# Deterministic ECDSA on x86 (32-bit): the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the instance of the
contract it implements (P-256, the hash function's HMAC, its output length,
8 candidates), the functions PBKDF2's code calls, verified (`FnsOK`: the
streaming `update`, and HMAC's `init` and `finalize`, which take their
working space as an argument), what is proven of `vg_ecdsa_p256_sign`, which
each candidate calls (`coreX`, `coreCT`: its proof's heavy algebra stays out
of the modules generic over the hash function), and the sizes the frame and
`scratch` are laid out for: the output and block sizes of SHA-256, SHA-384
or SHA-512, and states and working space no larger than SHA-512's. Each hash
function's file builds one for each implementation of its compression
function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK ReprOK)

/-- A hash function, for RFC 6979 over P-256 on x86. -/
structure RfcHash where
  /-- The instance of the contract. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The functions the code calls, verified. -/
  F : Fns
  ok : FnsOK F
  /-- The instance is of P-256, with this hash function's HMAC, its output
  length and 8 candidates. -/
  ecdsa : I.ecdsa = Spec.Ecdsa.P256.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  tries : I.tries = 8
  /-- The sizes the frame and `scratch` hold: the output and block sizes of
  SHA-256, SHA-384 or SHA-512, and states and working space no larger than
  SHA-512's. -/
  hDB : (F.H.D = 32 ∧ F.H.B = 64) ∨ (F.H.D = 48 ∧ F.H.B = 128) ∨ (F.H.D = 64 ∧ F.H.B = 128)
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872
  /-- `vg_ecdsa_p256_sign` is correct and constant time. -/
  coreX : ∀ s, Proof.Ecdsa.X86.signX86.pre s → ∃ t s', Exec isa Impl.Ecdsa.X86.signP256 s t s' ∧
    abiPreserved s s' ∧ Proof.Ecdsa.X86.signX86.post s s'
  coreCT : ConstantTime isa Proof.Ecdsa.X86.signX86.pre Proof.Ecdsa.X86.signX86.pub Impl.Ecdsa.X86.signP256

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

theorem reprOK : ReprOK P.ok.hH.SH := fun m m' p q msg hb =>
  P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi))

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    32 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 8 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 0 < P.F.H.S := by
  have hWb := P.ok.hH.hWb
  have hW := P.ok.hH.hW
  have hS0 := P.ok.hH.hS0
  refine ⟨P.hS, P.hWi, P.hWf, by omega, ?_, ?_, ?_, ?_, ?_, hS0⟩ <;>
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> omega

/-- The digest is at least 32 bytes. -/
theorem len32 : 32 ≤ P.I.hashLen := by
  rw [P.len]; rcases P.hDB with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  F := P.F
  n := Spec.P256.n
  tries := 8
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.X86.signP256

end VG.Proof.Ecdsa.Rfc6979.X86
