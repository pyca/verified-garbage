import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA on x86-64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`):
the curve (`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign`,
which each candidate calls), the instance of the contract it implements (the
curve's, the hash function's HMAC, its output length, 8 candidates), its
code (`Hash`), what PBKDF2's proofs know of it (`HashOK`, `CoreOK`,
`Callees`, so that HMAC's `init`, `update` and `finalize` are verified), and
the sizes the frame and `scratch` are laid out for: the output and block
sizes of SHA-256, SHA-384 or SHA-512, no shorter than the curve's scalars
(so that one `V` makes a candidate), and states and working space no larger
than SHA-512's. Each hash function's file
builds one for each implementation of its compression function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK CoreOK Callees core hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin
  core_hmacInit_depth core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)

/-- A curve and a hash function, for RFC 6979 on x86-64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.X86_64.Hash
  ok : HashOK H
  C : CoreOK (core H)
  K : Callees H
  satI : ∃ s, (Spec.Hmac.initScratchContract ok.SH H.W X86_64.abi 16).pre s
  satF : ∃ s, (Spec.Hmac.finalizeScratchContract ok.SH H.W X86_64.abi 16).pre s
  /-- The instance is of the curve, with this hash function's HMAC, its
  output length and 8 candidates. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  tries : I.tries = 8
  /-- The sizes the frame and `scratch` hold: the output and block sizes of
  SHA-256, SHA-384 or SHA-512. -/
  hDB : (H.D = 32 ∧ H.P.B = 64) ∨ (H.D = 48 ∧ H.P.B = 128) ∨ (H.D = 64 ∧ H.P.B = 128)
  hS : H.S ≤ 192
  hW : 8 * H.W ≤ 1872
  hWb : ok.stream.Wb ≤ 1872
  /-- The hash is no shorter than the scalars. -/
  hQ : 8 * R.E.n ≤ H.D
  /-- The streaming `update`'s own code writes `rsp` only by its calls' pushes and pops. -/
  updSp : (core H).updC.allInstrs (fun i => !isa.writesSp i) = true

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

theorem hI : Verified X86_64.target P.H.hmacInit (initG P.ok.SH P.H.W) := hmacInit_ok P.ok P.C P.K P.satI

theorem hIsp : NoSp P.H.hmacInit := nosp_of (core_hmacInit P.K.cNs P.K.iNs P.C.hinitNs)

theorem hId : P.H.hmacInit.depth ≤ 2 := core_hmacInit_depth P.K.cD P.K.iD P.C.hinitD

theorem hF : Verified X86_64.target P.H.hmacFin (finG P.ok.SH P.H.W) := hmacFin_ok P.ok P.C P.K P.satF

theorem hFsp : NoSp P.H.hmacFin := nosp_of (core_hmacFin P.K.cNs P.C.hfinNs)

theorem hFd : P.H.hmacFin.depth ≤ 2 := core_hmacFin_depth P.K.cD P.C.hfinD

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ 8 * P.H.W ≤ 1872 ∧ P.ok.stream.Wb ≤ 1872 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 32 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 8 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 4 ≤ P.w ∧ P.w ≤ 6 ∧ 8 * P.w ≤ P.H.D := by
  have hDL := P.ok.hDL
  refine ⟨P.hS, P.hS, P.hW, P.hWb, P.hS, rfl, ?_, ?_, ?_, by omega, ?_, P.R.n4, P.R.n6, P.hQ⟩ <;>
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> omega

/-- The digest is at least 32 bytes. -/
theorem len32 : 32 ≤ P.I.hashLen := by
  rw [P.len]; rcases P.hDB with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The digest is at least the scalars' `8 w` bytes. -/
theorem lenQ : 8 * P.w ≤ P.I.hashLen := by rw [P.len]; exact P.hQ

/-- The curve's scalars are `8 w` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = 8 * P.w := by rw [P.ecdsa, P.R.curve, P.R.len]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  H := P.H
  w := P.R.E.n
  n := P.R.E.C.n
  tries := 8
  coreN := P.R.coreN
  coreC := P.R.coreC

end VG.Proof.Ecdsa.Rfc6979.X86_64
