module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Hmac.Contract
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
import VerifiedGarbage.Proof.Pbkdf2.Hmac

/-!
# Deterministic ECDSA on AArch64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, the bound on candidates), its
code and what the proofs of HMAC's functions know of it (`Hash`, `HashOK`,
`CoreOK`: HMAC's `init` and `finalize` and the streaming `update`, which the
table holds), the functions an indirect call of a table's functions may
reach (`f`, of which the table's are, `TabOK`, a fact of the state), and the
sizes the frame and `scratch` hold: the output and block sizes of one of the
hash functions of `shapes` (MD5's, SHA-1's or the SHA-2 family's), and
states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the frame holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK CoreOK core hmacInit_ok hmacFin_ok hmacInit_fdepth hmacFin_fdepth)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- The digest lengths and block sizes of the hash functions with HMAC on
AArch64: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on AArch64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.AArch64.Hash
  ok : HashOK H
  C : CoreOK (core H)
  satI : ∃ s, (Proof.Hmac.initScratchContract ok.SH H.W AArch64.abi 16).pre s
  satF : ∃ s, (Proof.Hmac.finalizeScratchContract ok.SH H.W AArch64.abi 16).pre s
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 16-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 16
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (H.D, H.P.B) ∈ shapes
  hS : H.S ≤ 192
  hW : 8 * H.W ≤ 1872
  hWb : ok.stream.Wb ≤ 1872

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

theorem hI : Verified AArch64.target P.H.hmacInit (initG P.ok.SH P.H.W) := hmacInit_ok P.ok P.C P.satI

theorem hId : P.H.hmacInit.aarch64Depth ≤ 1 := hmacInit_fdepth P.ok.stream.initDepth P.ok.comp.noFrames

theorem hF : Verified AArch64.target P.H.hmacFin (finG P.ok.SH P.H.W) := hmacFin_ok P.ok P.C P.satF

theorem hFd : P.H.hmacFin.aarch64Depth ≤ 1 := hmacFin_fdepth P.ok.stream.finDepth P.ok.comp.noFrames

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

theorem shape (h : (P.H.D, P.H.P.B) ∈ shapes) :
    16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧ P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ 8 * P.H.W ≤ 1872 ∧ P.ok.stream.Wb ≤ 1872 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B ∧ 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧
    P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hs := P.shape P.hDB
  have hQ : P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb; simp only [Q]; omega
    · have := P.R.sizesW hb; simp only [Q]; omega
  refine ⟨P.hS, P.hS, P.hW, P.hWb, P.hS, rfl, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2,
    P.R.n4, hn9, hw.1, hQ, hw.2.2, hw.2.1⟩

/-- Unless `big`, the scalars are `8 w` bytes (or 24 or 28 in 4 words), at most 8 words. -/
theorem sizesA (h : P.R.big = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] <;> omega

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.Q = 66 ∧ P.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := P.sizes.2.2.2.2.2.2.2.1
  exact ⟨h₁.1, h₁.2.1, by simp only [Q]; omega⟩

/-- The digest is at least 16 bytes. -/
theorem len16 : 16 ≤ P.I.hashLen := by rw [P.len]; exact P.sizes.2.2.2.2.2.2.1

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

/-- HMAC's output is the hash function's. -/
theorem mac_length (K t : List Byte) : (P.mac K t).length = P.H.D := by
  have := P.ok.sizes.DN
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.ok.hash, List.length_take,
    Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, for the curve of `P` and the functions an indirect call may reach. -/
def cfgOf (P : RfcHash) : Cfg where
  f := P.f
  w := P.R.E.n
  len := P.R.E.C.len
  big := P.R.big
  sh := P.R.sh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

end VG.Proof.Ecdsa.Rfc6979.AArch64
