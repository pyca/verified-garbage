module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.HashFns.Streaming
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Pbkdf2.Memory
public import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy

/-!
# Deterministic ECDSA on x86-64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`):
the curve (`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign`,
which each candidate calls), the instance of the contract it implements (the
curve's, the hash function's HMAC, its output length, the candidates), and
the hash function's number `k` and its streaming functions `T`
(`Spec.HashFns.streaming k`), which the code calls through the table. The
sizes the frame and `scratch` are laid out for are those of SHA-1 and the
SHA-2 functions (`sizes`): outputs of 20 to 64 bytes, a multiple of 4, blocks
of 64 or 128 bytes, and states and working space no larger than SHA-512's.
Whether the hash is shorter than the scalars (`wide`) decides how
`bits2octets`, the candidate and the digest for `core` are made.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.HashFns (StreamingOK streaming_ok)

/-- A curve and a hash function, for RFC 6979 on x86-64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's number and its streaming functions. -/
  k : Nat
  T : Spec.HashFns.Streaming
  hT : Spec.HashFns.streaming k = some T
  hk : k ∈ hashIds
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 32-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = T.S.H
  len : I.hashLen = T.S.digestBytes
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.T.S.H K text

/-- The bytes of the hash function's output and of its block. -/
abbrev D : Nat := P.T.S.digestBytes
abbrev B : Nat := P.T.S.H.blockSize

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- Whether the hash is shorter than the scalars. -/
abbrev wide : Bool := decide (P.D < P.Q)

/-- The words above the frame's pointers: the streaming functions'
addresses, and 18 more. -/
abbrev e (_P : RfcHash) : Nat := 21

/-- Where `h` is, from the stack's lowest byte: in the frame below its
pointers, or above the streaming functions' addresses for scalars of 8
words. -/
abbrev hB : Nat := if P.R.hHigh then 264 else 152

/-- The sizes of the hash function the number `k` names, as the code has them. -/
theorem sizesOf_of {k : Nat} {T : Spec.HashFns.Streaming} (hT : Spec.HashFns.streaming k = some T)
    (hk : k ∈ hashIds) : sizesOf k = (T.S.digestBytes, T.S.H.blockSize) := by
  simp only [hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h | h | h | h | h <;> subst h <;>
    simp only [Spec.HashFns.streaming, Option.some.injEq] at hT <;> subst hT <;> rfl

/-- The hash function's sizes, as the code has them. -/
theorem sizesOf_eq : sizesOf P.k = (P.D, P.B) := sizesOf_of P.hT P.hk

/-- What the proofs of the streaming functions' calls need of them. -/
theorem ok : ∃ H, Spec.HashId.mgf1 P.k = some H ∧ StreamingOK P.T H := streaming_ok P.hT

/-- The sizes of SHA-1's and the SHA-2 functions' output, block, state and
working space. -/
theorem hDB_of {k : Nat} {T : Spec.HashFns.Streaming} (hT : Spec.HashFns.streaming k = some T)
    (hk : k ∈ hashIds) :
    T.S.stateBytes ≤ 192 ∧ T.outBytes ≤ 64 ∧ 8 * T.scratch ≤ 1376 ∧ T.S.digestBytes ≤ T.outBytes ∧
      ((T.S.digestBytes = 20 ∧ T.S.H.blockSize = 64) ∨ (T.S.digestBytes = 28 ∧ T.S.H.blockSize = 64) ∨
        (T.S.digestBytes = 32 ∧ T.S.H.blockSize = 64) ∨ (T.S.digestBytes = 48 ∧ T.S.H.blockSize = 128) ∨
        (T.S.digestBytes = 64 ∧ T.S.H.blockSize = 128) ∨ (T.S.digestBytes = 28 ∧ T.S.H.blockSize = 128) ∨
        (T.S.digestBytes = 32 ∧ T.S.H.blockSize = 128)) := by
  simp only [hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h | h | h | h | h <;> subst h <;>
    simp only [Spec.HashFns.streaming, Option.some.injEq] at hT <;> subst hT <;> decide

theorem hDB : P.T.S.stateBytes ≤ 192 ∧ P.T.outBytes ≤ 64 ∧ 8 * P.T.scratch ≤ 1376 ∧ P.D ≤ P.T.outBytes ∧
    ((P.D = 20 ∧ P.B = 64) ∨ (P.D = 28 ∧ P.B = 64) ∨ (P.D = 32 ∧ P.B = 64) ∨ (P.D = 48 ∧ P.B = 128) ∨
      (P.D = 64 ∧ P.B = 128) ∨ (P.D = 28 ∧ P.B = 128) ∨ (P.D = 32 ∧ P.B = 128)) := hDB_of P.hT P.hk

/-- The sizes, as the proofs use them. -/
theorem sizes : P.T.S.stateBytes ≤ 192 ∧ P.T.outBytes ≤ 64 ∧ 8 * P.T.scratch ≤ 1376 ∧ P.D ≤ P.T.outBytes ∧
    20 ≤ P.D ∧ P.D ≤ 64 ∧ P.D % 4 = 0 ∧ P.D < P.B ∧ P.B ≤ 128 ∧ P.B % 8 = 0 ∧
    4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 66 := by
  obtain ⟨h₁, h₂, h₃, h₄, h⟩ := P.hDB
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hn4 := P.R.n4
  have hQ66 : P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb
      rcases this.1 with h' | h' | h' <;> simp only [Q] <;> omega
    · have := P.R.sizesW hb; simp only [Q]; omega
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  have hD : 20 ≤ P.D ∧ P.D ≤ 64 ∧ P.D % 4 = 0 ∧ P.D < P.B ∧ P.B ≤ 128 ∧ P.B % 8 = 0 := by
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  simp only [w, Q] at hw hQ66 ⊢
  omega

/-- Unless the hash is shorter than the scalars, the curve's scalars are no
longer than any hash function's output. -/
theorem big_false (h : P.wide = false) : P.R.big = false := by
  have hQD : P.Q ≤ P.D := by simpa [wide] using h
  have hz := P.sizes
  cases hb : P.R.big
  · rfl
  · have := P.R.sizesW hb
    have := hz.2.2.2.2.2.1
    simp only [Q, D] at hQD this; omega

/-- Unless the hash is shorter than the scalars, the scalars are `8 w` bytes
(or 24 or 28 in 4 words), at most 8 words, and no longer than the digest,
whose order `n` has exactly `8 Q` bits, with `2^(8 Q) < 2 n`. -/
theorem sizesA (h : P.wide = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧
    P.w ≤ 8 ∧ P.Q ≤ P.D := by
  have hQD : P.Q ≤ P.D := by simpa [wide] using h
  obtain ⟨hn, hl, -, -⟩ := P.R.sizesA (P.big_false h)
  exact ⟨hl, by simp only [w]; omega, hQD⟩

/-- Unless the hash is shorter than the scalars, the scalars are 32, 48, 64,
28 or 24 bytes. -/
theorem sizesQ (h : P.wide = false) : P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 28 ∨ P.Q = 24 := by
  have := P.R.sizesA (P.big_false h)
  rcases this.1 with hn | hn | hn <;> simp only [Q] <;> omega

/-- `h` fits its place, unless the hash is shorter than the scalars: 48
bytes below the frame's pointers, or, for scalars of 8 words (64 bytes),
the 64 above the streaming functions' addresses. -/
theorem hFits (h : P.wide = false) : (P.w = 8 → P.Q = 64) ∧ (P.w ≠ 8 → P.Q ≤ 48) := by
  have := P.R.sizesA (P.big_false h)
  rcases this.1 with hn | hn | hn <;> simp only [Q, w] <;> omega

/-- `h` is above the streaming functions' addresses for scalars of 64
bytes, which are those of 8 words. -/
theorem hHigh_eq : P.R.hHigh = decide (P.Q = 64) := by
  rw [P.R.hHigh_eq]
  cases hb : P.R.big
  · have := P.R.sizesA hb
    rcases this.1 with hn | hn | hn <;> simp only [Q] <;> rcases this.2.1 with h | ⟨h, h'⟩ <;> simp <;> omega
  · have := P.R.sizesW hb
    simp only [Q]; simp; omega

/-- The digest is at least 20 bytes. -/
theorem len20 : 20 ≤ P.I.hashLen := by rw [P.len]; exact P.sizes.2.2.2.2.1

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`: the configuration
`Cfg.ofCurve` makes for the curve and the hash function's number
(`cfgOf_eq`). -/
def cfgOf (P : RfcHash) : Cfg where
  D := P.D
  B := P.B
  w := P.R.E.n
  len := P.R.E.C.len
  wide := P.wide
  blocks := (Spec.Ecdsa.nBits P.R.E.C + 8 * P.D - 1) / (8 * P.D)
  sh := P.R.sh
  hHigh := P.R.hHigh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

theorem cfgOf_eq (P : RfcHash) : cfgOf P = Cfg.ofCurve (P.R.cc P.I.tries) P.k := by
  simp only [cfgOf, Cfg.ofCurve, P.sizesOf_eq, RfcCurve.cc]
  rw [P.hHigh_eq]
  rfl

theorem cfgOf_D (P : RfcHash) : (cfgOf P).D = P.D := rfl
theorem cfgOf_B (P : RfcHash) : (cfgOf P).B = P.B := rfl
theorem cfgOf_wide (P : RfcHash) : (cfgOf P).wide = P.wide := rfl
theorem cfgOf_len (P : RfcHash) : (cfgOf P).len = P.Q := rfl
theorem cfgOf_w (P : RfcHash) : (cfgOf P).w = P.w := rfl
theorem cfgOf_sh (P : RfcHash) : (cfgOf P).sh = P.R.sh := rfl
theorem cfgOf_n (P : RfcHash) : (cfgOf P).n = P.R.E.C.n := rfl
theorem cfgOf_tries (P : RfcHash) : (cfgOf P).tries = P.I.tries := rfl
theorem cfgOf_coreC (P : RfcHash) : (cfgOf P).coreC = P.R.coreC := rfl
theorem cfgOf_coreN (P : RfcHash) : (cfgOf P).coreN = P.R.coreN := rfl
theorem cfgOf_hHigh (P : RfcHash) : (cfgOf P).hHigh = P.R.hHigh := rfl
theorem cfgOf_blocks (P : RfcHash) :
    (cfgOf P).blocks = (Spec.Ecdsa.nBits P.R.E.C + 8 * P.D - 1) / (8 * P.D) := rfl

/-- `h`'s place in the frame, from `rsp`: `hB` less the 24 bytes below the frame. -/
theorem fHo_eq (P : RfcHash) : (cfgOf P).fHo = P.hB - 24 := by
  cases h : P.R.hHigh <;> simp [Cfg.fHo, cfgOf, RfcHash.hB, h, fX, fH]

end VG.Proof.Ecdsa.Rfc6979.X86_64
