module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, the bound on candidates), its
streaming functions, verified (`HashOK`), the functions an indirect call of
a table's functions may reach (`f`, of which the table's are, `TabOK`, a fact
of the state), and the sizes the frame and `scratch` are laid out for: the
output and block sizes of one of the hash functions of `shapes` (MD5's,
SHA-1's or the SHA-2 family's), and states and working space no larger than
SHA-512's. Whether the hash is shorter than the scalars (`wide`) decides the
code's path, and the number of `V`s in a candidate (`m`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Stream.Arm (HashOK)
open VG.Impl.RsaOaep.Arm (Fns)

/-- A curve and a hash function, for RFC 6979 on 32-bit ARM. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's streaming functions. -/
  H : Impl.Pbkdf2.Stream.Arm.Hash
  ok : HashOK H
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  /-- The hash function's digests have `H.D` bytes. -/
  macLen : ∀ x, (ok.SH.H.hash x).length = H.D
  /-- It tries at least one candidate, as many as a 16-bit immediate holds. -/
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 16
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (H.D, H.B) ∈ shapes
  hS : H.S ≤ 192
  hWb : ok.Wb ≤ 1408

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

/-- The 64-bit words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- Their 32-bit words: seven for P-224, otherwise two per 64-bit word. -/
abbrev k : Nat := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- Whether the hash is shorter than the scalars. -/
abbrev wide : Bool := decide (P.H.D < P.Q)

/-- The 32-bit words at the frame's top: `h`, the digest for `core` and the
candidate, if the hash is shorter, or `h`, for 64-byte scalars. -/
abbrev e : Nat := Impl.Ecdsa.Rfc6979.Arm.extra P.wide P.R.hHigh

/-- Where `h` is, from the stack's lowest byte: in the frame below `out`, or
at its top. -/
abbrev hB : Nat := if P.wide || P.R.hHigh then 240 else 152

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.ok.Wb ≤ 1408 ∧ 16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧ P.H.D < P.H.B ∧
    P.H.B ≤ 128 ∧ P.H.B % 4 = 0 ∧ P.H.D ≤ P.H.F ∧ P.H.F ≤ 64 ∧ 0 < P.H.S ∧
    P.ok.SH.stateBytes = P.H.S ∧ P.ok.SH.digestBytes = P.H.D ∧ P.ok.SH.H.blockSize = P.H.B := by
  refine ⟨P.hS, P.hWb, ?_, ?_, ?_, ?_, ?_, ?_, P.ok.hDF, P.ok.hF, P.ok.hS0, P.ok.hS, P.ok.hD, P.ok.hB⟩ <;>
    have h := P.hDB <;> simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h <;>
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [h, h'] <;> omega

/-- The sizes of the scalars, as the proofs use them. -/
theorem wsizes : 3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k ∧ P.k ≤ 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 ∧ P.e ≤ 68 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQ66 : P.Q ≤ 66 := by
    cases hr : P.R.wide
    · have := P.R.sizesA hr; simp only [Q]; omega
    · have := P.R.sizesW hr; simp only [Q]; omega
  exact ⟨P.R.n3, P.R.n9, (by have := P.R.len_words; have := P.R.n3; simp only [k]; split <;> omega), (by simp only [k, w]; omega), hw.1, hQ66, hw.2.2, hw.2.1, by
    simp only [e, Impl.Ecdsa.Rfc6979.Arm.extra]; split <;> (try split) <;> omega⟩

/-- The curve is not P-521 unless the hash is shorter. -/
theorem curveA (h : P.wide = false) : P.R.wide = false := by
  have hQD : P.Q ≤ P.H.D := by simpa [wide] using h
  cases hr : P.R.wide
  · rfl
  · have := (P.R.sizesW hr).2.1
    have := P.sizes
    simp only [Q] at hQD; omega

/-- Unless the hash is shorter, the scalars fill at most sixteen 32-bit
words and are no longer than the digest. -/
theorem sizesA (h : P.wide = false) : P.Q = 4 * P.k ∧ P.k ≤ 16 ∧ P.Q ≤ P.H.D := by
  have hQD : P.Q ≤ P.H.D := by simpa [wide] using h
  have := P.R.sizesA (P.curveA h)
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k] at hQD ⊢ <;> split <;> omega

/-- The possible byte lengths of a single-candidate scalar. -/
theorem lengthsA (h : P.wide = false) : P.Q = 24 ∨ P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 28 := by
  have := P.R.sizesA (P.curveA h)
  simp only [Q]
  omega

/-- Unless the hash is shorter, `h` fits its place: 48 bytes below `out`,
or, for 64-byte scalars (in 8 64-bit words), the 64 at the frame's top. -/
theorem hFits (h : P.wide = false) : (P.w = 8 → P.Q = 64) ∧ (P.w ≠ 8 → P.Q ≤ 48) := by
  have := P.R.sizesA (P.curveA h)
  simp only [Q, w]
  omega

theorem mac_length (K t : List Byte) : (P.mac K t).length = P.H.D := by
  simp only [mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›
   obtain ⟨_, _, _, _, _, _, _, _, _⟩ := RfcHash.wsizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  D := P.H.D
  B := P.H.B
  f := P.f
  w := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)
  len := P.R.E.C.len
  sh := P.R.sh
  hHigh := P.R.hHigh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

theorem cfgOf_wide (P : RfcHash) : (cfgOf P).wide = P.wide := rfl

/-- Unless the hash is shorter, `h` is at the frame's top just for 64-byte
scalars. -/
theorem hHigh_q (P : RfcHash) (hw : P.wide = false) : P.R.hHigh = decide (P.Q = 64) := by
  have hF := P.hFits hw
  rw [P.R.hHigh_eq]
  by_cases h8 : P.R.E.n = 8
  · simp only [h8, decide_true, show P.Q = 64 from hF.1 h8]
  · have := hF.2 h8
    simp only [h8, decide_false, show P.Q ≠ 64 by omega]

/-- `h`'s place in the frame: `hB` less the 24 bytes below the frame. -/
theorem fHo_eq (P : RfcHash) : (cfgOf P).fHo = P.hB - 24 := by
  show (if (P.wide || P.R.hHigh) = true then fX else fH) = (if (P.wide || P.R.hHigh) = true then 240 else 152) - 24
  split <;> rfl

/-- The words at the frame's top. -/
theorem extra_eq (P : RfcHash) : extra (cfgOf P).wide (cfgOf P).hHigh = P.e := rfl

end VG.Proof.Ecdsa.Rfc6979.Arm
