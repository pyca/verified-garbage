module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Layout
public import VerifiedGarbage.Spec.Hmac

/-!
# Deterministic ECDSA on AArch64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the curve (`R`, with
what is proven of its `vg_ecdsa_<curve>_sign_k`, which each candidate
calls), the instance of the contract it implements (the curve's, the hash
function's HMAC, its output length, the bound on candidates), its code and
what the streaming proofs know of it (`Hash`, `HashOK`: its streaming
`init`, `update` and `finalize`, which the table holds, are verified), the
functions an indirect call of a table's functions may reach (`f`, none of
whose instructions writes a callee-saved SIMD register), and the sizes the
frame and `scratch` are laid out for: the output and block sizes of one of
`shapes`, and states and working space no larger than SHA-512's. `Table.lean`
builds one for each variant whose table the function takes.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- None of the instructions of the functions `ts` writes a callee-saved
SIMD register. -/
def FnsKeep (ts : List (String × Prog isa)) : Prop := ∀ q ∈ ts, q.2.allInstrs keepsV = true

/-- A curve and a hash function, for RFC 6979 on AArch64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.AArch64.Hash
  ok : HashOK H
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  fInit : FnsKeep f.init
  fUpd : FnsKeep f.upd
  fFin : FnsKeep f.fin
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
  hWb : ok.stream.Wb ≤ 1408

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- Whether the hash is shorter than the scalars. -/
abbrev wide : Bool := decide (P.H.D < P.Q)

/-- The bytes at the frame's top: `h`, the digest for `core` and the
candidate if the hash is shorter than the scalars, or `h`, for 64-byte
scalars. -/
abbrev e : Nat := if P.wide then 272 else if P.R.hHigh then 64 else 0

theorem e_eq : P.e = 0 ∨ P.e = 64 ∨ P.e = 272 := by
  simp only [e]; split
  · exact .inr (.inr rfl)
  · split
    · exact .inr (.inl rfl)
    · exact .inl rfl

/-- Where `h` is, from the stack's lowest byte: in the frame below its
pointers, or at its top. -/
abbrev hB : Nat := if P.wide || P.R.hHigh then 240 else 144

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ P.ok.stream.Wb ≤ 1408 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ P.H.P.B % 8 = 0 ∧ 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧
    P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 ∧ P.e ≤ 272 ∧ P.H.stream.F ≤ 64 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hF : P.H.stream.F ≤ 64 := P.ok.stream.hF
  have hQ66 : P.Q ≤ 66 := by
    cases hr : P.R.wide
    · have := P.R.sizesA hr; simp only [Q]; omega
    · have := P.R.sizesW hr; simp only [Q]; omega
  refine ⟨P.hS, P.hS, P.hWb, P.hS, rfl, ?_, ?_, ?_, ?_, ?_, ?_, P.R.n4, hn9, hw.1, by omega, hw.2.2, hw.2.1,
    by rcases P.e_eq with h | h | h <;> omega, hF⟩ <;>
    have h := P.hDB <;> simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h <;>
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [h, h'] <;> omega

/-- The curve is not P-521 unless the hash is shorter. -/
theorem curveA (h : P.wide = false) : P.R.wide = false := by
  have hQD : P.Q ≤ P.H.D := by simpa [wide] using h
  cases hr : P.R.wide
  · rfl
  · have := (P.R.sizesW hr).2.1
    have := P.sizes
    simp only [Q] at hQD; omega

/-- Unless the hash is shorter, the scalars are `8 w` bytes (or 24 or 28 in
4 words), at most 8 words, and no longer than the digest. -/
theorem sizesA (h : P.wide = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 ∧ P.Q ≤ P.H.D := by
  have hQD : P.Q ≤ P.H.D := by simpa [wide] using h
  have := P.R.sizesA (P.curveA h)
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] at hQD ⊢ <;> omega

/-- Unless the hash is shorter, the scalars are 32, 48, 64, 28 or 24 bytes. -/
theorem sizesQ (h : P.wide = false) : P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 28 ∨ P.Q = 24 := by
  have := P.R.sizesA (P.curveA h)
  rcases this.1 with hn | hn | hn <;> simp only [Q] <;> omega

/-- Unless the hash is shorter, `h` fits its place: 48 bytes below the
frame's pointers, or, for 64-byte scalars (in 8 words), the 64 at its top. -/
theorem hFits (h : P.wide = false) : (P.w = 8 → P.Q = 64) ∧ (P.w ≠ 8 → P.Q ≤ 48) := by
  have := P.R.sizesA (P.curveA h)
  rcases this.1 with hn | hn | hn <;> simp only [Q, w] <;> omega

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

/-- The digest is at least 16 bytes. -/
theorem len16 : 16 ≤ P.I.hashLen := by rw [P.len]; have := P.sizes; omega

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
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  D := P.H.D
  B := P.H.P.B
  f := P.f
  w := P.R.E.n
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

/-- `h`'s place in the frame, from `sp`: `hB` less the 16 bytes below the frame. -/
theorem fHo_eq (P : RfcHash) : (cfgOf P).fHo = P.hB - 16 := by
  show (if (P.wide || P.R.hHigh) = true then fX else fH) = (if (P.wide || P.R.hHigh) = true then 240 else 144) - 16
  split <;> rfl

/-- The bytes at the frame's top. -/
theorem extra_eq (P : RfcHash) : (cfgOf P).extra = P.e := by
  simp only [Cfg.extra, cfgOf_wide, RfcHash.e]; rfl

/-- The frame's size. -/
theorem frameBytes_eq (P : RfcHash) : (cfgOf P).frameBytes = 224 + P.e := by
  rw [Cfg.frameBytes, extra_eq]

end VG.Proof.Ecdsa.Rfc6979.AArch64
