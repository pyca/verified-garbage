module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Hmac
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Deterministic ECDSA on x86-64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`):
the curve (`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`,
which each candidate calls), the instance of the contract it implements (the
curve's, the hash function's HMAC, its output length, the bound on
candidates), its code and what the streaming proofs know of it (`Hash`,
`HashOK`: the streaming functions the table names, `HashOK.stream`), the
functions an indirect call of a table's functions may reach (`f`, of
which the table's are, `TabOK`, a fact of the state), and the sizes the
frame and `scratch` are laid out for: the output and block sizes of one of
the hash functions of `shapes` (MD5's, SHA-1's or the SHA-2 family's), and
states and working space no larger than SHA-512's. Whether the hash is
shorter than the scalars (`wide`) decides the code's path, and the number
of `V`s in a candidate (`m`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.RsaOaep.X86_64.Table (FnsGood)

/-- A curve and a hash function, for RFC 6979 on x86-64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.X86_64.Hash
  ok : HashOK H
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  fInit : FnsGood f.init
  fUpd : FnsGood f.upd
  fFin : FnsGood f.fin
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 32-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32
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

/-- The words above the frame's pointers: `h`, the digest for `core` and
the candidate if the hash is shorter than the scalars, or `h`, for 64-byte
scalars. -/
abbrev e : Nat := if P.wide then 34 else if P.R.hHigh then 8 else 0

/-- Where `h` is, from the stack's lowest byte: in the frame below its
pointers, or above them. -/
abbrev hB : Nat := if P.wide || P.R.hHigh then 240 else 152

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ P.ok.stream.Wb ≤ 1408 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ P.H.P.B % 8 = 0 ∧ 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧
    P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 ∧ P.e ≤ 34 ∧ P.H.stream.F ≤ 64 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hF : P.H.P.N ≤ 64 := P.ok.N_le
  have hQ66 : P.Q ≤ 66 := by
    cases hr : P.R.wide
    · have := P.R.sizesA hr; simp only [Q]; omega
    · have := P.R.sizesW hr; simp only [Q]; omega
  refine ⟨P.hS, P.hS, P.hWb, P.hS, rfl, ?_, ?_, ?_, ?_, ?_, ?_, P.R.n4, hn9, hw.1, by omega, hw.2.2, hw.2.1,
    by simp only [e]; split <;> (try split) <;> omega, hF⟩ <;>
    have h := P.hDB <;> simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h <;>
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [h, h'] <;> omega

/-- Unless the hash is shorter, the scalars are `8 w` bytes (or 24 or 28 in
4 words), at most 8 words, and no longer than the digest. -/
theorem sizesA (h : P.wide = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 ∧ P.Q ≤ P.H.D := by
  have hQD : P.Q ≤ P.H.D := by simpa [wide] using h
  have hnw : P.R.wide = false := by
    cases hr : P.R.wide
    · rfl
    · have := (P.R.sizesW hr).2.1
      have := P.sizes
      simp only [Q] at hQD; omega
  have := P.R.sizesA hnw
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] at hQD ⊢ <;> omega

/-- The curve is not P-521 unless the hash is shorter. -/
theorem curveA (h : P.wide = false) : P.R.wide = false := by
  have hQD : P.Q ≤ P.H.D := by simpa [wide] using h
  cases hr : P.R.wide
  · rfl
  · have := (P.R.sizesW hr).2.1
    have := P.sizes
    simp only [Q] at hQD; omega

/-- Unless the hash is shorter, the scalars are 32, 48, 64, 28 or 24 bytes. -/
theorem sizesQ (h : P.wide = false) : P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 28 ∨ P.Q = 24 := by
  have := P.R.sizesA (P.curveA h)
  rcases this.1 with hn | hn | hn <;> simp only [Q] <;> omega

/-- Unless the hash is shorter, `h` fits its place: 48 bytes below the
frame's pointers, or, for 64-byte scalars (in 8 words), the 64 above them. -/
theorem hFits (h : P.wide = false) : (P.w = 8 → P.Q = 64) ∧ (P.w ≠ 8 → P.Q ≤ 48) := by
  have := P.R.sizesA (P.curveA h)
  rcases this.1 with hn | hn | hn <;> simp only [Q, w] <;> omega

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
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

/-- Unless the hash is shorter, `h` is above the frame's pointers just for
64-byte scalars. -/
theorem hHigh_q (P : RfcHash) (hw : P.wide = false) : P.R.hHigh = decide (P.Q = 64) := by
  have hF := P.hFits hw
  rw [P.R.hHigh_eq]
  by_cases h8 : P.R.E.n = 8
  · simp only [h8, decide_true, show P.Q = 64 from hF.1 h8]
  · have := hF.2 h8
    simp only [h8, decide_false, show P.Q ≠ 64 by omega]

/-- `h`'s place in the frame, from `rsp`: `hB` less the 24 bytes below the frame. -/
theorem fHo_eq (P : RfcHash) : (cfgOf P).fHo = P.hB - 24 := by
  show (if (P.wide || P.R.hHigh) = true then fX else fH) = (if (P.wide || P.R.hHigh) = true then 240 else 152) - 24
  split <;> rfl

/-- The words above the frame's pointers. -/
theorem extra_eq (P : RfcHash) : (cfgOf P).extra = P.e := by
  simp only [Cfg.extra, cfgOf_wide, RfcHash.e]; rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64
