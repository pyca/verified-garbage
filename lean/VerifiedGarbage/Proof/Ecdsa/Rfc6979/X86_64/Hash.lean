module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Pbkdf2.Memory
public import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit
public import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Proof.Framework.X86_64.Dispatch
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash

/-!
# Deterministic ECDSA on x86-64: the hash function

What the proof needs of the curve and the hash function `hash` names, for
any one of them (`RfcHash`): the curve (`RfcCurve`, with what is proven of
`vg_ecdsa_<curve>_sign`, which each candidate calls), the tier `T` of hash
functions the code calls (an implementation of each, `Tier`), the curve's
instance of RFC 6979 (whose hash function the code does not use), and the
number `k` of the hash function, one of `hashIds`, whose implementation in
`T` is `v`. From the tier's facts (`Tier.mgf_ok`, `Tier.hmac_ok`) and what
`v` carries (`HashOK`, `CoreOK`, `Callees`), it has the output and block
sizes of SHA-1 or a SHA-2 function (`dims`), states and working space that
fit `scratch`'s layout (`sizes`), and the instance of the contract the proof
of `k` is written against (`I`: the curve's, with `k`'s HMAC and output
length).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK CoreOK Callees MdHash Tier core hmacInit_ok hmacFin_ok core_hmacInit
  core_hmacFin core_hmacInit_depth core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)

/-- The hash functions of the tier `T` the code dispatches among: each of
`hashIds`, with its number. -/
def hsOf (T : Tier) : List (Nat × Impl.Pbkdf2.Md.X86_64.Hash) :=
  Spec.Ecdsa.Rfc6979.hashIds.filterMap fun i => T.hashes[i]?.map fun v => (i, v.H)

theorem tier_length (T : Tier) : T.hashes.length = 8 := by
  simpa using congrArg List.length T.mgf_ok

theorem mem_hsOf {T : Tier} {i : Nat} {H : Impl.Pbkdf2.Md.X86_64.Hash} :
    (i, H) ∈ hsOf T ↔ i ∈ Spec.Ecdsa.Rfc6979.hashIds ∧ ∃ v, T.hashes[i]? = some v ∧ v.H = H := by
  simp only [hsOf, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, v, hv, rfl, rfl⟩; exact ⟨hj, v, hv, rfl⟩
  · rintro ⟨hj, v, hv, rfl⟩; exact ⟨i, hj, v, hv, rfl, rfl⟩

/-- The numbers of `hsOf`, in order: `hashIds`. -/
theorem keys_hsOf (T : Tier) : (hsOf T).map Prod.fst = Spec.Ecdsa.Rfc6979.hashIds := by
  have h := tier_length T
  unfold hsOf
  generalize T.hashes = l at h ⊢
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at h <;> try omega
  simp only [Spec.Ecdsa.Rfc6979.hashIds, List.filterMap_cons, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, List.filterMap_nil, List.map_cons, List.map_nil]

/-- A curve and the hash function `k` of a tier, for RFC 6979 on x86-64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The hash functions' implementations. -/
  T : Tier
  /-- The curve's instance of RFC 6979. -/
  I0 : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's number, and its implementation. -/
  k : Nat
  v : MdHash
  hv : T.hashes[k]? = some v
  hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds
  /-- The instance is of the curve, and tries at least one candidate, as
  many as a 32-bit immediate holds. -/
  ecdsa : I0.ecdsa = R.inst
  tries_pos : 0 < I0.tries
  tries_lt : I0.tries < 2 ^ 32

namespace RfcHash

variable (P : RfcHash)

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- The words above the frame's pointers. -/
abbrev e (_ : RfcHash) : Nat := 38

/-- The hash function's code, and what the proofs know of it. -/
abbrev H : Impl.Pbkdf2.Md.X86_64.Hash := P.v.H
abbrev ok : HashOK P.H := P.v.ok
abbrev C : CoreOK (core P.H) := P.v.C
abbrev K : Callees P.H := P.v.K

/-- The instance of the contract the proof of `k` is written against: the
curve's, with the hash function's HMAC and output length. -/
abbrev I : Spec.Ecdsa.Rfc6979.Instance := { P.I0 with hash := P.ok.SH.H, hashLen := P.H.D }

theorem hash : P.I.hash = P.ok.SH.H := rfl
theorem len : P.I.hashLen = P.H.D := rfl

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

/-- The hash function is `HashId.mgf1 k`'s, as RSA's padding takes it, and
`HashId.hmac k`'s, as HMAC does. -/
theorem mgf_eq : some P.v.mgf.G = Spec.HashId.mgf1 P.k := by
  have h := congrArg (·[P.k]?) P.T.mgf_ok
  simp only [List.getElem?_map, P.hv, Option.map_some] at h
  have hk : P.k < 8 := by have := P.hk; simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons,
    List.not_mem_nil, or_false] at this; omega
  rw [List.getElem?_range hk, Option.map_some] at h
  exact Option.some.inj h

theorem hmac_eq : some P.ok.SH.H = Spec.HashId.hmac P.k := by
  have h := congrArg (·[P.k]?) P.T.hmac_ok
  simp only [List.getElem?_map, P.hv, Option.map_some] at h
  have hk : P.k < 8 := by have := P.hk; simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons,
    List.not_mem_nil, or_false] at this; omega
  rw [List.getElem?_range hk, Option.map_some] at h
  rw [show P.ok.SH = P.v.I.S from P.v.hSH]
  exact Option.some.inj h

/-- The output and block sizes: SHA-1's, SHA-224's, SHA-256's, SHA-384's,
SHA-512's, SHA-512/224's or SHA-512/256's. -/
theorem dims : (P.H.D = 20 ∧ P.H.P.B = 64) ∨ (P.H.D = 28 ∧ P.H.P.B = 64) ∨ (P.H.D = 32 ∧ P.H.P.B = 64) ∨
    (P.H.D = 48 ∧ P.H.P.B = 128) ∨ (P.H.D = 64 ∧ P.H.P.B = 128) ∨ (P.H.D = 28 ∧ P.H.P.B = 128) ∨
    (P.H.D = 32 ∧ P.H.P.B = 128) := by
  have hm := P.mgf_eq
  have hh := P.hmac_eq
  have hD : P.H.D = P.v.mgf.G.len := P.v.mgf.len.symm
  have hB : P.H.P.B = P.ok.SH.H.blockSize := P.ok.hB.symm
  have hk := P.hk
  generalize P.v.mgf.G = G at hm hD
  generalize P.ok.SH.H = F at hh hB
  generalize P.k = k at hk hm hh
  simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Spec.HashId.mgf1, Spec.HashId.hmac, Spec.Mgf1.hashes, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at hm hh <;> subst hm hh <;> rw [hD, hB] <;> decide

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 256 ∧ P.H.P.N + P.H.P.B ≤ 256 ∧ 8 * P.H.W ≤ 2048 ∧ P.ok.stream.Wb ≤ 2048 ∧
    P.H.stream.S ≤ 256 ∧ P.H.stream.D = P.H.D ∧ 20 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧
    P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 ∧ P.e = 38 := by
  have hNL := P.ok.hNL
  have hW := P.ok.hW
  have hso := P.ok.hso
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have h9 := P.R.n9
  have h4 := P.R.n4
  have hWb : P.ok.stream.Wb = P.H.P.so + 48 := rfl
  have hSt : P.H.stream.S = P.H.P.N + P.H.P.B := rfl
  have hQ : P.Q ≤ 66 := by
    cases h : P.R.wide
    · have := P.R.sizesA h; show P.R.E.C.len ≤ 66; omega
    · have := P.R.sizesW h; show P.R.E.C.len ≤ 66; omega
  refine ⟨?_, ?_, by omega, by omega, ?_, rfl, ?_, ?_, ?_, ?_, ?_, h4, h9, hw.1, by omega, hw.2.2, hw.2.1, rfl⟩ <;>
    rcases P.dims with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [h, h', Impl.Pbkdf2.Md.X86_64.Hash.S] at * <;> omega

/-- Unless `wide`, the scalars are `8 w` bytes (or 24 or 28 in 4 words), at
most 8 words. -/
theorem sizesA (h : P.R.wide = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] <;> omega

/-- If `wide`, P-521's sizes. -/
theorem sizesW (h : P.R.wide = true) : P.w = 9 ∧ P.Q = 66 := by
  have := P.R.sizesW h
  exact ⟨this.1, this.2.1⟩

/-- HMAC's `init` and `finalize`, verified against the contracts the proof
calls them with, from the ones the tier proves them against. -/
theorem hI : Verified X86_64.target P.H.hmacInit (initG P.ok.SH P.H.W) := by
  refine hmacInit_ok P.ok P.C P.K ?_
  have := P.v.hmacInit.2.2
  simp only [Spec.Hmac.Instance.initScratchContract] at this
  rw [P.v.hSH, P.v.hW]; exact this

theorem hIsp : NoSp P.H.hmacInit := nosp_of (core_hmacInit P.K.cNs P.K.iNs P.C.hinitNs)

theorem hId : P.H.hmacInit.depth ≤ 2 := core_hmacInit_depth P.K.cD P.K.iD P.C.hinitD

theorem hF : Verified X86_64.target P.H.hmacFin (finG P.ok.SH P.H.W) := by
  refine hmacFin_ok P.ok P.C P.K ?_
  have := P.v.hmacFin.2.2
  simp only [Spec.Hmac.Instance.finalizeScratchContract] at this
  rw [P.v.hSH, P.v.hW]; exact this

theorem hFsp : NoSp P.H.hmacFin := nosp_of (core_hmacFin P.K.cNs P.C.hfinNs)

theorem hFd : P.H.hmacFin.depth ≤ 2 := core_hmacFin_depth P.K.cD P.C.hfinD

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by
  show P.I0.ecdsa.curve.len = _; rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, for the curve and the tier of `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  hs := hsOf P.T
  w := P.R.E.n
  len := P.R.E.C.len
  wide := P.R.wide
  sh := P.R.sh
  n := P.R.E.C.n
  tries := P.I0.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

/-- The cases of a dispatch of `cfgOf P` on the hash function. -/
theorem keys_cases (P : RfcHash) {α : Type} (f : Impl.Pbkdf2.Md.X86_64.Hash → α) :
    ((cfgOf P).hs.map fun p => (p.1, f p.2)).map Prod.fst = Spec.Ecdsa.Rfc6979.hashIds := by
  rw [List.map_map]; exact keys_hsOf P.T

/-- The case of `k` is the one of `P`'s hash function. -/
theorem case_eq (P : RfcHash) {α : Type} (f : Impl.Pbkdf2.Md.X86_64.Hash → α) {a : α}
    (h : (P.k, a) ∈ (cfgOf P).hs.map fun p => (p.1, f p.2)) : a = f P.H := by
  obtain ⟨⟨i, H⟩, hm, he⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨-, v, hv, rfl⟩ := mem_hsOf.mp hm
  rw [P.hv] at hv
  cases hv; rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64
