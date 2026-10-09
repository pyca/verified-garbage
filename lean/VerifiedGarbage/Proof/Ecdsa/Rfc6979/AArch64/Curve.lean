import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract
import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# Deterministic ECDSA on AArch64: the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.AArch64.Cfg`),
the instance of ECDSA it is, its sizes: `n` 4 or 6, scalars of `8 n`
bytes (or P-224's 28 in 4 words), the order `n` of its base point of
exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that
`bits2octets` is one conditional subtraction), or, if `wide` (P-521), `n` 9,
scalars of 66 bytes and the order of 521 bits; and what is proven of the
code: that it meets the contract the proof of each curve is written against
(`coreK`: P-256's `signAArch64`, P-384's and P-521's at the curve's sizes), in
constant time, that it pushes no frame and writes no callee-saved SIMD
register, and, unless `wide`, the taint check of the block computing
`bits2octets`, which holds `n`'s words as immediates. Each curve's file builds one, so that the heavy algebra of its
proof stays out of the modules generic over the curve and the hash function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.AArch64.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, with the
comb's tables at the static `E.tsym`, as each curve's proof states it
(`Proof.Ecdsa.AArch64.signAArch64` for P-256). -/
def coreK (E : Impl.Ecdsa.AArch64.Cfg) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 2 * E.C.len⟩
    let d : Region := ⟨s.gpr .x1, E.C.len⟩
    let digest : Region := ⟨s.gpr .x2, E.C.len⟩
    let k : Region := ⟨s.gpr .x3, E.C.len⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k] ++ tableRegions E (tableAddr E s.syms) ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 2 * E.C.len ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblOk E s [out, scratch]
  post s s' :=
    match coreSigOf E s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) (2 * E.C.len) = encode E.C rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) (2 * E.C.len) =
        List.replicate (2 * E.C.len) 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧ tableAddr E s₁.syms = tableAddr E s₂.syms

/-- The code's blocks that depend on neither the hash function nor the
compression function, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.AArch64.Cfg) : Impl.Ecdsa.Rfc6979.AArch64.Cfg where
  H := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params, 32, 104, "", .block [], "", .block [], "",
    .block [], "", .block [], "", "", ""⟩
  w := E.n
  len := E.C.len
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on AArch64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.AArch64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output, so
  that two `V`s make a candidate (`Impl.Ecdsa.Rfc6979.AArch64.Cfg.wide`). -/
  wide : Bool
  /-- Scalars of 4 or 6 words, `8 n` bytes (or 24 or 28 in 4 words), and `n` of
  exactly `8 len` bits, with `2^(8 len) < 2 n`; or, if `wide`, of 9 words and
  66 bytes, and `n` of 521 bits. -/
  sizes : if wide then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ (E.C.len = 28 ∨ E.C.len = 24)) ∧ nBits E.C = 8 * E.C.len ∧
      2 ^ (8 * E.C.len) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : E.sh = sh
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It pushes no frame, and none of its instructions writes a callee-saved SIMD register. -/
  coreNoFrames : coreC.noFrames = true
  coreKeepsV : coreC.allInstrs keepsV = true
  /-- Unless `wide`, `bits2octets` and the initial `K` and `V` address
  memory only from `sp` and `x1` (the taint analysis, of the block for `n`'s
  words), and write no callee-saved SIMD register. -/
  reduceT : wide = false → ∃ hc, (taint.check (Taint.ofRegs [.x1])
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.AArch64.Cfg.initKV)) hc).isSome = true
  reduceKeepsV : wide = false →
    (Code.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.AArch64.Cfg.initKV) : Prog isa).allInstrs keepsV = true

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.wide = false) :
    (R.E.n = 4 ∨ R.E.n = 6) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ (R.E.C.len = 28 ∨ R.E.C.len = 24)) ∧
      nBits R.E.C = 8 * R.E.C.len ∧ 2 ^ (8 * R.E.C.len) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.wide = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n4 : 4 ≤ R.E.n := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h <;> omega
  · rw [(R.sizesW h).1]; omega

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h <;> omega
  · rw [(R.sizesW h).1]

/-- The scalars' bytes fill their words, the last possibly zero. -/
theorem len_words : 8 ≤ R.E.C.len ∧ 8 * R.E.n ≤ R.E.C.len + 8 ∧ R.E.C.len ≤ 8 * R.E.n := by
  cases h : R.wide
  · have := R.sizesA h; have := R.n4; omega
  · have := R.sizesW h; omega

/-- `nBits` is within the scalars' last byte, and `sh` the bits beyond it. -/
theorem nBits_len : 8 * R.E.C.len < nBits R.E.C + 8 ∧ nBits R.E.C ≤ 8 * R.E.C.len ∧
    R.sh = 8 * R.E.C.len - nBits R.E.C := by
  rw [← R.sh_eq]
  cases h : R.wide
  · have := R.sizesA h; exact ⟨by omega, by omega, rfl⟩
  · have := R.sizesW h; exact ⟨by omega, by omega, rfl⟩

theorem n_ne : R.E.C.n ≠ 0 := fun h => by
  have h₁ := R.nBits_len; have h₂ := R.len_words
  have : nBits R.E.C = 1 := by show R.E.C.n.log2 + 1 = 1; rw [h]; rfl
  omega

end RfcCurve

end VG.Proof.Ecdsa.Rfc6979.AArch64
