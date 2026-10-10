import VerifiedGarbage.Impl.Ecdsa.X86
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Contract
import VerifiedGarbage.Proof.Ecdsa.X86.Layout

/-!
# Deterministic ECDSA on x86 (32-bit): the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` 64-bit words
(`Impl.Ecdsa.X86.Cfg`, `n` 3, 4 or 6), the instance of ECDSA it is, that the
order `n` of its base point has exactly `64 n` bits and `2^(64 n) < 2 n` (so
that `bits2octets` is one conditional subtraction), and what is proven of the
code: that it meets the contract the proof of each curve is written against
(`coreK`, including any comb tables), in constant time, that it never
writes `esp` and uses at most 20 stack bytes (its calls of the field
arithmetic's functions), and the taint check of
the block computing `bits2octets`, which holds `n`'s words as immediates.
Each curve's file builds one, so that the heavy algebra of its proof stays
out of the modules generic over the curve and the hash function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.X86.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, as each
curve's proof states it, including immutable comb tables and the `E.stk`
bytes of stack below the return address that its calls (and the comb's
four-byte position-independent address setup) use. -/
def coreK (E : Impl.Ecdsa.X86.Cfg) : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 2 * E.C.len⟩
    let d : Region := ⟨(arg s 1).setWidth 64, E.C.len⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, E.C.len⟩
    let k : Region := ⟨(arg s 3).setWidth 64, E.C.len⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 E.stk, E.stk⟩
    s.rd = [d, digest, k, args] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) E.combConsts ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 2 * E.C.len ≤ 2 ^ 32 ∧ (arg s 1).toNat + E.C.len ≤ 2 ^ 32 ∧
      (arg s 2).toNat + E.C.len ≤ 2 ^ 32 ∧ (arg s 3).toNat + E.C.len ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      E.stk ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      d.Disjoint (below (s.gpr .esp) 4) ∧
      digest.Disjoint (below (s.gpr .esp) 4) ∧ k.Disjoint (below (s.gpr .esp) 4) ∧
      TblsOk E.combConsts s (below (s.gpr .esp) E.stk :: s.wr)
  post s s' :=
    match coreSigOf E s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (2 * E.C.len) = encode E.C rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (2 * E.C.len) = List.replicate (2 * E.C.len) 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧ ∀ c ∈ E.combConsts, s₁.syms c.1 = s₂.syms c.1

/-- The code's blocks that depend on neither the hash function nor the
functions it calls, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.X86.Cfg) : Impl.Ecdsa.Rfc6979.X86.Cfg where
  F := ⟨⟨0, 0, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩, 0, "", .block [], "", .block [], "",
    .block []⟩
  w := 2 * E.n
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on x86. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.X86.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output, so
  that two `V`s make a candidate (`Impl.Ecdsa.Rfc6979.X86.Cfg.wide`). -/
  wide : Bool
  /-- Scalars of 3, 4 or 6 64-bit words, `8 n` bytes, and `n` of exactly `64 n`
  bits, with `2^(64 n) < 2 n`; or, if `wide`, of 9 words and 66 bytes, and
  `n` of 521 bits. -/
  sizes : if wide then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 3 ∨ E.n = 4 ∨ E.n = 6) ∧ E.C.len = 8 * E.n ∧ nBits E.C = 64 * E.n ∧ 2 ^ (64 * E.n) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : E.sh = sh
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It never writes `esp`, and uses at most 20 stack bytes (its calls'). -/
  coreNs : NoSp coreC
  coreStack : stackUse coreC ≤ E.stk
  /-- Unless `wide`, `bits2octets` and the initial `K` and `V` address
  memory only from `esp` and `esi` (the taint analysis, of the block for
  `n`'s words). -/
  reduceT : wide = false → ∃ hc, (VG.Taint.check taint (τr [.esp, .esi])
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.X86.Cfg.initKV)) hc).isSome = true

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.wide = false) :
    (R.E.n = 3 ∨ R.E.n = 4 ∨ R.E.n = 6) ∧ R.E.C.len = 8 * R.E.n ∧ nBits R.E.C = 64 * R.E.n ∧
      2 ^ (64 * R.E.n) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.wide = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n3 : 3 ≤ R.E.n := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h | h <;> omega
  · rw [(R.sizesW h).1]; omega

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h | h <;> omega
  · rw [(R.sizesW h).1]

/-- The scalars' bytes fill their words, the last at least in part. -/
theorem len_words : 8 ≤ R.E.C.len ∧ 8 * R.E.n < R.E.C.len + 8 ∧ R.E.C.len ≤ 8 * R.E.n := by
  cases h : R.wide
  · have := R.sizesA h; have := R.n3; omega
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

end VG.Proof.Ecdsa.Rfc6979.X86
