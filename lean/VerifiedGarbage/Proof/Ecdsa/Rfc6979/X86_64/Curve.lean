import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
import VerifiedGarbage.Impl.Sha256.X86_64.Stream
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Contract

/-!
# Deterministic ECDSA on x86-64: the curve

What the proof needs of the curve (`RfcCurve`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.X86_64.Cfg`),
the instance of ECDSA it is, its sizes: scalars of `Q` bytes in 4 or 6 words
(32 or 48 bytes, or P-224's 28 in 4) whose order `n` has exactly `8 Q` bits
and `2^(8 Q) < 2 n` (so that one `V` makes a candidate and `bits2octets` is
one conditional subtraction), or, if `wide`,
P-521's (9 words, 66 bytes, 521 bits: two `V`s make a candidate); the bits
`sh` the signature drops from its digest; and what is proven of the code:
that it meets the contract the proof of each curve is written against
(`coreK`: each curve's `signX86_64` at its sizes), in constant time, and the
facts of every instruction the proof of the whole function needs. Each
curve's file builds one, so that the heavy algebra of its proof stays out
of the modules generic over the curve and the hash function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.X86_64.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, with the
comb's tables (`E.combConsts`, if any) at their statics, as each curve's
proof states it (`Proof.Ecdsa.X86_64.signX86_64` for P-256). -/
def coreK (E : Impl.Ecdsa.X86_64.Cfg) : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 2 * E.C.len⟩
    let d : Region := ⟨s.gpr .rsi, E.C.len⟩
    let digest : Region := ⟨s.gpr .rdx, E.C.len⟩
    let k : Region := ⟨s.gpr .rcx, E.C.len⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ++ Abi.constRegions (fun n => s.syms n) E.combConsts ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 2 * E.C.len ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧
      TblsOk E.combConsts s [out, scratch, ret]
  post s s' :=
    match coreSigOf E s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) (2 * E.C.len) = encode E.C rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) (2 * E.C.len) =
        List.replicate (2 * E.C.len) 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    ∀ c ∈ E.combConsts, s₁.syms c.1 = s₂.syms c.1

/-- The code's blocks that depend on neither the hash function nor the
compression function, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.X86_64.Cfg) : Impl.Ecdsa.Rfc6979.X86_64.Cfg where
  H := ⟨Impl.Sha256.X86_64.Stream.params, 32, 104, "", .block [], "", .block [], "", "", "", "", ""⟩
  w := E.n
  len := E.C.len
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on x86-64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.X86_64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output, so
  that two `V`s make a candidate (`Impl.Ecdsa.Rfc6979.X86_64.Cfg.wide`). -/
  wide : Bool
  /-- Scalars of 4 or 6 words, `8 n` bytes (or 28 in 4 words), and `n` of
  exactly `8 len` bits, with `2^(8 len) < 2 n`; or, if `wide`, of 9 words and
  66 bytes, and `n` of 521 bits. -/
  sizes : if wide then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ E.C.len = 28) ∧ nBits E.C = 8 * E.C.len ∧
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
  /-- Its instructions: none writes `rsp` (or loads MXCSR), and it calls nothing. -/
  coreNs : coreC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  coreSp : coreC.allInstrs (fun i => !isa.writesSp i) = true
  coreMx : coreC.allInstrs (fun i => !loadsMxcsr i) = true
  coreD : coreC.depth = 0
  /-- Unless `wide`, `bits2octets` and the initial `K` and `V` address
  memory only from `rsp` and `rsi` (the taint analysis, of the block for
  `n`'s words). -/
  reduceT : wide = false → ∃ hc, (taint.check (Taint.ofRegs [.rsp, .rsi])
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.X86_64.Cfg.initKV)) hc).isSome = true
  /-- None of its instructions writes `rsp` or loads MXCSR. -/
  reduceSp : wide = false →
    (Code.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.X86_64.Cfg.initKV) : Prog isa).allInstrs
      (fun i => !isa.writesSp i) = true
  reduceMx : wide = false →
    (Code.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.X86_64.Cfg.initKV) : Prog isa).allInstrs
      (fun i => !loadsMxcsr i) = true

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.wide = false) :
    (R.E.n = 4 ∨ R.E.n = 6) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ R.E.C.len = 28) ∧
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

/-- The scalars' bytes fill their words, the last at least in part. -/
theorem len_words : 8 ≤ R.E.C.len ∧ 8 * R.E.n < R.E.C.len + 8 ∧ R.E.C.len ≤ 8 * R.E.n := by
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

end VG.Proof.Ecdsa.Rfc6979.X86_64
