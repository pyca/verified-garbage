module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract

/-!
# Deterministic ECDSA on AArch64: the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign_k` for curves of `n` words (`Impl.Ecdsa.AArch64.Cfg`),
the instance of ECDSA it is, its sizes: scalars of `Q` bytes in 4, 6 or 8
words (32, 48 or 64 bytes, or P-192's 24 and P-224's 28 in 4) whose order
`n` has exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that `bits2octets` is one
conditional subtraction), or, if `big`, P-521's (9 words, 66 bytes, 521
bits: longer than any digest); the bits `sh` the signature drops from its
digest; the facts of its blocks (`RfcT`); and what is proven of the code:
that it meets the contract the proof of each curve is written against
(`coreK`: P-256's `signAArch64`, the others' at the curve's sizes), in
constant time, that it pushes no frame and writes no callee-saved SIMD
register. Each curve's file builds one, so that the heavy algebra of its
proof stays out of the modules generic over the curve and the hash
function.
-/

@[expose] public section

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

/-- The code's blocks for scalars of `E` (with `h = X` and `core`'s digest
shifted if `big`, by `sh` bits), without the functions it calls. -/
def cfgC (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh : Nat) : Impl.Ecdsa.Rfc6979.AArch64.Cfg where
  f := ⟨[], [], []⟩
  w := E.n
  len := E.C.len
  big := big
  sh := sh
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- The taint check of a block whose addresses depend only on `sp` and `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- None of the instructions of the block `is` writes a callee-saved SIMD register. -/
abbrev OkB (is : List Instr) : Prop := (Code.block is : Prog isa).allInstrs keepsV = true

open Impl.Ecdsa.Rfc6979.AArch64 in
/-- The blocks whose contents depend on the curve: each addresses memory
only from `sp` and the registers that hold the pointers the code put there
(the taint analysis), and none of their instructions writes a callee-saved
SIMD register. -/
structure RfcT (c : Impl.Ecdsa.Rfc6979.AArch64.Cfg) : Prop where
  xArgs : TaintOk [] c.xArgs
  reduce : c.big = false → TaintOk [] c.reduce
  msgF₀ : TaintOk [.x9, .x10, .x15] (c.msg 0 true)
  msgF₁ : TaintOk [.x9, .x10, .x15] (c.msg 1 true)
  updM : TaintOk [] (Cfg.updMArgs (1 + 2 * c.len))
  finM : TaintOk [] (Cfg.finArgs (1 + 2 * c.len) fK)
  tStep : TaintOk [] c.tStep
  coreArgs : TaintOk [] c.coreArgs
  xcArgs : c.big = true → TaintOk [] c.xcArgs
  convC : c.big = true → TaintOk [.x0] (c.convB fXc (8 - c.sh))
  convT : c.big = true → TaintOk [.x0] (c.convB fT c.sh)
  iXArgs : OkB c.xArgs
  iReduce : OkB c.reduce
  iMsgF₀ : OkB (c.msg 0 true)
  iMsgF₁ : OkB (c.msg 1 true)
  iUpdM : OkB (Cfg.updMArgs (1 + 2 * c.len))
  iFinM : OkB (Cfg.finArgs (1 + 2 * c.len) fK)
  iTStep : OkB c.tStep
  iCoreArgs : OkB c.coreArgs
  iXcArgs : OkB c.xcArgs
  iConvC : OkB (c.convB fXc (8 - c.sh))
  iConvT : OkB (c.convB fT c.sh)

/-- `RfcT` of a curve's blocks, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { xArgs := ⟨_, by taint_decide⟩, reduce := by exact (Function.const _ ⟨_, by taint_decide⟩),
    msgF₀ := ⟨_, by taint_decide⟩, msgF₁ := ⟨_, by taint_decide⟩, updM := ⟨_, by taint_decide⟩,
    finM := ⟨_, by taint_decide⟩, tStep := ⟨_, by taint_decide⟩, coreArgs := ⟨_, by taint_decide⟩,
    xcArgs := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convC := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convT := by exact (Function.const _ ⟨_, by taint_decide⟩),
    iXArgs := by decide +kernel, iReduce := by decide +kernel, iMsgF₀ := by decide +kernel,
    iMsgF₁ := by decide +kernel, iUpdM := by decide +kernel, iFinM := by decide +kernel,
    iTStep := by decide +kernel, iCoreArgs := by decide +kernel, iXcArgs := by decide +kernel,
    iConvC := by decide +kernel, iConvT := by decide +kernel })

/-- A curve, for RFC 6979 on AArch64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign_k` has it. -/
  E : Impl.Ecdsa.AArch64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output and
  `n` has fewer bits than they do (P-521's), so that `h` is the digest's
  integer and `core` takes it shifted (`Impl.Ecdsa.Rfc6979.AArch64.Cfg.big`). -/
  big : Bool
  /-- Scalars of 4, 6 or 8 words, `8 n` bytes (or 24 or 28 in 4 words), and `n` of
  exactly `8 len` bits, with `2^(8 len) < 2 n`; or, if `big`, of 9 words and
  66 bytes, and `n` of 521 bits. -/
  sizes : if big then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6 ∨ E.n = 8) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ (E.C.len = 28 ∨ E.C.len = 24)) ∧
      nBits E.C = 8 * E.C.len ∧ 2 ^ (8 * E.C.len) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : E.sh = sh
  /-- `vg_ecdsa_<curve>_sign_k`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It pushes no frame, and none of its instructions writes a callee-saved SIMD register. -/
  coreNoFrames : coreC.noFrames = true
  coreKeepsV : coreC.allInstrs keepsV = true
  /-- The taint checks and instruction facts of the curve's blocks. -/
  blk : RfcT (cfgC E big sh)

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.big = false) :
    (R.E.n = 4 ∨ R.E.n = 6 ∨ R.E.n = 8) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ (R.E.C.len = 28 ∨ R.E.C.len = 24)) ∧
      nBits R.E.C = 8 * R.E.C.len ∧ 2 ^ (8 * R.E.C.len) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.big = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n4 : 4 ≤ R.E.n := by
  cases h : R.big
  · rcases (R.sizesA h).1 with h | h | h <;> omega
  · rw [(R.sizesW h).1]; omega

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.big
  · rcases (R.sizesA h).1 with h | h | h <;> omega
  · rw [(R.sizesW h).1]

/-- The scalars' bytes fill their words, the last possibly zero. -/
theorem len_words : 8 ≤ R.E.C.len ∧ 8 * R.E.n ≤ R.E.C.len + 8 ∧ R.E.C.len ≤ 8 * R.E.n := by
  cases h : R.big
  · have := R.sizesA h; have := R.n4; omega
  · have := R.sizesW h; omega

/-- `nBits` is within the scalars' last byte, and `sh` the bits beyond it. -/
theorem nBits_len : 8 * R.E.C.len < nBits R.E.C + 8 ∧ nBits R.E.C ≤ 8 * R.E.C.len ∧
    R.sh = 8 * R.E.C.len - nBits R.E.C := by
  rw [← R.sh_eq]
  cases h : R.big
  · have := R.sizesA h; exact ⟨by omega, by omega, rfl⟩
  · have := R.sizesW h; exact ⟨by omega, by omega, rfl⟩

theorem n_ne : R.E.C.n ≠ 0 := fun h => by
  have h₁ := R.nBits_len; have h₂ := R.len_words
  have : nBits R.E.C = 1 := by show R.E.C.n.log2 + 1 = 1; rw [h]; rfl
  omega

end RfcCurve

end VG.Proof.Ecdsa.Rfc6979.AArch64
