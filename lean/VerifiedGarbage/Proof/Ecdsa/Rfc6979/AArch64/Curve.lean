module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract

/-!
# Deterministic ECDSA on AArch64: the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.AArch64.Cfg`),
the instance of ECDSA it is, its sizes: `n` 4, 6 or 8, scalars of `8 n`
bytes (or P-224's 28 in 4 words), the order `n` of its base point of
exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that
`bits2octets` is one conditional subtraction), or, if `wide` (P-521), `n` 9,
scalars of 66 bytes and the order of 521 bits; and what is proven of the
code: that it meets the contract the proof of each curve is written against
(`coreK`: P-256's `signAArch64`, P-384's and P-521's at the curve's sizes), in
constant time, that it pushes no frame and writes no callee-saved SIMD
register, unless `wide`, the taint check of the block computing
`bits2octets`, which holds `n`'s words as immediates, and the checks of the
blocks that depend on both the scalars' and each hash function's sizes
(`RfcT`, for each of `shapes`). Each curve's file builds one, so that the heavy algebra of its
proof stays out of the modules generic over the curve and the hash function.
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

/-- The code's blocks that depend on neither the hash function nor the
compression function, for scalars of `E` (with `h` at the frame's top if
`hHigh`). -/
def cfgC (E : Impl.Ecdsa.AArch64.Cfg) (hHigh : Bool := false) : Impl.Ecdsa.Rfc6979.AArch64.Cfg where
  D := 64
  B := 128
  f := ⟨[], [], []⟩
  w := E.n
  len := E.C.len
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []
  hHigh := hHigh

/-- The digest lengths and block sizes of the hash functions whose tables
the code takes (`Impl.Ecdsa.Rfc6979.AArch64.shapeOf`). -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- The taint check of a block whose addresses depend only on `sp` and `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- None of the instructions of the block `is` writes a callee-saved SIMD register. -/
abbrev OkB (is : List Instr) : Prop := (Code.block is : Prog isa).allInstrs keepsV = true

/-- The code's blocks for scalars of `E` (with `h` at the frame's top if
`hHigh`, and digests shifted by `sh` bits) and a hash function of output
length `D` and block size `B`. -/
def cfgS (E : Impl.Ecdsa.AArch64.Cfg) (hHigh : Bool) (sh D B : Nat) : Impl.Ecdsa.Rfc6979.AArch64.Cfg :=
  { cfgC E hHigh with D := D, B := B, sh := sh }

open Impl.Ecdsa.Rfc6979.AArch64 in
/-- The blocks that depend on both the scalars' and the hash function's
sizes, each addressing memory only from `sp` and the registers that hold
the pointers the code put there (the taint analysis). The blocks that
differ only in immediates and offsets (`Instr.eraseOff`) are checked once. -/
structure RfcT (c : Impl.Ecdsa.Rfc6979.AArch64.Cfg) : Prop where
  msgF : TaintOk [.x9, .x10, .x15] (Cfg.msg c.w c.len c.D 0 true c.fHo)
  msgN : TaintOk [.x9, .x10, .x15] (Cfg.msg c.w c.len c.D 0 false)
  prepW : c.wide = true → TaintOk [.x0, .x1] c.prep
  coreArgs : TaintOk [] c.coreArgs
  keepV : TaintOk [] (c.keepV 0)
  candTop : c.sh ≠ 0 → TaintOk [.x0] (c.convB fT c.sh)
  wipe : TaintOk [] c.wipe
  digestPtr : TaintOk [] c.digestPtr
  pad : TaintOk [.x9] (c.padBody 0)
  hfinCopy : TaintOk [.x9] (c.copyOut 0)
  /-- None of their instructions writes a callee-saved SIMD register. -/
  iMsgF : OkB (Cfg.msg c.w c.len c.D 0 true c.fHo)
  iMsgN : OkB (Cfg.msg c.w c.len c.D 0 false)
  iPrep : OkB c.prep
  iCoreArgs : OkB c.coreArgs
  iKeepV : OkB (c.keepV 0)
  iCandTop : OkB (c.convB fT c.sh)
  iWipe : OkB c.wipe
  iDigestPtr : OkB c.digestPtr
  iPad : OkB (c.padBody 0)
  iCopy : OkB (c.copyOut 0)
  /-- At most 8 `V`s make a candidate. -/
  m8 : c.m ≤ 8

/-- `RfcT` of the code's blocks for literal sizes, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { msgF := ⟨_, by taint_decide⟩, msgN := ⟨_, by taint_decide⟩, prepW := by exact (Function.const _ ⟨_, by taint_decide⟩),
    coreArgs := ⟨_, by taint_decide⟩, keepV := ⟨_, by taint_decide⟩, candTop := by exact (Function.const _ ⟨_, by taint_decide⟩),
    wipe := ⟨_, by taint_decide⟩, digestPtr := ⟨_, by taint_decide⟩, pad := ⟨_, by taint_decide⟩,
    hfinCopy := ⟨_, by taint_decide⟩, iMsgF := by decide +kernel, iMsgN := by decide +kernel,
    iPrep := by decide +kernel, iCoreArgs := by decide +kernel, iKeepV := by decide +kernel,
    iCandTop := by decide +kernel, iWipe := by decide +kernel, iDigestPtr := by decide +kernel,
    iPad := by decide +kernel, iCopy := by decide +kernel, m8 := by decide +kernel })

/-- `blkT` from `RfcT` for each of the shapes. -/
theorem blkT_of {E : Impl.Ecdsa.AArch64.Cfg} {hHigh : Bool} {sh : Nat}
    (h₀ : RfcT (cfgS E hHigh sh 16 64)) (h₁ : RfcT (cfgS E hHigh sh 20 64)) (h₂ : RfcT (cfgS E hHigh sh 28 64))
    (h₃ : RfcT (cfgS E hHigh sh 32 64)) (h₄ : RfcT (cfgS E hHigh sh 48 128)) (h₅ : RfcT (cfgS E hHigh sh 64 128))
    (h₆ : RfcT (cfgS E hHigh sh 28 128)) (h₇ : RfcT (cfgS E hHigh sh 32 128)) :
    ∀ D B, (D, B) ∈ shapes → RfcT (cfgS E hHigh sh D B) := by
  intro D B h
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-- A curve, for RFC 6979 on AArch64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.AArch64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output
  (P-521's), so that several `V`s make a candidate whatever the hash
  function (`Impl.Ecdsa.Rfc6979.AArch64.Cfg.wide`). -/
  wide : Bool
  /-- Scalars of 4, 6 or 8 words, `8 n` bytes (or 24 or 28 in 4 words), and `n` of
  exactly `8 len` bits, with `2^(8 len) < 2 n`; or, if `wide`, of 9 words and
  66 bytes, and `n` of 521 bits. -/
  sizes : if wide then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6 ∨ E.n = 8) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ (E.C.len = 28 ∨ E.C.len = 24)) ∧ nBits E.C = 8 * E.C.len ∧
      2 ^ (8 * E.C.len) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- Whether `h` is kept at the frame's top
  (`Impl.Ecdsa.Rfc6979.AArch64.Cfg.hHigh`): for scalars of 8 words. -/
  hHigh : Bool := false
  hHigh_eq : hHigh = decide (E.n = 8) := by decide
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
  /-- Unless `wide`, `bits2octets` and the initial `K` and `V` address
  memory only from `sp` and `x1` (the taint analysis, of the block for `n`'s
  words). -/
  reduceT : wide = false → ∃ hc, (taint.check (Taint.ofRegs [.x1])
    (.block ((cfgC E hHigh).reduce ++ Impl.Ecdsa.Rfc6979.AArch64.Cfg.initKV)) hc).isSome = true
  /-- The blocks for each hash function's sizes. -/
  blkT : ∀ D B, (D, B) ∈ shapes → RfcT (cfgS E hHigh sh D B)

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.wide = false) :
    (R.E.n = 4 ∨ R.E.n = 6 ∨ R.E.n = 8) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ (R.E.C.len = 28 ∨ R.E.C.len = 24)) ∧
      nBits R.E.C = 8 * R.E.C.len ∧ 2 ^ (8 * R.E.C.len) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.wide = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n4 : 4 ≤ R.E.n := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h | h <;> omega
  · rw [(R.sizesW h).1]; omega

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h | h <;> omega
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
