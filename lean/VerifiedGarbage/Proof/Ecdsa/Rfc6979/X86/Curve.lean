module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout

/-!
# Deterministic ECDSA on x86 (32-bit): the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign_k` for curves of `n` 64-bit words
(`Impl.Ecdsa.X86.Cfg`, `n` 3, 4, 6 or 8), the instance of ECDSA it is, that
the order `n` of its base point has exactly `64 n` bits and `2^(64 n) < 2 n`
(so that `bits2octets` is one conditional subtraction), or, if `wide`,
P-521's sizes, and what is proven of the code: that it meets the contract
the proof of each curve is written against (`coreK`, including any comb
tables), in constant time, that it never writes `esp` and uses at most
`E.stk` stack bytes, the taint check of the block computing `bits2octets`,
which holds `n`'s words as immediates, and the checks of the blocks that
depend on both the scalars' and the hash function's sizes, for each hash
function's (`RfcT`, `shapes`). Each curve's file builds one, so that the
heavy algebra of its proof stays out of the modules generic over the curve
and the hash function.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.X86.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign_k` on the curve `E`, as each
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
functions it calls, for scalars of `E` (with `h` at the frame's top if
`hHigh`). -/
def cfgC (E : Impl.Ecdsa.X86.Cfg) (hHigh : Bool := false) : Impl.Ecdsa.Rfc6979.X86.Cfg where
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
the code takes (`Impl.Ecdsa.Rfc6979.X86.shapeOf`). -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr rs) (.block is) hc).isSome = true

/-- None of the instructions of the block `is` writes `esp`. -/
abbrev OkB (is : List Instr) : Prop :=
  (Code.block is : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true

/-- The code's blocks for scalars of `E` (with `h` at the frame's top if
`hHigh`, and digests shifted by `sh` bits) and a hash function of output
length `D` and block size `B`. -/
def cfgS (E : Impl.Ecdsa.X86.Cfg) (hHigh : Bool) (sh D B : Nat) : Impl.Ecdsa.Rfc6979.X86.Cfg :=
  { cfgC E hHigh with D := D, B := B, sh := sh }

open Impl.Ecdsa.Rfc6979.X86 in
/-- The blocks that depend on both the scalars' and the hash function's
sizes, each addressing memory only from the registers that hold the frame's
base and the pointers the code put there (the taint analysis): those that
load `scratch` from our arguments first (`Cfg.scrPtr`), from `edi` after it. -/
structure RfcT (c : Impl.Ecdsa.Rfc6979.X86.Cfg) : Prop where
  msgF : TaintOk [.esp, .edi, .esi] (Cfg.msg c.len c.D 0 true c.fHo)
  msgF₁ : TaintOk [.esp, .edi, .esi] (Cfg.msg c.len c.D 1 true c.fHo)
  msgN : TaintOk [.esp, .edi, .esi] (Cfg.msg c.len c.D 0 false)
  prepW : c.wide = true → TaintOk [.esp, .esi, .edi] c.prep
  coreArgs : TaintOk [.esp] c.coreArgs
  keepV : ∀ j < 8, TaintOk [.esp] (c.keepV j)
  candTop : c.sh ≠ 0 → TaintOk [.esp, .edi] (c.conv fT c.sh)
  wipe : TaintOk [.esp] c.wipe
  digestPtr : TaintOk [.esp] (save ++ c.digestPtr)
  padI : TaintOk [.esp, .edi] (([.mov .ecx (.imm ipad32)] : List Instr) ++ (List.range (c.B / 4)).flatMap c.padW)
  padO : TaintOk [.esp, .edi] (([.mov .ecx (.imm opad32)] : List Instr) ++ (List.range (c.B / 4)).flatMap c.padW)
  hfinCopyK : TaintOk [.esp, .edi] (Cfg.copyBytes c.D .edi sTmp .esp fK)
  hfinCopyV : TaintOk [.esp, .edi] (Cfg.copyBytes c.D .edi sTmp .esp fV)
  /-- None of their instructions writes `esp`. -/
  iMsgF₀ : OkB (Cfg.msg c.len c.D 0 true c.fHo)
  iMsgF₁ : OkB (Cfg.msg c.len c.D 1 true c.fHo)
  iMsgN : OkB (Cfg.msg c.len c.D 0 false)
  iPrep : OkB c.prep
  iCoreArgs : OkB c.coreArgs
  iKeepV : ∀ j < 8, OkB (c.keepV j)
  iCandTop : OkB c.candTop
  iWipe : OkB c.wipe
  iDigestPtr : OkB (save ++ c.digestPtr)
  iPadI : OkB (c.padBlk ipad32)
  iPadO : OkB (c.padBlk opad32)
  iCopyK : OkB (c.scrPtr ++ Cfg.copyBytes c.D .edi sTmp .esp fK)
  iCopyV : OkB (c.scrPtr ++ Cfg.copyBytes c.D .edi sTmp .esp fV)
  /-- At most 8 `V`s make a candidate, which fit `T`. -/
  m8 : c.m ≤ 8
  mD : c.wide = true → c.m * c.D ≤ 128

/-- `RfcT` of the code's blocks for literal sizes, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { msgF := ⟨_, by taint_decide⟩, msgF₁ := ⟨_, by taint_decide⟩, msgN := ⟨_, by taint_decide⟩, prepW := by exact (Function.const _ ⟨_, by taint_decide⟩),
    coreArgs := ⟨_, by taint_decide⟩,
    keepV := fun j hj => match j, hj with
      | 0, _ => ⟨_, by taint_decide⟩ | 1, _ => ⟨_, by taint_decide⟩ | 2, _ => ⟨_, by taint_decide⟩
      | 3, _ => ⟨_, by taint_decide⟩ | 4, _ => ⟨_, by taint_decide⟩ | 5, _ => ⟨_, by taint_decide⟩
      | 6, _ => ⟨_, by taint_decide⟩ | 7, _ => ⟨_, by taint_decide⟩,
    candTop := by exact (Function.const _ ⟨_, by taint_decide⟩),
    wipe := ⟨_, by taint_decide⟩, digestPtr := ⟨_, by taint_decide⟩, padI := ⟨_, by taint_decide⟩, padO := ⟨_, by taint_decide⟩,
    hfinCopyK := ⟨_, by taint_decide⟩, hfinCopyV := ⟨_, by taint_decide⟩, iMsgF₀ := by decide +kernel,
    iMsgF₁ := by decide +kernel,
    iMsgN := by decide +kernel, iPrep := by decide +kernel, iCoreArgs := by decide +kernel,
    iKeepV := by decide +kernel, iCandTop := by decide +kernel, iWipe := by decide +kernel,
    iDigestPtr := by decide +kernel, iPadI := by decide +kernel, iPadO := by decide +kernel,
    iCopyK := by decide +kernel, iCopyV := by decide +kernel, m8 := by decide +kernel,
    mD := by decide +kernel })

/-- `blkT` from `RfcT` for each of the shapes. -/
theorem blkT_of {E : Impl.Ecdsa.X86.Cfg} {hHigh : Bool} {sh : Nat}
    (h₀ : RfcT (cfgS E hHigh sh 16 64)) (h₁ : RfcT (cfgS E hHigh sh 20 64)) (h₂ : RfcT (cfgS E hHigh sh 28 64))
    (h₃ : RfcT (cfgS E hHigh sh 32 64)) (h₄ : RfcT (cfgS E hHigh sh 48 128)) (h₅ : RfcT (cfgS E hHigh sh 64 128))
    (h₆ : RfcT (cfgS E hHigh sh 28 128)) (h₇ : RfcT (cfgS E hHigh sh 32 128)) :
    ∀ D B, (D, B) ∈ shapes → RfcT (cfgS E hHigh sh D B) := by
  intro D B h
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-- A curve, for RFC 6979 on x86. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign_k` has it. -/
  E : Impl.Ecdsa.X86.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output
  (P-521's), so that several `V`s make a candidate whatever the hash
  function (`Impl.Ecdsa.Rfc6979.X86.Cfg.wide`). -/
  wide : Bool
  /-- Scalars of 3, 4, 6 or 8 64-bit words, `8 n` bytes, and `n` of exactly `64 n`
  bits, with `2^(64 n) < 2 n`; or P-224, 28 bytes in 4 words;
  or, if `wide`, of 9 words and 66 bytes, and
  `n` of 521 bits. -/
  sizes : if wide then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 3 ∨ E.n = 4 ∨ E.n = 6 ∨ E.n = 8) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ E.C.len = 28) ∧ nBits E.C = 8 * E.C.len ∧ 2 ^ (8 * E.C.len) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- Whether `h` is kept at the frame's top
  (`Impl.Ecdsa.Rfc6979.X86.Cfg.hHigh`): for scalars of 8 words. -/
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
  /-- It never writes `esp`, and uses at most `E.stk` stack bytes. -/
  coreNs : NoSp coreC
  coreStack : stackUse coreC ≤ E.stk
  /-- Unless `wide`, `bits2octets` and the initial `K` and `V` address
  memory only from `esp` and `esi` (the taint analysis, of the block for
  `n`'s words). -/
  reduceT : wide = false → ∃ hc, (VG.Taint.check taint (τr [.esp, .esi])
    (.block ((cfgC E hHigh).reduce ++ Impl.Ecdsa.Rfc6979.X86.Cfg.initKV)) hc).isSome = true
  /-- The blocks for each hash function's sizes. -/
  blkT : ∀ D B, (D, B) ∈ shapes → RfcT (cfgS E hHigh sh D B)

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.wide = false) :
    (R.E.n = 3 ∨ R.E.n = 4 ∨ R.E.n = 6 ∨ R.E.n = 8) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ R.E.C.len = 28) ∧ nBits R.E.C = 8 * R.E.C.len ∧
      2 ^ (8 * R.E.C.len) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.wide = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n3 : 3 ≤ R.E.n := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h | h | h <;> omega
  · rw [(R.sizesW h).1]; omega

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h | h | h <;> omega
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
