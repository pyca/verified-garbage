module

public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-!
# Deterministic ECDSA on x86-64: the curve

What the proof needs of the curve (`RfcCurve`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.X86_64.Cfg`),
the instance of ECDSA it is, its sizes: scalars of `Q` bytes in 4, 6 or 8 words
(32, 48 or 64 bytes, or P-192's 24 and P-224's 28 in 4) whose order `n` has
exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that `bits2octets` is one
conditional subtraction), or, if `big`, P-521's (9 words, 66 bytes, 521
bits: longer than any digest); the bits `sh` the signature drops from its
digest; the facts of its blocks (`RfcT`); and what is proven of the code:
that it meets the contract the proof of each curve is written against
(`coreK`: each curve's `signX86_64` at its sizes), in constant time, and the
facts of every instruction the proof of the whole function needs. Each
curve's file builds one, so that the heavy algebra of its proof stays out
of the modules generic over the curve and the hash function.
-/

@[expose] public section

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

/-- The code's blocks for scalars of `E` (with `h = X` and `core`'s digest
shifted if `big`, by `sh` bits), without the functions it calls. -/
def cfgC (E : Impl.Ecdsa.X86_64.Cfg) (big : Bool) (sh : Nat) : Impl.Ecdsa.Rfc6979.X86_64.Cfg where
  f := ⟨[], [], []⟩
  w := E.n
  len := E.C.len
  big := big
  sh := sh
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- None of the instructions of the block `is` writes `rsp` or loads MXCSR. -/
abbrev OkB (is : List Instr) : Prop :=
  (Code.block is : Prog isa).allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true

open Impl.Ecdsa.Rfc6979.X86_64 in
/-- The blocks whose contents depend on the curve: each addresses memory
only from the registers that hold the frame's base and the pointers the code
put there (the taint analysis), and none of their instructions writes `rsp`
or loads MXCSR. -/
structure RfcT (c : Impl.Ecdsa.Rfc6979.X86_64.Cfg) : Prop where
  xArgs : TaintOk [.rsp] c.xArgs
  reduce : c.big = false → TaintOk [.rsp] c.reduce
  msgF : TaintOk [.rsp, .rdi, .rsi] (c.msg 0 true)
  msgN : TaintOk [.rsp, .rdi, .rsi] (c.msg 0 false)
  updM : TaintOk [.rsp] (Cfg.updMArgs (1 + 2 * c.len))
  finM : TaintOk [.rsp] (Cfg.finArgs (1 + 2 * c.len) fK)
  tStep : TaintOk [.rsp] c.tStep
  coreArgs : TaintOk [.rsp] c.coreArgs
  xcArgs : c.big = true → TaintOk [.rsp] c.xcArgs
  convC : c.big = true → TaintOk [.rsp, .rdi] (c.conv fXc (8 - c.sh))
  convT : c.big = true → TaintOk [.rsp, .rdi] (c.conv fT c.sh)
  iXArgs : OkB c.xArgs
  iReduce : OkB c.reduce
  iMsgF₀ : OkB (c.msg 0 true)
  iMsgF₁ : OkB (c.msg 1 true)
  iMsgN : OkB (c.msg 0 false)
  iUpdM : OkB (Cfg.updMArgs (1 + 2 * c.len))
  iFinM : OkB (Cfg.finArgs (1 + 2 * c.len) fK)
  iTStep : OkB c.tStep
  iCandTop : OkB c.candTop
  iCoreArgs : OkB c.coreArgs
  iXcArgs : OkB c.xcArgs
  iConvC : OkB (Cfg.scrPtr ++ c.conv fXc (8 - c.sh))

/-- `RfcT` of a curve's blocks, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { xArgs := ⟨_, by taint_decide⟩, reduce := by exact (Function.const _ ⟨_, by taint_decide⟩),
    msgF := ⟨_, by taint_decide⟩, msgN := ⟨_, by taint_decide⟩, updM := ⟨_, by taint_decide⟩,
    finM := ⟨_, by taint_decide⟩, tStep := ⟨_, by taint_decide⟩, coreArgs := ⟨_, by taint_decide⟩,
    xcArgs := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convC := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convT := by exact (Function.const _ ⟨_, by taint_decide⟩),
    iXArgs := by decide +kernel, iReduce := by decide +kernel, iMsgF₀ := by decide +kernel,
    iMsgF₁ := by decide +kernel, iMsgN := by decide +kernel, iUpdM := by decide +kernel,
    iFinM := by decide +kernel, iTStep := by decide +kernel, iCandTop := by decide +kernel,
    iCoreArgs := by decide +kernel, iXcArgs := by decide +kernel, iConvC := by decide +kernel })

/-- A curve, for RFC 6979 on x86-64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.X86_64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output and
  `n` has fewer bits than they do (P-521's), so that `h` is the digest's
  integer and `core` takes it shifted (`Impl.Ecdsa.Rfc6979.X86_64.Cfg.big`). -/
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
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct (with the 8
  bytes below `rsp` apart from its buffers, for the return addresses of its
  own calls) and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → Clear (hole (s.gpr .rsp)) s →
    ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- Its instructions: none writes `rsp` (or loads MXCSR), and the functions
  it calls call nothing. -/
  coreNs : coreC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  coreSp : coreC.allInstrs (fun i => !isa.writesSp i) = true
  coreMx : coreC.allInstrs (fun i => !loadsMxcsr i) = true
  coreD : coreC.depth ≤ 1
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

end VG.Proof.Ecdsa.Rfc6979.X86_64
