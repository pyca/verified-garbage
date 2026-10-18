module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Scalar
public import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
public import VerifiedGarbage.Proof.MlKem.X86_64.Prfs
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
public import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
public import VerifiedGarbage.Proof.MlKem.X86_64.Zero
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# Implementations of `vg_mlkem_sample_ntt4` on x86-64

A `Sample4Impl` is what a function that calls `vg_mlkem_sample_ntt4` needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `MlKemSample4` on x86-64 (`Variants/MlKemSample4/X86_64/`),
and each caller (the top-level functions of ML-KEM-768 and ML-KEM-1024, in
`Generic/MlKemSample4/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Each is proven with 24 bytes of stack below its return
address: the baseline's calls of `vg_mlkem_sample_ntt`, three deep (the
others call nothing).

Each also comes with the computation of several outputs of `PRF₂` that its
callers inline (`Callee4.prfs`): one at a time for the baseline, and four
at a time with AVX2 for `vg_mlkem_sample_ntt4_avx2` (`Prfs.lean`); and, for
those with AVX2, the fragment encapsulation inlines to sample three entries
of the matrix while absorbing blocks of `ek` (`Callee4.batchH`,
`Sample4.sampleH`), with its proofs (`BatchHOk`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- What encapsulation needs of a fragment it inlines (`Callee4.batchH`):
it meets `sampleHK`, in constant time, calls nothing, keeps MXCSR's control
bits and never writes the stack pointer. -/
structure BatchHOk (b : Prog isa) : Prop where
  ok : ∀ s, sampleHK.pre s → ∃ t s', Exec isa b s t s' ∧ abiPreserved s s' ∧ sampleHK.post s s'
  ct : ConstantTime isa sampleHK.pre sampleHK.pub b
  noCalls : b.noCalls = true
  ctl : ctlOk b = true
  sp : b.all (fun i => !isa.writesSp i) = true

/-- The checks of every instruction of a fragment, at once. -/
def BatchHOk.checks (b : Prog isa) : Bool :=
  b.noCalls && ctlOk b && b.allInstrs (fun i => !isa.writesSp i)

theorem BatchHOk.of_checks {b : Prog isa} (hv : ∀ s, sampleHK.pre s → ∃ t s', Exec isa b s t s' ∧
    abiPreserved s s' ∧ sampleHK.post s s') (hct : ConstantTime isa sampleHK.pre sampleHK.pub b)
    (h : BatchHOk.checks b = true) : BatchHOk b := by
  simp only [BatchHOk.checks, Bool.and_eq_true] at h
  exact ⟨hv, hct, h.1.1, h.1.2, Code.all_of_allInstrs h.2⟩

theorem sampleH_checks (fast : Bool) : BatchHOk.checks (Impl.MlKem.X86_64.Sample4.sampleH fast) = true := by
  cases fast <;> decide +kernel

theorem sampleH_ok (fast : Bool) : BatchHOk (Impl.MlKem.X86_64.Sample4.sampleH fast) :=
  .of_checks (SH.correct (fast := fast)) (SH.ct (fast := fast)) (sampleH_checks fast)

/-- An implementation of `vg_mlkem_sample_ntt4` on x86-64. -/
structure Sample4Impl where
  /-- Its symbol and code. -/
  callee : Impl.MlKem.X86_64.Callee4
  /-- It is correct. -/
  ok : ∀ s, sample4K.pre s → ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ sample4K.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa sample4K.pre sample4K.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- Its calls are at most three deep. -/
  depth_le : callee.code.depth ≤ 3
  /-- It keeps MXCSR's control bits. -/
  mxcsr : ctlOk callee.code = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- Its outputs of `PRF₂` are correct. -/
  prfs_ok : ∀ {rbs wbs : List (Reg × Nat)} {s : State}, Lay rbs wbs s → (∀ b ∈ rbs ++ wbs, b.1 ∈ bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → prfsChk (rbs ++ wbs) wbs n o wl = true →
      WP isa (callee.prfs N₀ n o wl) s (PrfsPost s N₀ n o wl)
  /-- They are constant time. -/
  prfs_tr : ∀ {rbs wbs : List (Reg × Nat)}, (∀ b ∈ rbs ++ wbs, b.1 ∈ bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → prfsChk (rbs ++ wbs) wbs n o wl = true →
      RelCT isa (LRel rbs wbs) (callee.prfs N₀ n o wl) fun _ _ => True
  prfs_ctl : ∀ N₀ n o wl, ctlOk (callee.prfs N₀ n o wl) = true
  prfs_sp : ∀ N₀ n o wl, (callee.prfs N₀ n o wl).all (fun i => !isa.writesSp i) = true
  /-- The polynomial arithmetic that goes with it is correct, constant
  time, and safe to call. -/
  arith : ArithOk callee.arith
  /-- Its fragment for encapsulation, if any, is verified. -/
  batchH : ∀ b, callee.batchH = some b → BatchHOk b
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- How its callers compute the outputs of `PRF₂`, for their documentation. -/
  prfsDoc : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Sample4Impl

/-- The checks of every instruction of an implementation's code, at once:
the kernel builds the code once for all four. -/
def codeChecks (c : Prog isa) : Bool :=
  c.allInstrs (fun i => !Taint.clobbers i .rsp) && decide (c.depth ≤ 3) && ctlOk c &&
    c.allInstrs (fun i => !isa.writesSp i)

theorem codeChecks_spec {c : Prog isa} (h : codeChecks c = true) :
    NoSp c ∧ c.depth ≤ 3 ∧ ctlOk c = true ∧ c.all (fun i => !isa.writesSp i) = true := by
  simp only [codeChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨nosp_of h.1.1.1, h.1.1.2, h.1.2, Code.all_of_allInstrs h.2⟩

theorem scalar_checks : codeChecks (Impl.MlKem.X86_64.Callee4.scalar).code = true := by decide +kernel

/-- The baseline implementation, `vg_mlkem_sample_ntt4`, which calls `vg_mlkem_sample_ntt`. -/
def scalar : Sample4Impl where
  callee := .scalar
  ok := sample4_scalar_correct
  ct := sample4_scalar_ct
  nosp := (codeChecks_spec scalar_checks).1
  depth_le := (codeChecks_spec scalar_checks).2.1
  mxcsr := (codeChecks_spec scalar_checks).2.2.1
  spSafe := (codeChecks_spec scalar_checks).2.2.2
  prfs_ok := fun L hcs => prfsScalar_ok L hcs
  prfs_tr := fun hcs => prfsScalar_tr hcs
  prfs_ctl := prfsScalar_ctl
  prfs_sp := prfsScalar_sp
  arith := ArithOk.sse
  batchH := fun _ h => nomatch h
  suffix := ""
  prfsDoc := "one at a time"
  features := []

theorem avx2_checks : codeChecks (Impl.MlKem.X86_64.Callee4.avx2).code = true := by decide +kernel

/-- The AVX2 implementation, `vg_mlkem_sample_ntt4_avx2`. -/
def avx2 : Sample4Impl where
  callee := .avx2
  ok := sample4_correct (fast := false)
  ct := sample4_ct (fast := false)
  nosp := (codeChecks_spec avx2_checks).1
  depth_le := (codeChecks_spec avx2_checks).2.1
  mxcsr := (codeChecks_spec avx2_checks).2.2.1
  spSafe := (codeChecks_spec avx2_checks).2.2.2
  prfs_ok := fun L hcs => prfsAvx2_ok L hcs
  prfs_tr := fun hcs => prfsAvx2_tr hcs
  prfs_ctl := prfsAvx2_ctl
  prfs_sp := prfsAvx2_sp
  arith := ArithOk.avx2
  batchH := fun _ h => Option.some.inj h ▸ sampleH_ok false
  suffix := "_avx2"
  prfsDoc := "four at a time, with AVX2 (and the first one or two of `4k + 1` or `4k + 2` on their own)"
  features := ["avx", "avx2"]

theorem avx512_checks : codeChecks (Impl.MlKem.X86_64.Callee4.avx512).code = true := by decide +kernel

/-- The AVX-512VL implementation, `vg_mlkem_sample_ntt4_avx512`. -/
def avx512 : Sample4Impl where
  callee := .avx512
  ok := sample4_correct (fast := true)
  ct := sample4_ct (fast := true)
  nosp := (codeChecks_spec avx512_checks).1
  depth_le := (codeChecks_spec avx512_checks).2.1
  mxcsr := (codeChecks_spec avx512_checks).2.2.1
  spSafe := (codeChecks_spec avx512_checks).2.2.2
  prfs_ok := fun L hcs => prfsAvx2_ok L hcs
  prfs_tr := fun hcs => prfsAvx2_tr hcs
  prfs_ctl := prfsAvx2_ctl
  prfs_sp := prfsAvx2_sp
  arith := ArithOk.avx2
  batchH := fun _ h => Option.some.inj h ▸ sampleH_ok true
  suffix := "_avx512"
  prfsDoc := "four at a time, with AVX-512VL quadword rotates (and the first one or two of `4k + 1` or `4k + 2` on their own)"
  features := ["avx", "avx2", "avx512f", "avx512vl"]

end Sample4Impl

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v`: the kernel evaluates only
code that does not call the implementation `v`, each part once (rather than
failing on code that does, after evaluating its other parts). -/
elab "closed_in " v:ident : tactic => withMainContext do
  let e ← elabTerm v none
  if (← instantiateMVars (← getMainTarget)).containsFVar e.fvarId! then
    throwError "the goal mentions {e}"

/-- `ctlOk` of code that calls the implementation `v`: evaluated by the
kernel but for the calls of `v`. -/
tactic_template "s4_ctl " v:ident : tactic =>
  `(tactic| repeat' (first
    | (closed_in $v; decide +kernel) | with_reducible exact ($v).arith.dm_ctl
    | with_reducible exact ($v).arith.em_ctl | with_reducible exact ($v).arith.km_ctl | apply ctlOk_seq | apply ctlOk_ite
    | (apply ctlOk_call; exact ($v).mxcsr) | exact ($v).prfs_ctl _ _ _ _
    | exact ($v).arith.nttInv.ctl | exact ($v).arith.add.ctl | exact ($v).arith.sub.ctl
    | exact ($v).arith.cbd.ctl | exact ($v).arith.dec12.ctl | exact ($v).arith.enc12.ctl | exact Codecs.ce_ctl _ | exact Codecs.dd_ctl _
    | rfl))

/-- Code that does not call the implementation `v` never writes the stack pointer: by evaluation. -/
tactic_template "s4_sp_closed " v:ident : tactic =>
  `(tactic| (closed_in $v; exact Code.all_of_allInstrs (by decide +kernel)))

/-- That code that calls the implementation `v` never writes the stack pointer. -/
tactic_template "s4_sp " v:ident : tactic =>
  `(tactic| repeat' (first
    | s4_sp_closed $v | with_reducible exact ($v).arith.dm_sp | with_reducible exact ($v).arith.em_sp | with_reducible exact ($v).arith.km_sp
    | apply all_seq | apply all_ite
    | (apply all_call; exact ($v).spSafe) | exact ($v).prfs_sp _ _ _ _
    | exact ($v).arith.nttInv.sp | exact ($v).arith.add.sp | exact ($v).arith.sub.sp
    | exact ($v).arith.cbd.sp | exact ($v).arith.dec12.sp | exact ($v).arith.enc12.sp | exact Codecs.ce_sp _ | exact Codecs.dd_sp _
    | rfl))

end VG.Proof.MlKem.X86_64
