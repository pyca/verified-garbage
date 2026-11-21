module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.TaintOps
public meta import Lean.Meta.Eval
public meta import Lean.Elab.Term
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The residue analysis with MXCSR the same in both runs (x86-64)

`rtaintMx` is the residue analysis (`RTaint.rtaint`) whose states also agree
on MXCSR, as two runs that `NoResidue` relates do (`Outside`): it rejects
`ldmxcsr`, so they keep agreeing. As `X86_64.taintMx` for constant time, it
is for operations (`Taint.Op`) whose effect depends on MXCSR (a call of
`vg_mcdt_enter`, `Proof/Mcdt/X86_64/Op.lean`): the analysis with them
(`Taint.checkOps`, `OpsCheck`) gives `Scrub.ResOk` as the analysis alone
does (`resOk_of_opsCheck`, as `RScrub.resOk_of_check`), and `keep_for_ops%`
the granules to wipe (as `keep_for%`).
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.X86_64 VG.X86_64.Taint

/-- `Agree`, and the same MXCSR. -/
def AgreeMx (τ : FT) (s₁ s₂ : State) : Prop := Agree τ s₁ s₂ ∧ s₁.mxcsr = s₂.mxcsr

/-- `stepF`, but for `ldmxcsr`, which fails. -/
def stepMx (τ : FT) : Instr → Option FT
  | .ldmxcsr _ => none
  | i => rtaint.step τ i

theorem stepMx_eq {τ : FT} {i : Instr} {τ' : FT} (h : stepMx τ i = some τ') :
    loadsMxcsr i = false ∧ rtaint.step τ i = some τ' := by
  cases i <;> first | cases h | exact ⟨rfl, h⟩

end VG.X86_64.RTaint

namespace VG.X86_64

open RTaint in
/-- The residue analysis with MXCSR the same in both runs. -/
def rtaintMx : VG.Taint isa where
  T := FT
  Agree := AgreeMx
  step := RTaint.stepMx
  step_sound ha hs e₁ e₂ := by
    obtain ⟨hl, hs⟩ := stepMx_eq hs
    obtain ⟨h₁, h₂⟩ := rtaint.step_sound ha.1 hs e₁ e₂
    exact ⟨h₁, h₂, by rw [exec_mxcsr hl e₁, exec_mxcsr hl e₂, ha.2]⟩
  condPub := rtaint.condPub
  cond_sound h := rtaint.cond_sound h.1
  meet := rtaint.meet
  meet_left h := ⟨rtaint.meet_left h.1, h.2⟩
  meet_right h := ⟨rtaint.meet_right h.1, h.2⟩
  le := rtaint.le
  le_sound hle h := ⟨rtaint.le_sound hle h.1, h.2⟩
  call := rtaint.call
  call_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := rtaint.call_sound h.1 hs e₁ e₂
    refine ⟨a, b, ?_⟩
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact h.2
  ret := rtaint.ret
  ret_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := rtaint.ret_sound h.1 hs e₁ e₂
    refine ⟨a, b, ?_⟩
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact h.2
  push := rtaint.push
  push_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := rtaint.push_sound h.1 hs e₁ e₂
    exact ⟨a, b, by rw [push_mxcsr e₁, push_mxcsr e₂, h.2]⟩
  pop := rtaint.pop
  pop_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := rtaint.pop_sound h.1 hs e₁ e₂
    exact ⟨a, b, by rw [pop_mxcsr e₁, pop_mxcsr e₂, h.2]⟩

namespace RScrub

open VG.X86_64.Taint VG.X86_64.RTaint VG.X86_64.Scrub VG.Impl.Scrub.X86_64

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- `resOk_of_check`, from the analysis with sound operations `S`. -/
theorem resOk_of_opsCheck {c : Prog isa} {ks cs : List Nat} {pubs : List (Nat × Nat × Nat)} (hA : ScrubAbi A)
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hcs : cs.sum = stack)
    {S : List (VG.Taint.Op isa FT)} (hS : VG.Taint.AllSound rtaintMx S)
    (hfit : pubsFit sig pubs = true) (hpub : PubOk (sig.contract A pre post wa stack leak) pubs)
    (hc : VG.Taint.OpsCheck rtaintMx S (init sig stack pubs) c (resOkB · stack ks cs)) :
    ResOk c (sig.contract A pre post wa stack leak) stack ks cs := by
  obtain ⟨τf, hb, hsem⟩ := hc.sound hS
  simp only [resOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨hok, hroom⟩, hdep⟩, hcov⟩ := hb
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu _ e₁ e₂ x hx hw
  obtain ⟨-, ha⟩ := hsem _ _ _ _ _ _ ⟨init_agree hA hfit hpub h₁ h₂ ho hp hu, ho.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    e₁ e₂
  have inv := ha.1 hok
  obtain ⟨hcor, -, -⟩ := hv
  have hsp : u₁.gpr .rsp = s₁.gpr .rsp := by
    obtain ⟨t', u', he', hab, -⟩ := hcor s₁ h₁
    obtain ⟨-, rfl⟩ := Exec.det e₁ he'
    exact hab.1 .rsp (by decide)
  have hwr : u₁.wr = s₁.wr := (Exec.rdwr e₁).2
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA h₁
  have hj : (x - (s₁.gpr .rsp - BitVec.ofNat 64 stack)).toNat < stack := by
    simp only [Region.Contains] at hx; omega_using [hx]
  generalize hJ : (x - (s₁.gpr .rsp - BitVec.ofNat 64 stack)).toNat = j at hj
  have hxe : x = RTaint.wa u₁ τf j := by
    simp only [RTaint.wa, wb, hroom, hsp, ← hJ, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hcj : cov ks cs j = false := by
    cases h' : cov ks cs j
    · rfl
    · exact absurd ⟨hcs ▸ hx, by rw [hcs, hJ]; exact h'⟩ hw
  have hns : ¬ InSec τf.sec j := by
    intro hin
    rcases hcov j hj with h | h
    · rw [hcj] at h; cases h
    · rw [show τf.sec.testBit j = true from hin] at h; cases h
  have hfree : ∀ r ∈ u₁.wr, ¬ r.Contains (RTaint.wa u₁ τf j) 1 := by
    intro r hr hc
    rw [hwr] at hr
    rw [← hxe] at hc
    exact (hdis r (List.mem_append_right _ hr)).2 (by omega_using [hj]) x hx hc
  have := inv.dead j (by rw [hroom, hdep]; omega_using [hj]) hns hfree
  have e2 : RTaint.wa u₂ τf j = RTaint.wa u₁ τf j := by simp only [RTaint.wa, wb, inv.rsp]
  rw [e2, ← hxe] at this
  exact this

end

/-- The residue analysis with the operations `S`, for the chunks `chunksA r.stack` of
`Impl.Scrub.X86_64.scrubSel`, from the analysis with the operations `S`
ending with every byte it may leave different in the granules `ks`. -/
theorem resOk_regOpsA {api : Api} (r : Unscrubbed api target) {pubs : List (Nat × Nat × Nat)}
    (hfit : pubsFit api.sig pubs = true) (hpub : PubOk r.contract pubs) {ks : List Nat}
    {S : List (VG.Taint.Op isa FT)} (hS : VG.Taint.AllSound rtaintMx S)
    (hc : VG.Taint.OpsCheck rtaintMx S (init api.sig r.stack pubs) r.code
      (resOkB · r.stack ks (Impl.Scrub.X86_64.chunksA r.stack)))
    (hcs : (Impl.Scrub.X86_64.chunksA r.stack).sum = r.stack) :
    ResOk r.code r.contract r.stack ks (Impl.Scrub.X86_64.chunksA r.stack) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpub
  rw [e] at hv hp ⊢
  exact resOk_of_opsCheck (ScrubAbi.of r.consts api.sig r.tables) hv hcs hS hfit hp hc

/-- `keepForOps`, for the chunks `chunksA stack` of `scrubSel`, as the runs of
granules it wipes (as `keepRuns`). -/
def keepRunsOps (sig : Sig) (stack : Nat) (code : Prog isa) (ops : List (VG.Taint.Op isa FT))
    (pubs : List (Nat × Nat × Nat) := []) : List (Nat × Nat) :=
  let ks := match VG.Taint.hintOpsA rtaintMx ops (fun _ _ => false) (fun _ _ => none) [] (init sig stack pubs) code with
    | some (τ, _) => keepOf τ.sec (Impl.Scrub.X86_64.chunksA stack)
    | none => []
  (ks.mergeSort (· ≤ ·)).foldr (fun k acc => match acc with
    | (o, m) :: rest => if k + 16 = o then (k, m + 1) :: rest else (k, 1) :: acc
    | [] => [(k, 1)]) []

/-- The granules to wipe, from the analysis with the operations `ops` (none
if it fails, which the check then rejects), as `keepFor`. -/
def keepForOps (sig : Sig) (stack : Nat) (code : Prog isa) (ops : List (VG.Taint.Op isa FT))
    (pubs : List (Nat × Nat × Nat) := []) : List Nat :=
  match VG.Taint.hintOpsA rtaintMx ops (fun _ _ => false) (fun _ _ => none) [] (init sig stack pubs) code with
  | some (τ, _) => keepOf τ.sec (chunks stack)
  | none => []

end RScrub

end VG.X86_64

/-- `keep_for_ops% sig stack code ops`: `RScrub.keepForOps sig stack code ops`,
computed in compiled code, as a literal (as `keep_for%`). -/
syntax "keep_for_ops% " term:max term:max term:max term:max : term

open Lean Elab Term Meta in
elab_rules : term
  | `(keep_for_ops% $sig $stack $code $ops) => do
  let e ← elabTerm (← `(VG.X86_64.RScrub.keepForOps $sig $stack $code $ops)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr (List Nat) (← inferType e) e
  return toExpr v
