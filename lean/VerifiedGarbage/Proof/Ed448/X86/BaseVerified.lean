import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.Framework.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.RestCT`. -/
section

/-!
# Constant time of Ed448's base-point multiplication and verification on x86 (32-bit), after their entry

Base-point multiplication and verification's equation run much of the same
field arithmetic (`Impl/Ed448/X86/ScalarBase.lean`): the doublings and
additions of the loops over the bits, and most of X448's addition chain,
which the inversion and the square root share. The kernel analyses the same
code from the same taint once within one check, so the code after the entry
block of both functions is analysed here in one check (`rest_ct`).

Their taints differ on entry (the working space is writable region 1 of one
and region 0 of the other, and their arguments differ), so each function's
entry block, which loads the pointers, is analysed on its own
(`relCT_split`), and the analysis then forgets all it knows about memory but
the arguments' first 12 bytes (`fieldτ`): the rest of both functions needs
nothing else public, as every store and load is at a public register plus a
constant, and the only loads that must be public are of the arguments.

Knowing no region, the analysis of the rest does not read the displacements
of its memory operands (but at `esp`) or its immediates
(`Framework/X86/TaintErase.lean`): the code without them (`Code.erase`), in
which the field arithmetic on different slots is the same code, is analysed
instead, and the kernel analyses each operation once.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86

/-- What the code after the entry needs public: the stack pointer, the loop
counter, the working space, and the arguments' first 12 bytes. -/
def fieldτ : VG.X86.Taint.T := { regs := .ofList [.esp, .esi, .edi], flags := false, argLen := 12 }

/-- A taint with at least what `fieldτ` has public, and no stack frames. -/
def weakOk (τ : VG.X86.Taint.T) : Bool :=
  fieldτ.regs.subset τ.regs && τ.stk == [] && Nat.ble 12 τ.argLen

theorem wf_fieldτ {τ : VG.X86.Taint.T} {s : State} (hstk : τ.stk = []) (hl : 12 ≤ τ.argLen)
    (h : VG.X86.Taint.Wf τ s) : VG.X86.Taint.Wf VG.Proof.Ed448.X86.fieldτ s := by
  obtain ⟨a1, a2⟩ := h.args (by omega)
  rw [hstk] at a1 a2
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨?_, fun r hr => ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0)⟩
  · change (s.gpr .esp).toNat + 0 + 12 ≤ 2 ^ 32
    simp only [VG.X86.Taint.depth] at a1
    omega
  · exact (a2 r hr).sub_left (Region.sub_prefix hl)
  · change (s.gpr .esp).toNat + 0 < 2 ^ 32
    have := (s.gpr .esp).isLt
    omega

/-- Two states that agree on what `τ` says is public agree on what `fieldτ`
says, if `weakOk τ`. -/
theorem agree_fieldτ {τ : VG.X86.Taint.T} {s t : State} (hw : VG.Proof.Ed448.X86.weakOk τ = true)
    (h : VG.X86.Taint.Agree τ s t) : VG.X86.Taint.Agree VG.Proof.Ed448.X86.fieldτ s t := by
  simp only [VG.Proof.Ed448.X86.weakOk, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨hr, hstk⟩, hl⟩ := hw
  have hl := Nat.le_of_ble_eq_true hl
  refine ⟨⟨fun r hr' => h.rf.1 r (RegSet.mem_of_subset hr hr'), fun h => absurd h (by decide)⟩,
    fun h => absurd rfl h, VG.Proof.Ed448.X86.wf_fieldτ hstk hl h.wf₁, VG.Proof.Ed448.X86.wf_fieldτ hstk hl h.wf₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => h.sp (by omega), fun k h4 hk => ?_⟩
  have := h.argMem k h4 (by change k < 12 at hk; omega)
  rw [hstk] at this
  exact this

/-- The entry block of code that starts with one, and the rest. -/
def head : Prog isa → Prog isa
  | .seq a _ => a
  | c => c

def tail : Prog isa → Prog isa
  | .seq _ b => b
  | _ => .block []

/-- Constant time of the entry block `head c` from `τ`, ending with at least
what `fieldτ` has public, and of the rest from `fieldτ`. -/
theorem relCT_split {P : State → State → Prop} {c : Prog isa} (hc : c = .seq (VG.Proof.Ed448.X86.head c) (VG.Proof.Ed448.X86.tail c))
    (τ : VG.X86.Taint.T) (hp : ∀ s t, P s t → VG.X86.Taint.Agree τ s t)
    {h₁ : VG.Taint.Hint VG.X86.Taint.T} (c₁ : (taint.check τ (VG.Proof.Ed448.X86.head c) h₁).any VG.Proof.Ed448.X86.weakOk = true)
    (c₂ : ∃ h₂, (taint.check VG.Proof.Ed448.X86.fieldτ (VG.Proof.Ed448.X86.tail c) h₂).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, c₂⟩ := c₂
  rw [hc]
  refine RelCT.seq ?_ (RelCT.taint (A := taint) VG.Proof.Ed448.X86.fieldτ (fun _ _ h => h) c₂)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hw⟩ : ∃ τ', taint.check τ (VG.Proof.Ed448.X86.head c) h₁ = some τ' ∧ VG.Proof.Ed448.X86.weakOk τ' = true := by
    cases e : taint.check τ (VG.Proof.Ed448.X86.head c) h₁ with
    | none => rw [e] at c₁; cases c₁
    | some τ' => rw [e] at c₁; exact ⟨τ', rfl, c₁⟩
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, VG.Proof.Ed448.X86.agree_fieldτ hw ha⟩

open Lean Meta Elab Tactic in
/-- `taint_decide` for a goal with several `Taint.check`s: computes the hint
of each (`Taint.hintOf`), and has the kernel evaluate the goal once, so that
it analyses code the checks share once. -/
elab "taint_decide_all" : tactic => do
  -- The goal of the equation; the others are the hints it assigns.
  let some g := (← getGoals).getLast? | throwError "taint_decide_all: no goals"
  for _ in [0:16] do
    let ty ← instantiateMVars (← g.getType)
    let some chk := ty.find? fun e => e.isAppOfArity ``Taint.check 5 && (e.getArg! 4).isMVar
      | break
    let args := chk.getAppArgs
    let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
    let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
    let hty := mkApp (mkConst ``Taint.Hint) tT
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
    let hint := mkApp4 (mkConst ``Taint.hintOf) m a τ c
    let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
    h.mvarId!.assign hv
  setGoals [g]
  evalTactic (← `(tactic| lit_decide))

/-- The code after the entry of both functions, without its displacements and
immediates (`Code.erase`): the field arithmetic on different slots is then
the same code. -/
def verifyRest : Prog isa := Code.erase (VG.Proof.Ed448.X86.tail Impl.Ed448.X86.verifyEquation)
def baseRest : Prog isa := Code.erase (VG.Proof.Ed448.X86.tail Impl.Ed448.X86.scalarBase)

materialize_code VG.Proof.Ed448.X86.verifyRest
materialize_code VG.Proof.Ed448.X86.baseRest

/-- The code after the entry of both functions, analysed from `fieldτ` in one
check. -/
theorem rest_ct : ∃ h₁ h₂, (Taint.hintNoBases h₁ && (taint.check VG.Proof.Ed448.X86.fieldτ VG.Proof.Ed448.X86.verifyRest h₁).isSome &&
    Taint.hintNoBases h₂ && (taint.check VG.Proof.Ed448.X86.fieldτ VG.Proof.Ed448.X86.baseRest h₂).isSome) = true := by
  refine ⟨?_, ?_, ?_⟩
  taint_decide_all

theorem verifyRest_ct : ∃ h, (taint.check VG.Proof.Ed448.X86.fieldτ (VG.Proof.Ed448.X86.tail Impl.Ed448.X86.verifyEquation) h).isSome = true := by
  obtain ⟨h₁, _, h⟩ := VG.Proof.Ed448.X86.rest_ct
  simp only [Bool.and_eq_true] at h
  refine ⟨h₁, ?_⟩
  rw [← Taint.check_erase _ _ _ rfl h.1.1.1]
  exact h.1.1.2

theorem baseRest_ct : ∃ h, (taint.check VG.Proof.Ed448.X86.fieldτ (VG.Proof.Ed448.X86.tail Impl.Ed448.X86.scalarBase) h).isSome = true := by
  obtain ⟨_, h₂, h⟩ := VG.Proof.Ed448.X86.rest_ct
  simp only [Bool.and_eq_true] at h
  refine ⟨h₂, ?_⟩
  rw [← Taint.check_erase _ _ _ rfl h.1.2]
  exact h.2

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.BaseVerified`. -/
section

/-!
# Ed448 base-point multiplication on x86 (32-bit): `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`, given that the ladder the
code computes encodes as `[k]B` (`Proof.Ed448.BaseLadderOk`, proven with the
group law in `Proof/Ed448/Facts.lean`, which only the registration file
imports). The local contract only reads the arguments; the shared one lets
the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (BaseLadderOk decodeLE_below)
open VG.Impl.Ed448.X86 (scalarBase)

theorem scalarBase_wf {s : State} (h : scalarBaseLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := BasePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarBase_agree {s t : State} (hs : scalarBaseLocal.pre s) (ht : scalarBaseLocal.pre t)
    (hp : scalarBaseLocal.pub s t) : VG.X86.Taint.Agree (scalarTaint 2 3) s t := by
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := BasePre.of hs
  have pt := BasePre.of ht
  refine scalarTaint_agree (VG.Proof.Ed448.X86.scalarBase_wf hs) (VG.Proof.Ed448.X86.scalarBase_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

/-- Constant time: the entry block from `scalarTaint 2 3`, and the rest from
`fieldτ`, in one check with verification's (`RestCT.lean`). -/
theorem scalarBase_ct :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase :=
  RelCT.constantTime (VG.Proof.Ed448.X86.relCT_split rfl (scalarTaint 2 3) (fun _ _ h => VG.Proof.Ed448.X86.scalarBase_agree h.1 h.2.1 h.2.2)
    (by taint_decide) VG.Proof.Ed448.X86.baseRest_ct)

theorem scalarBase_ok (hl : BaseLadderOk) (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := scalarBase_ladder (BasePre.of h)
  refine ⟨tr, t, he, h1, ?_⟩
  change Spec.Ed448.bytesAt t.mem _ 57 =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul _ Spec.Ed448.basePoint)
  rw [h2, hl _ (decodeLE_below (by simp [Spec.Ed448.bytesAt]))]

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def scalarBaseSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the shared contract's precondition. -/
def scalarBaseSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed448.X86.scalarBaseSatMem
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

/-- `scalarBaseLocal`, the arguments writable as the shared contract has them. -/
def scalarBaseWide : Contract isa :=
  { scalarBaseLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [scalar] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarBaseRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
def scalarBaseWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarBaseWide_pre (s : State) (h : scalarBaseWide.pre s) :
    scalarBaseLocal.pre (s.withRegions (VG.Proof.Ed448.X86.scalarBaseRd s) (VG.Proof.Ed448.X86.scalarBaseWr s)) := by
  simp only [scalarBaseLocal, VG.Proof.Ed448.X86.scalarBaseRd, VG.Proof.Ed448.X86.scalarBaseWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarBaseWide_implies :
    scalarBaseWide.Implies (Spec.Ed448.scalarBaseContract X86.abi) := by
  have a0 : arg VG.Proof.Ed448.X86.scalarBaseSat 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Ed448.X86.scalarBaseSat 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Ed448.X86.scalarBaseSat 2 = 0x4000 := by decide
  have e : argAddr VG.Proof.Ed448.X86.scalarBaseSat 0 = 0x8004 := by decide
  have esp : scalarBaseSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
    Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.scalarBaseWide, scalarBaseLocal, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, e, esp] using VG.Proof.Ed448.X86.scalarBaseSat

theorem scalarBase_verified (hl : BaseLadderOk) :
    Verified X86.target scalarBase (Spec.Ed448.scalarBaseContract X86.abi) := by
  have hsat := scalarBaseWide_implies.sat_left
  have satLocal : ∃ s, scalarBaseLocal.pre s := hsat.elim fun s h => ⟨_, VG.Proof.Ed448.X86.scalarBaseWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarBase scalarBaseLocal :=
    Verified.of_correct (VG.Proof.Ed448.X86.scalarBase_ok hl) VG.Proof.Ed448.X86.scalarBase_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal VG.Proof.Ed448.X86.scalarBaseRd VG.Proof.Ed448.X86.scalarBaseWr
    VG.Proof.Ed448.X86.scalarBaseWide_pre ?_ ?_ ?_ ?_ hsat) VG.Proof.Ed448.X86.scalarBaseWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.scalarBaseRd, VG.Proof.Ed448.X86.scalarBaseWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.scalarBaseWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [VG.Proof.Ed448.X86.scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [VG.Proof.Ed448.X86.scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86

end
