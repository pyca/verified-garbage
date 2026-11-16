module

public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# Public scalar values held in vector registers

Memory remains secret. DUP can preserve a public GPR in a whole vector,
and UMOV recovers a public scalar from a public vector. ADD and SUB preserve
publicity when both input vectors are public. Other SIMD
operations and vector loads conservatively erase all vector publicity.
-/

@[expose] public section

namespace VG.AArch64.VectorTaint

instance : RegIdx VReg := ⟨VReg.ctorIdx, fun {a b} h => by
  rw [← VReg.ofNat_ctorIdx a, h, VReg.ofNat_ctorIdx]⟩

abbrev T := Taint.T × RegSet VReg

def ofRegs (rs : List Reg) : T := (Taint.ofRegs rs, RegSet.ofList [])

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  Taint.Agree τ.1 s₁ s₂ ∧ ∀ v ∈ τ.2, s₁.v v = s₂.v v

def setV (τ : RegSet VReg) (v : VReg) (p : Bool) : RegSet VReg :=
  if p then τ.insert v else τ.erase v

/-- Instructions that leave every vector register unchanged. -/
def scalar : Instr → Bool
  | .vop _ | .ldrq .. | .ldrqTbl .. | .umov .. => false
  | _ => true

def afterV (τ : RegSet VReg) (i : Instr) : RegSet VReg :=
  if scalar i then τ else RegSet.ofList []

def step (τ : T) : Instr → Option T
  | .vop (.dup _ d n) => some (τ.1, setV τ.2 d (Taint.pub τ.1 n))
  | .vop (.add _ d n m) | .vop (.sub _ d n m) =>
    some (τ.1, setV τ.2 d (τ.2.mem n && τ.2.mem m))
  | .umov _ d n _ => some (Taint.set τ.1 d (τ.2.mem n), τ.2)
  -- Words of a table of constants, the same in every run: public. Its
  -- offset in the table, an immediate, is observed.
  | .ldrqTbl t .. => some (τ.1, setV τ.2 t true)
  | i => (Taint.step τ.1 i).map (fun g => (g, afterV τ.2 i))

private theorem scalar_vectors {i : Instr} {s s' : State}
    (hi : scalar i = true) (he : exec i s = some s') : s'.v = s.v := by
  cases i <;> simp only [scalar, Bool.false_eq_true] at hi
  case ldp => obtain ⟨_, _, rfl⟩ := exec_ldp_eq he; rfl
  case stp => obtain ⟨_, rfl⟩ := exec_stp_eq he; rfl
  all_goals
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  all_goals
    repeat' first
      | split at he
      | simp only [Option.map_eq_some_iff] at he
      | rcases he with ⟨_, _, he⟩
  all_goals
    simp_all only [State.store]
  all_goals
    repeat' first | split at he | cases he
  all_goals rfl

private theorem vectors_set {τ : RegSet VReg} {s₁ s₂ : State}
    (h : ∀ v ∈ τ, s₁.v v = s₂.v v) (d : VReg) {p : Bool} {x₁ x₂ : BitVec 128}
    (hx : p = true → x₁ = x₂) :
    ∀ v ∈ setV τ d p, (s₁.setV d x₁).v v = (s₂.setV d x₂).v v := by
  intro v hv
  unfold setV at hv
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hv
    by_cases hd : v = d
    · simp only [RegUpd.v_setV, hd, ite_true, hx hp]
    · simp only [RegUpd.v_setV, ite_eq_right hd, h v (hv.resolve_left hd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hv
    simp only [RegUpd.v_setV, ite_eq_right hv.1, h v hv.2]

private theorem ordinary_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂)
    (hs : (Taint.step τ.1 i).map (fun g => (g, afterV τ.2 i)) = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
  have h := Taint.step_sound ha.1 hg e₁ e₂
  refine ⟨h.1, h.2, ?_⟩
  intro v hv
  unfold afterV at hv
  split at hv
  · rw [scalar_vectors (by assumption) e₁, scalar_vectors (by assumption) e₂]
    exact ha.2 v hv
  · simp only [RegSet.mem_ofList, List.not_mem_nil] at hv

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | vop op =>
    cases op <;> try exact ordinary_sound ha hs e₁ e₂
    case dup a d n =>
      simp only [step, Option.some.injEq] at hs; subst hs
      cases a <;> simp only [reduceExec, reduceVOpEval, Option.map_some, Option.some.injEq] at e₁ e₂
      all_goals
        subst e₁; subst e₂
        refine ⟨rfl, ⟨ha.1.1, ha.1.2⟩, vectors_set ha.2 d ?_⟩
        intro hp; rw [ha.1.reg hp]
    case add a d n m =>
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [reduceExec, reduceVOpEval, Option.map_some, Option.some.injEq] at e₁ e₂
      subst e₁; subst e₂
      refine ⟨rfl, ⟨ha.1.1, ha.1.2⟩, vectors_set ha.2 d ?_⟩
      intro hp
      simp only [Bool.and_eq_true] at hp
      rw [ha.2 n hp.1, ha.2 m hp.2]
    case sub a d n m =>
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [reduceExec, reduceVOpEval, Option.map_some, Option.some.injEq] at e₁ e₂
      subst e₁; subst e₂
      refine ⟨rfl, ⟨ha.1.1, ha.1.2⟩, vectors_set ha.2 d ?_⟩
      intro hp
      simp only [Bool.and_eq_true] at hp
      rw [ha.2 n hp.1, ha.2 m hp.2]
  | umov sz d n k =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hk
    simp only [hk, ite_true, Option.some.injEq] at e₁ e₂
    subst e₁; subst e₂
    refine ⟨rfl, ha.1.write sz d (fun hp => ?_), fun v hv => ha.2 v hv⟩
    rw [ha.2 n hp]
  | ldrqTbl t n off name ws =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, ⟨ha.1.1, ha.1.2⟩, vectors_set ha.2 t fun _ => rfl⟩
  | _ =>
    exact ordinary_sound ha hs e₁ e₂

/-! ## The step the kernel evaluates

`stepK` is `step` (`stepK_eq`), as `Taint.stepK` is `Taint.step`
(`Proof/Framework/AArch64/Taint.lean`): a function of the instruction first,
with its cases closed (`inline_match%`), which gives a taint whose set the
instruction writes is evaluated (`RegSet.force`) and whose other set is the
term it was, in a pair whose types are written the same in every case
(`RegSet Reg`, not `Taint.T`), so that equal taints are the same term. The
kernel then finds again every step it has made of the same instruction from
the same taint. -/

/-- What an instruction does to a taint, as a function of its two sets. -/
structure Step where
  run : RegSet Reg → RegSet VReg → Option T

/-- An instruction `step` leaves to `Taint.step`, `s` being its `Taint.stepFn`:
the general-purpose registers by `s`, evaluated, and the vector registers
kept (`true`: the instruction is `scalar`) or none public. -/
def ordinary (s : Taint.Step) : Bool → Step
  | true => ⟨fun g v => Taint.forceO (s.run g) fun g' => some (@Prod.mk (RegSet Reg) (RegSet VReg) g' v)⟩
  | false => ⟨fun g _ => Taint.forceO (s.run g) fun g' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg) g' ⟨nat_lit 0⟩)⟩

/-- `step` of a vector instruction. -/
def vopFn : VOp → Step
  | .dup _ d n => ⟨fun g v => (setV v d (Taint.pub g n)).force fun v' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg) g v')⟩
  | .add _ d n m | .sub _ d n m => ⟨fun g v => (setV v d (v.mem n && v.mem m)).force fun v' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg) g v')⟩
  | _ => ⟨fun g _ => some (@Prod.mk (RegSet Reg) (RegSet VReg) g ⟨nat_lit 0⟩)⟩

/-- `vopFn`, with its cases closed (`inline_match%`). -/
def vopFnK : VOp → Step := inline_match% vopFn

theorem vopFnK_eq (op : VOp) : vopFnK op = vopFn op := by cases op <;> rfl

/-- `step`, as a function of the instruction first. -/
def stepFn : Instr → Step
  | .vop op => vopFnK op
  | .umov _ d n _ => ⟨fun g v => (Taint.set g d (v.mem n)).force fun g' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg) g' v)⟩
  | .ldrqTbl t .. => ⟨fun g v => (setV v t true).force fun v' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg) g v')⟩
  | i => ordinary (Taint.stepFn i) (scalar i)

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → Step := inline_match% stepFn Taint.stepFn scalar ordinary

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

theorem ordinary_run (s : Taint.Step) (b : Bool) (g : RegSet Reg) (v : RegSet VReg) :
    (ordinary s b).run g v = (s.run g).map fun g' => (g', if b then v else RegSet.ofList []) := by
  cases b <;> simp only [ordinary, Taint.forceO_eq] <;> cases s.run g <;> rfl

theorem ordinary_step (i : Instr) (g : RegSet Reg) (v : RegSet VReg)
    (h : stepFn i = ordinary (Taint.stepFn i) (scalar i))
    (h' : step (g, v) i = (Taint.step g i).map fun g' => (g', afterV v i)) :
    (stepFn i).run g v = step (g, v) i := by
  rw [h, h', ordinary_run]; rfl

/-- `step`, giving a taint that is evaluated. -/
def stepK (τ : T) (i : Instr) : Option T :=
  match τ with
  | (g, v) => (stepFnK i).run g v

theorem stepK_eq : stepK = step := by
  funext ⟨g, v⟩ i
  show (stepFnK i).run g v = step (g, v) i
  rw [stepFnK_eq]
  cases i with
  | vop op =>
    show (vopFnK op).run g v = _
    rw [vopFnK_eq]; cases op <;> rfl
  | umov | ldrqTbl => rfl
  | _ => exact ordinary_step _ g v rfl rfl

def taint : VG.Taint isa where
  T := T
  Agree := Agree
  step := stepK
  step_sound h hs := step_sound h ((congrFun (congrFun stepK_eq _) _).symm.trans hs)
  condPub τ := Taint.condPub τ.1
  cond_sound h hc := Taint.cond_sound h.1 hc
  meet τ σ := (τ.1.inter σ.1, τ.2.inter σ.2)
  meet_left h := ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).1⟩,
    fun v hv => h.2 v (RegSet.mem_inter.mp hv).1⟩
  meet_right h := ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).2⟩,
    fun v hv => h.2 v (RegSet.mem_inter.mp hv).2⟩
  le τ σ := τ.1.subset σ.1 && τ.2.subset σ.2
  le_sound hl h := by
    simp only [Bool.and_eq_true] at hl
    obtain ⟨hg, hv⟩ := hl
    exact ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_of_subset hg hr)⟩,
      fun v hr => h.2 v (RegSet.mem_of_subset hv hr)⟩
  call τ := (VG.AArch64.taint.call τ.1).map (fun g => (g, τ.2))
  call_sound h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := VG.AArch64.taint.call_sound h.1 hg e₁ e₂
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁; subst e₂
    exact ⟨ht.1, ht.2, h.2⟩
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  push τ i := (Taint.push τ.1 i).map (fun g => (g, τ.2))
  push_sound {τ τ' i s₁ s₂ s₁' s₂'} h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := Taint.push_sound h.1 hg e₁ e₂
    cases i <;> simp only [Taint.push, reduceCtorEq] at hg
    all_goals
      simp only [isa, push] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      exact ⟨ht.1, ht.2, h.2⟩
  pop τ i := (Taint.pop τ.1 i).map (fun g => (g, τ.2))
  pop_sound {τ τ' i a₁ a₂ b₁ b₂ c₁ c₂} h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := Taint.pop_sound h.1 hg e₁ e₂
    cases i <;> simp only [Taint.pop, reduceCtorEq] at hg
    all_goals
      simp only [isa, pop] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      exact ⟨ht.1, ht.2, h.2⟩

/-- The step of `taint` is `step`, for the proofs about it: the kernel
evaluates `stepK`. -/
theorem taint_step (τ : T) (i : Instr) : taint.step τ i = step τ i :=
  congrFun (congrFun stepK_eq τ) i

end VG.AArch64.VectorTaint
