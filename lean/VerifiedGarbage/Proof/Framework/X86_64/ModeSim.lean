module

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# x86-64: code that never touches MXCSR runs the same from any MXCSR

Only `ldmxcsr` and `stmxcsr` read or write MXCSR (`TCB/X86_64/Isa.lean`).
-/

@[expose] public section

namespace VG.X86_64

/-- `ldmxcsr` and `stmxcsr`, the instructions that read or write MXCSR. -/
def touchesMxcsr : Instr → Bool
  | .ldmxcsr _ | .stmxcsr _ => true
  | _ => false

/-- `s` with MXCSR `m`. -/
abbrev State.withMx (s : State) (m : BitVec 32) : State := { s with mxcsr := m }

theorem setVy_withMx (s : State) (r : VReg) (v : BitVec 256) (m : BitVec 32) :
    (s.withMx m).setVy r v = (s.setVy r v).withMx m := by
  cases r <;> rfl

theorem setVz_withMx (s : State) (r : VReg) (l0 l1 l2 l3 : BitVec 128) (m : BitVec 32) :
    (s.withMx m).setVz r l0 l1 l2 l3 = (s.setVz r l0 l1 l2 l3).withMx m := by
  cases r <;> rfl

theorem vy_withMx (s : State) (r : VReg) (m : BitVec 32) : (s.withMx m).vy r = s.vy r := by
  cases r <;> rfl

theorem vz_withMx (s : State) (r : VReg) (i : Nat) (m : BitVec 32) : (s.withMx m).vz r i = s.vz r i := by
  cases r <;> rfl

theorem stackArg_withMx (s : State) (m : BitVec 32) (i : Nat) : stackArg (s.withMx m) i = stackArg s i := rfl

theorem eval_withMx (c : Cond) (s : State) (m : BitVec 32) : eval c (s.withMx m) = eval c s := by
  cases c <;> rfl

theorem setReg_withMx (s : State) (r : Reg) (v : BitVec 64) (m : BitVec 32) :
    (s.withMx m).setReg r v = (s.setReg r v).withMx m := rfl

theorem withMx_ite {c : Prop} [Decidable c] (a b : State) (m : BitVec 32) :
    (if c then a else b).withMx m = if c then a.withMx m else b.withMx m := by
  split <;> rfl

theorem exec_withMx {i : Instr} (hi : touchesMxcsr i = false) (s : State) (m : BitVec 32) :
    exec i (s.withMx m) = (exec i s).map (State.withMx · m) := by
  cases i <;> simp only [touchesMxcsr, Bool.true_eq_false] at hi
  all_goals first
    | rfl
    | (simp only [reduceExec, Option.map_map, Function.comp_def]; rfl)
    | (simp only [reduceExec, State.store64, State.store32, State.store16, State.store8, State.store128,
        State.store256, State.store512, State.storeMasked512, State.storeMasked512B, apply_ite (Option.map _),
        Option.map_some, Option.map_none]; rfl)
    | (simp only [reduceExec, execShift32, execShift, execRorx32, execRorx, execShld, execBtr, execMulx,
        execAdcx, execAdox, apply_ite (Option.map _), Option.map_some, Option.map_none, Option.map_map,
        Function.comp_def]; rfl)
    | skip
  case alu op _ _ | alu32 op _ _ =>
    cases op <;> simp only [reduceExec, execAlu, execAlu32, Option.map_bind, Option.map_map, Function.comp_def,
      Option.map_some] <;> rfl
  case aluTbl op _ _ _ _ =>
    cases op <;> simp only [reduceExec, execAluW, apply_ite (Option.map _), Option.map_none, Option.map_map,
      Function.comp_def, Option.map_some] <;> rfl
  case shift32 op _ _ | shift op _ _ =>
    cases op <;> simp only [reduceExec, execShift32, execShift, apply_ite (Option.map _), Option.map_none,
      Option.map_some] <;> rfl
  case xop op | zop op => simp only [reduceExec, Option.map_some]; cases op <;> rfl
  case vop op =>
    simp only [reduceExec, Option.map_some]
    cases op <;> simp only [reduceVOpExec, withMx_ite] <;> rfl
  case eop op =>
    simp only [reduceExec, Option.map_some]
    cases op <;> simp only [EOp.exec, setVy_withMx, vy_withMx] <;> rfl
  case e5op op =>
    simp only [reduceExec, Option.map_some]
    cases op <;> simp only [E5Op.exec, setVz_withMx, vz_withMx] <;> rfl
  case vmovdquLoad len _ _ | vmovdquStore len _ _ | vbinLoad _ len _ _ _ =>
    cases len <;> simp only [reduceExec, State.store128, State.store256, apply_ite (Option.map _),
      Option.map_some, Option.map_none, Option.map_map, Function.comp_def] <;> rfl
  case evLoad d _ | evMadd52Load _ d _ _ | evBroadcastLoad d _ =>
    simp only [reduceExec, Option.map_map, Function.comp_def, setVy_withMx, vy_withMx]; rfl
  case e5InsertLoad d _ _ _ =>
    simp only [reduceExec, Option.map_map, Function.comp_def, setVz_withMx]; rfl
  case cmov _ _ src =>
    cases src <;> simp only [reduceExec, execCmov, Option.map_bind, Option.map_map, Function.comp_def,
      Option.map_none, withMx_ite, eval_withMx, setReg_withMx] <;> rfl
  case mulx _ _ src | adcx _ src | adox _ src =>
    cases src <;> simp only [reduceExec, execMulx, execAdcx, execAdox, Option.map_bind, Option.map_map,
      Function.comp_def, Option.map_none] <;> rfl

theorem addrs_withMx (i : Instr) (s : State) (m : BitVec 32) : addrs i (s.withMx m) = addrs i s := by
  cases i <;> rfl

theorem pushRegs_withMx (s : State) (rs : List Reg) (m : BitVec 32) :
    pushRegs (s.withMx m) rs = (pushRegs s rs).withMx m := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    show pushRegs (({ s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr r) } : State).withMx m) rs = _
    exact ih _

theorem popReg_withMx (s : State) (r : Reg) (k : Nat) (m : BitVec 32) :
    popReg (s.withMx m) r k = (popReg s r k).withMx m := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show popReg (((s.setReg r (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8)).withMx m) r k = _
    exact ih _

theorem push_withMx (i : Instr) (s : State) (m : BitVec 32) :
    push i (s.withMx m) = (push i s).map (State.withMx · m) := by
  cases i <;> simp only [push, Option.map_none] <;>
    simp only [pushRegs_withMx, apply_ite (Option.map _), Option.map_some, Option.map_none] <;> rfl

theorem pop_withMx (i : Instr) (s₁ s₂ : State) (m₁ m₂ : BitVec 32) :
    pop i (s₁.withMx m₁) (s₂.withMx m₂) = (pop i s₁ s₂).map (State.withMx · m₂) := by
  cases i <;> simp only [pop, Option.map_none] <;>
    simp only [popReg_withMx, apply_ite (Option.map _), Option.map_some, Option.map_none] <;> rfl

theorem ret_withMx (s₁ s₂ : State) (m₁ m₂ : BitVec 32) :
    ret (s₁.withMx m₁) (s₂.withMx m₂) = (ret s₁ s₂).map (State.withMx · m₂) := by
  simp only [ret, apply_ite (Option.map _), Option.map_some, Option.map_none]
  rfl

theorem execBlock_withMx {is : List Instr} (hc : ∀ i ∈ is, touchesMxcsr i = false) {s s' : State}
    {t : List Leak} (h : execBlock isa is s = some (s', t)) (m : BitVec 32) :
    execBlock isa is (s.withMx m) = some (s'.withMx m, t) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h ⊢
    rw [h.1, h.2]; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    have hi := hc i (List.mem_cons_self ..)
    have ex := exec_withMx hi s m
    have ad := addrs_withMx i s m
    simp only [execBlock] at h ⊢
    cases he : exec i s with
    | none => rw [he] at h; cases h
    | some s₁ =>
      rw [he] at ex
      rw [he] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨u, t'⟩, h₂, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [ex, Option.map_some, ad, ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h₂]

/-- Code that never reads or writes MXCSR runs, with the same trace, from any MXCSR. -/
theorem Exec.withMx {c : Prog isa} (hc : ∀ i ∈ instrs c, touchesMxcsr i = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') (m : BitVec 32) :
    Exec isa c (s.withMx m) t (s'.withMx m) := by
  induction h with
  | block h => exact .block (execBlock_withMx hc h m)
  | seq _ _ ih₁ ih₂ =>
    exact .seq (ih₁ fun i hi => hc i (List.mem_append_left _ hi))
      (ih₂ fun i hi => hc i (List.mem_append_right _ hi))
  | iteT he _ ih =>
    exact .iteT (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withMx]; exact he)
      (ih fun i hi => hc i (List.mem_append_left _ hi))
  | iteF he _ ih =>
    exact .iteF (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withMx]; exact he)
      (ih fun i hi => hc i (List.mem_append_right _ hi))
  | loopExit _ he ih =>
    exact .loopExit (ih hc) (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withMx]; exact he)
  | loopNext _ he _ ih₁ ih₂ =>
    exact .loopNext (ih₁ hc) (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withMx]; exact he) (ih₂ hc)
  | @frame i j body s s₁ s₂ s' t hp _ hq ih =>
    have e := Exec.frame (M := isa) (i := i) (j := j)
      (show isa.push i (s.withMx m) = some (s₁.withMx m) by
        rw [show isa.push i _ = push i _ from rfl, push_withMx]
        rw [show isa.push i s = push i s from rfl] at hp; rw [hp]; rfl)
      (ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)))
      (show isa.pop j (s₁.withMx m) (s₂.withMx m) = some (s'.withMx m) by
        rw [show isa.pop j _ _ = pop j _ _ from rfl, pop_withMx]
        rw [show isa.pop j s₁ s₂ = pop j s₁ s₂ from rfl] at hq; rw [hq]; rfl)
    rwa [show isa.addrs i (s.withMx m) = isa.addrs i s from addrs_withMx i s m,
      show isa.addrs j (s₂.withMx m) = isa.addrs j s₂ from addrs_withMx j s₂ m] at e
  | @call n body s s₁ s₂ s' t hc₁ _ hr ih =>
    have hc₁' : isa.call (s.withMx m) = some (s₁.withMx m) := by
      simp only [isa, call, Option.some.injEq] at hc₁ ⊢; subst hc₁; rfl
    have hr' : isa.ret (s₁.withMx m) (s₂.withMx m) = some (s'.withMx m) := by
      rw [show isa.ret _ _ = ret _ _ from rfl, ret_withMx]
      rw [show isa.ret s₁ s₂ = ret s₁ s₂ from rfl] at hr; rw [hr]; rfl
    exact Exec.call (name := n) (s₂ := s₂.withMx m) hc₁' (ih hc) hr'
  | @icall i n body next s s₁ s₂ s' t hi hc₁ _ hr ih =>
    have hc₁' : isa.call (s.withMx m) = some (s₁.withMx m) := by
      simp only [isa, call, Option.some.injEq] at hc₁ ⊢; subst hc₁; rfl
    have hr' : isa.ret (s₁.withMx m) (s₂.withMx m) = some (s'.withMx m) := by
      rw [show isa.ret _ _ = ret _ _ from rfl, ret_withMx]
      rw [show isa.ret s₁ s₂ = ret s₁ s₂ from rfl] at hr; rw [hr]; rfl
    have hi' : isa.icall i (s.withMx m) = some (isa.fnAddr (s.withMx m) n) := by
      cases i <;> exact hi
    have e := Exec.icall (next := next) (s₂ := s₂.withMx m) hi' hc₁'
      (ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))) hr'
    rwa [show isa.addrs i (s.withMx m) = isa.addrs i s from addrs_withMx i s m] at e
  | @icallNext i n body n' body' next s s' t a ha hne _ ih =>
    have ha' : isa.icall i (s.withMx m) = some a := by cases i <;> exact ha
    exact Exec.icallNext ha' hne (ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi)))

theorem noTouch_instrs {c : Prog isa} (hc : c.allInstrs (fun i => !touchesMxcsr i) = true) :
    ∀ i ∈ instrs c, touchesMxcsr i = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  exact fun i hi => by simpa using hc i hi

/-- A callee that never touches MXCSR is constant time from public data that
agree but in MXCSR: its second run, from the first's MXCSR instead, leaks the
same (`Exec.withMx`). So a caller proves its contract's public data of the
second run's entry with the first's MXCSR, which agrees by construction. -/
theorem ConstantTime.withMx {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (hc : c.allInstrs (fun i => !touchesMxcsr i) = true) (hct : ConstantTime isa pre pub c)
    (hpre : ∀ s m, pre s → pre (s.withMx m)) :
    ConstantTime isa pre (fun a b => pub a (b.withMx a.mxcsr)) c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  exact hct s₁ (s₂.withMx s₁.mxcsr) t₁ t₂ s₁' (s₂'.withMx s₁.mxcsr) h₁ (hpre _ _ h₂) hp e₁
    (Exec.withMx (noTouch_instrs hc) e₂ _)

/-- `k`, its public data those of the second run's entry with the first's mode:
what a caller shows of a callee that never touches the mode (`Contract.ct_mxFree`). -/
def _root_.VG.Contract.mxFree (k : Contract isa) : Contract isa :=
  { k with pub := fun a b => k.pub a (b.withMx a.mxcsr) }

theorem _root_.VG.Contract.ct_mxFree {k : Contract isa} {c : Prog isa} (hc : c.allInstrs (fun i => !touchesMxcsr i) = true)
    (hct : ConstantTime isa k.pre k.pub c) (hpre : ∀ s m, k.pre s → k.pre (s.withMx m)) :
    ConstantTime isa k.mxFree.pre k.mxFree.pub c :=
  ConstantTime.withMx hc hct hpre

/-- Constant time against public data with the mode, for code that never
touches it, is constant time against public data without it. -/
theorem ConstantTime.dropMx {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (hc : c.allInstrs (fun i => !touchesMxcsr i) = true) (hct : ConstantTime isa pre (fun a b => pub a b ∧ a.mxcsr = b.mxcsr) c)
    (hpre : ∀ s m, pre s → pre (s.withMx m)) (hpub : ∀ a b, pub a b → pub a (b.withMx a.mxcsr)) :
    ConstantTime isa pre pub c := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
  ConstantTime.withMx hc hct hpre s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨hpub _ _ hp, rfl⟩ e₁ e₂

end VG.X86_64
