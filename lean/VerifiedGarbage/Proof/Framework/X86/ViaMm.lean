module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.ViaMm.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# x86 (32-bit): calls of functions by addresses held in MMX registers

PROTOTYPE (local). `Code.viaMm ld fs c` is `c` with each call of a function
`n` that `fs` maps to an MMX register `r` made a call by the address in the
low 32 bits of `r`: `ld r` (which puts them in `eax`), then `call eax`, one
candidate. Where each such register holds its function's address (`MmOk`)
and `c` runs no MMX instruction, so that they still do at each call, each run
of `c` is one of `c` made so, from the same state to the same state: the
callee is entered from the state the direct call does, `eax` aside, which the
callee's first instruction overwrites (`Kills`).
-/

@[expose] public section

namespace VG.X86

open VG.Impl.ViaMm.X86

/-- Each register of `fs` holds its function's address, inside an MMX frame. -/
def MmOk (fs : List (String × MReg)) (s : State) : Prop :=
  s.mmx = true ∧ ∀ p ∈ fs, (s.mm p.2).extractLsb' 0 32 = s.syms p.1

/-- An instruction that changes no MMX register and does not enter or leave
an MMX frame. -/
def Instr.mmFree : Instr → Bool
  | .mop _ | .mmxEnter | .emms => false
  | _ => true

/-! ## Entering a callee with another `eax` -/

/-- An instruction that overwrites `eax` without reading it. -/
def Instr.killsEax : Instr → Bool
  | .mov .eax (.imm _) => true
  | .mov .eax (.mem m) => m.base != .eax
  | _ => false

/-- Code whose first instruction overwrites `eax` without reading it. -/
def Code.kills : Prog isa → Bool
  | .block (i :: _) => i.killsEax
  | .seq a _ => Code.kills a
  | _ => false

/-- Code each of whose calls of a function of `fs` enters code that `kills`. -/
def Code.callsKill (fs : List (String × MReg)) : Prog isa → Bool
  | .block _ => true
  | .seq a b | .ite _ a b => callsKill fs a && callsKill fs b
  | .loop b _ => callsKill fs b
  | .call m b => ((fs.lookup m).isNone || Code.kills b) && callsKill fs b
  | .frame _ b _ => callsKill fs b
  | .icall .. => true

theorem setReg_setReg_self (s : State) (r : Reg) (x v : BitVec 32) :
    (s.setReg r x).setReg r v = s.setReg r v := by
  simp only [State.setReg]; congr 1; funext r'; split <;> rfl

theorem readSrc_setReg_eax {src : Src} (h : ∀ m, src = .mem m → m.base ≠ .eax) (hr : src ≠ .reg .eax)
    (s : State) (x : BitVec 32) :
    readSrc (s.setReg .eax x) src = readSrc s src ∧ srcAddrs (s.setReg .eax x) src = srcAddrs s src := by
  cases src with
  | reg r =>
    have : r ≠ .eax := fun e => hr (by rw [e])
    simp only [readSrc, srcAddrs, State.setReg, this, ↓reduceIte, and_self]
  | imm v => exact ⟨rfl, rfl⟩
  | mem m =>
    have he : (s.setReg .eax x).ea m = s.ea m := by
      simp only [State.ea, State.setReg, h m rfl, ↓reduceIte]
    exact ⟨by show (s.setReg .eax x).load32 _ = s.load32 _; rw [he]; rfl,
      by simp only [srcAddrs, he]⟩

theorem killsEax_exec {i : Instr} (h : i.killsEax = true) (s : State) (x : BitVec 32) :
    exec i (s.setReg .eax x) = exec i s ∧ addrs i (s.setReg .eax x) = addrs i s := by
  match i, h with
  | .mov .eax (.imm v), _ =>
    simp only [exec, readSrc, Option.map_some, addrs, srcAddrs, setReg_setReg_self, and_self]
  | .mov .eax (.mem m), h =>
    have hb : m.base ≠ .eax := by simpa [Instr.killsEax] using h
    obtain ⟨hr, ha⟩ := readSrc_setReg_eax (src := .mem m) (fun _ e => by cases e; exact hb) (by simp) s x
    refine ⟨?_, by simp only [addrs]; exact ha⟩
    simp only [exec, hr]
    cases readSrc s (.mem m) with
    | none => rfl
    | some v => simp only [Option.map_some, setReg_setReg_self]

theorem execBlock_killsEax {i : Instr} {is : List Instr} (h : i.killsEax = true) (s : State) (x : BitVec 32) :
    execBlock isa (i :: is) (s.setReg .eax x) = execBlock isa (i :: is) s := by
  obtain ⟨he, ha⟩ := killsEax_exec h s x
  simp only [execBlock, he, ha]

/-- **Code that overwrites `eax` first runs the same whatever `eax` held.** -/
theorem Exec.kills {c : Prog isa} (hk : Code.kills c = true) {s s' : State} {t : List Leak} (x : BitVec 32) :
    Exec isa c (s.setReg .eax x) t s' ↔ Exec isa c s t s' := by
  induction c generalizing s s' t with
  | block is =>
    match is, hk with
    | i :: is, hk =>
      constructor
      · intro e; cases e with
        | block h => exact Exec.block (by rw [← execBlock_killsEax hk s x]; exact h)
      · intro e; cases e with
        | block h => exact Exec.block (by rw [execBlock_killsEax hk s x]; exact h)
  | seq a b iha _ =>
    simp only [Code.kills] at hk
    constructor
    · intro e; cases e with
      | seq e₁ e₂ => exact Exec.seq ((iha hk).mp e₁) e₂
    · intro e; cases e with
      | seq e₁ e₂ => exact Exec.seq ((iha hk).mpr e₁) e₂
  | _ => simp only [Code.kills, Bool.false_eq_true] at hk

/-! ## The direct call and the call by `eax` -/

theorem call_setReg_eax {s s₁ : State} (h : isa.call s = some s₁) (x : BitVec 32) :
    isa.call (s.setReg .eax x) = some (s₁.setReg .eax x) := by
  simp only [isa, call, Option.some.injEq] at h ⊢
  subst h
  cases s
  simp only [State.setReg, State.mk.injEq, and_true, reduceCtorEq, ↓reduceIte]
  funext r
  by_cases h1 : r = .esp
  · subst h1; simp
  · by_cases h2 : r = .eax
    · subst h2; simp
    · simp [h1, h2]

/-! ## MMX registers along a run -/

/-- The MMX state of a state. -/
abbrev mmOf (s : State) : (MReg → BitVec 64) × Bool := (s.mm, s.mmx)

theorem exec_mm {i : Instr} (hi : i.mmFree = true) {s s' : State} (h : exec i s = some s') :
    mmOf s' = mmOf s := by
  cases i with
  | store m r | store8 m r | movdquStore m r | movqStore m r =>
    simp only [exec, State.store32, State.store8, State.store128, State.store64] at h
    split at h <;> cases h; rfl
  | mov _ _ | movzx8 _ _ | movdquLoad _ _ | movqLoad _ _ =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | xop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [SseTaint.XOp.exec_eq op s]
  | mop op => simp only [Instr.mmFree, Bool.false_eq_true] at hi
  | mmxStore m r =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    simp only [State.store64] at h
    split at h <;> cases h; rfl
  | symPush | push | pop | alloc | free | callr | mmxEnter | emms | mcdtEnter | mcdtLeave =>
    simp only [exec, reduceCtorEq] at h
  | pmuludq | movdquTbl | movqTbl | mmxMovd =>
    simp only [exec] at h
    split at h <;> cases h; rfl
  | _ => simp only [exec, Option.some.injEq] at h; subst h; rfl

theorem execBlock_mm : ∀ {is : List Instr}, (∀ i ∈ is, i.mmFree = true) → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → mmOf s' = mmOf s
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, hi, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_mm (fun j hj => hi j (List.mem_cons_of_mem _ hj)) h₂).trans
        (exec_mm (hi i (List.mem_cons_self ..)) e)

theorem call_mm {s s₁ : State} (h : isa.call s = some s₁) : mmOf s₁ = mmOf s := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_mm {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : mmOf s' = mmOf s₂ := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

theorem pushRegs_mm (t : State) (rs : List Reg) : mmOf (pushRegs t rs) = mmOf t := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans rfl

theorem push_mm {i : Instr} (hi : i.mmFree = true) {s s' : State} (h : push i s = some s') :
    mmOf s' = mmOf s := by
  cases i <;> simp only [Instr.mmFree, Bool.false_eq_true] at hi <;>
    simp only [push, reduceCtorEq] at h <;> split at h <;> cases h <;> first | rfl | exact pushRegs_mm _ _

theorem pop_mm {j : Instr} (hj : j.mmFree = true) {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') :
    mmOf s' = mmOf s₂ := by
  have hp : ∀ (k : Nat) (r : Reg) (t : State), mmOf (popReg t r k) = mmOf t := by
    intro k; induction k with
    | zero => intro r t; rfl
    | succ k ih => intro r t; exact (ih _ _).trans rfl
  cases j <;> simp only [Instr.mmFree, Bool.false_eq_true] at hj <;>
    simp only [pop, reduceCtorEq] at h <;> split at h <;> cases h <;> first | rfl | exact hp _ _ _

/-- **Code that runs no MMX instruction keeps the MMX registers**, its
callees' included. -/
theorem Exec.mm {c : Prog isa} (hc : ∀ i ∈ instrs c, i.mmFree = true) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : mmOf s' = mmOf s := by
  induction h with
  | icall _ e₁ _ e₂ ih =>
    exact (ret_mm e₂).trans ((ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))).trans
      (call_mm e₁))
  | icallNext _ _ _ ih => exact ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))
  | block e => exact execBlock_mm hc e
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ fun i hi => hc i (List.mem_append_right _ hi)).trans
      (ih₁ fun i hi => hc i (List.mem_append_left _ hi))
  | iteT _ _ ih => exact ih fun i hi => hc i (List.mem_append_left _ hi)
  | iteF _ _ ih => exact ih fun i hi => hc i (List.mem_append_right _ hi)
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => exact (ih₂ hc).trans (ih₁ hc)
  | call e₁ _ e₂ ih => exact (ret_mm e₂).trans ((ih hc).trans (call_mm e₁))
  | frame e₁ _ e₂ ih =>
    exact (pop_mm (hc _ (by simp [instrs])) e₂).trans ((ih fun i hi => hc i (by simp [instrs, hi])).trans
      (push_mm (hc _ (by simp [instrs])) e₁))

theorem MmOk.of {fs : List (String × MReg)} {s s' : State} (h : MmOk fs s) (hm : mmOf s' = mmOf s)
    (hy : s'.syms = s.syms) : MmOk fs s' := by
  simp only [mmOf, Prod.mk.injEq] at hm
  exact ⟨hm.2 ▸ h.1, fun p hp => by rw [hm.1, hy]; exact h.2 p hp⟩

/-! ## Runs of the code are runs of the code made so -/

theorem lookup_mem' : ∀ {fs : List (String × MReg)} {m : String} {r : MReg}, fs.lookup m = some r → (m, r) ∈ fs
  | [], _, _, h => by simp at h
  | (a, b) :: fs, m, r, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he; simp only [Option.some.injEq] at h; subst h
      simp only [beq_iff_eq] at he; subst he; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem' h)

theorem call_syms' {s s₁ : State} (h : isa.call s = some s₁) : s₁.syms = s.syms := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem call_some (s : State) : ∃ s₁, isa.call s = some s₁ := ⟨_, rfl⟩

theorem ret_setReg_eax (s₁ s₂ : State) (x : BitVec 32) : isa.ret (s₁.setReg .eax x) s₂ = isa.ret s₁ s₂ := by
  simp only [isa, ret, State.setReg, reduceCtorEq, ↓reduceIte]

theorem MmOk.call {fs : List (String × MReg)} {s s₁ : State} (h : MmOk fs s) (hc : isa.call s = some s₁) :
    MmOk fs s₁ := h.of (call_mm hc) (call_syms' hc)

theorem MmOk.exec {fs : List (String × MReg)} {c : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') (hc : ∀ i ∈ instrs c, i.mmFree = true) (h : MmOk fs s) : MmOk fs s' :=
  h.of (Exec.mm hc e) (Exec.syms e)

theorem MmOk.push {fs : List (String × MReg)} {i : Instr} (hi : i.mmFree = true) {s s₁ : State}
    (hp : isa.push i s = some s₁) (h : MmOk fs s) : MmOk fs s₁ := h.of (push_mm hi hp) (push_syms hp)

theorem MmOk.addr {fs : List (String × MReg)} {s : State} (h : MmOk fs s) {m : String} {r : MReg}
    (hl : fs.lookup m = some r) : (s.mm r).extractLsb' 0 32 = s.syms m :=
  h.2 (m, r) (lookup_mem' hl)

theorem movd_run {s : State} (h : s.mmx = true) (r : MReg) :
    execBlock isa [.mmxMovd .eax r] s = some (s.setReg .eax ((s.mm r).extractLsb' 0 32), []) := by
  simp only [execBlock, isa, exec, h, ↓reduceIte, addrs, List.map_nil]; rfl

theorem kills_viaMm (fs : List (String × MReg)) : ∀ c : Prog isa, Code.kills (Code.viaMm fs c) = Code.kills c
  | .block _ => rfl
  | .seq a _ => by simp only [Code.viaMm, Code.kills]; exact kills_viaMm fs a
  | .ite .. | .loop .. | .frame .. | .icall .. => rfl
  | .call m b => by
    simp only [Code.viaMm]; split <;> rfl

/-- The run of `callVia (movd eax, r) m b'` from a run of the call. -/
theorem Exec.toCallVia {fs : List (String × MReg)} {m : String} {r : MReg} {b : Prog isa} {s s₁ s₂ s' : State}
    {t : List Leak} (hd : MmOk fs s) (hl : fs.lookup m = some r) (hk : Code.kills b = true)
    (hc : isa.call s = some s₁) (e : Exec isa b s₁ t s₂) (hr : isa.ret s₁ s₂ = some s') :
    ∃ t', Exec isa (Impl.ViaMm.X86.callVia r m b) s t' s' := by
  have ha := hd.addr hl
  have hi : isa.icall (.callr .eax) (s.setReg .eax ((s.mm r).extractLsb' 0 32)) =
      some (isa.fnAddr (s.setReg .eax ((s.mm r).extractLsb' 0 32)) m) := by
    show some (((s.setReg .eax _).gpr .eax).setWidth 64) = some ((s.syms m).setWidth 64)
    simp only [State.setReg, ↓reduceIte, ha]
  have e' := Exec.seq (Exec.block (movd_run hd.1 r))
    (Exec.icall (next := .block []) hi (call_setReg_eax hc _) ((Exec.kills hk _).mpr e)
      (by rw [ret_setReg_eax]; exact hr))
  exact ⟨_, e'⟩

/-- **A run of `c` is a run of `c` made to call by the MMX registers**, from and
to the same states. -/
theorem Exec.toMm {fs : List (String × MReg)} {c : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') (hv : ∀ i ∈ instrs c, i.mmFree = true) (hk : Code.callsKill fs c = true)
    (hd : MmOk fs s) : ∃ t', Exec isa (Code.viaMm fs c) s t' s' := by
  induction e with
  | block h => exact ⟨_, Exec.block h⟩
  | @seq a b _ _ _ _ _ e₁ e₂ ih₁ ih₂ =>
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    have hv₁ : ∀ i ∈ instrs a, i.mmFree = true := fun i hi => hv i (List.mem_append_left _ hi)
    have hv₂ : ∀ i ∈ instrs b, i.mmFree = true := fun i hi => hv i (List.mem_append_right _ hi)
    obtain ⟨_, e₁'⟩ := ih₁ hv₁ hk.1 hd
    obtain ⟨_, e₂'⟩ := ih₂ hv₂ hk.2 (MmOk.exec e₁ hv₁ hd)
    exact ⟨_, Exec.seq e₁' e₂'⟩
  | iteT hc _ ih =>
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    obtain ⟨_, e'⟩ := ih (fun i hi => hv i (List.mem_append_left _ hi)) hk.1 hd
    exact ⟨_, Exec.iteT hc e'⟩
  | iteF hc _ ih =>
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    obtain ⟨_, e'⟩ := ih (fun i hi => hv i (List.mem_append_right _ hi)) hk.2 hd
    exact ⟨_, Exec.iteF hc e'⟩
  | loopExit _ hc ih =>
    obtain ⟨_, e'⟩ := ih hv hk hd
    exact ⟨_, Exec.loopExit e' hc⟩
  | loopNext e₁ hc _ ih₁ ih₂ =>
    obtain ⟨_, e₁'⟩ := ih₁ hv hk hd
    obtain ⟨_, e₂'⟩ := ih₂ hv hk (MmOk.exec e₁ hv hd)
    exact ⟨_, Exec.loopNext e₁' hc e₂'⟩
  | @call m b _ _ _ _ _ hc _ hr ih =>
    simp only [Code.callsKill, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hk
    obtain ⟨_, e'⟩ := ih hv hk.2 (hd.call hc)
    cases hl : fs.lookup m with
    | none => exact ⟨_, by simp only [Code.viaMm, hl]; exact Exec.call hc e' hr⟩
    | some r =>
      have hkb : Code.kills b = true := hk.1.resolve_left (by rw [hl]; simp)
      obtain ⟨_, e''⟩ := Exec.toCallVia hd hl (by rw [kills_viaMm]; exact hkb) hc e' hr
      exact ⟨_, by simp only [Code.viaMm, hl]; exact e''⟩
  | @frame i j b _ _ _ _ _ hp _ hq ih =>
    obtain ⟨_, e'⟩ := ih (fun i hi => hv i (by simp [instrs, hi])) hk (hd.push (hv i (by simp [instrs])) hp)
    exact ⟨_, Exec.frame hp e' hq⟩
  | icall h₁ h₂ e h₃ _ => exact ⟨_, Exec.icall h₁ h₂ e h₃⟩
  | icallNext h₁ h₂ e _ => exact ⟨_, Exec.icallNext h₁ h₂ e⟩

/-! ## Where a run's leaks end -/

/-- Whether code makes no indirect call. -/
def Code.icallFree : Prog isa → Bool
  | .block _ => true
  | .seq a b => icallFree a && icallFree b
  | .ite _ a b => icallFree a && icallFree b
  | .loop b _ => icallFree b
  | .call _ b => icallFree b
  | .frame _ b _ => icallFree b
  | .icall .. => false

/-- How many addresses an instruction leaks does not depend on the state. -/
theorem addrs_length (i : Instr) (s₁ s₂ : State) : (addrs i s₁).length = (addrs i s₂).length := by
  cases i <;> (try cases ‹Src›) <;> (try cases ‹MOp›) <;> (try cases ‹MSrc›) <;>
    simp [addrs, srcAddrs, MOp.addrs, MSrc.addrs]

theorem isa_addrs_length (i : Instr) (s₁ s₂ : State) :
    (isa.addrs i s₁).length = (isa.addrs i s₂).length := addrs_length i s₁ s₂

theorem execBlock_length {is : List Instr} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : execBlock isa is s₁ = some (s₁', t₁)) (h₂ : execBlock isa is s₂ = some (s₂', t₂)) :
    t₁.length = t₂.length := by
  induction is generalizing s₁ s₂ s₁' s₂' t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2]
  | cons i is ih =>
    simp only [execBlock] at h₁ h₂
    split at h₁ <;> rename_i heq₁
    · cases h₁
    split at h₂ <;> rename_i heq₂
    · cases h₂
    obtain ⟨⟨a₁, r₁⟩, ha₁, e₁⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨⟨a₂, r₂⟩, ha₂, e₂⟩ := Option.map_eq_some_iff.mp h₂
    simp only [Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2, List.length_append, List.length_append, List.length_map, List.length_map,
      isa_addrs_length i _ s₂, ih ha₁ ha₂]

/-- Of two lists made of parts of the same lengths, equal, the parts are. -/
theorem append3_inj {a₁ a₂ b₁ b₂ c₁ c₂ u₁ u₂ : List Leak} (ha : a₁.length = a₂.length)
    (hb : ∀ {v₁ v₂ : List Leak}, b₁ ++ v₁ = b₂ ++ v₂ → b₁ = b₂) (hc : c₁.length = c₂.length)
    (h : a₁ ++ b₁ ++ c₁ ++ u₁ = a₂ ++ b₂ ++ c₂ ++ u₂) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ u₁ = u₂ := by
  simp only [List.append_assoc] at h
  obtain ⟨rfl, h⟩ := List.append_inj h ha
  have h := List.append_cancel_left h
  have hB := hb h
  subst hB
  obtain ⟨rfl, rfl⟩ := List.append_inj (List.append_cancel_left h) hc
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **What a run of code without indirect calls leaks tells where it ends**:
of two runs, whose leaks followed by others are the same, the two leak the
same. -/
theorem Exec.prefix {c : Prog isa} (hc : Code.icallFree c = true) {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') {u₁ u₂ : List Leak} (h : t₁ ++ u₁ = t₂ ++ u₂) :
    t₁ = t₂ := by
  induction e₁ generalizing s₂ s₂' t₂ u₁ u₂ with
  | block h₁ =>
    cases e₂ with
    | block h₂ => exact (List.append_inj h (execBlock_length h₁ h₂)).1
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | seq f₁ f₂ =>
      rw [List.append_assoc, List.append_assoc] at h
      have ha := ih₁ hc.1 f₁ h
      rw [ha] at h
      rw [ha, ih₂ hc.2 f₂ (List.append_cancel_left h)]
  | iteT _ _ ih =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ f => simp only [List.cons_append, List.cons.injEq, true_and] at h; rw [ih hc.1 f h]
    | iteF _ _ => simp only [List.cons_append, List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
  | iteF _ _ ih =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ _ => simp only [List.cons_append, List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
    | iteF _ f => simp only [List.cons_append, List.cons.injEq, true_and] at h; rw [ih hc.2 f h]
  | loopExit _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | loopExit f _ =>
      simp only [List.append_assoc, List.singleton_append] at h
      rw [ih hc f h]
    | loopNext f _ _ =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, Leak.branch.injEq] at h
      exact absurd h.1 (by decide)
  | loopNext _ _ _ ih₁ ih₂ =>
    have hc' := hc
    simp only [Code.icallFree] at hc
    cases e₂ with
    | loopExit f _ =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih₁ hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, Leak.branch.injEq] at h
      exact absurd h.1 (by decide)
    | loopNext f _ f' =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih₁ hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at h
      rw [hb, ih₂ hc' f' h]
  | call _ _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | call _ f _ =>
      obtain ⟨h1, h2, h3, -⟩ := append3_inj (by simp) (fun hv => ih hc f hv) (by simp) h
      rw [h1, h2, h3]
  | frame _ _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | frame _ f _ =>
      obtain ⟨h1, h2, h3, -⟩ := append3_inj (by simp only [List.length_map]; exact isa_addrs_length _ _ _)
        (fun hv => ih hc f hv) (by simp only [List.length_map]; exact isa_addrs_length _ _ _) h
      rw [h1, h2, h3]
  | icall => simp only [Code.icallFree, Bool.false_eq_true] at hc
  | icallNext => simp only [Code.icallFree, Bool.false_eq_true] at hc

/-! ## Runs of the code made so are runs of the code -/

/-- A run of `callVia (movd eax, r) m b`: the call of `m` from the state it
starts in, its callee entered with `eax` the address, `m`'s address leaked
first. -/
theorem Exec.callVia_inv {m : String} {r : MReg} {b : Prog isa} {s s' : State} {t : List Leak}
    (hx : s.mmx = true) (e : Exec isa (Impl.ViaMm.X86.callVia r m b) s t s') :
    ∃ s₁ s₂ tb, isa.call s = some s₁ ∧ Exec isa b (s₁.setReg .eax ((s.mm r).extractLsb' 0 32)) tb s₂ ∧
      isa.ret s₁ s₂ = some s' ∧
      t = .addr (isa.fnAddr s m) :: ((isa.callAddrs s).map .addr ++ tb ++ (isa.retAddrs s₂).map .addr) := by
  obtain ⟨s₁, hc⟩ := call_some s
  change Exec isa (.seq (.block [.mmxMovd .eax r]) (.icall (.callr .eax) m b (.block []))) s t s' at e
  cases e with
  | seq e₁ e₂ =>
    cases e₁ with
    | block hu =>
      rw [movd_run hx, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      cases e₂ with
      | icall _ hc' fb hr =>
        rw [call_setReg_eax hc, Option.some.injEq] at hc'
        subst hc'
        refine ⟨s₁, _, _, hc, fb, by rw [← ret_setReg_eax]; exact hr, ?_⟩
        simp only [addrs, List.map_nil, List.nil_append, State.setReg, reduceCtorEq, ↓reduceIte]

/-- **A run of `c` made to call by the MMX registers is a run of `c`**, from
and to the same states. -/
theorem Exec.ofMm₁ {fs : List (String × MReg)} : ∀ (c : Prog isa), Code.icallFree c = true →
    (∀ i ∈ instrs c, i.mmFree = true) → Code.callsKill fs c = true → ∀ {s s' : State} {t' : List Leak},
    Exec isa (Code.viaMm fs c) s t' s' → MmOk fs s → ∃ t, Exec isa c s t s'
  | .block is, _, _, _, _, _, _, e, _ => ⟨_, e⟩
  | .seq a b, hc, hv, hk, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    cases e with
    | seq e₁ e₂ =>
      have hv₁ : ∀ i ∈ instrs a, i.mmFree = true := fun i hi => hv i (List.mem_append_left _ hi)
      obtain ⟨_, o₁⟩ := Exec.ofMm₁ a hc.1 hv₁ hk.1 e₁ hd
      obtain ⟨_, o₂⟩ := Exec.ofMm₁ b hc.2 (fun i hi => hv i (List.mem_append_right _ hi)) hk.2 e₂
        (MmOk.exec o₁ hv₁ hd)
      exact ⟨_, Exec.seq o₁ o₂⟩
  | .ite cd a b, hc, hv, hk, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    cases e with
    | iteT h e =>
      obtain ⟨_, o⟩ := Exec.ofMm₁ a hc.1 (fun i hi => hv i (List.mem_append_left _ hi)) hk.1 e hd
      exact ⟨_, Exec.iteT h o⟩
    | iteF h e =>
      obtain ⟨_, o⟩ := Exec.ofMm₁ b hc.2 (fun i hi => hv i (List.mem_append_right _ hi)) hk.2 e hd
      exact ⟨_, Exec.iteF h o⟩
  | .loop b cd, hc, hv, hk, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    simp only [Code.callsKill] at hk
    change Exec isa (.loop (Code.viaMm fs b) cd) s t' s' at e
    have ihb := fun {s s' : State} {t' : List Leak} (e : Exec isa (Code.viaMm fs b) s t' s') (hd : MmOk fs s) =>
      Exec.ofMm₁ b hc hv hk e hd
    generalize hL : (Code.loop (Code.viaMm fs b) cd : Prog isa) = L at e
    induction e with
    | loopExit f h =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      exact ⟨_, Exec.loopExit o h⟩
    | loopNext f h _ _ ihr =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      obtain ⟨_, r⟩ := ihr (MmOk.exec o hv hd) rfl
      exact ⟨_, Exec.loopNext o h r⟩
    | _ => cases hL
  | .call m b, hc, hv, hk, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    simp only [Code.callsKill, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hk
    cases hl : fs.lookup m with
    | some r =>
      have hkb : Code.kills b = true := hk.1.resolve_left (by rw [hl]; simp)
      have e' : Exec isa (Impl.ViaMm.X86.callVia r m (Code.viaMm fs b)) s t' s' := by
        simp only [Code.viaMm, hl] at e; exact e
      obtain ⟨s₁, _, _, hcall, fb, hr, -⟩ := Exec.callVia_inv hd.1 e'
      have fb' := (Exec.kills (by rw [kills_viaMm]; exact hkb) _).mp fb
      obtain ⟨_, o⟩ := Exec.ofMm₁ b hc hv hk.2 fb' (hd.call hcall)
      exact ⟨_, Exec.call hcall o hr⟩
    | none =>
      have e' : Exec isa (.call m (Code.viaMm fs b)) s t' s' := by
        simp only [Code.viaMm, hl] at e; exact e
      cases e' with
      | call hcall fb hr =>
        obtain ⟨_, o⟩ := Exec.ofMm₁ b hc hv hk.2 fb (hd.call hcall)
        exact ⟨_, Exec.call hcall o hr⟩
  | .frame i b j, hc, hv, hk, _, _, _, e, hd => by
    simp only [Code.icallFree] at hc
    simp only [Code.callsKill] at hk
    cases e with
    | frame hp fb hq =>
      obtain ⟨_, o⟩ := Exec.ofMm₁ b hc (fun i hi => hv i (by simp [instrs, hi])) hk fb
        (hd.push (hv i (by simp [instrs])) hp)
      exact ⟨_, Exec.frame hp o hq⟩
  | .icall .., hc, _, _, _, _, _, _, _ => by simp only [Code.icallFree, Bool.false_eq_true] at hc

theorem Exec.ofMm_det {fs : List (String × MReg)} {c : Prog isa} (hc : Code.icallFree c = true)
    (hv : ∀ i ∈ instrs c, i.mmFree = true) (hk : Code.callsKill fs c = true) {s s' s'' : State}
    {t' t : List Leak} (e : Exec isa (Code.viaMm fs c) s t' s') (o : Exec isa c s t s'') (hd : MmOk fs s) :
    s'' = s' := by
  obtain ⟨_, x⟩ := Exec.ofMm₁ c hc hv hk e hd
  exact (Exec.det o x).2

/-! ## Two runs leak the same if the runs of the code do -/

/-- Two states agree on the addresses of the functions of `fs`. -/
def SymsAgree (fs : List (String × MReg)) (a b : State) : Prop := ∀ p ∈ fs, a.syms p.1 = b.syms p.1

theorem SymsAgree.of {fs : List (String × MReg)} {a b a' b' : State} (h : SymsAgree fs a b)
    (ha : a'.syms = a.syms) (hb : b'.syms = b.syms) : SymsAgree fs a' b' := fun p hp => by
  rw [ha, hb]; exact h p hp

theorem append3_inj' {a₁ a₂ b₁ b₂ c₁ c₂ : List Leak} (ha : a₁.length = a₂.length)
    (hb : ∀ {v₁ v₂ : List Leak}, b₁ ++ v₁ = b₂ ++ v₂ → b₁ = b₂) (hc : c₁.length = c₂.length)
    (h : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ :=
  let ⟨h1, h2, h3, _⟩ := append3_inj (u₁ := []) (u₂ := []) ha hb hc (by rw [List.append_nil, List.append_nil]; exact h)
  ⟨h1, h2, h3⟩

/-- **Two runs of `c` made to call by the MMX registers leak the same if the
runs of `c` do**: each leaks what that run of `c` does, with the callee's
address at each call made so, which the two agree on. -/
theorem Exec.ofMm₂ {fs : List (String × MReg)} : ∀ (c : Prog isa), Code.icallFree c = true →
    (∀ i ∈ instrs c, i.mmFree = true) → Code.callsKill fs c = true →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak},
    Exec isa (Code.viaMm fs c) s₁ t₁' s₁' → Exec isa (Code.viaMm fs c) s₂ t₂' s₂' → MmOk fs s₁ → MmOk fs s₂ →
    SymsAgree fs s₁ s₂ → Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → t₁ = t₂ → t₁' = t₂'
  | .block is, _, _, _, _, _, _, _, _, _, _, _, e₁, e₂, _, _, _, o₁, o₂, h => by
    rw [(Exec.det e₁ o₁).1, (Exec.det e₂ o₂).1]; exact h
  | .seq a b, hc, hv, hk, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    have hva : ∀ i ∈ instrs a, i.mmFree = true := fun i hi => hv i (List.mem_append_left _ hi)
    have hvb : ∀ i ∈ instrs b, i.mmFree = true := fun i hi => hv i (List.mem_append_right _ hi)
    cases e₁ with
    | seq f₁ g₁ =>
    cases e₂ with
    | seq f₂ g₂ =>
    cases o₁ with
    | seq p₁ q₁ =>
    cases o₂ with
    | seq p₂ q₂ =>
    obtain rfl := Exec.ofMm_det hc.1 hva hk.1 f₁ p₁ hd₁
    obtain rfl := Exec.ofMm_det hc.1 hva hk.1 f₂ p₂ hd₂
    have hA := Exec.prefix hc.1 p₁ p₂ h
    rw [hA] at h
    have hB := List.append_cancel_left h
    rw [Exec.ofMm₂ a hc.1 hva hk.1 f₁ f₂ hd₁ hd₂ hy p₁ p₂ hA,
      Exec.ofMm₂ b hc.2 hvb hk.2 g₁ g₂ (MmOk.exec p₁ hva hd₁) (MmOk.exec p₂ hva hd₂)
        (hy.of (Exec.syms p₁) (Exec.syms p₂)) q₁ q₂ hB]
  | .ite cd a b, hc, hv, hk, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.callsKill, Bool.and_eq_true] at hk
    have hva : ∀ i ∈ instrs a, i.mmFree = true := fun i hi => hv i (List.mem_append_left _ hi)
    have hvb : ∀ i ∈ instrs b, i.mmFree = true := fun i hi => hv i (List.mem_append_right _ hi)
    cases e₁ with
    | iteT c₁ f₁ =>
      cases o₁ with
      | iteF c₁' _ => rw [c₁] at c₁'; cases c₁'
      | iteT _ p₁ =>
        cases e₂ with
        | iteF c₂ _ =>
          cases o₂ with
          | iteT c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteF _ _ => simp only [List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
        | iteT c₂ f₂ =>
          cases o₂ with
          | iteF c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteT _ p₂ =>
            simp only [List.cons.injEq, true_and] at h ⊢
            exact Exec.ofMm₂ a hc.1 hva hk.1 f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
    | iteF c₁ f₁ =>
      cases o₁ with
      | iteT c₁' _ => rw [c₁] at c₁'; cases c₁'
      | iteF _ p₁ =>
        cases e₂ with
        | iteT c₂ _ =>
          cases o₂ with
          | iteF c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteT _ _ => simp only [List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
        | iteF c₂ f₂ =>
          cases o₂ with
          | iteT c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteF _ p₂ =>
            simp only [List.cons.injEq, true_and] at h ⊢
            exact Exec.ofMm₂ b hc.2 hvb hk.2 f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
  | .loop b cd, hc, hv, hk, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    simp only [Code.callsKill] at hk
    have ihb := fun {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak}
      (e₁ : Exec isa (Code.viaMm fs b) s₁ t₁' s₁') (e₂ : Exec isa (Code.viaMm fs b) s₂ t₂' s₂')
      (hd₁ : MmOk fs s₁) (hd₂ : MmOk fs s₂) (hy : SymsAgree fs s₁ s₂) (o₁ : Exec isa b s₁ t₁ s₁')
      (o₂ : Exec isa b s₂ t₂ s₂') (h : t₁ = t₂) => Exec.ofMm₂ b hc hv hk e₁ e₂ hd₁ hd₂ hy o₁ o₂ h
    change Exec isa (.loop (Code.viaMm fs b) cd) s₁ t₁' s₁' at e₁
    change Exec isa (.loop (Code.viaMm fs b) cd) s₂ t₂' s₂' at e₂
    generalize hL : (Code.loop (Code.viaMm fs b) cd : Prog isa) = L at e₁ e₂
    induction e₁ generalizing s₂ s₂' t₂' t₁ t₂ with
    | loopExit f₁ c₁ =>
      cases hL
      cases o₁ with
      | loopNext p₁ c₁' _ =>
        rw [Exec.ofMm_det hc hv hk f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopExit p₁ _ =>
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofMm_det hc hv hk f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb]
        | loopNext f₂ c₂ _ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofMm_det hc hv hk f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
      | _ => skip
    | loopNext f₁ c₁ r₁ _ ihr =>
      cases hL
      cases o₁ with
      | loopExit p₁ c₁' =>
        rw [Exec.ofMm_det hc hv hk f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopNext p₁ _ q₁ =>
        obtain rfl := Exec.ofMm_det hc hv hk f₁ p₁ hd₁
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofMm_det hc hv hk f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
        | loopNext f₂ c₂ r₂ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofMm_det hc hv hk f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ q₂ =>
            obtain rfl := Exec.ofMm_det hc hv hk f₂ p₂ hd₂
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq, List.cons.injEq] at h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb,
              ihr _ _ _ _ _ (MmOk.exec p₁ hv hd₁) (MmOk.exec p₂ hv hd₂)
                (hy.of (Exec.syms p₁) (Exec.syms p₂)) q₁ q₂ h.2 rfl r₂]
    | _ => cases hL
  | .call m b, hc, hv, hk, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    simp only [Code.callsKill, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hk
    cases o₁ with
    | call hco₁ p₁ hro₁ =>
    cases o₂ with
    | call hco₂ p₂ hro₂ =>
    obtain ⟨hA, hT, hR⟩ := append3_inj' (by simp only [List.length_map]; rfl)
      (fun hv => Exec.prefix hc p₁ p₂ hv) (by simp only [List.length_map]; rfl) h
    cases hl : fs.lookup m with
    | some r =>
      have hkb : Code.kills (Code.viaMm fs b) = true := by
        rw [kills_viaMm]; exact hk.1.resolve_left (by rw [hl]; simp)
      have e₁' : Exec isa (Impl.ViaMm.X86.callVia r m (Code.viaMm fs b)) s₁ t₁' s₁' := by
        simp only [Code.viaMm, hl] at e₁; exact e₁
      have e₂' : Exec isa (Impl.ViaMm.X86.callVia r m (Code.viaMm fs b)) s₂ t₂' s₂' := by
        simp only [Code.viaMm, hl] at e₂; exact e₂
      obtain ⟨r₁, q₁, _, hc₁, fb₁, hr₁, rfl⟩ := Exec.callVia_inv hd₁.1 e₁'
      obtain ⟨r₂, q₂, _, hc₂, fb₂, hr₂, rfl⟩ := Exec.callVia_inv hd₂.1 e₂'
      rw [hc₁, Option.some.injEq] at hco₁
      rw [hc₂, Option.some.injEq] at hco₂
      subst hco₁ hco₂
      have fb₁' := (Exec.kills hkb _).mp fb₁
      have fb₂' := (Exec.kills hkb _).mp fb₂
      obtain rfl := Exec.ofMm_det hc hv hk.2 fb₁' p₁ (hd₁.call hc₁)
      obtain rfl := Exec.ofMm_det hc hv hk.2 fb₂' p₂ (hd₂.call hc₂)
      have hf : isa.fnAddr s₁ m = isa.fnAddr s₂ m := by
        show (s₁.syms m).setWidth 64 = (s₂.syms m).setWidth 64
        rw [hy (m, r) (lookup_mem' hl)]
      rw [hf, hA, hR, Exec.ofMm₂ b hc hv hk.2 fb₁' fb₂' (hd₁.call hc₁) (hd₂.call hc₂)
        (hy.of (call_syms' hc₁) (call_syms' hc₂)) p₁ p₂ hT]
    | none =>
      have e₁' : Exec isa (.call m (Code.viaMm fs b)) s₁ t₁' s₁' := by
        simp only [Code.viaMm, hl] at e₁; exact e₁
      have e₂' : Exec isa (.call m (Code.viaMm fs b)) s₂ t₂' s₂' := by
        simp only [Code.viaMm, hl] at e₂; exact e₂
      cases e₁' with
      | call hc₁ fb₁ hr₁ =>
      cases e₂' with
      | call hc₂ fb₂ hr₂ =>
      rw [hc₁, Option.some.injEq] at hco₁
      rw [hc₂, Option.some.injEq] at hco₂
      subst hco₁ hco₂
      obtain rfl := Exec.ofMm_det hc hv hk.2 fb₁ p₁ (hd₁.call hc₁)
      obtain rfl := Exec.ofMm_det hc hv hk.2 fb₂ p₂ (hd₂.call hc₂)
      rw [hA, hR, Exec.ofMm₂ b hc hv hk.2 fb₁ fb₂ (hd₁.call hc₁) (hd₂.call hc₂)
        (hy.of (call_syms' hc₁) (call_syms' hc₂)) p₁ p₂ hT]
  | .frame i b j, hc, hv, hk, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    simp only [Code.callsKill] at hk
    have hvb : ∀ i ∈ instrs b, i.mmFree = true := fun i' hi => hv i' (by simp [instrs, hi])
    have hvi : i.mmFree = true := hv i (by simp [instrs])
    cases e₁ with
    | frame hp₁ fb₁ hq₁ =>
    cases e₂ with
    | frame hp₂ fb₂ hq₂ =>
    cases o₁ with
    | frame hpo₁ p₁ hqo₁ =>
    cases o₂ with
    | frame hpo₂ p₂ hqo₂ =>
    rw [hp₁, Option.some.injEq] at hpo₁
    rw [hp₂, Option.some.injEq] at hpo₂
    subst hpo₁ hpo₂
    obtain rfl := Exec.ofMm_det hc hvb hk fb₁ p₁ (hd₁.push hvi hp₁)
    obtain rfl := Exec.ofMm_det hc hvb hk fb₂ p₂ (hd₂.push hvi hp₂)
    obtain ⟨hA, hT, hR⟩ := append3_inj' (by simp only [List.length_map]; exact isa_addrs_length _ _ _)
      (fun hv => Exec.prefix hc p₁ p₂ hv) (by simp only [List.length_map]; exact isa_addrs_length _ _ _) h
    rw [hA, hR, Exec.ofMm₂ b hc hvb hk fb₁ fb₂ (hd₁.push hvi hp₁) (hd₂.push hvi hp₂)
      (hy.of (push_syms hp₁) (push_syms hp₂)) p₁ p₂ hT]
  | .icall .., hc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Code.icallFree, Bool.false_eq_true] at hc

/-! ## The lift -/

/-- `k`, from states where each register of `fs` holds its function's address
inside an MMX frame, for runs that agree on those addresses. -/
def Contract.mm (fs : List (String × MReg)) (k : Contract isa) : Contract isa :=
  ⟨fun s => k.pre s ∧ MmOk fs s, k.post, fun s t => k.pub s t ∧ SymsAgree fs s t⟩

/-- **Code verified against `k` that runs no MMX instruction, makes no
indirect call and whose calls of the functions of `fs` enter code that
overwrites `eax` first is verified made to call them by the addresses in
their MMX registers**, against `k` from states where those registers hold
them. -/
theorem Verified.viaMm {fs : List (String × MReg)} {c : Prog isa} {k : Contract isa}
    (h : Verified X86.target c k) (hc : Code.icallFree c = true) (hv : ∀ i ∈ instrs c, i.mmFree = true)
    (hk : Code.callsKill fs c = true) (hsat : ∃ s, (Contract.mm fs k).pre s) :
    Verified X86.target (Code.viaMm fs c) (Contract.mm fs k) := by
  obtain ⟨hok, hct, -⟩ := h
  refine ⟨fun s ⟨hp, hd⟩ => ?_, fun s₁ s₂ t₁' t₂' s₁' s₂' ⟨hp₁, hd₁⟩ ⟨hp₂, hd₂⟩ ⟨hpub, hy⟩ e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', e, ha, hq⟩ := hok s hp
    obtain ⟨t', e'⟩ := Exec.toMm e hv hk hd
    exact ⟨t', s', e', ha, hq⟩
  · obtain ⟨t₁, o₁⟩ := Exec.ofMm₁ c hc hv hk e₁ hd₁
    obtain ⟨t₂, o₂⟩ := Exec.ofMm₁ c hc hv hk e₂ hd₂
    exact Exec.ofMm₂ c hc hv hk e₁ e₂ hd₁ hd₂ hy o₁ o₂ (hct _ _ _ _ _ _ hp₁ hp₂ hpub o₁ o₂)

end VG.X86
