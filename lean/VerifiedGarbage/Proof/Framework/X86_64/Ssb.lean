import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Prototype: speculative store bypass (Spectre v4) for x86-64

**Untrusted prototype**, for a feasibility experiment.

## Semantics

`Ssb.isa W` is the x86-64 model in which every load may read stale memory:
byte `a` of the memory a load sees is, at the attacker's choice, its current
value or the value it had before any of the last `W` instructions (a store to
`a` among them not yet resolved: Spectre v4, speculative store bypass,
CVE-2018-3639; the forwarding model of Cauligi et al., PLDI 2020, §3, with a
bounded window and without rollback). The state keeps the memories before the
last `W` instructions (`hist`), and the attacker's choices (`dirs`), which are
the same in both runs of the constant-time property, as the return addresses
of calls are in `TCB/Code.lean`.

An instruction runs twice from the same registers: on the memory loads see
(its registers and flags, everything a transient execution then computes
with) and on the current memory (its stores, whose addresses and values come
from the registers alone). There is no rollback: a transient execution goes
on to the end of the program, so its leakage contains every transient
prefix's. `lfence` waits for every earlier store (Intel, "Speculative Store
Bypass", mitigation by `LFENCE`): after it no load sees a value older than
the fence.

`SpecCT W` is constant time in this model: any two runs from states that
agree on public data, with the same choices, leak the same.

## Analysis

`Ssb.taint W` lifts the x86-64 taint analysis (`X86_64.taint`): besides the
taint of the state it keeps the public slots of each remembered memory
(`hist`). A load is public only if it reads a slot public in the current
memory and in each of the last `W` (`specBase`).
-/

namespace VG.X86_64.Ssb

open VG.X86_64.Taint (byteAddr region)

structure SState where
  arch : State
  /-- The memory before each of the last instructions, newest first. -/
  hist : List Mem
  /-- At the `n`-th instruction, byte `a` is read from the memory `dirs n a`
  instructions old (`0`, or more than the window: the current memory). -/
  dirs : Nat → Addr → Nat
  n : Nat

variable (W : Nat)

/-- The memory the loads of the next instruction see. -/
def view (ss : SState) : Mem := fun a =>
  if 0 < ss.dirs ss.n a ∧ ss.dirs ss.n a ≤ W then ss.hist.getD (ss.dirs ss.n a - 1) ss.arch.mem a
  else ss.arch.mem a

def fence : Instr → Bool
  | .lfence => true
  | _ => false

/-- The state after an instruction leaves `s'`. -/
def next (ss : SState) (fenced : Bool) (s' : State) : SState where
  arch := s'
  hist := if fenced then List.replicate W s'.mem else (ss.arch.mem :: ss.hist).take W
  dirs := ss.dirs
  n := ss.n + 1

/-- Run `f` with its loads seeing `view`: the registers come from that run,
the memory from the run on the current memory. -/
def spec (f : State → Option State) (ss : SState) (fenced : Bool) : Option SState :=
  (f ss.arch).bind fun r₀ => (f { ss.arch with mem := view W ss }).map fun r =>
    next W ss fenced { r with mem := r₀.mem }

abbrev isa : ISA where
  State := SState
  Instr := Instr
  Cond := Cond
  exec i ss := spec W (X86_64.exec i) ss (fence i)
  addrs i ss := X86_64.addrs i ss.arch
  eval c ss := X86_64.eval c ss.arch
  call ss := (X86_64.call ss.arch).map (next W ss false)
  callAddrs ss := [ss.arch.gpr .rsp - 8]
  ret ss₁ ss₂ := (X86_64.ret ss₁.arch ss₂.arch).map (next W ss₂ false)
  retAddrs ss := [ss.arch.gpr .rsp]
  writesSp := X86_64.isa.writesSp
  push i ss := (X86_64.push i ss.arch).map (next W ss false)
  pop j ss₁ ss₂ := spec W (X86_64.pop j ss₁.arch) ss₂ false
  requires := Instr.requires

/-- Speculative constant time (Spectre v4, window `W`). -/
def SpecCT (Pre : State → Prop) (Pub : State → State → Prop) (c : Prog X86_64.isa) : Prop :=
  ConstantTime (isa W) (fun ss => Pre ss.arch ∧ ss.hist.length = W)
    (fun a b => Pub a.arch b.arch ∧ a.dirs = b.dirs ∧ a.n = b.n) c

/-! ## The sequential semantics is the case of no stale load -/

theorem view_seq {ss : SState} (h : ∀ a, ss.dirs ss.n a = 0) : view W ss = ss.arch.mem := by
  funext a; simp only [view, h, Nat.lt_irrefl, false_and, ite_false]

theorem spec_seq {f : State → Option State} {ss ss' : SState} {b : Bool}
    (h : ∀ a, ss.dirs ss.n a = 0) (e : spec W f ss b = some ss') : f ss.arch = some ss'.arch := by
  simp only [spec, view_seq W h, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
  obtain ⟨r₀, h₀, r, h₁, rfl⟩ := e
  rw [h₀] at h₁; cases h₁; exact h₀

theorem execBlock_seq {is : List Instr} {ss ss' : SState} {t : List Leak}
    (hd : ∀ n a, ss.dirs n a = 0) (e : execBlock (isa W) is ss = some (ss', t)) :
    execBlock X86_64.isa is ss.arch = some (ss'.arch, t) ∧ ∀ n a, ss'.dirs n a = 0 := by
  induction is generalizing ss t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; exact ⟨rfl, hd⟩
  | cons i is ih =>
    simp only [execBlock] at e
    split at e <;> rename_i h₁ <;> [cases e; skip]
    rename_i s₁
    simp only [Option.map_eq_some_iff, Prod.exists] at e
    obtain ⟨_, u, e, he⟩ := e
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have h₁' := spec_seq W (hd _) h₁
    have hd₁ : ∀ n a, s₁.dirs n a = 0 := by
      simp only [isa, spec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁
      obtain ⟨_, _, _, _, rfl⟩ := h₁; exact hd
    obtain ⟨ih₁, ih₂⟩ := ih hd₁ e
    refine ⟨?_, ih₂⟩
    simp only [execBlock, X86_64.isa, h₁', ih₁, Option.map_some]

/-- With no stale load, a run of the speculative model is a run of the
sequential one, with the same leakage. -/
theorem exec_seq {c : Prog (isa W)} {ss ss' : SState} {t : List Leak}
    (e : Exec (isa W) c ss t ss') (hd : ∀ n a, ss.dirs n a = 0) :
    Exec X86_64.isa c ss.arch t ss'.arch ∧ ∀ n a, ss'.dirs n a = 0 := by
  induction e with
  | block h => obtain ⟨h₁, h₂⟩ := execBlock_seq W hd h; exact ⟨.block h₁, h₂⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨a, ha⟩ := ih₁ hd; obtain ⟨b, hb⟩ := ih₂ ha; exact ⟨.seq a b, hb⟩
  | iteT hc _ ih => obtain ⟨a, ha⟩ := ih hd; exact ⟨.iteT hc a, ha⟩
  | iteF hc _ ih => obtain ⟨a, ha⟩ := ih hd; exact ⟨.iteF hc a, ha⟩
  | loopExit _ hc ih => obtain ⟨a, ha⟩ := ih hd; exact ⟨.loopExit a hc, ha⟩
  | loopNext _ hc _ ih₁ ih₂ =>
    obtain ⟨a, ha⟩ := ih₁ hd; obtain ⟨b, hb⟩ := ih₂ ha; exact ⟨.loopNext a hc b, hb⟩
  | call hc _ hr ih =>
    simp only [isa, Option.map_eq_some_iff] at hc hr
    obtain ⟨_, hc, rfl⟩ := hc; obtain ⟨_, hr, rfl⟩ := hr
    obtain ⟨a, ha⟩ := ih hd; exact ⟨.call hc a hr, ha⟩
  | frame hp _ hq ih =>
    simp only [isa, Option.map_eq_some_iff] at hp
    obtain ⟨_, hp, rfl⟩ := hp
    obtain ⟨a, ha⟩ := ih hd
    refine ⟨.frame hp a (spec_seq W (ha _) hq), ?_⟩
    simp only [spec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨_, _, _, _, rfl⟩ := hq; exact ha

/-- The run with no stale load of a sequential run. -/
def lift (s : State) (hist : List Mem) (n : Nat) : SState := ⟨s, hist, fun _ _ => 0, n⟩

theorem spec_lift {f : State → Option State} {s s' : State} {hist : List Mem} {n : Nat} {b : Bool}
    (e : f s = some s') : ∃ hist', spec W f (lift s hist n) b = some (lift s' hist' (n + 1)) := by
  have hv : view W (lift s hist n) = s.mem := view_seq W fun _ => rfl
  refine ⟨if b then List.replicate W s'.mem else (s.mem :: hist).take W, ?_⟩
  unfold spec
  rw [hv, show ({ (lift s hist n).arch with mem := s.mem } : State) = s from rfl]
  simp only [lift, e, Option.bind_some, Option.map_some]
  rfl

theorem execBlock_lift {is : List Instr} {s s' : State} {t : List Leak}
    (e : execBlock X86_64.isa is s = some (s', t)) (hist : List Mem) (n : Nat) :
    ∃ hist' n', execBlock (isa W) is (lift s hist n) = some (lift s' hist' n', t) := by
  induction is generalizing s t hist n with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; exact ⟨hist, n, rfl⟩
  | cons i is ih =>
    simp only [execBlock] at e
    split at e <;> rename_i h₁ <;> [cases e; skip]
    rename_i s₁
    simp only [Option.map_eq_some_iff, Prod.exists] at e
    obtain ⟨_, u, e, he⟩ := e
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h', hs⟩ := spec_lift W (hist := hist) (n := n) (b := fence i) h₁
    obtain ⟨h'', n'', ih⟩ := ih e h' (n + 1)
    refine ⟨h'', n'', ?_⟩
    simp only [execBlock, isa, hs, ih, Option.map_some]; rfl

theorem exec_lift {c : Prog X86_64.isa} {s s' : State} {t : List Leak}
    (e : Exec X86_64.isa c s t s') (hist : List Mem) (n : Nat) :
    ∃ hist' n', Exec (isa W) c (lift s hist n) t (lift s' hist' n') := by
  induction e generalizing hist n with
  | block h => obtain ⟨h', n', h⟩ := execBlock_lift W h hist n; exact ⟨h', n', .block h⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁, n₁, a⟩ := ih₁ hist n; obtain ⟨h₂, n₂, b⟩ := ih₂ h₁ n₁; exact ⟨h₂, n₂, .seq a b⟩
  | iteT hc _ ih => obtain ⟨h₁, n₁, a⟩ := ih hist n; exact ⟨h₁, n₁, .iteT hc a⟩
  | iteF hc _ ih => obtain ⟨h₁, n₁, a⟩ := ih hist n; exact ⟨h₁, n₁, .iteF hc a⟩
  | loopExit _ hc ih => obtain ⟨h₁, n₁, a⟩ := ih hist n; exact ⟨h₁, n₁, .loopExit a hc⟩
  | loopNext _ hc _ ih₁ ih₂ =>
    obtain ⟨h₁, n₁, a⟩ := ih₁ hist n; obtain ⟨h₂, n₂, b⟩ := ih₂ h₁ n₁
    exact ⟨h₂, n₂, .loopNext a hc b⟩
  | @call _ _ s s₁ s₂ s₃ _ hc _ hr ih =>
    obtain ⟨h₁, n₁, a⟩ := ih ((s.mem :: hist).take W) (n + 1)
    have hc' : (isa W).call (lift s hist n) = some (lift s₁ ((s.mem :: hist).take W) (n + 1)) := by
      have hc : X86_64.call s = some s₁ := hc
      simp only [isa, lift, hc, Option.map_some]; rfl
    have hr' : (isa W).ret (lift s₁ ((s.mem :: hist).take W) (n + 1)) (lift s₂ h₁ n₁) =
        some (lift s₃ ((s₂.mem :: h₁).take W) (n₁ + 1)) := by
      have hr : X86_64.ret s₁ s₂ = some s₃ := hr
      simp only [isa, lift, hr, Option.map_some]; rfl
    exact ⟨_, _, Exec.call (M := isa W) hc' a hr'⟩
  | @frame i _ _ s s₁ _ _ _ hp _ hq ih =>
    obtain ⟨h₁, n₁, a⟩ := ih ((s.mem :: hist).take W) (n + 1)
    obtain ⟨h₂, hq'⟩ := spec_lift W (hist := h₁) (n := n₁) (b := false) hq
    have hp' : (isa W).push i (lift s hist n) = some (lift s₁ ((s.mem :: hist).take W) (n + 1)) := by
      have hp : X86_64.push i s = some s₁ := hp
      simp only [isa, lift, hp, Option.map_some]; rfl
    exact ⟨_, _, Exec.frame (M := isa W) hp' a hq'⟩

/-- Speculative constant time implies constant time. -/
theorem SpecCT.ct {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog X86_64.isa}
    (h : SpecCT W Pre Pub c) : ConstantTime X86_64.isa Pre Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨_, _, f₁⟩ := exec_lift W e₁ (List.replicate W s₁.mem) 0
  obtain ⟨_, _, f₂⟩ := exec_lift W e₂ (List.replicate W s₂.mem) 0
  exact h (lift s₁ _ 0) (lift s₂ _ 0) t₁ t₂ _ _ ⟨h₁, List.length_replicate⟩ ⟨h₂, List.length_replicate⟩ ⟨hp, rfl, rfl⟩ f₁ f₂

/-! ## Instructions keep the regions -/

theorem exec_wr {i : Instr} {s s' : State} (h : X86_64.exec i s = some s') : s'.wr = s.wr := by
  cases i with
  | alu op d src =>
    simp only [X86_64.exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | alu32 op d src =>
    simp only [X86_64.exec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift32 op d n =>
    simp only [X86_64.exec, execShift32] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | shift op d n =>
    simp only [X86_64.exec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | xop op => simp only [X86_64.exec, Option.some.injEq] at h; subst h; rw [Taint.XOp.exec_eq op s]
  | vop op => simp only [X86_64.exec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]
  | vmovdquLoad len d m =>
    cases len <;> simp only [X86_64.exec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl
  | vmovdquStore len m r =>
    cases len
    · simp only [X86_64.exec, State.store128] at h; split at h <;> cases h; rfl
    · simp only [X86_64.exec, State.store256] at h; split at h <;> cases h; rfl
  | store m r => simp only [X86_64.exec, State.store64] at h; split at h <;> cases h; rfl
  | store32 m r => simp only [X86_64.exec, State.store32] at h; split at h <;> cases h; rfl
  | store8 m r => simp only [X86_64.exec, State.store8] at h; split at h <;> cases h; rfl
  | movdquStore m r => simp only [X86_64.exec, State.store128] at h; split at h <;> cases h; rfl
  | stmxcsr m => simp only [X86_64.exec, State.store32] at h; split at h <;> cases h; rfl
  | ldmxcsr m =>
    simp only [X86_64.exec, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h; split at h <;> cases h; rfl
  | vmovdqu32Store m r => simp only [X86_64.exec, State.store512] at h; split at h <;> cases h; rfl
  | zop op => simp only [X86_64.exec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]
  | mov | mov32 | movzx8 | movdquLoad | vbroadcasti128 | vmovdqu32Load | vbroadcasti32x4 | zbcst =>
    simp only [X86_64.exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | bswap32 | bswap | movImm64 | lfence | mul | andn32 | andn | vpmovmskb =>
    simp only [X86_64.exec, Option.some.injEq] at h; subst h; rfl
  | rorx32 => simp only [X86_64.exec, execRorx32] at h; split at h <;> cases h; rfl
  | rorx => simp only [X86_64.exec, execRorx] at h; split at h <;> cases h; rfl
  | mulx =>
    simp only [X86_64.exec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | adcx =>
    simp only [X86_64.exec, execAdcx] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | adox =>
    simp only [X86_64.exec, execAdox] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | push | pop | alloc | free => simp only [X86_64.exec, reduceCtorEq] at h

/-! ## The analysis

The analysis keeps the taint of the current state (`base`) and the *young*
public slots: `(sl, a)` means that `sl` may be public only in the memories
less than `a` instructions old (it was stored `a` instructions ago). A public
slot without such an entry is public in every memory up to `W` instructions
old. Only a store of a public register adds a young slot, every instruction
ages them, and they are forgotten once `W` old.

The kernel evaluates `step` for every instruction, so its common case costs
little more than `Taint.stepKD`: with nothing young (`stepFast`), one match on
the instruction, which also adds the slot a public store creates. Otherwise
only a load into a register is analysed a second time, on the slots the
loads see (`specBase`); for any other instruction those do not matter
(`stepKD_slots_irrel`). -/

abbrev Slot := Nat × Nat × Nat

structure T where
  base : Taint.T
  young : List (Slot × Nat) := []
  deriving DecidableEq, Lean.ToExpr

/-- Nothing is young: the initial memory has no public slot. -/
def T.init (τ : Taint.T) : T := { base := τ }

/-- The instructions that may change the public slots. -/
def writesMem : Instr → Bool
  | .store .. | .store32 .. | .store8 .. | .movdquStore .. | .vmovdquStore .. | .vmovdqu32Store ..
  | .stmxcsr _ => true
  | _ => false

/-- No young entry for `sl` is younger than `W`. -/
def old (σ : T) (sl : Slot) : Bool := KList.all σ.young fun p => !Taint.mem3 sl [p.1] || Nat.ble W p.2

/-- What the loads of the next instruction see as public: the public slots
with no young entry. -/
def specBase (σ : T) : Taint.T :=
  { σ.base with slots := KList.filter (old W σ) σ.base.slots }

/-- The young entry of the slot a store added: a store keeps or removes
slots, or adds one at the head (`stepKD_slots_cases`). -/
def added (σ : T) (slots' : List Slot) : List (Slot × Nat) :=
  match slots' with
  | x :: _ => bif Taint.mem3 x σ.base.slots then [] else [(x, 0)]
  | [] => []

/-- The young slots one instruction later, with the slot it added if any. -/
def aged (σ : T) (slots' : List Slot) : List (Slot × Nat) :=
  KList.append (added σ slots')
    (KList.filter (fun p => Nat.blt p.2 W) (KList.map (fun p => (p.1, p.2 + 1)) σ.young))

/-- Whether an instruction may add a public slot: a store of a public register. -/
def mayAdd (τ : Taint.T) : Instr → Bool
  | .store _ r | .store32 _ r | .store8 _ r => Taint.pub τ r
  | _ => false

section
open _root_.VG.X86_64.Taint (srcOkK setK srcPub loadPubK movBasesK killK loPub storeStepKD aluStepK pub memPub
  storeStepK mulStep mulxStepK adxStepK)

/-- `step` when nothing is young (`stepFast_eq`): `Taint.stepKD` with the
young entry of the slot a store of a public register may add, in one match on
the instruction (most instructions take this path). -/
def stepFast (σ : T) (τ : Taint.T) : Instr → Option T
  | .mov d src =>
    bif srcOkK τ src then
      some { base := { τ with
        regs := setK τ d (srcPub τ src || loadPubK τ 8 src), bases := movBasesK τ d src, lo := .empty } }
    else none
  | .mov32 d src =>
    bif srcOkK τ src then
      some { base := { τ with
        regs := setK τ d (srcPub τ src || loadPubK τ 4 src || loPub τ src), bases := killK τ d, lo := .empty } }
    else none
  | .store m r => (storeStepKD τ m 8 (pub τ r)).map fun τ₀ =>
    { base := τ₀, young := bif pub τ r then added σ τ₀.slots else [] }
  | .store32 m r => (storeStepKD τ m 4 (pub τ r)).map fun τ₀ =>
    { base := τ₀, young := bif pub τ r then added σ τ₀.slots else [] }
  | .store8 m r => (storeStepKD τ m 1 (pub τ r)).map fun τ₀ =>
    { base := τ₀, young := bif pub τ r then added σ τ₀.slots else [] }
  | .alu op d src => (aluStepK τ op d src true).map fun τ₀ => { base := τ₀ }
  | .alu32 op d src => (aluStepK τ op d src false).map fun τ₀ => { base := τ₀ }
  | .shift32 _ d _ | .shift _ d _ =>
    some { base := { τ with flags := τ.flags && pub τ d, bases := killK τ d, lo := .empty } }
  | .bswap32 d | .bswap d => some { base := { τ with bases := killK τ d, lo := .empty } }
  | .rorx32 d r _ | .rorx d r _ =>
    some { base := { τ with regs := setK τ d (pub τ r), bases := killK τ d, lo := .empty } }
  | .andn32 d a b | .andn d a b =>
    let p := pub τ a && pub τ b
    some { base := { τ with regs := setK τ d p, flags := p, bases := killK τ d, lo := .empty } }
  | .movImm64 d _ => some { base := { τ with regs := setK τ d true, bases := killK τ d, lo := .empty } }
  | .movzx8 d m =>
    bif memPub τ m then some { base := { τ with regs := setK τ d false, bases := killK τ d, lo := .empty } } else none
  | .vpmovmskb _ d _ => some { base := { τ with regs := setK τ d false, bases := killK τ d, lo := .empty } }
  | .movdquLoad _ m => bif memPub τ m then some { base := τ } else none
  | .movdquStore m _ => (storeStepK τ m 16 false).map fun τ₀ => { base := τ₀ }
  | .xop _ | .vop _ => some { base := τ }
  | .vmovdquLoad _ _ m | .vbroadcasti128 _ m => bif memPub τ m then some { base := τ } else none
  | .vmovdquStore .l128 m _ => (storeStepK τ m 16 false).map fun τ₀ => { base := τ₀ }
  | .vmovdquStore .l256 m _ => (storeStepK τ m 32 false).map fun τ₀ => { base := τ₀ }
  | .zop _ => some { base := τ }
  | .vmovdqu32Load _ m | .vbroadcasti32x4 _ m | .zbcst _ _ _ m =>
    bif memPub τ m then some { base := τ } else none
  | .vmovdqu32Store m _ => (storeStepK τ m 64 false).map fun τ₀ => { base := τ₀ }
  | .stmxcsr m => (storeStepK τ m 4 false).map fun τ₀ => { base := τ₀ }
  | .ldmxcsr m => bif memPub τ m then some { base := τ } else none
  | .lfence => some { base := τ }
  | .mul r => some { base := mulStep τ r }
  | .mulx hi lo src => bif srcOkK τ src then some { base := mulxStepK τ hi lo src } else none
  | .adcx d src | .adox d src => (adxStepK τ d src).map fun τ₀ => { base := τ₀ }
  | .push _ | .pop .. | .alloc _ | .free _ => none


end

/-- The instructions whose taint depends on the public slots: loads into a
general-purpose register. For the others, the slots the loads see do not
matter (`stepKD_slots_irrel`). -/
def readsSlots : Instr → Bool
  | .mov _ (.mem _) | .mov32 _ (.mem _) => true
  | _ => false

inductive Kind | other | reads | fence
  deriving DecidableEq

/-- `readsSlots` and `fence` in one match on the instruction (`kind_reads`,
`kind_fence`, `kind_other`). -/
def kind : Instr → Kind
  | .mov _ (.mem _) | .mov32 _ (.mem _) => .reads
  | .lfence => .fence
  | _ => .other

def step (σ : T) (i : Instr) : Option T :=
  match σ.young with
  | [] => stepFast σ σ.base i
  | _ :: _ => (Taint.stepKD σ.base i).bind fun τ₀ =>
    match kind i with
    | .reads => (Taint.stepKD (specBase W σ) i).bind fun τv =>
      bif τv.lens == τ₀.lens then some { base := { τv with slots := τ₀.slots }, young := aged W σ τ₀.slots }
      else none
    | .fence => some { base := τ₀, young := [] }
    | .other => some { base := τ₀, young := aged W σ τ₀.slots }

def meet (σ₁ σ₂ : T) : T :=
  { base := Taint.meet σ₁.base σ₂.base, young := KList.append σ₁.young σ₂.young }

/-- Every young entry of `σ` for a slot public in `τ` has an entry in `τ` at most as old. -/
def le (τ σ : T) : Bool :=
  Taint.leK τ.base σ.base && KList.all σ.young fun q =>
    !Taint.mem3 q.1 τ.base.slots || KList.any τ.young fun p => Taint.mem3 p.1 [q.1] && Nat.ble p.2 q.2

/-- The memories `k` old agree on the public slots that are not younger. -/
def HistAgree (σ : T) (a b : SState) : Prop :=
  ∀ sl ∈ σ.base.slots, ∀ k < W, (∀ p ∈ σ.young, p.1 = sl → k < p.2) →
    ∀ j, sl.2.1 ≤ j → j < sl.2.1 + sl.2.2 →
    a.hist.getD k a.arch.mem (byteAddr a.arch sl.1 j) = b.hist.getD k b.arch.mem (byteAddr b.arch sl.1 j)

structure Agree (σ : T) (a b : SState) : Prop where
  base : Taint.Agree σ.base a.arch b.arch
  dirs : a.dirs = b.dirs
  n : a.n = b.n
  len₁ : a.hist.length = W
  len₂ : b.hist.length = W
  hist : HistAgree W σ a b

/-! ## Soundness -/

variable {W}

theorem mem3_iff {sl : Slot} {l : List Slot} : Taint.mem3 sl l = true ↔ sl ∈ l := by
  rw [Taint.mem3_eq, List.contains_iff_mem]

theorem stepKD_slots {τ τ' : Taint.T} {i : Instr} (hw : writesMem i = false)
    (h : Taint.stepKD τ i = some τ') : τ'.slots = τ.slots := by
  cases i <;> simp only [writesMem, Bool.true_eq_false] at hw <;>
    simp only [Taint.stepKD, Taint.aluStepK, Taint.adxStepK, Bool.cond_eq_ite] at h <;>
    (try split at h) <;> (try cases h) <;> rfl

theorem storeSlotsKD_cases (τ : Taint.T) (m : MemOp) (w : Nat) (p : Bool) :
    (∀ sl ∈ Taint.storeSlotsKD τ m w p, sl ∈ τ.slots) ∨
      (p = true ∧ ∃ x, Taint.storeSlotsKD τ m w p = x :: τ.slots) := by
  unfold Taint.storeSlotsKD
  split
  · cases Nat.ble _ _ <;> cases p <;> simp only [Bool.cond_false, Bool.cond_true]
    · exact .inl fun _ h => by simp at h
    · exact .inl fun _ h => h
    · exact .inl fun _ h => by simp only [KList.filter_eq, List.mem_filter] at h; exact h.1
    · cases Taint.mem3 _ _ <;> simp only [Bool.cond_false, Bool.cond_true]
      · exact .inr ⟨by trivial, _, rfl⟩
      · exact .inl fun _ h => h
  · cases p <;> simp only [Bool.cond_false, Bool.cond_true]
    · exact .inl fun _ h => by simp at h
    · exact .inl fun _ h => h

theorem storeSlotsK_false (τ : Taint.T) (m : MemOp) (w : Nat) :
    ∀ sl ∈ Taint.storeSlotsK τ m w false, sl ∈ τ.slots := by
  unfold Taint.storeSlotsK
  split
  · cases Nat.ble _ _ <;> simp only [Bool.cond_false, Bool.cond_true]
    · intro _ h; simp at h
    · intro _ h; simp only [KList.filter_eq, List.mem_filter] at h; exact h.1
  · intro _ h; simp at h

/-- A store keeps or removes slots, or adds one at the head; any other
instruction keeps them. -/
theorem stepKD_slots_cases {τ τ' : Taint.T} {i : Instr} (h : Taint.stepKD τ i = some τ') :
    (∀ sl ∈ τ'.slots, sl ∈ τ.slots) ∨ (mayAdd τ i = true ∧ ∃ x, τ'.slots = x :: τ.slots) := by
  cases hw : writesMem i
  · exact .inl fun sl hs => stepKD_slots hw h ▸ hs
  · have kd : ∀ {m w p}, Taint.storeStepKD τ m w p = some τ' →
        (∀ sl ∈ τ'.slots, sl ∈ τ.slots) ∨ (p = true ∧ ∃ x, τ'.slots = x :: τ.slots) := by
      intro m w p h
      simp only [Taint.storeStepKD] at h
      cases hm : Taint.memPub τ m <;> simp only [hm, Bool.cond_false, Bool.cond_true, reduceCtorEq,
        Option.some.injEq] at h
      subst h
      rcases storeSlotsKD_cases τ m w p with h | h
      · exact .inl h
      · exact .inr h
    have k : ∀ {m w}, Taint.storeStepK τ m w false = some τ' → ∀ sl ∈ τ'.slots, sl ∈ τ.slots := by
      intro m w h
      simp only [Taint.storeStepK] at h
      cases hm : Taint.memPub τ m <;> simp only [hm, Bool.cond_false, Bool.cond_true, reduceCtorEq,
        Option.some.injEq] at h
      subst h
      exact storeSlotsK_false τ m w
    cases i <;> simp only [writesMem, reduceCtorEq] at hw <;> simp only [Taint.stepKD] at h
    case store => exact kd h
    case store32 => exact kd h
    case store8 => exact kd h
    case movdquStore => exact .inl (k h)
    case vmovdquStore l _ _ => cases l <;> exact .inl (k h)
    case vmovdqu32Store => exact .inl (k h)
    case stmxcsr => exact .inl (k h)

theorem mem_specBase {σ : T} {sl : Slot} (h : sl ∈ (specBase W σ).slots) :
    sl ∈ σ.base.slots ∧ ∀ p ∈ σ.young, p.1 = sl → W ≤ p.2 := by
  simp only [specBase, old, KList.filter_eq, List.mem_filter, KList.all_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq] at h
  refine ⟨h.1, fun p hp he => ?_⟩
  rcases h.2 p hp with h' | h'
  · subst he; simp only [Bool.eq_false_iff, ne_eq, mem3_iff, List.mem_singleton, not_true_eq_false] at h'
  · exact h'

theorem specBase_nil {σ : T} (h : σ.young = []) : specBase W σ = σ.base := by
  have : old W σ = fun _ => true := by funext sl; simp only [old, h]; rfl
  simp only [specBase, this, KList.filter_eq]
  rw [List.filter_eq_self.mpr (fun _ _ => rfl)]

/-- The state the loads of an instruction see agrees on `specBase`. -/
theorem Agree.view {σ : T} {a b : SState} (ha : Agree W σ a b) :
    Taint.Agree (specBase W σ) { a.arch with mem := Ssb.view W a } { b.arch with mem := Ssb.view W b } where
  rf := ha.base.rf
  wr := ha.base.wr
  wf₁ := ha.base.wf₁
  wf₂ := ha.base.wf₂
  lo := ha.base.lo
  ok sl h := ha.base.ok sl (mem_specBase h).1
  slots sl h j h₁ h₂ := by
    obtain ⟨hb, hh⟩ := mem_specBase h
    have he : byteAddr a.arch sl.1 j = byteAddr b.arch sl.1 j := ha.base.byteAddr_eq hb h₂
    show Ssb.view W a (byteAddr a.arch sl.1 j) = Ssb.view W b (byteAddr b.arch sl.1 j)
    simp only [Ssb.view, ← he, ← ha.dirs, ← ha.n]
    split
    · exact (ha.hist sl hb _ (by omega) (fun p hp hs => by have := hh p hp hs; omega) j h₁ h₂).trans
        (by rw [he])
    · exact (ha.base.slots sl hb j h₁ h₂).trans (by rw [he])

theorem getD_shift {α} (x : α) (l : List α) (d d' : α) {k : Nat} (hk : k + 1 < W) (hl : W ≤ l.length + 1) :
    ((x :: l).take W).getD (k + 1) d = l.getD k d' := by
  have : k < l.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hk, ite_true, List.getElem?_cons_succ,
    List.getElem?_eq_getElem this, Option.getD_some]

theorem getD_shift0 {α} (x : α) (l : List α) (d : α) (hW : 0 < W) : ((x :: l).take W).getD 0 d = x := by
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rfl

/-- A slot of `slots'` that is not public now is young. -/
theorem old_of_aged {σ : T} {slots' : List Slot} {sl : Slot} (hs : sl ∈ slots')
    (hn : (∀ sl ∈ slots', sl ∈ σ.base.slots) ∨ ∃ x, slots' = x :: σ.base.slots)
    {k : Nat} (hy : ∀ p ∈ aged W σ slots', p.1 = sl → k < p.2) : sl ∈ σ.base.slots := by
  rcases hn with hn | ⟨x, rfl⟩
  · exact hn sl hs
  · rcases List.mem_cons.mp hs with rfl | hs
    · by_contra hc
      have := hy (sl, 0) (by
        have : Taint.mem3 sl σ.base.slots = false := by
          rw [Bool.eq_false_iff, ne_eq, mem3_iff]; exact hc
        simp only [aged, added, this, KList.append_eq, Bool.cond_false,
          List.mem_append, List.mem_singleton, true_or]) rfl
      omega
    · exact hs

theorem mem_aged {σ : T} {slots' : List Slot} {sl : Slot} (hs : sl ∈ slots')
    (hn : (∀ sl ∈ slots', sl ∈ σ.base.slots) ∨ ∃ x, slots' = x :: σ.base.slots)
    {k : Nat} (hW : k + 1 < W)
    (hy : ∀ p ∈ aged W σ slots', p.1 = sl → k + 1 < p.2) :
    sl ∈ σ.base.slots ∧ ∀ p ∈ σ.young, p.1 = sl → k < p.2 := by
  have hin : sl ∈ σ.base.slots := old_of_aged hs hn fun p hp he => by have := hy p hp he; omega
  refine ⟨hin, fun p hp he => ?_⟩
  by_cases hb : p.2 + 1 < W
  · have := hy (p.1, p.2 + 1) (by
      simp only [aged, KList.append_eq, KList.map_eq, KList.filter_eq, List.mem_append, List.mem_filter,
        List.mem_map, Nat.blt_eq]
      exact .inr ⟨⟨p, hp, rfl⟩, hb⟩) he
    omega
  · omega

/-- The remembered memories after an instruction that keeps the regions. -/
theorem Agree.shift {σ : T} {a b : SState} (ha : Agree W σ a b) {τ' : Taint.T}
    (hn : (∀ sl ∈ τ'.slots, sl ∈ σ.base.slots) ∨ ∃ x, τ'.slots = x :: σ.base.slots) {s₁ s₂ : State}
    (hw₁ : s₁.wr = a.arch.wr) (hw₂ : s₂.wr = b.arch.wr) :
    HistAgree W { base := τ', young := aged W σ τ'.slots } (next W a false s₁) (next W b false s₂) := by
  intro sl hsl k hW hy j h₁ h₂
  have ba₁ : byteAddr s₁ sl.1 j = byteAddr a.arch sl.1 j := by simp only [byteAddr, region, hw₁]
  have ba₂ : byteAddr s₂ sl.1 j = byteAddr b.arch sl.1 j := by simp only [byteAddr, region, hw₂]
  simp only [next, Bool.false_eq_true, ite_false, ba₁, ba₂]
  rcases k with _ | k
  · have hin : sl ∈ σ.base.slots := old_of_aged hsl hn hy
    rw [getD_shift0 _ _ _ hW, getD_shift0 _ _ _ hW]
    exact ha.base.slots sl hin j h₁ h₂
  · obtain ⟨hin, hy'⟩ := mem_aged hsl hn hW hy
    rw [getD_shift _ _ _ a.arch.mem hW (by rw [ha.len₁]; omega),
      getD_shift _ _ _ b.arch.mem hW (by rw [ha.len₂]; omega)]
    exact ha.hist sl hin k (by omega) hy' j h₁ h₂

theorem length_shift {α} (a : List α) (x : α) (h : a.length = W) : ((x :: a).take W).length = W := by
  simp only [List.length_take, List.length_cons, h]; omega

set_option hygiene false in
/-- For `stepKD_slots_irrel` (on its hypothesis `h`): the analysis of an
instruction, from a taint that differs only in its slots, differs only in its
slots. -/
local macro "irrel_tac" : tactic => `(tactic| (
  simp only [Taint.stepKD, Taint.aluStepK, Taint.adxStepK, Taint.storeStepKD, Taint.storeStepK,
    Bool.cond_eq_ite] at h ⊢
  first
  | (cases h; exact ⟨_, rfl, rfl⟩)
  | cases h
  | (split at h
     · rename_i hc; cases h; exact ⟨_, ite_eq_left hc, rfl⟩
     · cases h)))

theorem stepKD_slots_irrel {τ τ₀ : Taint.T} {i : Instr} (hr : readsSlots i = false)
    (h : Taint.stepKD τ i = some τ₀) (S : List Slot) :
    ∃ τv, Taint.stepKD { τ with slots := S } i = some τv ∧ { τv with slots := τ₀.slots } = τ₀ := by
  cases i
  case vmovdquStore l _ _ => cases l <;> irrel_tac
  case mov d src => cases src <;> simp only [readsSlots, reduceCtorEq] at hr <;> irrel_tac
  case mov32 d src => cases src <;> simp only [readsSlots, reduceCtorEq] at hr <;> irrel_tac
  all_goals irrel_tac

theorem kind_reads {i : Instr} (h : kind i ≠ .reads) : readsSlots i = false := by
  cases i <;> simp only [readsSlots]
  all_goals first | rfl | (rename_i src; cases src <;> first | rfl | exact absurd rfl h)

theorem kind_fence {i : Instr} : kind i = .fence → fence i = true := by
  cases i <;> simp only [kind, fence, reduceCtorEq, imp_false, imp_self]
  all_goals (rename_i src; cases src <;> simp only [reduceCtorEq, not_false_eq_true])

theorem stepFast_eq (σ : T) (τ : Taint.T) (i : Instr) :
    stepFast σ τ i = (Taint.stepKD τ i).map fun τ₀ =>
      { base := τ₀, young := bif mayAdd τ i then added σ τ₀.slots else [] } := by
  cases i
  case vmovdquStore l _ _ => cases l <;> rfl
  all_goals simp only [stepFast, Taint.stepKD, mayAdd, Bool.cond_eq_ite, Bool.false_eq_true,
    ite_false] <;> (try split) <;> rfl

theorem added_of_sub {σ : T} {s : List Slot} (h : ∀ sl ∈ s, sl ∈ σ.base.slots) : added σ s = [] := by
  cases s with
  | nil => rfl
  | cons x _ =>
    have : Taint.mem3 x σ.base.slots = true := mem3_iff.mpr (h x (List.mem_cons_self ..))
    simp only [added, this, Bool.cond_true]

theorem aged_nil {σ : T} (h : σ.young = []) (slots' : List Slot) : aged W σ slots' = added σ slots' := by
  simp only [aged, h, KList.append_eq, KList.map_eq, KList.filter_eq, List.map_nil, List.filter_nil,
    List.append_nil]

theorem step_sound {σ σ' : T} {i : Instr} {a b a' b' : SState} (ha : Agree W σ a b)
    (hs : step W σ i = some σ') (e₁ : (isa W).exec i a = some a') (e₂ : (isa W).exec i b = some b') :
    (isa W).addrs i a = (isa W).addrs i b ∧ Agree W σ' a' b' := by
  obtain ⟨τ₀, h₀, τv, hv, hl, y, hy, rfl⟩ : ∃ τ₀, Taint.stepKD σ.base i = some τ₀ ∧
      ∃ τv, Taint.stepKD (specBase W σ) i = some τv ∧ τv.lens = τ₀.lens ∧
      ∃ y, (fence i = false → y = aged W σ τ₀.slots) ∧
      σ' = { base := { τv with slots := τ₀.slots }, young := y } := by
    clear e₁ e₂
    simp only [step] at hs
    split at hs
    · rename_i hy
      rw [stepFast_eq, Option.map_eq_some_iff] at hs
      obtain ⟨τ₀, h₀, rfl⟩ := hs
      refine ⟨τ₀, h₀, τ₀, by rw [specBase_nil hy]; exact h₀, rfl, _, fun _ => ?_, rfl⟩
      rw [aged_nil hy]
      rcases stepKD_slots_cases h₀ with h | ⟨hm, -⟩
      · rw [added_of_sub h]; cases mayAdd σ.base i <;> rfl
      · rw [hm, Bool.cond_true]
    · simp only [Option.bind_eq_some_iff] at hs
      obtain ⟨τ₀, h₀, hs⟩ := hs
      split at hs
      · rename_i hk
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨τv, hv, hs⟩ := hs
        cases hl : τv.lens == τ₀.lens <;> simp only [hl, Bool.cond_false, Bool.cond_true, reduceCtorEq,
          Option.some.injEq] at hs
        subst hs
        exact ⟨τ₀, h₀, τv, hv, beq_iff_eq.mp hl, _, fun _ => rfl, rfl⟩
      · rename_i hk; cases hs
        obtain ⟨τv, hv, he⟩ := stepKD_slots_irrel (kind_reads (by rw [hk]; decide)) h₀ (specBase W σ).slots
        refine ⟨τ₀, h₀, τv, hv, (congrArg (·.lens) he :), [], fun hf => ?_, by rw [he]⟩
        rw [kind_fence hk] at hf; cases hf
      · rename_i hk; cases hs
        obtain ⟨τv, hv, he⟩ := stepKD_slots_irrel (kind_reads (by rw [hk]; decide)) h₀ (specBase W σ).slots
        exact ⟨τ₀, h₀, τv, hv, (congrArg (·.lens) he :), _, fun _ => rfl, by rw [he]⟩
  simp only [isa, spec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨r₀₁, f₀₁, r₁, f₁, rfl⟩ := e₁
  obtain ⟨r₀₂, f₀₂, r₂, f₂, rfl⟩ := e₂
  obtain ⟨hadd, a₀⟩ := (X86_64.taint).step_sound ha.base h₀ f₀₁ f₀₂
  obtain ⟨-, av⟩ := (X86_64.taint).step_sound ha.view hv f₁ f₂
  have w₀₁ := exec_wr f₀₁
  have w₀₂ := exec_wr f₀₂
  have w₁ : r₁.wr = a.arch.wr := by have := exec_wr f₁; exact this
  have w₂ : r₂.wr = b.arch.wr := by have := exec_wr f₂; exact this
  have base : Taint.Agree { τv with slots := τ₀.slots } { r₁ with mem := r₀₁.mem } { r₂ with mem := r₀₂.mem } :=
    { rf := av.rf
      wr := av.wr
      wf₁ := av.wf₁
      wf₂ := av.wf₂
      lo := av.lo
      ok := fun sl h => by show _ ≤ τv.lens.getD _ _; rw [hl]; exact a₀.ok sl h
      slots := fun sl h j h₁ h₂ => by
        show r₀₁.mem (byteAddr r₁ _ _) = r₀₂.mem (byteAddr r₂ _ _)
        have := a₀.slots sl h j h₁ h₂
        simp only [byteAddr, region, w₁, w₂, w₀₁, w₀₂] at this ⊢
        exact this }
  refine ⟨hadd, ⟨base, ha.dirs, by simp only [next, ha.n], ?_, ?_, ?_⟩⟩ <;>
    cases hf : fence i <;> simp only [next, Bool.false_eq_true, ite_false, ite_true]
  · exact length_shift _ _ ha.len₁
  · exact List.length_replicate
  · exact length_shift _ _ ha.len₂
  · exact List.length_replicate
  · rw [hy hf]
    exact ha.shift (τ' := { τv with slots := τ₀.slots })
      ((stepKD_slots_cases (τ' := τ₀) h₀).imp_right (·.2)) w₁ w₂
  · intro sl hsl k hW _ j h₁ h₂
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hW, ite_true, Option.getD_some]
    have := a₀.slots sl hsl j h₁ h₂
    simp only [byteAddr, region, w₁, w₂, w₀₁, w₀₂] at this ⊢
    exact this

theorem meet_left {σ₁ σ₂ : T} {a b : SState} (h : Agree W σ₁ a b) : Agree W (meet σ₁ σ₂) a b where
  base := Taint.meet_left h.base
  dirs := h.dirs
  n := h.n
  len₁ := h.len₁
  len₂ := h.len₂
  hist sl hsl k hk hy := by
    simp only [meet, Taint.meet] at hsl
    split at hsl <;> [skip; cases hsl]
    refine h.hist sl (List.mem_filter.mp hsl).1 k hk fun p hp => hy p ?_
    simp only [meet, KList.append_eq, List.mem_append]; exact .inl hp

theorem meet_right {σ₁ σ₂ : T} {a b : SState} (h : Agree W σ₂ a b) : Agree W (meet σ₁ σ₂) a b where
  base := Taint.meet_right h.base
  dirs := h.dirs
  n := h.n
  len₁ := h.len₁
  len₂ := h.len₂
  hist sl hsl k hk hy := by
    simp only [meet, Taint.meet] at hsl
    split at hsl <;> [skip; cases hsl]
    refine h.hist sl (by simpa only [List.contains_eq_mem, decide_eq_true_eq] using
      (List.mem_filter.mp hsl).2) k hk fun p hp => hy p ?_
    simp only [meet, KList.append_eq, List.mem_append]; exact .inr hp

theorem le_sound {τ σ : T} {a b : SState} (hle : le τ σ = true) (h : Agree W σ a b) : Agree W τ a b := by
  simp only [le, Bool.and_eq_true, KList.all_eq, KList.any_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq, mem3_iff, List.mem_singleton] at hle
  obtain ⟨hb, hh⟩ := hle
  have hb' := Taint.leK_eq ▸ hb
  refine { base := Taint.le_sound hb' h.base
           dirs := h.dirs
           n := h.n
           len₁ := h.len₁
           len₂ := h.len₂
           hist := fun sl hsl k hk hy => ?_ }
  have hs : sl ∈ σ.base.slots := by
    simp only [Taint.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hb'
    exact hb'.1.2 sl hsl
  refine h.hist sl hs k hk fun q hq he => ?_
  rcases hh q hq with h' | ⟨p, hp, hpq, hle⟩
  · subst he; simp only [Bool.eq_false_iff, ne_eq, mem3_iff] at h'; exact absurd hsl h'
  · have := hy p hp (by rw [hpq, he]); omega

theorem call_wr {s s' : State} (h : X86_64.call s = some s') : s'.wr = s.wr := by
  simp only [X86_64.call, Option.some.injEq] at h; subst h; rfl

theorem ret_wr {s₁ s₂ s' : State} (h : X86_64.ret s₁ s₂ = some s') : s'.wr = s₂.wr := by
  simp only [X86_64.ret] at h; split at h <;> cases h; rfl

/-- A call forgets every slot, so nothing is young. -/
def call (σ : T) : Option T := (Taint.callStep σ.base).map fun τ => { base := τ, young := [] }

variable (W) in
def ret (σ : T) : Option T := (Taint.retStep σ.base).map fun τ => { base := τ, young := aged W σ τ.slots }

theorem call_sound {σ σ' : T} {a b a' b' : SState} (ha : Agree W σ a b) (hs : call σ = some σ')
    (e₁ : (isa W).call a = some a') (e₂ : (isa W).call b = some b') :
    (isa W).callAddrs a = (isa W).callAddrs b ∧ Agree W σ' a' b' := by
  simp only [call, Option.map_eq_some_iff] at hs
  obtain ⟨τ, hτ, rfl⟩ := hs
  simp only [isa, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨s₁, f₁, rfl⟩ := e₁
  obtain ⟨s₂, f₂, rfl⟩ := e₂
  obtain ⟨hadd, h⟩ := Taint.call_sound ha.base hτ f₁ f₂
  have hsl : τ.slots = [] := by
    simp only [Taint.callStep] at hτ; split at hτ <;> cases hτ; rfl
  refine ⟨hadd, ⟨h, ha.dirs, by simp only [next, ha.n], length_shift _ _ ha.len₁, length_shift _ _ ha.len₂,
    fun sl hs => ?_⟩⟩
  simp only [hsl, List.not_mem_nil] at hs

theorem retStep_slots {τ τ' : Taint.T} (h : Taint.retStep τ = some τ') : τ'.slots = τ.slots := by
  simp only [Taint.retStep] at h; split at h <;> cases h; rfl

theorem ret_sound {σ σ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : SState} (ha : Agree W σ b₁ b₂) (hs : ret W σ = some σ')
    (e₁ : (isa W).ret a₁ b₁ = some c₁) (e₂ : (isa W).ret a₂ b₂ = some c₂) :
    (isa W).retAddrs b₁ = (isa W).retAddrs b₂ ∧ Agree W σ' c₁ c₂ := by
  simp only [ret, Option.map_eq_some_iff] at hs
  obtain ⟨τ, hτ, rfl⟩ := hs
  simp only [isa, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨s₁, f₁, rfl⟩ := e₁
  obtain ⟨s₂, f₂, rfl⟩ := e₂
  obtain ⟨hadd, h⟩ := Taint.ret_sound ha.base hτ f₁ f₂
  exact ⟨hadd, ⟨h, ha.dirs, by simp only [next, ha.n], length_shift _ _ ha.len₁, length_shift _ _ ha.len₂,
    ha.shift (τ' := τ) (.inl fun sl hs => retStep_slots hτ ▸ hs) (ret_wr f₁) (ret_wr f₂)⟩⟩

variable (W) in
/-- Taint tracking for speculative store bypass. Frames are not analysed (as
in `X86_64.taint`). -/
def taint : VG.Taint (isa W) where
  T := T
  Agree := Agree W
  step := step W
  step_sound := step_sound
  condPub σ _ := σ.base.flags
  cond_sound ha hc := Taint.cond_sound ha.base hc
  meet := meet
  meet_left := meet_left
  meet_right := meet_right
  le := le
  le_sound := le_sound
  call := call
  call_sound := call_sound
  ret := ret W
  ret_sound := ret_sound
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

/-- A successful check proves speculative constant time. -/
theorem specCT {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog X86_64.isa}
    (τ : Taint.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → Taint.Agree τ s₁ s₂)
    (hτ : τ.slots = [])
    {hc : VG.Taint.Hint T} (h : ((taint W).check (T.init τ) c hc).isSome = true) :
    SpecCT W Pre Pub c :=
  VG.Taint.constantTime (A := taint W) (T.init τ)
    (fun a b h₁ h₂ hp => ⟨hpub _ _ h₁.1 h₂.1 hp.1, hp.2.1, hp.2.2, h₁.2, h₂.2,
      fun sl hs => by simp only [T.init, hτ, List.not_mem_nil] at hs⟩) h

end VG.X86_64.Ssb
