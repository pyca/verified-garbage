module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Offset

/-!
# x86-64 residue: clearing only the registers that may hold secrets

`scrub v rb xs ps gs ks cs c` clears the SSE registers `xs` and the
general-purpose registers `ps` and `gs` (and the upper bits of `rax`).
`Verified.scrubM` takes those from the code's instructions: every SSE
register if any instruction may write one, every caller-saved register any
instruction may write (`xsOf`, `gsOf`). Code that calls a function using the
vector registers on one path only, and clears them itself at the end of that
path, needs none of them cleared on return; nor the general-purpose registers
it leaves public on every path.

`Verified.scrubPart` clears the registers `xs` and `gs` given, any of them,
if two runs end agreeing on every register the clearing keeps (`RegsOk`):
the clearing of fewer registers runs along the same trace to the same state
but for the registers it keeps, so it is verified, and returns without
secret residue, if the clearing of those `Verified.scrubM` chooses does
(`hall`). The clearing of the stack and of MXCSR is the same in both.
`RegsOk` follows from what each run leaves in those registers, as
`resOk_of_leaves` gives the stack's `ResOk` (`RegLeaves`, `regsOk_of_leaves`).
`withScrubResCR` is `RScrub.withScrubResC` with the registers cleared given.

Code that clears what it leaves need not wipe the stack either, but for
the return addresses its calls leave below the stack pointer: which of the
state's `unknowns` each is depends on the path, and on how many calls the
functions it calls make. Two runs that agree on them on entry, along the
same trace, leave the same ones (`StackLock.lock`): their traces split
alike (`UpperLock.lock`), so their calls are the same calls, from the same
stack pointer, and push the same unknowns. So, too, with the vector
registers of code that clears them after the calls that use them
(`VecLock.step`, `VecLock.lock`, `regsOk_of_vec`): what they hold after
each piece of the code is either what they held before it or zero, as the
path says.

It is a module of its own, not part of `Scrub.lean`, so that the many
modules that import `Scrub.lean` are not rebuilt for it.
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- Two runs of `c` from states that `NoResidue` relates end agreeing on the
registers that the clearing of `xs`, `ps` and `gs` keeps: the caller-saved
general-purpose registers but `rax` outside `ps` and `gs`, and the vector
registers `zmm0`–`zmm15` outside `xs`, all their bits. -/
def RegsOk (c : Prog isa) (k : Contract isa) (xs : List XReg) (ps gs : List Reg) : Prop :=
  ∀ s₁ s₂ t₁ t₂ u₁ u₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
    (∀ r ∈ scratchRegs, r ∉ ps → r ∉ gs → u₁.gpr r = u₂.gpr r) ∧
    ∀ x, x ∉ xs → u₁.xmm x = u₂.xmm x ∧ u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

end

/-! ## Registrations -/

end VG.X86_64.Scrub

/-! ## Return addresses, in two runs along the same path -/

namespace VG.X86_64.StackLock

open VG VG.X86_64 VG.X86_64.UpperLock

/-- Two states agree on the stack pointer, on the return addresses calls
will push (`State.unknowns`), and on the bytes `S`, which neither may
write. -/
structure Same (S : Addr → Prop) (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  unk : s₁.unknowns = s₂.unknowns
  out₁ : ∀ x, S x → ∀ r ∈ s₁.wr, ¬ r.Contains x 1
  out₂ : ∀ x, S x → ∀ r ∈ s₂.wr, ¬ r.Contains x 1
  mem : ∀ x, S x → s₁.mem x = s₂.mem x

theorem writeW_congr {m₁ m₂ : Mem} {x : Addr} (h : m₁ x = m₂ x) (a : Addr) {w : Nat} (v : BitVec w) :
    m₁.writeW a v x = m₂.writeW a v x := by
  simp only [Mem.writeW, Mem.write]; split
  · rfl
  · exact h

theorem block_same {S : Addr → Prop} {is : List Instr} {s₁ s₂ u₁ u₂ : State} {t₁ t₂ : List Leak}
    (hb : ∀ i ∈ is, Taint.clobbers i .rsp = false) (e₁ : execBlock isa is s₁ = some (u₁, t₁))
    (e₂ : execBlock isa is s₂ = some (u₂, t₂)) (h : Same S s₁ s₂) : Same S u₁ u₂ := by
  obtain ⟨-, w₁, f₁⟩ := execBlock_regions e₁
  obtain ⟨-, w₂, f₂⟩ := execBlock_regions e₂
  have k₁ := execBlock_keep (M := isa) (fun s : State => s.unknowns) (ok := fun _ => True)
    (fun _ he => RTaint.exec_unknowns he) (fun _ _ => trivial) e₁
  have k₂ := execBlock_keep (M := isa) (fun s : State => s.unknowns) (ok := fun _ => True)
    (fun _ he => RTaint.exec_unknowns he) (fun _ _ => trivial) e₂
  refine ⟨by rw [execBlock_gpr hb e₁, execBlock_gpr hb e₂, h.rsp], by rw [k₁, k₂, h.unk],
    fun x hx => w₁ ▸ h.out₁ x hx, fun x hx => w₂ ▸ h.out₂ x hx, fun x hx => ?_⟩
  rw [f₁ x (h.out₁ x hx), f₂ x (h.out₂ x hx), h.mem x hx]

/-- A call, from states that agree: the same return address, at the same
place. -/
theorem call_same {S : Addr → Prop} {s₁ s₂ u₁ u₂ : State} (c₁ : isa.call s₁ = some u₁)
    (c₂ : isa.call s₂ = some u₂) (h : Same S s₁ s₂) : Same S u₁ u₂ := by
  simp only [isa, call, Option.some.injEq] at c₁ c₂
  subst c₁ c₂
  exact ⟨by simp only [RegUpd.gpr_setReg_self, h.rsp], by rw [h.unk], h.out₁, h.out₂,
    fun x hx => by rw [h.rsp, h.unk]; exact writeW_congr (h.mem x hx) _ _⟩

/-- A return, to states that agree. -/
theorem ret_same {S : Addr → Prop} {a₁ a₂ s₁ s₂ u₁ u₂ : State} (r₁ : isa.ret a₁ s₁ = some u₁)
    (r₂ : isa.ret a₂ s₂ = some u₂) (h : Same S s₁ s₂) : Same S u₁ u₂ := by
  simp only [isa, ret] at r₁ r₂
  split at r₁ <;> cases r₁
  split at r₂ <;> cases r₂
  exact ⟨by simp only [RegUpd.gpr_setReg_self, h.rsp], h.unk, h.out₁, h.out₂, h.mem⟩

theorem nosp_frame {i j : Instr} {b : Prog isa} {s s₁ : State} (hc : NoSp (.frame i b j))
    (hp : isa.push i s = some s₁) : False := by
  have hi := hc i (List.mem_cons_self ..)
  cases i <;> simp only [isa, push, reduceCtorEq] at hp
  all_goals simp [Taint.clobbers] at hi

/-- Two runs of code that never writes `rsp` (`NoSp`, so with no frame),
whose traces agree, extended by `r₁` and `r₂`, from states whose functions
called indirectly are at the same addresses and that agree on the stack
pointer, the unknowns and the bytes `S` they may not write (`Same`), end
agreeing on them: they take the same path (`UpperLock.lock`), so make the
same calls, each from the same stack pointer, with the same unknown as its
return address. -/
theorem lock {S : Addr → Prop} {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    NoSp c → ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → Same S s₁ s₂ → Same S s₁' s₂' := by
  induction e₁ with
  | block h₁ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ _ _ hs
    cases e₂ with
    | block h₂ => exact block_same hc h₁ h₂ hs
  | seq x₁ y₁ ihx ihy =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | seq x₂ y₂ =>
      have hca : NoSp _ := fun i hi => hc i (List.mem_append_left _ hi)
      have hcb : NoSp _ := fun i hi => hc i (List.mem_append_right _ hi)
      simp only [List.append_assoc] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨hx, -⟩ := UpperLock.lock x₁ x₂ ht fun n hn => hf n (.inl hn)
      subst hx
      exact ihy hcb y₂ (List.append_cancel_left ht) (fun n hn => by
        rw [Exec.syms x₁, Exec.syms x₂]; exact hf n (.inr hn)) (ihx hca x₂ ht (fun n hn => hf n (.inl hn)) hs)
  | iteT _ x₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact ih (fun i hi => hc i (List.mem_append_left _ hi)) x₂ ht (fun n hn => hf n (.inl hn)) hs
    | iteF _ _ => exact (branch_ne ht).elim
  | iteF _ x₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact ih (fun i hi => hc i (List.mem_append_right _ hi)) x₂ ht (fun n hn => hf n (.inr hn)) hs
    | iteT _ _ => exact (branch_ne ht.symm).elim
  | loopExit x₁ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      exact ih hc x₂ ht hf hs
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
  | loopNext x₁ _ _ ihx ihl =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      exact ihl hc l₂ ht' (fun n hn => by rw [Exec.syms x₁, Exec.syms x₂]; exact hf n hn) (ihx hc x₂ ht hf hs)
  | call hc₁ x₁ hr₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | call hc₂ x₂ hr₂ =>
      simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.cons.injEq] at ht
      exact ret_same hr₁ hr₂ (ih hc x₂ ht.2 (fun n hn => by rw [call_syms hc₁, call_syms hc₂]; exact hf n hn)
        (call_same hc₁ hc₂ hs))
  | frame hp₁ => exact fun hc => (nosp_frame hc hp₁).elim
  | icall hi₁ hc₁ x₁ hr₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    have hn := hf _ (List.mem_cons_self ..)
    have hcb : NoSp _ := fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    cases e₂ with
    | icall hi₂ hc₂ x₂ hr₂ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at ht
      exact ret_same hr₁ hr₂ (ih hcb x₂ ht.2.2 (fun m hm => by
        rw [call_syms hc₁, call_syms hc₂]; exact hf m (by simp [inames, hm])) (call_same hc₁ hc₂ hs))
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1, hn]
  | icallNext hi₁ hne₁ x₁ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hf hs
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      exact ih (fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))) x₂ ht
        (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))) hs
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

/-- `lock`, for two runs with the same trace. -/
theorem lock_eq {S : Addr → Prop} {c : Prog isa} (hc : NoSp c) {s₁ s₂ s₁' s₂' : State} {t : List Leak}
    (e₁ : Exec isa c s₁ t s₁') (e₂ : Exec isa c s₂ t s₂') (hf : ∀ n ∈ inames c, s₁.syms n = s₂.syms n)
    (h : Same S s₁ s₂) : Same S s₁' s₂' :=
  lock e₁ hc e₂ (r₁ := []) (r₂ := []) rfl hf h

/-- Code that never writes `rsp` and calls no function indirectly: what
`lock_eq` needs. -/
def Plain (c : Prog isa) : Prop := NoSp c ∧ inames c = []

namespace Plain

theorem block {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .rsp) = true) : Plain (.block is) :=
  ⟨fun i hi => by simpa using List.all_eq_true.mp h i hi, rfl⟩

theorem seq {a b : Prog isa} (ha : Plain a) (hb : Plain b) : Plain (.seq a b) :=
  ⟨fun i hi => (List.mem_append.mp hi).elim (ha.1 i) (hb.1 i), by simp only [inames, ha.2, hb.2, List.append_nil]⟩

theorem ite {c : Cond} {a b : Prog isa} (ha : Plain a) (hb : Plain b) : Plain (.ite c a b) :=
  ⟨fun i hi => (List.mem_append.mp hi).elim (ha.1 i) (hb.1 i), by simp only [inames, ha.2, hb.2, List.append_nil]⟩

theorem loop {c : Cond} {a : Prog isa} (ha : Plain a) : Plain (.loop a c) := ⟨ha.1, ha.2⟩

theorem call {n : String} {a : Prog isa} (ha : Plain a) : Plain (.call n a) := ⟨ha.1, ha.2⟩

end Plain

/-- `Plain` of code made of blocks, branches, loops and calls of plain code
(the hypotheses in context). -/
macro "plain_tac" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | refine Plain.seq ?_ ?_
  | refine Plain.ite ?_ ?_
  | refine Plain.loop ?_
  | refine Plain.call ?_
  | exact Plain.block (by decide))

/-- `RelCT`, keeping `Same S`: two runs that agree on the stack pointer,
the unknowns and the bytes `S` end agreeing on them. Code that never writes
`rsp` keeps it of itself (`RelS.lift`); a frame does with what its push
stores and its body leaves in the frame (`RelS` of the frame, by hand). -/
def RelS (S : Addr → Prop) (P : State → State → Prop) (c : Prog isa) (Q : State → State → Prop) : Prop :=
  RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ Same S s₁ s₂) c fun s₁ s₂ => Q s₁ s₂ ∧ Same S s₁ s₂

namespace RelS

variable {S : Addr → Prop} {P Q R : State → State → Prop}

/-- Code that never writes `rsp` and calls no function indirectly keeps
`Same` along the trace both runs share (`lock_eq`). -/
theorem lift {c : Prog isa} (h : RelCT isa P c Q) (hc : Plain c) : RelS S P c Q := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
  obtain ⟨rfl, hq⟩ := h s₁ s₂ t₁ t₂ u₁ u₂ hp.1 e₁ e₂
  exact ⟨rfl, hq, lock_eq hc.1 e₁ e₂ (by rw [hc.2]; nofun) hp.2⟩

/-- `RelS` with nothing after, and `RelCT` with `Q` after: `RelS` with `Q`. -/
theorem post {c : Prog isa} (h : RelS S P c fun _ _ => True) (h' : RelCT isa P c Q) : RelS S P c Q := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
  exact ⟨(h' _ _ _ _ _ _ hp.1 e₁ e₂).1, (h' _ _ _ _ _ _ hp.1 e₁ e₂).2, (h _ _ _ _ _ _ hp e₁ e₂).2.2⟩

theorem seq {c d : Prog isa} (a : RelS S P c R) (b : RelS S R d Q) : RelS S P (.seq c d) Q := RelCT.seq a b

theorem mono {P' Q' : State → State → Prop} {c : Prog isa} (h : RelS S P c Q) (hp : ∀ s₁ s₂, P' s₁ s₂ → P s₁ s₂)
    (hq : ∀ s₁ s₂, Q s₁ s₂ → Q' s₁ s₂) : RelS S P' c Q' :=
  RelCT.mono h (fun _ _ h => ⟨hp _ _ h.1, h.2⟩) fun _ _ h => ⟨hq _ _ h.1, h.2⟩

theorem ite {c : Cond} {t e : Prog isa} (hc : ∀ s₁ s₂, P s₁ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelS S (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some true) t Q)
    (he : RelS S (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some false) e Q) : RelS S P (.ite c t e) Q :=
  RelCT.ite (fun _ _ h => hc _ _ h.1) (RelCT.mono ht (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) fun _ _ h => h)
    (RelCT.mono he (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) fun _ _ h => h)

theorem of_false {c : Prog isa} (h : ∀ s₁ s₂, ¬ P s₁ s₂) : RelS S P c Q :=
  RelCT.of_false fun _ _ hp => h _ _ hp.1

theorem block_nil (h : ∀ s₁ s₂, P s₁ s₂ → Q s₁ s₂) : RelS S P (.block []) Q :=
  RelCT.block_nil fun _ _ hp => ⟨h _ _ hp.1, hp.2⟩

end RelS

section
open VG.Impl.StackScratch.X86_64
variable {sig : Sig} {nm : String} {e : Elem} {n bytes stack : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}

end

end VG.X86_64.StackLock

/-! ## The vector registers, in two runs along the same path -/

namespace VG.X86_64.VecLock

open VG VG.X86_64 VG.X86_64.UpperLock VG.Impl.Scrub.X86_64

/-- The SSE registers agree if `lo`, and their bits above 127 if `hi`. -/
def VA (a : Bool × Bool) (s₁ s₂ : State) : Prop :=
  (a.1 = true → s₁.xmm = s₂.xmm) ∧ (a.2 = true → s₁.ymmHi = s₂.ymmHi ∧ s₁.zmmHi = s₂.zmmHi)

/-- An instruction that keeps every vector register. -/
def plainI (i : Instr) : Bool := i.vecLevel == 0 && !writesVec i

/-- A block that zeroes the SSE registers at the level `lv` (`clearVec`),
then keeps them. -/
def clrB (lv : VecLevel) (is : List Instr) : Bool := is.take 16 == clearVec lv && (is.drop 16).all plainI

/-- What two runs along the same path agree on after `c`, from `a`: a block
that keeps the vector registers keeps the agreement; one that clears them
makes the SSE registers agree (zero), and the bits above too at a level
above `sse` (`vpxor`'s VEX encoding zeroes them); a call of code that may
write them keeps only the agreement of the bits above, if that code keeps
them (`UpperLock.up`). A loop agrees on what its body keeps from what it
agrees on. -/
def step (lv : VecLevel) : Prog isa → Bool × Bool → Bool × Bool
  | .block is, a => if clrB lv is then (true, lv != .sse || a.2) else if is.all plainI then a else (false, false)
  | .seq x y, a => step lv y (step lv x a)
  | .ite _ t e, a => ((step lv t a).1 && (step lv e a).1, (step lv t a).2 && (step lv e a).2)
  | .loop b _, a =>
    let a₁ := (a.1 && (step lv b a).1, a.2 && (step lv b a).2)
    if (!a₁.1 || (step lv b a₁).1) && (!a₁.2 || (step lv b a₁).2) then a₁ else (false, false)
  | .call _ b, a => if (instrs b).all plainI then a else (false, a.2 && up b true)
  | .frame _ b _, a => step lv b a
  | .icall .., _ => (false, false)

theorem va_mono {a b : Bool × Bool} {s₁ s₂ : State} (h : VA b s₁ s₂) (h₁ : a.1 = true → b.1 = true)
    (h₂ : a.2 = true → b.2 = true) : VA a s₁ s₂ :=
  ⟨fun e => h.1 (h₁ e), fun e => h.2 (h₂ e)⟩

theorem va_none {s₁ s₂ : State} : VA (false, false) s₁ s₂ := ⟨nofun, nofun⟩

theorem plain_keep {c : Prog isa} (hc : ∀ i ∈ instrs c, plainI i = true) {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') : s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  have hx := Residue.Exec.xmmKeep (fun i hi => by
    have := hc i hi; simp only [plainI, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this; exact this.2) e
  have hv := Residue.Exec.vecKeep0 (fun i hi => by
    have := hc i hi; simp only [plainI, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this; exact this.1) e
  simp only [Residue.vk0, Prod.mk.injEq] at hv
  exact ⟨hx, hv.2.2.2.1, hv.2.2.2.2⟩

theorem keep_va {a : Bool × Bool} {s₁ s₂ u₁ u₂ : State}
    (k₁ : u₁.xmm = s₁.xmm ∧ u₁.ymmHi = s₁.ymmHi ∧ u₁.zmmHi = s₁.zmmHi)
    (k₂ : u₂.xmm = s₂.xmm ∧ u₂.ymmHi = s₂.ymmHi ∧ u₂.zmmHi = s₂.zmmHi) (h : VA a s₁ s₂) : VA a u₁ u₂ :=
  ⟨fun e => by rw [k₁.1, k₂.1, h.1 e], fun e => by rw [k₁.2.1, k₂.2.1, k₁.2.2, k₂.2.2]; exact h.2 e⟩

/-- A block that clears: zero SSE registers, and the bits above zero too at
a level above `sse`, or kept. -/
theorem clr_run {lv : VecLevel} {is : List Instr} (h : clrB lv is = true) {s u : State} {t : List Leak}
    (e : execBlock isa is s = some (u, t)) :
    u.xmm = (fun _ => 0) ∧ (lv ≠ .sse → u.ymmHi = (fun _ => 0) ∧ u.zmmHi = (fun _ => 0)) ∧
      (lv = .sse → u.ymmHi = s.ymmHi ∧ u.zmmHi = s.zmmHi) := by
  simp only [clrB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [← List.take_append_drop 16 is, execBlock_append, h₁, clearVec, Scrub.execBlock_vecs] at e
  simp only [Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at e
  obtain ⟨⟨u', t'⟩, e', rfl, -⟩ := e
  have k := plain_keep (c := .block (is.drop 16)) (fun i hi => List.all_eq_true.mp h₂ i hi) (Exec.block e')
  rw [k.1, k.2.1, k.2.2]
  refine ⟨funext fun x => by simp [Scrub.clearedV, Scrub.mem_xregs x], fun hv => ⟨funext fun x => ?_,
    funext fun x => ?_⟩, fun hv => ⟨funext fun x => ?_, funext fun x => ?_⟩⟩
  all_goals simp [Scrub.clearedV, Scrub.mem_xregs x, hv]

theorem push_xmm {i : Instr} {s s₁ : State} (hp : isa.push i s = some s₁) : s₁.xmm = s.xmm := by
  cases i <;> simp only [isa, push, reduceCtorEq] at hp
  case push rs => split at hp <;> cases hp; exact Residue.pushRegs_xmm s rs
  case alloc => split at hp <;> cases hp; rfl

theorem pop_xmm {j : Instr} {s₁ s₂ s' : State} (hq : isa.pop j s₁ s₂ = some s') : s'.xmm = s₂.xmm := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at hq
  case pop r k => split at hq <;> cases hq; exact Residue.popReg_xmm s₂ _ _
  case free => split at hq <;> cases hq; rfl

theorem pushpop_keep {i : Instr} {s s₁ : State} (hp : isa.push i s = some s₁) :
    s₁.xmm = s.xmm ∧ s₁.ymmHi = s.ymmHi ∧ s₁.zmmHi = s.zmmHi := by
  have := Residue.push_vk0 hp
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨push_xmm hp, this.2.2.2.1, this.2.2.2.2⟩

theorem pop_keep {j : Instr} {s₁ s₂ s' : State} (hq : isa.pop j s₁ s₂ = some s') :
    s'.xmm = s₂.xmm ∧ s'.ymmHi = s₂.ymmHi ∧ s'.zmmHi = s₂.zmmHi := by
  have := Residue.pop_vk0 hq
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨pop_xmm hq, this.2.2.2.1, this.2.2.2.2⟩

theorem step_loop_fix {lv : VecLevel} {b : Prog isa} {c : Cond} {a : Bool × Bool}
    (h : (!a.1 || (step lv b a).1) && (!a.2 || (step lv b a).2) = true) : step lv (.loop b c) a = a := by
  rcases a with ⟨x, y⟩
  simp only [step]
  generalize hs : step lv b (x, y) = p at h ⊢
  rcases p with ⟨p₁, p₂⟩
  cases x <;> cases y <;> cases p₁ <;> cases p₂ <;> simp_all

/-- Two runs of `c` whose traces agree, extended by `r₁` and `r₂`, from
states whose functions called indirectly are at the same addresses and that
agree on the vector registers as `a` says, agree on them at the end as
`step lv c a` says. -/
theorem lock {lv : VecLevel} {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak} {a : Bool × Bool}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → VA a s₁ s₂ → VA (step lv c a) s₁' s₂' := by
  induction e₁ with
  | @block is _ _ _ h₁ =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ _ _ hs
    cases e₂ with
    | block h₂ =>
      simp only [step]
      split
      · rename_i hc
        obtain ⟨x₁, y₁, z₁⟩ := clr_run hc h₁
        obtain ⟨x₂, y₂, z₂⟩ := clr_run hc h₂
        refine ⟨fun _ => by rw [x₁, x₂], fun hh => ?_⟩
        by_cases hv : lv = .sse
        · subst hv
          simp only [bne_self_eq_false, Bool.false_or] at hh
          rw [(z₁ rfl).1, (z₂ rfl).1, (z₁ rfl).2, (z₂ rfl).2]; exact hs.2 hh
        · rw [(y₁ hv).1, (y₂ hv).1, (y₁ hv).2, (y₂ hv).2]; exact ⟨rfl, rfl⟩
      · split
        · rename_i _ hp
          exact keep_va (plain_keep (c := .block is) (fun i hi => List.all_eq_true.mp hp i hi) (Exec.block h₁))
            (plain_keep (c := .block is) (fun i hi => List.all_eq_true.mp hp i hi) (Exec.block h₂)) hs
        · exact va_none
  | seq x₁ y₁ ihx ihy =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | seq x₂ y₂ =>
      simp only [List.append_assoc] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨hx, -⟩ := UpperLock.lock x₁ x₂ ht fun n hn => hf n (.inl hn)
      subst hx
      exact ihy y₂ (List.append_cancel_left ht) (fun n hn => by
        rw [Exec.syms x₁, Exec.syms x₂]; exact hf n (.inr hn)) (ihx x₂ ht (fun n hn => hf n (.inl hn)) hs)
  | iteT _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact va_mono (ih x₂ ht (fun n hn => hf n (.inl hn)) hs) (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.1)
        (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.1)
    | iteF _ _ => exact (branch_ne ht).elim
  | iteF _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact va_mono (ih x₂ ht (fun n hn => hf n (.inr hn)) hs) (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.2)
        (fun e => by simp only [step, Bool.and_eq_true] at e; exact e.2)
    | iteT _ _ => exact (branch_ne ht.symm).elim
  | @loopExit b c _ _ _ x₁ _ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      have hb := ih x₂ ht hf hs
      simp only [step]
      split
      · exact va_mono hb (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
          (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
      · exact va_none
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
  | @loopNext b c _ _ _ _ _ x₁ _ _ ihx ihl =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      have hb := ihx x₂ ht hf hs
      simp only [step]
      split
      · rename_i hfix
        have a₁ := va_mono hb (a := ((a.1 && (step lv b a).1), (a.2 && (step lv b a).2)))
          (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
          (fun e => by simp only [Bool.and_eq_true] at e; exact e.2)
        have := ihl l₂ ht' (fun n hn => by rw [Exec.syms x₁, Exec.syms x₂]; exact hf n hn) a₁
        rwa [step_loop_fix hfix] at this
      · exact va_none
  | @call nm b _ _ _ _ _ hc₁ x₁ hr₁ _ =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    have e₁ : Exec isa (.call nm b) _ _ _ := .call hc₁ x₁ hr₁
    simp only [step]
    split
    · rename_i hp
      exact keep_va (plain_keep (c := .call nm b) (fun i hi => List.all_eq_true.mp hp i hi) e₁)
        (plain_keep (c := .call nm b) (fun i hi => List.all_eq_true.mp hp i hi) e₂) hs
    · refine ⟨nofun, fun e => ?_⟩
      simp only [Bool.and_eq_true] at e
      exact (UpperLock.lock e₁ e₂ ht hf).2 true e.2 fun _ => hs.2 e.1
  | frame hp₁ x₁ hq₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | frame hp₂ x₂ hq₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      have hb := ih x₂ ht (fun n hn => by rw [push_syms hp₁, push_syms hp₂]; exact hf n hn)
        (keep_va (pushpop_keep hp₁) (pushpop_keep hp₂) hs)
      exact keep_va (pop_keep hq₁) (pop_keep hq₂) hb
  | icall => intros; exact va_none
  | icallNext => intros; exact va_none

end VG.X86_64.VecLock

namespace VG.X86_64.HLock

open VG VG.X86_64 VG.X86_64.UpperLock VG.Impl.Scrub.X86_64

/-- `zmm16`–`zmm31` agree, if `a`. -/
def HA (a : Bool) (s₁ s₂ : State) : Prop := a = true → s₁.ymmH = s₂.ymmH ∧ s₁.zmmHiH = s₂.zmmHiH

/-- An instruction that keeps `zmm16`–`zmm31`. -/
def keepI (i : Instr) : Bool := decide (i.vecLevelR ≤ 1)

/-- A block that ends by zeroing `zmm16`–`zmm31` (`clearHigh .evex`). -/
def clrH (is : List Instr) : Bool := is.drop (is.length - 16) == hregs.map zeroH

/-- What two runs along the same path agree on in `zmm16`–`zmm31` after `c`,
from `a`: a block that ends by zeroing them makes them agree, one that keeps
them keeps the agreement; a call or frame as its body says. -/
def step : Prog isa → Bool → Bool
  | .block is, a => if clrH is then true else if is.all keepI then a else false
  | .seq x y, a => step y (step x a)
  | .ite _ t e, a => step t a && step e a
  | .loop b _, a =>
    let a₁ := a && step b a
    if !a₁ || step b a₁ then a₁ else false
  | .call _ b, a => step b a
  | .frame _ b _, a => step b a
  | .icall .., _ => false

theorem ha_mono {a b : Bool} {s₁ s₂ : State} (h : HA b s₁ s₂) (e : a = true → b = true) : HA a s₁ s₂ :=
  fun ha => h (e ha)

theorem keep_ha {a : Bool} {s₁ s₂ u₁ u₂ : State} (k₁ : u₁.ymmH = s₁.ymmH ∧ u₁.zmmHiH = s₁.zmmHiH)
    (k₂ : u₂.ymmH = s₂.ymmH ∧ u₂.zmmHiH = s₂.zmmHiH) (h : HA a s₁ s₂) : HA a u₁ u₂ :=
  fun e => by rw [k₁.1, k₂.1, k₁.2, k₂.2]; exact h e

theorem keep_run {c : Prog isa} (hc : ∀ i ∈ instrs c, keepI i = true) {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') : s'.ymmH = s.ymmH ∧ s'.zmmHiH = s.zmmHiH := by
  have := Residue.Exec.vecKeep1R (fun i hi => by simpa [keepI] using hc i hi) e
  simp only [Residue.vk1R, Prod.mk.injEq] at this
  exact this

theorem clr_run {is : List Instr} (h : clrH is = true) {s u : State} {t : List Leak}
    (e : execBlock isa is s = some (u, t)) : u.ymmH = (fun _ => 0) ∧ u.zmmHiH = (fun _ => 0) := by
  simp only [clrH, beq_iff_eq] at h
  rw [← List.take_append_drop (is.length - 16) is, execBlock_append, h] at e
  cases e₁ : execBlock isa (is.take (is.length - 16)) s with
  | none => rw [e₁] at e; cases e
  | some p =>
    rw [e₁] at e
    rw [Option.bind_some, Scrub.execBlock_zeroH, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨funext fun h => by simp [Scrub.mem_hregs h], funext fun h => by simp [Scrub.mem_hregs h]⟩

theorem push_hk {i : Instr} {s s₁ : State} (hp : isa.push i s = some s₁) :
    s₁.ymmH = s.ymmH ∧ s₁.zmmHiH = s.zmmHiH := by
  have := Residue.push_vk0 hp
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

theorem pop_hk {j : Instr} {s₁ s₂ s' : State} (hq : isa.pop j s₁ s₂ = some s') :
    s'.ymmH = s₂.ymmH ∧ s'.zmmHiH = s₂.zmmHiH := by
  have := Residue.pop_vk0 hq
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

theorem call_hk {s s₁ : State} (h : isa.call s = some s₁) : s₁.ymmH = s.ymmH ∧ s₁.zmmHiH = s.zmmHiH := by
  simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem ret_hk {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.ymmH = s₂.ymmH ∧ s'.zmmHiH = s₂.zmmHiH := by
  simp only [isa, ret] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

theorem step_loop_fix {b : Prog isa} {c : Cond} {a : Bool} (h : (!a || step b a) = true) :
    step (.loop b c) a = a := by
  cases a <;> simp_all [step]

/-- Two runs of `c` whose traces agree, extended by `r₁` and `r₂`, from
states whose functions called indirectly are at the same addresses and that
agree on `zmm16`–`zmm31` if `a`, agree on them at the end if `step c a`. -/
theorem lock {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak} {a : Bool}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → HA a s₁ s₂ → HA (step c a) s₁' s₂' := by
  induction e₁ with
  | @block is _ _ _ h₁ =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ _ _ hs
    cases e₂ with
    | block h₂ =>
      simp only [step]
      split
      · rename_i hc
        obtain ⟨y₁, z₁⟩ := clr_run hc h₁
        obtain ⟨y₂, z₂⟩ := clr_run hc h₂
        exact fun _ => ⟨by rw [y₁, y₂], by rw [z₁, z₂]⟩
      · split
        · rename_i _ hp
          exact keep_ha (keep_run (c := .block is) (fun i hi => List.all_eq_true.mp hp i hi) (Exec.block h₁))
            (keep_run (c := .block is) (fun i hi => List.all_eq_true.mp hp i hi) (Exec.block h₂)) hs
        · exact nofun
  | seq x₁ y₁ ihx ihy =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | seq x₂ y₂ =>
      simp only [List.append_assoc] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨hx, -⟩ := UpperLock.lock x₁ x₂ ht fun n hn => hf n (.inl hn)
      subst hx
      exact ihy y₂ (List.append_cancel_left ht) (fun n hn => by
        rw [Exec.syms x₁, Exec.syms x₂]; exact hf n (.inr hn)) (ihx x₂ ht (fun n hn => hf n (.inl hn)) hs)
  | iteT _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact ha_mono (ih x₂ ht (fun n hn => hf n (.inl hn)) hs) fun e => by
        simp only [step, Bool.and_eq_true] at e; exact e.1
    | iteF _ _ => exact (branch_ne ht).elim
  | iteF _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      exact ha_mono (ih x₂ ht (fun n hn => hf n (.inr hn)) hs) fun e => by
        simp only [step, Bool.and_eq_true] at e; exact e.2
    | iteT _ _ => exact (branch_ne ht.symm).elim
  | @loopExit b c _ _ _ x₁ _ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      have hb := ih x₂ ht hf hs
      simp only [step]
      split
      · exact ha_mono hb fun e => by simp only [Bool.and_eq_true] at e; exact e.2
      · exact nofun
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
  | @loopNext b c _ _ _ _ _ x₁ _ _ ihx ihl =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := UpperLock.lock x₁ x₂ ht hf
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      have hb := ihx x₂ ht hf hs
      simp only [step]
      split
      · rename_i hfix
        have a₁ := ha_mono hb (a := a && step b a) fun e => by simp only [Bool.and_eq_true] at e; exact e.2
        have := ihl l₂ ht' (fun n hn => by rw [Exec.syms x₁, Exec.syms x₂]; exact hf n hn) a₁
        rwa [step_loop_fix hfix] at this
      · exact nofun
  | call hc₁ x₁ hr₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | call hc₂ x₂ hr₂ =>
      simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.cons.injEq] at ht
      have hb := ih x₂ ht.2 (fun n hn => by rw [call_syms hc₁, call_syms hc₂]; exact hf n hn)
        (keep_ha (call_hk hc₁) (call_hk hc₂) hs)
      exact keep_ha (ret_hk hr₁) (ret_hk hr₂) hb
  | frame hp₁ x₁ hq₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ a e₂ ht hf hs
    cases e₂ with
    | frame hp₂ x₂ hq₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      have hb := ih x₂ ht (fun n hn => by rw [push_syms hp₁, push_syms hp₂]; exact hf n hn)
        (keep_ha (push_hk hp₁) (push_hk hp₂) hs)
      exact keep_ha (pop_hk hq₁) (pop_hk hq₂) hb
  | icall => intros; exact nofun
  | icallNext => intros; exact nofun

end VG.X86_64.HLock

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

end

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

end VG.X86_64.RScrub
