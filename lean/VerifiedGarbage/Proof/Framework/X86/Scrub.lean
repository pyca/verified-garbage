module

public import VerifiedGarbage.TCB.X86.Residue
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Returning without secret residue (x86, 32-bit)

`NoResidue` (`TCB/X86/Residue.lean`) asks that two runs of a function that
agree on its public data and on everything outside its buffers end agreeing
on everything outside the buffers but the result: the registers, the flags
(which must be defined), the XMM and MMX registers, the MMX mode, MXCSR, the
MCDT frames, and the memory outside the buffers.

The calling convention restores `ebx`, `esi`, `edi`, `ebp` and `esp`
(`abiPreserved`). What is left are the registers a callee may change, `eax`,
`ecx` and `edx`, the flags, and `xmm0`–`xmm7`: `tail rb`
(`Impl/Scrub/X86.lean`) sets them to constants, but the `rb` bits of the
result `edx ++ eax`. Every run leaves MXCSR and the MCDT frames as they were
(`Exec.keep`: an MCDT frame's pop restores what its push changed), and a run
of code with no MMX instruction (`Instr.isMmx`: none, nor an MMX frame)
leaves the MMX registers and mode as they were: a function whose code has
one is not covered here (the tail cannot clear the MMX registers, which only
an MMX frame may write, and which the precondition does not allow).

Code that calls nothing and has no frame (`Code.noCalls`) writes memory only
within the regions its state permits (`Exec.regions`), which are the
function's buffers: `scrub rb c` (`Verified.scrub`) returns without secret
residue. Code with calls and frames also writes the stack below `esp`: see
"Code with frames" below (`scrubF`, `Verified.scrubF`).

`scrubReg` and `scrubRegF` are registrations with their code scrubbed, which
prove it.
-/

@[expose] public section

namespace VG.X86

/-! ## What a run keeps -/

/-- An MMX instruction, or the push or pop of an MMX frame. -/
def Instr.isMmx : Instr → Bool
  | .mop _ | .mmxStore .. | .mmxEnter | .emms => true
  | _ => false

/-- `c`, and the functions it calls, make no indirect call. -/
def noIcall : Prog isa → Bool
  | .block _ => true
  | .seq a b => noIcall a && noIcall b
  | .ite _ t e => noIcall t && noIcall e
  | .loop b _ => noIcall b
  | .call _ b => noIcall b
  | .frame _ b _ => noIcall b
  | .icall .. => false

/-- What an instruction leaves: the unknowns, the MMX mode, MXCSR, the MCDT
frames, and, but for an MMX instruction, the MMX registers. -/
theorem exec_keep {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.unknowns = s.unknowns ∧ s'.mmx = s.mmx ∧ s'.mxcsr = s.mxcsr ∧ s'.mcdt = s.mcdt ∧
      (i.isMmx = false → s'.mm = s.mm) := by
  cases i with
  | store m r | store8 m r =>
    simp only [reduceExec, State.store32, State.store8] at h
    split at h <;> [skip; cases h]
    cases h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | movdquStore m r =>
    simp only [reduceExec, State.store128] at h
    split at h <;> [skip; cases h]
    cases h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | movqStore m r =>
    simp only [reduceExec, State.store64] at h
    split at h <;> [skip; cases h]
    cases h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | mov d src | movzx8 d src | movdquLoad d src | movqLoad d src =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | alu op d src =>
    simp only [reduceExec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split <;> exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | shift op d n =>
    simp only [reduceExec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | bswap d | mul d =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | pmuludq d r =>
    simp only [reduceExec] at h
    split at h <;> [skip; cases h]
    cases h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | xop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h
    cases op <;> exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | mop op =>
    simp only [reduceExec] at h
    rw [MOp.exec_eq h]; exact ⟨rfl, rfl, rfl, rfl, fun h => by simp [Instr.isMmx] at h⟩
  | mmxStore m r =>
    simp only [reduceExec, State.store64] at h
    split at h <;> [skip; cases h]
    split at h <;> [skip; cases h]
    cases h; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | symPush _ _ | push _ | pop _ _ | alloc _ | free _ | callr _ | mmxEnter | emms | mcdtEnter _ | mcdtLeave =>
    simp only [reduceExec, reduceCtorEq] at h

theorem pushRegs_keep (s : State) (rs : List Reg) :
    (pushRegs s rs).unknowns = s.unknowns ∧ (pushRegs s rs).mm = s.mm ∧ (pushRegs s rs).mmx = s.mmx ∧
      (pushRegs s rs).mxcsr = s.mxcsr ∧ (pushRegs s rs).mcdt = s.mcdt := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons x xs ih => exact ih _

theorem popReg_keep (s : State) (d : Reg) (k : Nat) :
    (popReg s d k).unknowns = s.unknowns ∧ (popReg s d k).mm = s.mm ∧ (popReg s d k).mmx = s.mmx ∧
      (popReg s d k).mxcsr = s.mxcsr ∧ (popReg s d k).mcdt = s.mcdt := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih => exact ih _

/-- How many of the unknowns a frame's push uses. -/
def pushUk : Instr → Nat
  | .symPush .. => 1
  | _ => 0

/-- How many of the unknowns a frame's pop uses. -/
def popUk : Instr → Nat
  | .free bytes => bytes / 2
  | .pop _ k => 2 * k
  | .mcdtLeave => 6
  | _ => 0

/-- What a frame's push leaves: it uses `pushUk i` unknowns, keeps MXCSR,
and, but for an MMX frame's, the MMX registers and mode; it adds a region
of `L` bytes at the head of `wr`, and opens an MCDT frame if and only if
`L = 9`. -/
theorem push_keep {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    s₁.unknowns = (fun n => s.unknowns (n + pushUk i)) ∧ s₁.mxcsr = s.mxcsr ∧
      (i.isMmx = false → s₁.mm = s.mm ∧ s₁.mmx = s.mmx) ∧
      ∃ a L, s₁.wr = ⟨a, L⟩ :: s.wr ∧ s₁.mcdt = s.mcdt + (if L = 9 then 1 else 0) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case symPush d name =>
    split at h <;> cases h
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, _, _, rfl, by
      simp only [show (4 : Nat) ≠ 9 by decide, ite_false, Nat.add_zero]; rfl⟩
  case mmxEnter =>
    split at h <;> cases h
    exact ⟨rfl, rfl, fun h => by simp [Instr.isMmx] at h, _, _, rfl, by
      simp only [show (0 : Nat) ≠ 9 by decide, ite_false, Nat.add_zero]⟩
  case mcdtEnter d =>
    split at h <;> cases h
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, _, _, rfl, by simp only [ite_true]⟩
  case alloc bytes =>
    split at h <;> cases h
    rename_i hc
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, _, _, rfl, by
      simp only [show bytes ≠ 9 by omega_using [hc.2.2.1], ite_false, Nat.add_zero]; rfl⟩
  case push rs =>
    split at h <;> cases h
    obtain ⟨u, m, x, c, d⟩ := pushRegs_keep s rs
    exact ⟨u, c, fun _ => ⟨m, x⟩, _, _, rfl, by
      simp only [show 4 * rs.length ≠ 9 by omega_using [], ite_false, Nat.add_zero]; exact d⟩

/-- What a frame's pop leaves: it uses `popUk j` unknowns, keeps MXCSR,
and, but for an MMX frame's, the MMX registers and mode; it closes an MCDT
frame if and only if the region at the head of `wr` has `L = 9` bytes. -/
theorem pop_keep {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.unknowns = (fun n => s₂.unknowns (n + popUk j)) ∧ s'.mxcsr = s₂.mxcsr ∧
      (j.isMmx = false → s'.mm = s₂.mm ∧ s'.mmx = s₂.mmx) ∧
      ∀ a L, s₁.wr.head? = some ⟨a, L⟩ → s'.mcdt = s₂.mcdt - (if L = 9 then 1 else 0) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case emms =>
    split at h <;> cases h
    rename_i hc
    refine ⟨rfl, rfl, fun h => by simp [Instr.isMmx] at h, fun a L hL => ?_⟩
    rw [hc.2.2.2, Option.some.injEq, Region.mk.injEq] at hL
    simp [← hL.2]
  case mcdtLeave =>
    split at h <;> cases h
    rename_i hc
    refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun a L hL => ?_⟩
    rw [hc.2.2.2.1, Option.some.injEq, Region.mk.injEq] at hL
    simp [← hL.2]
  case free bytes =>
    split at h <;> cases h
    rename_i hc
    refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun a L hL => ?_⟩
    rw [hc.2.2.2.2.2, Option.some.injEq, Region.mk.injEq] at hL
    simp only [← hL.2, show bytes ≠ 9 by omega_using [hc.2.2.1], ite_false, Nat.sub_zero]
    rfl
  case pop r k =>
    split at h <;> cases h
    rename_i hc
    obtain ⟨u, m, x, c, d⟩ := popReg_keep s₂ r k
    refine ⟨rfl, c, fun _ => ⟨m, x⟩, fun a L hL => ?_⟩
    rw [hc.2.2.2.2, Option.some.injEq, Region.mk.injEq] at hL
    simp only [← hL.2, show 4 * k ≠ 9 by omega_using [], ite_false, Nat.sub_zero]
    exact d

theorem ret_keep {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') :
    s'.unknowns = s₂.unknowns ∧ s'.mm = s₂.mm ∧ s'.mmx = s₂.mmx ∧ s'.mxcsr = s₂.mxcsr ∧
      s'.mcdt = s₂.mcdt ∧ s'.mem = s₂.mem := by
  simp only [isa, ret] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every run of code with no MMX instruction leaves the MMX registers and
mode, MXCSR and the MCDT frames as they were. -/
theorem Exec.keep {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hm : ∀ i ∈ instrs c, i.isMmx = false) :
    s'.mm = s.mm ∧ s'.mmx = s.mmx ∧ s'.mxcsr = s.mxcsr ∧ s'.mcdt = s.mcdt := by
  induction h with
  | block h =>
    have e := execBlock_keep (fun s : State => (s.mm, s.mmx, s.mxcsr, s.mcdt))
      (ok := fun i : Instr => i.isMmx = false) (fun hi he => by
        obtain ⟨-, x, c, d, m⟩ := exec_keep he
        simp only [m hi, x, c, d]) hm h
    simp only [Prod.mk.injEq] at e
    exact e
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨a, b, c, d⟩ := ih₁ fun i hi => hm i (List.mem_append_left _ hi)
    obtain ⟨a', b', c', d'⟩ := ih₂ fun i hi => hm i (List.mem_append_right _ hi)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  | iteT _ _ ih => exact ih fun i hi => hm i (List.mem_append_left _ hi)
  | iteF _ _ ih => exact ih fun i hi => hm i (List.mem_append_right _ hi)
  | loopExit _ _ ih => exact ih hm
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨a, b, c, d⟩ := ih₁ hm
    obtain ⟨a', b', c', d'⟩ := ih₂ hm
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  | call k _ q ih =>
    rw [call_callEntry, Option.some.injEq] at k; subst k
    obtain ⟨a, b, c, d⟩ := ih hm
    obtain ⟨-, a', b', c', d', -⟩ := ret_keep q
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  | icall _ k _ q ih =>
    rw [call_callEntry, Option.some.injEq] at k; subst k
    obtain ⟨a, b, c, d⟩ := ih fun i hi => hm i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    obtain ⟨-, a', b', c', d', -⟩ := ret_keep q
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  | icallNext _ _ _ ih => exact ih fun i hi => hm i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))
  | @frame i j _ s₀ s₁ s₂ _ _ p _ q ih =>
    have hi : i.isMmx = false := hm i (by simp [instrs])
    have hj : j.isMmx = false := hm j (by simp [instrs])
    obtain ⟨a, b, c, d⟩ := ih fun k hk => hm k (by simp [instrs, hk])
    obtain ⟨-, pc, pm, A, L, pw, pd⟩ := push_keep p
    obtain ⟨-, qc, qm, qd⟩ := pop_keep q
    have qd' := qd A L (by rw [pw]; rfl)
    refine ⟨((qm hj).1.trans a).trans (pm hi).1, ((qm hj).2.trans b).trans (pm hi).2,
      (qc.trans c).trans pc, ?_⟩
    rw [qd', d, pd]
    omega_using []

/-! ### Runs with the same trace use the same unknowns

The trace of a run records each branch it takes, and each instruction
leaks a number of addresses fixed by the instruction, so two runs of code
without indirect calls that leak the same trace take the same path: they
make the same calls and push and pop the same frames, and so use the same
number of the state's unknowns (`Exec.path`). Two runs that start with the
same unknowns therefore end with the same unknowns, which a proof that a
function returns without secret residue needs when what a release leaves
in a frame depends on them. -/

/-- How many addresses an instruction leaks depends on the instruction alone. -/
theorem addrs_length (i : Instr) (s s' : State) : (addrs i s).length = (addrs i s').length := by
  cases i <;> (try cases ‹Src›) <;> (try cases ‹MOp›) <;> (try cases ‹MSrc›) <;>
    simp [addrs, srcAddrs, MOp.addrs, MSrc.addrs]

theorem execBlock_path : ∀ {is : List Instr} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
    t₁.length = t₂.length ∧ (s₁.unknowns = s₂.unknowns → s₁'.unknowns = s₂'.unknowns)
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, id⟩
  | i :: is, s₁, s₂, s₁', s₂', t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    split at h₁
    · cases h₁
    · rename_i u₁ e₁
      split at h₂
      · cases h₂
      · rename_i u₂ e₂
        obtain ⟨⟨v₁, r₁⟩, k₁, q₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨⟨v₂, r₂⟩, k₂, q₂⟩ := Option.map_eq_some_iff.mp h₂
        cases q₁; cases q₂
        obtain ⟨hl, hu⟩ := execBlock_path k₁ k₂
        refine ⟨?_, fun h => hu ?_⟩
        · simp only [List.length_append, List.length_map, hl]
          rw [show (isa.addrs i s₁).length = (isa.addrs i s₂).length from addrs_length i s₁ s₂]
        · rw [(exec_keep e₁).1, (exec_keep e₂).1, h]

theorem callAddrs_map (s : State) : (isa.callAddrs s).map Leak.addr = [.addr ((s.gpr .esp - 4).setWidth 64)] :=
  rfl

theorem retAddrs_map (s : State) : (isa.retAddrs s).map Leak.addr = [.addr ((s.gpr .esp).setWidth 64)] :=
  rfl

/-- Two runs of code without indirect calls from states with the same
unknowns, whose traces agree up to what follows them, have the same trace
and end with the same unknowns. -/
theorem Exec.path {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    noIcall c = true → ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' →
      t₁ ++ r₁ = t₂ ++ r₂ → s₁.unknowns = s₂.unknowns → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h =>
    intro _ s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    cases e₂ with
    | block h' =>
      obtain ⟨hl, hk⟩ := execBlock_path h h'
      exact ⟨(List.append_inj ht hl).1, hk hu⟩
  | seq _ _ ih₁ ih₂ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | seq a b =>
      simp only [List.append_assoc] at ht
      obtain ⟨rfl, hm⟩ := ih₁ hc.1 a ht hu
      obtain ⟨rfl, he⟩ := ih₂ hc.2 b (List.append_cancel_left ht) hm
      exact ⟨rfl, he⟩
  | iteT _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih hc.1 b ht hu
      exact ⟨rfl, he⟩
    | iteF _ b => simp at ht
  | iteF _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ b => simp at ht
    | iteF _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih hc.2 b ht hu
      exact ⟨rfl, he⟩
  | loopExit _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | loopExit b _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨rfl, he⟩ := ih hc b ht hu
      exact ⟨rfl, he⟩
    | loopNext b _ _ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, -⟩ := ih hc b ht hu
      simp at ht
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    cases e₂ with
    | loopExit b _ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, -⟩ := ih₁ hc b ht hu
      simp at ht
    | loopNext b _ l =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, hm⟩ := ih₁ hc b ht hu
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih₂ hc l ht hm
      exact ⟨rfl, he⟩
  | call k _ q ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | call k' b q' =>
      rw [call_callEntry, Option.some.injEq] at k k'
      subst k k'
      rw [callAddrs_map, retAddrs_map, callAddrs_map, retAddrs_map] at ht ⊢
      simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at ht ⊢
      obtain ⟨ha, ht⟩ := ht
      obtain ⟨rfl, hm⟩ := ih hc b ht (by simp only [State.callEntry, hu])
      have hb := List.append_cancel_left ht
      simp only [List.cons.injEq] at hb
      refine ⟨?_, by rw [(ret_keep q).1, (ret_keep q').1, hm]⟩
      simp only [ha, hb.1, and_self]
  | frame p _ q ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | frame p' b q' =>
      simp only [List.append_assoc] at ht
      obtain ⟨ha, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      obtain ⟨rfl, hm⟩ := ih hc b ht (by rw [(push_keep p).1, (push_keep p').1, hu])
      have ht' := List.append_cancel_left ht
      obtain ⟨hb, -⟩ := List.append_inj ht' (by simp only [List.length_map]; exact addrs_length _ _ _)
      rw [ha, hb]
      exact ⟨rfl, by rw [(pop_keep q).1, (pop_keep q').1, hm]⟩
  | icall => intro hc; simp [noIcall] at hc
  | icallNext => intro hc; simp [noIcall] at hc

/-- Two releases of a frame of `n` bytes leave the same byte at `x` if it
was the same before them, in states with the same `esp` and unknowns. -/
theorem free_mem_congr {n : Nat} {a₁ b₁ c₁ a₂ b₂ c₂ : State} (h₁ : isa.pop (.free n) a₁ b₁ = some c₁)
    (h₂ : isa.pop (.free n) a₂ b₂ = some c₂) (hsp : b₁.gpr .esp = b₂.gpr .esp)
    (hu : b₁.unknowns = b₂.unknowns) {x : Addr} (hx : b₁.mem x = b₂.mem x) : c₁.mem x = c₂.mem x := by
  simp only [isa, pop] at h₁ h₂
  split at h₁ <;> [skip; cases h₁]
  split at h₂ <;> [skip; cases h₂]
  cases h₁; cases h₂
  simp only [lose, hsp, hu, hx]

/-- No instruction writes `esp` (`NoSp`) if `writesSp` holds of none
(`Artifact.spSafe`). -/
theorem noSp_of_all {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) : NoSp c := by
  have hall : ∀ i ∈ instrs c, isa.writesSp i = false := by
    induction c with
    | block is => simpa [Code.all, instrs, List.all_eq_true] using h
    | seq a b iha ihb =>
      simp only [Code.all, Bool.and_eq_true] at h
      intro i hi; simp only [instrs, List.mem_append] at hi
      exact hi.elim (iha h.1 i) (ihb h.2 i)
    | ite _ t e iht ihe =>
      simp only [Code.all, Bool.and_eq_true] at h
      intro i hi; simp only [instrs, List.mem_append] at hi
      exact hi.elim (iht h.1 i) (ihe h.2 i)
    | loop b _ ih => exact ih h
    | call _ b ih => exact ih h
    | frame i' b j ih =>
      simp only [Code.all, Bool.and_eq_true, Bool.not_eq_true'] at h
      intro i hi
      simp only [instrs, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | hi | rfl
      · exact h.1.1
      · exact ih h.1.2 i hi
      · exact h.2
    | icall i' _ b n ihb ihn =>
      simp only [Code.all, Bool.and_eq_true, Bool.not_eq_true'] at h
      intro i hi; simp only [instrs, List.cons_append, List.mem_cons, List.mem_append] at hi
      rcases hi with rfl | hi | hi
      · exact h.1.1
      · exact ihb h.1.2 i hi
      · exact ihn h.2 i hi
  intro i hi
  have := hall i hi
  cases i <;> simp_all [isa, Instr.dst, Taint.clobbers, Taint.dst]

end VG.X86

namespace VG.X86.Scrub

open VG.Impl.Scrub.X86

/-- A result on x86 is of 0, 32 or 64 bits. -/
theorem retBits_cases (sig : Sig) : sig.retBits 32 = 0 ∨ sig.retBits 32 = 32 ∨ sig.retBits 32 = 64 := by
  unfold Sig.retBits
  cases sig.ret with
  | none => exact .inl rfl
  | some ty => cases ty <;> simp [IntTy.bits]

theorem append_shr32 (a : BitVec 32) : (0#32 ++ a) >>> 32 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.zero_shiftLeft, Nat.zero_or, Nat.shiftRight_eq_div_pow]
  omega

theorem append_low32 (a b : BitVec 32) :
    BitVec.setWidth 32 (0#32 ++ a) = BitVec.setWidth 32 (b ++ a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [hi, decide_true, Bool.true_and, ↓reduceIte]

theorem shr64 (x : BitVec 64) : x >>> 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftRight_eq_div_pow]
  omega

/-- What `tail rb` leaves from `u`. -/
structure TailOk (rb : Nat) (u u' : State) : Prop where
  mem : u'.mem = u.mem
  rd : u'.rd = u.rd
  wr : u'.wr = u.wr
  unknowns : u'.unknowns = u.unknowns
  mm : u'.mm = u.mm
  mmx : u'.mmx = u.mmx
  mxcsr : u'.mxcsr = u.mxcsr
  mcdt : u'.mcdt = u.mcdt
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → u'.gpr r = u.gpr r
  ecx : u'.gpr .ecx = 0
  cf : u'.cf = some false
  zf : u'.zf = some true
  sf : u'.sf = some false
  of : u'.of = some false
  xmm : ∀ x, u'.xmm x = 0
  hi : (u'.gpr .edx ++ u'.gpr .eax) >>> rb = 0
  lo : (u'.gpr .edx ++ u'.gpr .eax).setWidth rb = (u.gpr .edx ++ u.gpr .eax).setWidth rb

theorem TailOk.flags {rb : Nat} {u u' : State} (h : TailOk rb u u') : FlagsDefined u' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h.cf, h.zf, h.sf, h.of]

/-- `tail rb` leaks nothing, and leaves what `TailOk` says. -/
theorem tail_run {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (u : State) :
    ∃ u', execBlock isa (tail rb) u = some (u', []) ∧ TailOk rb u u' := by
  rcases hrb with rfl | rfl | rfl
  · refine ⟨_, by simp [tail, retFix, clearXmm, execBlock, isa, reduceExec, readSrc, Taint.execAlu_eq,
      Taint.aluOut, Taint.writes, XOp.exec, XBinOp.eval, addrs, srcAddrs]; rfl, ?_⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r h0 h1 h2 => ?_, ?_, rfl, ?_, ?_, rfl,
      fun x => ?_, ?_, ?_⟩
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags, h0, h1, h2]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · cases x <;> simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · exact (BitVec.eq_nil _).trans (BitVec.eq_nil _).symm
  · refine ⟨_, by simp [tail, retFix, clearXmm, execBlock, isa, reduceExec, readSrc, Taint.execAlu_eq,
      Taint.aluOut, Taint.writes, XOp.exec, XBinOp.eval, addrs, srcAddrs]; rfl, ?_⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r h0 h1 h2 => ?_, ?_, rfl, ?_, ?_, rfl,
      fun x => ?_, ?_, ?_⟩
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags, h1, h2]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · cases x <;> simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp only [State.setXmm, State.setReg, arithFlags, State.setFlags]
      simpa using append_shr32 _
    · simp only [State.setXmm, State.setReg, arithFlags, State.setFlags]
      simpa using append_low32 _ _
  · refine ⟨_, by simp [tail, retFix, clearXmm, execBlock, isa, reduceExec, readSrc, Taint.execAlu_eq,
      Taint.aluOut, Taint.writes, XOp.exec, XBinOp.eval, addrs, srcAddrs]; rfl, ?_⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r h0 h1 h2 => ?_, ?_, rfl, ?_, ?_, rfl,
      fun x => ?_, shr64 _, ?_⟩
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags, h1]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · cases x <;> simp [State.setXmm, State.setReg, arithFlags, State.setFlags]
    · simp [State.setXmm, State.setReg, arithFlags, State.setFlags]

/-- The callee-saved registers are none of those the tail sets. -/
theorem saved_ne {r : Reg} (h : r ∈ calleeSaved) : r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by
  revert h; cases r <;> decide

/-- A register a callee may change, other than the result's, is `ecx`. -/
theorem saved_or_ecx (r : Reg) (h0 : r ≠ .eax) (h2 : r ≠ .edx) : r = .ecx ∨ r ∈ calleeSaved := by
  revert h0 h2; cases r <;> decide

/-- What a scrubbed run leaves, from `s`: the regions and the callee-saved
registers as they were, constants in `ecx`, the flags and the XMM registers,
zero above the result's `rb` bits, and the MMX registers and mode, MXCSR and
the MCDT frames as they were. -/
structure Ends (rb : Nat) (s u : State) : Prop where
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  saved : ∀ r ∈ calleeSaved, u.gpr r = s.gpr r
  ecx : u.gpr .ecx = 0
  cf : u.cf = some false
  zf : u.zf = some true
  sf : u.sf = some false
  of : u.of = some false
  xmm : ∀ x, u.xmm x = 0
  hi : (u.gpr .edx ++ u.gpr .eax) >>> rb = 0
  mm : u.mm = s.mm
  mmx : u.mmx = s.mmx
  mxcsr : u.mxcsr = s.mxcsr
  mcdt : u.mcdt = s.mcdt

theorem Ends.of_tail {rb : Nat} {s w u : State} (ht : TailOk rb w u) (hrd : w.rd = s.rd)
    (hwr : w.wr = s.wr) (hs : ∀ r ∈ calleeSaved, w.gpr r = s.gpr r)
    (hk : w.mm = s.mm ∧ w.mmx = s.mmx ∧ w.mxcsr = s.mxcsr ∧ w.mcdt = s.mcdt) : Ends rb s u :=
  ⟨ht.rd.trans hrd, ht.wr.trans hwr, fun r hr => by
      obtain ⟨h0, h1, h2⟩ := saved_ne hr
      rw [ht.gpr r h0 h1 h2]; exact hs r hr,
    ht.ecx, ht.cf, ht.zf, ht.sf, ht.of, ht.xmm, ht.hi, ht.mm.trans hk.1, ht.mmx.trans hk.2.1,
    ht.mxcsr.trans hk.2.2.1, ht.mcdt.trans hk.2.2.2⟩

/-- Two scrubbed runs from states that agree outside the buffers, which
agree on the memory outside the buffers on return, agree outside the
buffers but the result's `rb` bits. -/
theorem Ends.outside {rb : Nat} {s₁ s₂ u₁ u₂ : State} (ho : Outside 0 s₁ s₂) (k₁ : Ends rb s₁ u₁)
    (k₂ : Ends rb s₂ u₂) (hm : ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → u₁.mem x = u₂.mem x) :
    Outside rb u₁ u₂ ∧ FlagsDefined u₁ := by
  obtain ⟨ord, owr, oreg, -, -, -, -, -, -, omm, ommx, omxcsr, omcdt, -⟩ := ho
  refine ⟨⟨k₁.rd.trans (ord.trans k₂.rd.symm), k₁.wr.trans (owr.trans k₂.wr.symm), fun r h0 h2 => ?_,
    k₁.hi.trans k₂.hi.symm, k₁.cf.trans k₂.cf.symm, k₁.zf.trans k₂.zf.symm, k₁.sf.trans k₂.sf.symm,
    k₁.of.trans k₂.of.symm, funext fun x => (k₁.xmm x).trans (k₂.xmm x).symm,
    k₁.mm.trans (omm.trans k₂.mm.symm), k₁.mmx.trans (ommx.trans k₂.mmx.symm),
    k₁.mxcsr.trans (omxcsr.trans k₂.mxcsr.symm), k₁.mcdt.trans (omcdt.trans k₂.mcdt.symm),
    fun x hx => hm x (by rw [← k₁.rd, ← k₁.wr]; exact hx)⟩, ?_⟩
  · rcases saved_or_ecx r h0 h2 with rfl | hr
    · exact k₁.ecx.trans k₂.ecx.symm
    · rw [k₁.saved r hr, k₂.saved r hr]
      exact oreg r h0 h2
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [k₁.cf, k₁.zf, k₁.sf, k₁.of]

/-- What `Verified.scrub` and `Verified.scrubF` need of the calling convention
a contract is for: `abi`'s, possibly with tables of constants
(`Abi.withConsts`), which add readable regions apart from the stack the
function uses, and with tables of functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 32
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .edx ++ s.gpr .eax
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → (n = 0 ∨ n ≤ (s.gpr .esp).toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  simp only [abi] at h
  split at h <;> cases h
  simp only [List.length_map, List.length_zip, argSlots_length, Nat.min_self]

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    n = 0 ∨ n ≤ (s.gpr .esp).toNat := by
  cases n with
  | zero => exact .inl rfl
  | succ n => exact .inr h.1

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    fun _ _ _ h => ⟨abi_wf_stack h, fun _ hr hn => absurd hr hn⟩, fun _ _ h => h, fun _ _ h => h, abi_args_len⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨abi_wf_stack hw, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.mem, hA.ret, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.rdSub, hA.argsLen⟩

/-- The calling convention of every x86 artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi ((abi.withConsts cs).withTables sig ts) :=
  (ScrubAbi.consts cs).tables sig ts

/-- A postcondition of `Sig.contract` reads of the state on return its
memory and the bits of its result. -/
theorem contract_post_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s u u' : State}
    (h : (sig.contract A pre post wa stack leak).post s u) (hm : u'.mem = u.mem)
    (hr : (u'.gpr .edx ++ u'.gpr .eax).setWidth (sig.retBits A.ptrBits) =
      (u.gpr .edx ++ u.gpr .eax).setWidth (sig.retBits A.ptrBits)) :
    (sig.contract A pre post wa stack leak).post s u' := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · rename_i vals hv
    simp only [hA.mem, hA.ret] at h ⊢
    rw [hm, hr]
    exact h

/-- Two runs that agree on what is public have the same stack pointer. -/
theorem contract_pub_sp {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.gpr .esp = s₂.gpr .esp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

/-- The instructions of code with none an MMX instruction. -/
theorem noMmx_instrs {c : Prog isa} (h : c.allInstrs (fun i => !i.isMmx) = true) :
    ∀ i ∈ instrs c, i.isMmx = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using h i hi

/-- Running `scrub rb c` is running `c`, then `tail rb`. -/
theorem exec_scrub {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) {c : Prog isa} {s u' : State}
    {t : List Leak} (h : Exec isa (scrub rb c) s t u') :
    ∃ u, Exec isa c s t u ∧ execBlock isa (tail rb) u = some (u', []) := by
  cases h with
  | seq a b =>
    cases b with
    | block hb =>
      rename_i u t₁ t₂
      obtain ⟨w, hw, -⟩ := tail_run hrb u
      rw [hw, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨u, by simpa using a, hw⟩

/-- `scrub rb c` meets the contract of `c`, code that calls nothing, has no
frame and no MMX instruction, and returns without secret residue. -/
theorem Verified.scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hn : c.noCalls = true)
    (hm : c.allInstrs (fun i => !i.isMmx) = true)
    {rb : Nat} (e : rb = sig.retBits A.ptrBits) :
    Verified target (Impl.Scrub.X86.scrub rb c) (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86.scrub rb c) (sig.contract A pre post wa stack leak) rb := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, u, he, habi, hpost⟩ := hv.1 s hs
    obtain ⟨u', hb, ok⟩ := tail_run hrb u
    refine ⟨t ++ [], u', .seq he (.block hb), ⟨fun r hr => ?_, by rw [ok.mem]; exact habi.2⟩,
      contract_post_scrub hA hpost ok.mem (e ▸ ok.lo)⟩
    obtain ⟨h0, h1, h2⟩ := saved_ne hr
    rw [ok.gpr r h0 h1 h2]; exact habi.1 r hr
  · obtain ⟨w₁, a₁, -⟩ := exec_scrub hrb e₁
    obtain ⟨w₂, a₂, -⟩ := exec_scrub hrb e₂
    exact hv.2.1 s₁ s₂ t₁ t₂ w₁ w₂ p₁ p₂ hp a₁ a₂
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ _ ho _ e₁ e₂
    -- Each run keeps what the calling convention preserves, and the memory outside its buffers.
    have keep : ∀ {s u : State} {t : List Leak}, (sig.contract A pre post wa stack leak).pre s →
        Exec isa (Impl.Scrub.X86.scrub rb c) s t u → Ends rb s u ∧ Frame s.wr s.mem u.mem := by
      intro s u t hs h
      obtain ⟨w, a, b⟩ := exec_scrub hrb h
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s hs
      obtain ⟨-, rfl⟩ := Exec.det a a'
      obtain ⟨hrd, hwr, hf⟩ := Exec.regions a hn
      obtain ⟨u', hb, ok⟩ := tail_run hrb w
      rw [hb, Option.some.injEq, Prod.mk.injEq] at b
      obtain ⟨rfl, -⟩ := b
      exact ⟨Ends.of_tail ok hrd hwr habi.1 (Exec.keep a (noMmx_instrs hm)), ok.mem ▸ hf⟩
    obtain ⟨k₁, f₁⟩ := keep p₁ e₁
    obtain ⟨k₂, f₂⟩ := keep p₂ e₂
    refine Ends.outside ho k₁ k₂ fun x hx => ?_
    rw [f₁ x fun r hr => hx r (List.mem_append_right _ hr),
      f₂ x fun r hr => hx r (List.mem_append_right _ (ho.2.1 ▸ hr))]
    exact ho.2.2.2.2.2.2.2.2.2.2.2.2.2 x hx

/-! ## Code with frames

Code with calls and frames also writes the stack below `esp`: at most
`stackUse c` bytes of it (`Exec.frameSp`), which hold what its frames held
and the return addresses of its calls. `scrubF rb n c` is `c`, then a frame
of the `n` bytes below `esp` whose every doubleword is zeroed (`wipeBelow`),
then `tail rb`: so those bytes are zero when that frame is released, and
every other byte outside the buffers is what it was. The frame is apart
from the buffers and from the return address (the contract reserves it), so
a postcondition that reads the memory on return only within the buffers
(`PostOut`) still holds, and so does the calling convention.

The frame's size is one the model accepts (`FrameOk`: a multiple of 4
bytes, less than a page).

What the release then leaves in those bytes is the model's (`lose`), which a
proof may not read back: two releases leave the same bytes where they held
the same bytes, at the same `esp` and with the same unknowns
(`free_mem_congr`). Two runs of `c` without indirect calls (`noIcall`) whose
traces agree, as constant time makes them, end with the same unknowns
(`Exec.path`), so two runs of `scrubF rb n c` agree on those bytes on
return. -/

open VG.Impl.StackScratch.X86

/-- A frame size the model accepts. -/
abbrev FrameOk (n : Nat) : Prop := 0 < n ∧ n < 4096 ∧ n % 4 = 0

/-- What `Sig.contract` gives of the stack it reserves: there is that much,
apart from every region the code may read or write. -/
theorem contract_pre_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) (hn : stack ≠ 0) :
    stack ≤ (s.gpr .esp).toNat ∧ ∀ r ∈ s.rd ++ s.wr, (below (s.gpr .esp) stack).Disjoint r := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨hst, hcon⟩ := hA.wf _ _ _ hwf
  have hsp : stack ≤ (s.gpr .esp).toNat := hst.resolve_left hn
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have hb : below (s.gpr .esp) stack ∈ abi.reserved stack s := by
    cases stack with
    | zero => exact absurd rfl hn
    | succ n => simp [abi, stackBelow, below, Taint.sub_setWidth hsp]
  refine ⟨hsp, fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · by_cases hn' : r ∈ A.rd s
    · rw [hrd] at hn'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn'
      exact hres' _ hb a (List.mem_filter.mp ha).1
    · exact hcon r hr hn' _ hb
  · rw [← hA.wr, hwr] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact hres' _ hb a (List.mem_filter.mp ha).1

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits (`Verified.scrubF`'s `hpost`). -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .edx ++ u'.gpr .eax).setWidth rb = (u.gpr .edx ++ u.gpr .eax).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- The return address, at `esp`, is apart from the stack below it. -/
theorem ret_slot_disjoint {e : BitVec 32} {n : Nat} (hn : n ≤ e.toNat) :
    ∀ r' ∈ [below e n], Region.Disjoint ⟨e.setWidth 64, 4⟩ r' := by
  intro r' hr' x h₁ h₂
  rw [List.mem_singleton.mp hr'] at h₂
  simp only [below, Taint.sub_setWidth hn] at h₂
  refine Offset.disjoint_below_above (e.setWidth 64) (m := n) (a := 0) (l := 4) (by omega_using [hn]) x h₂ ?_
  simpa using h₁

/-- The stores of `wipeStores 0 words`, of a zero in `ecx`, change memory
only in the region `R`, which holds each of them and which `u` may write,
and leave the doublewords they store zero. -/
theorem wipeStores_zero (R : Region) (u : State) (hR : R ∈ u.wr) (h2 : u.gpr .ecx = 0) :
    ∀ words, (u.gpr .esp).toNat + 4 * words ≤ 2 ^ 32 →
    (∀ k < words, R.Contains ((u.gpr .esp + BitVec.ofNat 32 (0 + 4 * k)).setWidth 64) 4) →
    ∃ m', execBlock isa (wipeStores 0 words) u =
        some ({ u with mem := m' }, wipeTrace (u.gpr .esp) 0 words) ∧ Frame [R] u.mem m' ∧
      ∀ x, (x - (u.gpr .esp).setWidth 64).toNat < 4 * words → m' x = 0
  | 0, _, _ => ⟨u.mem, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | w + 1, hnw, hc => by
    obtain ⟨m', he, hf, hz⟩ := wipeStores_zero R u hR h2 w (by omega) fun k hk => hc k (by omega)
    have hin : InRegions u.wr ((u.gpr .esp + BitVec.ofNat 32 (0 + 4 * w)).setWidth 64) 4 :=
      ⟨R, hR, hc w (by omega)⟩
    refine ⟨m'.writeW ((u.gpr .esp + BitVec.ofNat 32 (0 + 4 * w)).setWidth 64) (u.gpr .ecx), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega)), fun x hx => ?_⟩
    · rw [wipeStores_succ, execBlock_append, he]
      simp only [Option.bind_some, execBlock, isa, reduceExec, State.store32, State.ea, hin, ↓reduceIte,
        Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, wipeTrace,
        List.range_succ, List.map_append]
    · have ha : (u.gpr .esp + BitVec.ofNat 32 (0 + 4 * w)).setWidth 64 =
          (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * w) := by
        rw [Nat.zero_add]; exact addr_eq (by omega)
      rw [h2, ha]
      simp only [Mem.writeW, Mem.write]
      split
      · simp
      · rename_i hx'
        refine hz x ?_
        have : ¬ (4 * w ≤ (x - (u.gpr .esp).setWidth 64).toNat ∧
            (x - (u.gpr .esp).setWidth 64).toNat < 4 * w + 4) :=
          fun h => hx' ((Offset.lt_iff x ((u.gpr .esp).setWidth 64) (d := 4 * w) (n := 32 / 8) (by omega)).mpr h)
        omega

/-- `wipeBelow n` zeroes the `n` bytes below `esp`, in a frame it then
releases (`v`, the state before the release), and changes no other byte,
with a trace of their addresses alone; it keeps the regions, the MMX
registers and mode, MXCSR, the MCDT frames and every register but `ecx`. -/
theorem wipeBelow_run {n : Nat} (hn : FrameOk n) (w : State) (hsp : n ≤ (w.gpr .esp).toNat) :
    ∃ u v, Exec isa (wipeBelow n) w (wipeTrace (w.gpr .esp - BitVec.ofNat 32 n) 0 (n / 4)) u ∧
      u.rd = w.rd ∧ u.wr = w.wr ∧ (∀ r, r ≠ .ecx → u.gpr r = w.gpr r) ∧
      u.mm = w.mm ∧ u.mmx = w.mmx ∧ u.mxcsr = w.mxcsr ∧ u.mcdt = w.mcdt ∧
      Frame [below (w.gpr .esp) n] w.mem u.mem ∧
      isa.pop (.free n) (allocFrame n w) v = some u ∧ v.gpr .esp = w.gpr .esp - BitVec.ofNat 32 n ∧
      v.unknowns = w.unknowns ∧ ∀ x, (below (w.gpr .esp) n).Contains x 1 → v.mem x = 0 := by
  obtain ⟨h0, h1, h4⟩ := hn
  have hE : (w.gpr .esp - BitVec.ofNat 32 n).toNat = (w.gpr .esp).toNat - n := sub_toNat hsp
  have hlt := (w.gpr .esp).isLt
  let a := allocFrame n w
  let v₀ := a.setReg .ecx 0
  have hesp : v₀.gpr .esp = w.gpr .esp - BitVec.ofNat 32 n := by
    simp [v₀, a, allocFrame, State.setReg]
  have hR : below (w.gpr .esp) n ∈ v₀.wr := by simp [v₀, a, allocFrame, State.setReg, below]
  obtain ⟨m', he, hf, hz⟩ := wipeStores_zero (below (w.gpr .esp) n) v₀ hR (by simp [v₀, State.setReg])
    (n / 4) (by rw [hesp, hE]; omega) (fun k hk => by
      rw [hesp, Nat.zero_add, show ((w.gpr .esp - BitVec.ofNat 32 n) + BitVec.ofNat 32 (4 * k)).setWidth 64 =
        (w.gpr .esp - BitVec.ofNat 32 n).setWidth 64 + BitVec.ofNat 64 (4 * k) from
        addr_eq (by rw [hE]; omega)]
      exact Offset.contains_base _ (by omega) (by omega))
  have hblk : execBlock isa (wipe 0 (n / 4)) a =
      some ({ v₀ with mem := m' }, wipeTrace (w.gpr .esp - BitVec.ofNat 32 n) 0 (n / 4)) := by
    simp only [wipe, execBlock, isa, reduceExec, readSrc, Option.map_some]
    rw [show a.setReg .ecx 0 = v₀ from rfl, he, hesp]
    simp [addrs, srcAddrs]
  have hpush : isa.push (.alloc n) w = some a := by
    simp only [isa, push, h0, h1, h4, hsp, and_self, ite_true]
    rfl
  have hpop : isa.pop (.free n) a { v₀ with mem := m' } = some { freed n { v₀ with mem := m' } with
      mem := lose m' ((v₀.gpr .esp).setWidth 64) n v₀.unknowns
      unknowns := fun k => v₀.unknowns (k + n / 2) } := by
    simp only [isa, pop]
    refine ite_eq_left ⟨h0, h1, h4, rfl, rfl, ?_⟩
    simp [a, allocFrame, State.setReg]
  have hex := Exec.frame hpush (Exec.block hblk) hpop
  rw [show (isa.addrs (.alloc n) w).map Leak.addr = [] from rfl, List.nil_append,
    show ∀ s, (isa.addrs (.free n) s).map Leak.addr = [] from fun _ => rfl, List.append_nil] at hex
  refine ⟨_, { v₀ with mem := m' }, hex, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl, ?_, hpop, hesp, rfl,
    fun x hx => ?_⟩
  · by_cases he' : r = .esp
    · subst he'
      simp [freed, v₀, a, allocFrame, State.setReg, BitVec.sub_add_cancel]
    · simp [freed, v₀, a, allocFrame, State.setReg, he', hr]
  · have hf' : Frame [below (w.gpr .esp) n] w.mem m' := hf
    refine hf'.trans ?_
    rw [hesp]
    simpa only [below] using lose_frame m' ((w.gpr .esp - BitVec.ofNat 32 n).setWidth 64) n v₀.unknowns
  · show m' x = 0
    refine hz x ?_
    rw [hesp]
    simp only [Region.Contains] at hx
    omega

/-- What a run of `scrubF rb n c` from `s` leaves, after `c`'s run to `w`
and the wipe's to `v'`. -/
structure ScrubFOk (rb n : Nat) (s w v' u : State) : Prop where
  tail : TailOk rb v' u
  rd : v'.rd = s.rd
  wr : v'.wr = s.wr
  gpr : ∀ r, r ≠ .ecx → v'.gpr r = w.gpr r
  keep : v'.mm = w.mm ∧ v'.mmx = w.mmx ∧ v'.mxcsr = w.mxcsr ∧ v'.mcdt = w.mcdt
  frame : Frame [below (s.gpr .esp) n] w.mem v'.mem
  zero : ∃ v a, v.gpr .esp = s.gpr .esp - BitVec.ofNat 32 n ∧ v.unknowns = w.unknowns ∧
    (∀ x, (below (s.gpr .esp) n).Contains x 1 → v.mem x = 0) ∧ isa.pop (.free n) a v = some v'
  below : Frame (s.wr ++ [below (s.gpr .esp) n]) s.mem w.mem

/-- A run of `scrubF rb n c` from `s`, after `c`'s run to `w`: what it leaks
after `c`'s trace are the addresses of the wiped doublewords. -/
theorem scrubF_run {rb n : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hn : FrameOk n) {c : Prog isa}
    (hns : NoSp c) (hd : stackUse c ≤ n) {s w : State} {t : List Leak} (hsp : n ≤ (s.gpr .esp).toNat)
    (he : Exec isa c s t w) :
    ∃ v' u, Exec isa (scrubF rb n c) s (t ++ (wipeTrace (s.gpr .esp - BitVec.ofNat 32 n) 0 (n / 4) ++ [])) u ∧
      ScrubFOk rb n s w v' u := by
  obtain ⟨hrd, hwr⟩ := Exec.rdwr he
  have hp : w.gpr .esp = s.gpr .esp := Exec.gpr hns he
  have hfs := Frame.below_mono (Exec.frameSp he hns (Nat.le_trans hd hsp)) hd hsp
  obtain ⟨v', v, hv, vrd, vwr, vreg, vk₁, vk₂, vk₃, vk₄, vf, vpop, vsp, vu, vz⟩ :=
    wipeBelow_run hn w (hp ▸ hsp)
  obtain ⟨u, hb, ok⟩ := tail_run hrb v'
  rw [hp] at hv vf vz vsp
  exact ⟨v', u, .seq he (.seq hv (.block hb)), ⟨ok, vrd.trans hrd, vwr.trans hwr, vreg, ⟨vk₁, vk₂, vk₃, vk₄⟩, vf,
    ⟨v, _, vsp, vu, vz, vpop⟩, hfs⟩⟩

/-- `scrubF rb stack c` meets the contract of `c`, whose frames and calls
use at most the `stack` bytes the contract reserves, which never writes
`esp`, makes no indirect call and has no MMX instruction, and whose
postcondition reads the memory on return only within the buffers, and
returns without secret residue. -/
theorem Verified.scrubF {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hns : NoSp c)
    (hd : stackUse c ≤ stack) (hni : noIcall c = true) (hm : c.allInstrs (fun i => !i.isMmx) = true)
    (hn : FrameOk stack) {rb : Nat} (e : rb = sig.retBits A.ptrBits)
    (hpost : PostOut (sig.contract A pre post wa stack leak) rb) :
    Verified target (Impl.Scrub.X86.scrubF rb stack c) (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86.scrubF rb stack c) (sig.contract A pre post wa stack leak) rb := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  have h0 : stack ≠ 0 := by have := hn.1; omega
  -- Every run is `c`'s run, then the wipe and the tail.
  have run : ∀ {s u : State} {T : List Leak}, (sig.contract A pre post wa stack leak).pre s →
      Exec isa (Impl.Scrub.X86.scrubF rb stack c) s T u → ∃ t w v', Exec isa c s t w ∧
        T = t ++ (wipeTrace (s.gpr .esp - BitVec.ofNat 32 stack) 0 (stack / 4) ++ []) ∧
        ScrubFOk rb stack s w v' u := by
    intro s u T hs h
    cases h with
    | seq a b =>
      rename_i w t₁ t₂
      obtain ⟨v', u', hu', facts⟩ := scrubF_run hrb hn hns hd (contract_pre_scrub hA hs h0).1 a
      obtain ⟨hT, rfl⟩ := Exec.det (Exec.seq a b) hu'
      exact ⟨t₁, w, v', a, hT, facts⟩
  -- The calling convention, from `c`'s.
  have abi_of : ∀ {s w v' u : State}, stack ≤ (s.gpr .esp).toNat → abiPreserved s w →
      ScrubFOk rb stack s w v' u → abiPreserved s u := by
    intro s w v' u hsp habi ok
    refine ⟨fun r hr => ?_, ?_⟩
    · obtain ⟨h0, h1, h2⟩ := saved_ne hr
      rw [ok.tail.gpr r h0 h1 h2, ok.gpr r h1]; exact habi.1 r hr
    · rw [ok.tail.mem, ok.frame.readW (Region.contains_self _ _) (ret_slot_disjoint hsp) (by decide)]
      exact habi.2
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, w, he, habi, hq⟩ := hv.1 s hs
    obtain ⟨hsp, hdis⟩ := contract_pre_scrub hA hs h0
    obtain ⟨v', u, hu, ok⟩ := scrubF_run hrb hn hns hd hsp he
    refine ⟨_, u, hu, abi_of hsp habi ok, hpost s w u hs hq (fun x ⟨r, hr, hx⟩ => ?_) ?_⟩
    · rw [ok.tail.mem]; exact ok.frame x fun r' hr' hb => by
        rw [List.mem_singleton.mp hr'] at hb; exact hdis r hr x hb hx
    · rw [ok.tail.lo, ok.gpr .edx (by decide), ok.gpr .eax (by decide)]
  · obtain ⟨a₁, w₁, -, x₁, rfl, -⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, -, x₂, rfl, -⟩ := run p₂ e₂
    rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂, contract_pub_sp hA hp]
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp ho hu e₁ e₂
    obtain ⟨a₁, w₁, v₁', x₁, -, ok₁⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, v₂', x₂, -, ok₂⟩ := run p₂ e₂
    have osp : s₁.gpr .esp = s₂.gpr .esp := contract_pub_sp hA hp
    -- The two runs of `c` leak the same trace, so end with the same unknowns.
    have hw : w₁.unknowns = w₂.unknowns :=
      (Exec.path x₁ hni (r₁ := []) (r₂ := []) x₂
        (by rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂]) hu).2
    -- Each run keeps what the calling convention preserves.
    have ends : ∀ {s w v' u : State} {t : List Leak}, (sig.contract A pre post wa stack leak).pre s →
        Exec isa c s t w → ScrubFOk rb stack s w v' u → Ends rb s u := by
      intro s w v' u t hs x ok
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s hs
      obtain ⟨-, rfl⟩ := Exec.det x a'
      obtain ⟨k₁, k₂, k₃, k₄⟩ := Exec.keep x (noMmx_instrs hm)
      exact Ends.of_tail ok.tail ok.rd ok.wr (fun r hr => by
          rw [ok.gpr r (saved_ne hr).2.1]; exact habi.1 r hr)
        ⟨ok.keep.1.trans k₁, ok.keep.2.1.trans k₂, ok.keep.2.2.1.trans k₃, ok.keep.2.2.2.trans k₄⟩
    refine Ends.outside ho (ends p₁ x₁ ok₁) (ends p₂ x₂ ok₂) fun x hx => ?_
    rw [ok₁.tail.mem, ok₂.tail.mem]
    by_cases hb : (below (s₁.gpr .esp) stack).Contains x 1
    · obtain ⟨v₁, _, vsp₁, vu₁, vz₁, vp₁⟩ := ok₁.zero
      obtain ⟨v₂, _, vsp₂, vu₂, vz₂, vp₂⟩ := ok₂.zero
      exact free_mem_congr vp₁ vp₂ (by rw [vsp₁, vsp₂, osp]) (by rw [vu₁, vu₂, hw])
        ((vz₁ x hb).trans (vz₂ x (osp ▸ hb)).symm)
    · have hb₂ : ¬ (below (s₂.gpr .esp) stack).Contains x 1 := osp ▸ hb
      have nb : ∀ {s : State}, ¬ (below (s.gpr .esp) stack).Contains x 1 →
          ∀ r' ∈ [below (s.gpr .esp) stack], ¬ r'.Contains x 1 := fun h r' hr' => by
        rw [List.mem_singleton.mp hr']; exact h
      rw [ok₁.frame x (nb hb), ok₂.frame x (nb hb₂),
        ok₁.below x fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · exact hx r (List.mem_append_right _ hr)
          · exact nb hb r hr,
        ok₂.below x fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · exact hx r (List.mem_append_right _ (ho.2.1 ▸ hr))
          · exact nb hb₂ r hr]
      exact ho.2.2.2.2.2.2.2.2.2.2.2.2.2 x hx

/-! ## Registrations -/

theorem tail_all (rb : Nat) : (tail rb).all (fun i => !isa.writesSp i) = true := by
  unfold tail retFix
  split
  · rfl
  · split <;> rfl

theorem wipe_all (k : Nat) : (wipe 0 k).all (fun i => !isa.writesSp i) = true := by
  simp [wipe, wipeStores, List.all_map, Function.comp_def, Instr.dst]

/-- A function that writes at most the first bytes of some of its buffers
still does when the state on return is replaced by one with its memory. -/
theorem writtenWithin_mem {sig : Sig} {written : List (String × Nat)} {s u u' : State}
    (h : Sig.writtenWithin abi sig written s u) (hm : u'.mem = u.mem) :
    Sig.writtenWithin abi sig written s u' := by
  cases written with
  | nil => exact True.intro
  | cons w ws =>
    simp only [Sig.writtenWithin] at h ⊢
    split
    · exact True.intro
    · rename_i vals hv
      rw [hv] at h
      intro w hw b hb hbw i hi hl
      have := h w hw b hb hbw i hi hl
      simp only [abi] at this ⊢
      rw [hm]; exact this

/-- `r`, a registration of code that calls nothing, has no frame and no MMX
instruction, scrubbed: its code followed by `tail`, which returns without
secret residue. -/
def scrubReg {api : Api} (r : Registration api target) (hn : r.code.noCalls = true)
    (hm : r.code.allInstrs (fun i => !i.isMmx) = true) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hn hm rfl).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := by
    simp only [scrub, Code.all, r.spSafe, Bool.true_and]
    exact tail_all _
  written := r.written
  writtenOk := by
    intro s t u' hs he
    have hrb := retBits_cases api.sig
    obtain ⟨u, a, b⟩ := exec_scrub
      (rb := api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (by rw [(ScrubAbi.of r.consts api.sig r.tables).ptrBits]; exact hrb) he
    obtain ⟨w, hw, ok⟩ := tail_run
      (rb := api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (by rw [(ScrubAbi.of r.consts api.sig r.tables).ptrBits]; exact hrb) u
    rw [hw, Option.some.injEq, Prod.mk.injEq] at b
    obtain ⟨rfl, -⟩ := b
    exact writtenWithin_mem (r.writtenOk s t u hs a) ok.mem
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hn hm rfl).2⟩

/-- `r`, a registration of code whose frames and calls use at most the
`stack` bytes its contract reserves, which makes no indirect call and has
no MMX instruction, scrubbed: its code, then those bytes zeroed, then
`tail`, which returns without secret residue, if its postcondition reads
the memory on return only within the buffers. -/
def scrubRegF {api : Api} (r : Registration api target) (hd : stackUse r.code ≤ r.stack)
    (hni : noIcall r.code = true) (hm : r.code.allInstrs (fun i => !i.isMmx) = true)
    (hn : FrameOk r.stack)
    (hpost : PostOut r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrubF (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    r.stack r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    rw [e] at hv hp ⊢
    exact (Verified.scrubF (ScrubAbi.of r.consts api.sig r.tables) hv (noSp_of_all r.spSafe) hd hni hm hn
      rfl hp).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := by
    simp only [scrubF, wipeBelow, Code.all, r.spSafe, wipe_all, tail_all, Bool.true_and, Bool.and_true]
    rfl
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    rw [e] at hv hp ⊢
    exact (Verified.scrubF (ScrubAbi.of r.consts api.sig r.tables) hv (noSp_of_all r.spSafe) hd hni hm hn
      rfl hp).2⟩

end VG.X86.Scrub
