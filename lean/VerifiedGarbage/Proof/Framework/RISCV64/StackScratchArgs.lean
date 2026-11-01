module

public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Covers

/-!
# A scratch buffer on the stack, for a function with stack arguments (RISC-V)

`Verified.stackScratchArgs`: code verified for a function whose arguments
fill `a0`–`a7` and `m` doublewords of stack, then a scratch buffer (so passed
on the stack too: its contract `Sig.scratchContract`), runs as a function
without that argument when `withStackScratchArgs` allocates the buffer in a
frame on the stack, with `bytes` more bytes of stack. As on PPC64LE
(`Proof/Framework/PPC64LE/StackScratchArgs.lean`), the frame holds what the
code expects from `sp` on entry: a copy of the stack arguments, then the
buffer's address (`setArgs`). The code runs from the state after the frame's
`alloc` and `setArgs`, with the permissions of the contract with the
argument (`narrowA`), and its run there is its run from that state
(`Exec.widen`).

The frame, from its stack pointer `E`: the copies and the buffer's address
(at `E`), and the buffer, at `E + 8 + 8m`. The copies are memory the code
reads on entry, which the contract without the argument says nothing of: the
precondition, postcondition and leak must read memory only within the
function's buffers (`hpre`, `hpost`, `hleak`), which the frame lies outside
of. The signature has no lists of slices.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.StackScratch.RISCV64

/-! ## Contracts with stack arguments -/

/-- Every argument is at most 64 bits wide. -/
theorem widths_le (sig : Sig) : ∀ w ∈ (sig.words abi.ptrBits).map (·.bits abi.ptrBits), w ≤ 64 := by
  intro w hw
  simp only [Sig.words, List.map_flatMap, List.mem_flatMap] at hw
  obtain ⟨p, -, hp⟩ := hw
  cases h : p.2 with
  | int ty _ =>
    rw [h] at hp; cases ty <;> simp [Param.words, ArgWord.bits, IntTy.bits, abi] at hp <;> omega
  | array _ _ _ => rw [h] at hp; simp [Param.words, ArgWord.bits, abi] at hp; omega
  | slice _ _ _ => rw [h] at hp; simp [Param.words, ArgWord.bits, abi] at hp; omega
  | slices _ _ => rw [h] at hp; simp [Param.words, ArgWord.bits, abi] at hp; omega

/-- The arguments of a function whose arguments fill `a0`–`a7` and `m`
doublewords of stack. -/
abbrev stkArgs (m : Nat) (s : State) : List (BitVec 64) :=
  argRegs.map s.gpr ++ (List.range m).map (stackArg s)

theorem stkArgs_length (m : Nat) (s : State) : (stkArgs m s).length = 8 + m := by
  simp [stkArgs, argRegs]; omega

/-- The `m` doublewords of stack arguments, which a contract lets the function
only read. -/
def argAreaStk (m : Nat) (s : State) : List (Region × Bool) :=
  if m = 0 then [] else [(⟨stackArgAddr s 0, 8 * m⟩, false)]

/-- The buffers and the stack arguments, and whether each is writable. -/
def allStk (sig : Sig) (m : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (stkArgs m s) ++ argAreaStk m s

section
variable {sig : Sig} {m : Nat}

theorem args_stk (hk : (sig.words abi.ptrBits).length = 8 + m) :
    abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some (stkArgs m) := by
  have hk' : (sig.words 64).length = 8 + m := hk
  have hall : ((List.map (fun x => ArgWord.bits 64 x) (sig.words 64)).drop argRegs.length).all
      (fun x => decide (x ≤ 64)) = true :=
    List.all_eq_true.mpr fun w hw => decide_eq_true (widths_le sig w (List.mem_of_mem_drop hw))
  simp only [abi, List.length_map]
  cases m with
  | zero =>
    rw [ite_eq_left (by rw [hk']; decide)]
    congr 1
    funext s
    simp [stkArgs, argRegs, hk']
  | succ m =>
    rw [ite_eq_right (by rw [hk']; simp [argRegs]), ite_eq_left hall]
    congr 1
    funext s
    simp [stkArgs, argRegs, hk']

theorem argArea_stk (hk : (sig.words abi.ptrBits).length = 8 + m) (wa : Bool) (s : State) :
    (abi.argArea ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)) = argAreaStk m s := by
  show (let n := ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).length - argRegs.length
    if n = 0 then [] else [((⟨stackArgAddr s 0, 8 * n⟩ : Region), false)]).map
      (fun (r, w) => (r, w && wa)) = _
  simp only [List.length_map, hk, argRegs, List.length_cons, List.length_nil]
  by_cases h : m = 0 <;> simp [argAreaStk, h]

theorem wf_stk (hk : (sig.words abi.ptrBits).length = 8 + m) (stack : Nat) (s : State) :
    abi.wf ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) stack s ↔
      (s.sp.toNat % 16 = 0 ∧ (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
        (m = 0 ∨ s.sp.toNat + 8 * m ≤ 2 ^ 64)) := by
  show (s.sp.toNat % 16 = 0 ∧ (match stack with | 0 => True | n => n ≤ s.sp.toNat) ∧
      (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).length ≤ argRegs.length ∨
        s.sp.toNat + 8 * (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).length - argRegs.length) ≤
          2 ^ 64)) ↔ _
  have hwf : (match stack with | 0 => True | n => n ≤ s.sp.toNat) ↔
      (stack = 0 ∨ stack ≤ s.sp.toNat) := by
    cases stack <;> simp
  simp only [List.length_map, hk, argRegs, List.length_cons, List.length_nil, hwf]
  cases m with
  | zero => simp
  | succ m => simp; intro _ _ h; omega

/-- The precondition of a contract, by where the arguments are. -/
theorem pre_stk {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : (sig.words abi.ptrBits).length = 8 + m) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (s.sp.toNat % 16 = 0 ∧ (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
        (m = 0 ∨ s.sp.toNat + 8 * m ≤ 2 ^ 64)) ∧
      s.rd = ((allStk sig m s).filter (!·.2)).map (·.1) ∧
      s.wr = ((allStk sig m s).filter (·.2)).map (·.1) ∧
      (allStk sig m s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ allStk sig m s, r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (stkArgs m s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (stkArgs m s) s.mem ∧
      ∀ p ∈ Sig.alignedBufs sig.params (stkArgs m s), p.1.toNat % p.2 = 0 := by
  simp only [Sig.contract]
  rw [args_stk hk]
  simp only [argArea_stk hk, Sig.lists_of_noLists _ _ _ _ hl, List.map_nil, List.append_nil]
  rw [wf_stk hk]
  exact Iff.rfl

/-- The postcondition of a contract, by where the arguments are. -/
theorem post_stk {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s s' : State}
    (hk : (sig.words abi.ptrBits).length = 8 + m) :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (stkArgs m s) s.mem s'.mem
        ((s'.gpr .a0).setWidth _) := by
  simp only [Sig.contract]
  rw [args_stk hk]
  exact Iff.rfl

/-- The public data of a contract, and what it may leak, by where the
arguments are. -/
theorem pubL_stk {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (hk : (sig.words abi.ptrBits).length = 8 + m) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.sp = s₂.sp ∧ leakAgree leak (stkArgs m s₁) s₁.mem (stkArgs m s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((stkArgs m s₁).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((stkArgs m s₂).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  simp only [Sig.contract]
  rw [args_stk hk]
  simp only [Sig.descs_of_noLists _ _ _ hl, List.not_mem_nil, false_implies, implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

end

/-! ## Copying the stack arguments -/

/-- The state after `copyArg bytes j` from `u`, whose `t0` is its stack
pointer. -/
def copyState (bytes j : Nat) (u : State) : State :=
  { u.write .t1 (u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64) with
    mem := u.mem.writeW (u.sp + BitVec.ofNat 64 (8 * j))
      (u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64) }

theorem copyArg_run {bytes j : Nat} {u : State} (ht0 : u.gpr .t0 = u.sp) (hal : u.sp.toNat % 8 = 0)
    (ho : bytes + 8 * j < 2048) (h8 : bytes % 8 = 0)
    (hr : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8)
    (hw : InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * j)) 8) :
    execBlock isa (copyArg bytes j) u = some (copyState bytes j u,
      [.addr (u.sp + BitVec.ofNat 64 (bytes + 8 * j)), .addr (u.sp + BitVec.ofNat 64 (8 * j))]) := by
  have hl := exec_load_d (s := u) (t := .t1) (n := .t0) (off := bytes + 8 * j) ho
    (by rw [ht0]; exact Spill.al8 hal (by omega)) (by rw [ht0]; exact hr)
  have hs := exec_store_d (s := u.write .t1 (u.mem.readW (u.gpr .t0 + BitVec.ofNat 64 (bytes + 8 * j)) 64))
    (t := .t1) (n := .t0) (off := 8 * j) (by omega)
    (by simp only [State.write, reduceCtorEq, ↓reduceIte, ht0]; exact Spill.al8 hal (by omega))
    (by simp only [State.write, reduceCtorEq, ↓reduceIte, ht0]; exact hw)
  simp only [copyArg, execBlock, isa, hl, hs, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  simp only [State.write, reduceCtorEq, ↓reduceIte, ht0, copyState]

@[simp] theorem copyState_sp (bytes j : Nat) (u : State) : (copyState bytes j u).sp = u.sp := rfl
@[simp] theorem copyState_rd (bytes j : Nat) (u : State) : (copyState bytes j u).rd = u.rd := rfl
@[simp] theorem copyState_wr (bytes j : Nat) (u : State) : (copyState bytes j u).wr = u.wr := rfl
theorem copyState_gpr (bytes j : Nat) (u : State) {q : Reg} (h : q ≠ .t1) :
    (copyState bytes j u).gpr q = u.gpr q := by
  simp [copyState, State.write, h]

/-- The state after copying the first `m` stack arguments from `u`. -/
def copiedState (bytes : Nat) (u : State) : Nat → State
  | 0 => u
  | m + 1 => copyState bytes m (copiedState bytes u m)

@[simp] theorem copiedState_sp (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).sp = u.sp
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_sp, copiedState_sp bytes u m]
@[simp] theorem copiedState_rd (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).rd = u.rd
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_rd, copiedState_rd bytes u m]
@[simp] theorem copiedState_wr (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).wr = u.wr
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_wr, copiedState_wr bytes u m]
theorem copiedState_gpr (bytes : Nat) (u : State) {q : Reg} (h : q ≠ .t1) :
    ∀ m, (copiedState bytes u m).gpr q = u.gpr q
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_gpr _ _ _ h, copiedState_gpr bytes u h m]

/-- The addresses copying the first `m` stack arguments accesses. -/
def copyTrace (bytes : Nat) (sp : Addr) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j =>
    [.addr (sp + BitVec.ofNat 64 (bytes + 8 * j)), .addr (sp + BitVec.ofNat 64 (8 * j))]

theorem copies_run {bytes : Nat} {u : State} (ht0 : u.gpr .t0 = u.sp) (hal : u.sp.toNat % 8 = 0)
    (h8 : bytes % 8 = 0) :
    ∀ m, bytes + 8 * m < 2048 →
      (∀ j < m, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8) →
      (∀ j < m, InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * j)) 8) →
      execBlock isa ((List.range m).flatMap (copyArg bytes)) u =
        some (copiedState bytes u m, copyTrace bytes u.sp m)
  | 0, _, _, _ => rfl
  | m + 1, ho, hr, hw => by
    rw [List.range_succ, List.flatMap_append, execBlock_append,
      copies_run ht0 hal h8 m (by omega_using [ho]) (fun j hj => hr j (by omega_using [hj]))
        (fun j hj => hw j (by omega_using [hj]))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [copyArg_run (by rw [copiedState_gpr _ _ (by decide), copiedState_sp]; exact ht0)
      (by rw [copiedState_sp]; exact hal) (by omega_using [ho]) h8
      (by simpa using hr m (by omega_using [])) (by simpa using hw m (by omega_using []))]
    simp only [Option.map_some, copiedState, copiedState_sp, copyTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` stack arguments writes only within the `m`
destination doublewords (from `sp`), which then hold the sources (from
`sp + bytes`). -/
theorem copiedState_mem {bytes : Nat} {u : State} :
    ∀ m, bytes + 8 + 8 * m < 2 ^ 64 → 8 * m ≤ bytes →
      Frame [⟨u.sp, 8 * m⟩] u.mem (copiedState bytes u m).mem ∧
      ∀ j < m, (copiedState bytes u m).mem.readW (u.sp + BitVec.ofNat 64 (8 * j)) 64 =
        u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u) m (by omega_using [hfit])
      (by omega_using [hb])
    have hR : Region.Sub ⟨u.sp, 8 * m⟩ ⟨u.sp, 8 * (m + 1)⟩ := Region.sub_prefix (by omega_using [])
    have f' : Frame [⟨u.sp, 8 * (m + 1)⟩] u.mem (copiedState bytes u m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    -- The source of argument `m` is above the first `m` destinations.
    have hsrc : (copiedState bytes u m).mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * m)) 64 =
        u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * m)) 64 := by
      refine f.readW (r := ⟨u.sp + BitVec.ofNat 64 (bytes + 8 * m), 8⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (d := bytes + 8 * m) (n := 8) (k := 8 * m)
        (by omega_using []) (by omega_using [hfit])
    refine ⟨?_, fun j hj => ?_⟩
    · show Frame _ u.mem ((copiedState bytes u m).mem.writeW _ _)
      rw [copiedState_sp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      exact Offset.contains_base _ (d := 8 * m) (k := 8 * (m + 1)) (by omega_using [])
        (by omega_using [hfit])
    · show ((copiedState bytes u m).mem.writeW
          ((copiedState bytes u m).sp + BitVec.ofNat 64 (8 * m))
          ((copiedState bytes u m).mem.readW
            ((copiedState bytes u m).sp + BitVec.ofNat 64 (bytes + 8 * m)) 64)).readW _ 64 = _
      rw [copiedState_sp]
      rcases Nat.lt_or_ge j m with hj' | hj'
      · rw [Mem.readW_writeW_sep, hv j hj']
        · exact Offset.sep _ (d := 8 * j) (n := 8) (e := 8 * m) (k := 8)
            (by omega_using [hj']) (by omega_using [hfit, hj']) (by omega_using [hfit])
        · decide
      · obtain rfl : j = m := by omega_using [hj, hj']
        rw [Mem.readW_writeW_self64, hsrc]

/-- `addi t1, t0, 8 + 8m; sd t1, 8m(t0)`: pass the buffer. -/
theorem tail_run {m : Nat} {w : State} (ht0 : w.gpr .t0 = w.sp) (hal : w.sp.toNat % 8 = 0)
    (hm : 8 + 8 * m < 2048) (hw : InRegions w.wr (w.sp + BitVec.ofNat 64 (8 * m)) 8) :
    execBlock isa [.addi .t1 .t0 ((8 + 8 * m : Nat) : Int), .store .d .t1 .t0 (8 * m)] w =
      some ({ w.write .t1 (w.sp + BitVec.ofNat 64 (8 + 8 * m)) with
          mem := w.mem.writeW (w.sp + BitVec.ofNat 64 (8 * m))
            (w.sp + BitVec.ofNat 64 (8 + 8 * m)) },
        [.addr (w.sp + BitVec.ofNat 64 (8 * m))]) := by
  have ha := exec_addi_nat (s := w) (d := .t1) (n := .t0) (m := 8 + 8 * m) hm
  have hs := exec_store_d (s := w.write .t1 (w.gpr .t0 + BitVec.ofNat 64 (8 + 8 * m)))
    (t := .t1) (n := .t0) (off := 8 * m) (by omega_using [hm])
    (by simp only [State.write, reduceCtorEq, ↓reduceIte, ht0]; exact Spill.al8 hal (by omega))
    (by simp only [State.write, reduceCtorEq, ↓reduceIte, ht0]; exact hw)
  simp only [execBlock, isa, ha, hs, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  simp only [State.write, reduceCtorEq, ↓reduceIte, ht0]

/-- The addresses `setArgs bytes m` accesses, from the stack pointer `sp`. -/
def setArgsTrace (bytes : Nat) (sp : Addr) (m : Nat) : List Leak :=
  copyTrace bytes sp m ++ [.addr (sp + BitVec.ofNat 64 (8 * m))]

/-- The state after `setArgs bytes m` from `u`, if it runs. -/
def setArgsState (bytes m : Nat) (u : State) : State :=
  ((execBlock isa (setArgs bytes m) u).map Prod.fst).getD u

/-- `setArgs`: the stack arguments copied into the frame, the buffer's
address after them; nothing else written, and only `t0` and `t1` changed. -/
theorem setArgs_run {bytes m : Nat} {u : State} (hal : u.sp.toNat % 8 = 0)
    (hfit : bytes + 8 + 8 * m < 2 ^ 64) (hb : 8 + 8 * m ≤ bytes)
    (ho : bytes + 8 * m < 2048) (h8 : bytes % 8 = 0)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8)
    (hw : ∀ j ≤ m, InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * j)) 8) :
    execBlock isa (setArgs bytes m) u = some (setArgsState bytes m u, setArgsTrace bytes u.sp m) ∧
      (setArgsState bytes m u).rd = u.rd ∧ (setArgsState bytes m u).wr = u.wr ∧
      (setArgsState bytes m u).sp = u.sp ∧
      (∀ q, q ≠ .t0 → q ≠ .t1 → (setArgsState bytes m u).gpr q = u.gpr q) ∧
      Frame [⟨u.sp, 8 * (m + 1)⟩] u.mem (setArgsState bytes m u).mem ∧
      (∀ j < m, (setArgsState bytes m u).mem.readW (u.sp + BitVec.ofNat 64 (8 * j)) 64 =
        u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64) ∧
      (setArgsState bytes m u).mem.readW (u.sp + BitVec.ofNat 64 (8 * m)) 64 =
        u.sp + BitVec.ofNat 64 (8 + 8 * m) := by
  -- `addi t0, sp, 0`.
  let u₀ := u.write .t0 (u.sp + BitVec.ofNat 64 0)
  have h0 : execBlock isa [.addSp .t0 0] u = some (u₀, []) := by
    simp only [execBlock, isa, exec_addSp (show (0 : Nat) < 2048 by decide), Option.map_some,
      addrs, List.map_nil, List.append_nil]; rfl
  have ht0 : u₀.gpr .t0 = u₀.sp := by
    simp only [u₀, State.write, ↓reduceIte, BitVec.add_zero]
  have hc := copies_run (bytes := bytes) (u := u₀) ht0 hal h8 m (by omega_using [ho])
    (fun j hj => hr j hj) (fun j hj => hw j (by omega_using [hj]))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u₀) m (by omega_using [hfit])
    (by omega_using [hb])
  have ht := tail_run (m := m) (w := copiedState bytes u₀ m)
    (by rw [copiedState_gpr _ _ (by decide), copiedState_sp]; exact ht0)
    (by rw [copiedState_sp]; exact hal) (by omega_using [ho, hb])
    (by rw [copiedState_wr, copiedState_sp]; exact hw m (Nat.le_refl _))
  have hsp₀ : u₀.sp = u.sp := rfl
  have hmem₀ : u₀.mem = u.mem := rfl
  rw [hsp₀, hmem₀] at f hv
  let w := copiedState bytes u₀ m
  let fin : State := { w.write .t1 (u.sp + BitVec.ofNat 64 (8 + 8 * m)) with
    mem := w.mem.writeW (u.sp + BitVec.ofNat 64 (8 * m)) (u.sp + BitVec.ofNat 64 (8 + 8 * m)) }
  have hrun : execBlock isa (setArgs bytes m) u = some (fin, setArgsTrace bytes u.sp m) := by
    rw [setArgs, execBlock_append, execBlock_append, h0]
    simp only [Option.bind_some, Option.map_some, hc, ht, copiedState_sp, setArgsTrace,
      List.nil_append]
    rfl
  have hst : setArgsState bytes m u = fin := by simp [setArgsState, hrun]
  rw [hst]
  refine ⟨hrun, by simp [fin, w, u₀, State.write], by simp [fin, w, u₀, State.write],
    by simp [fin, w, u₀, State.write], fun q h₁ h₂ => ?_, ?_, fun j hj => ?_, ?_⟩
  · show (w.write .t1 _).gpr q = _
    simp only [State.write, h₂, ↓reduceIte]
    rw [copiedState_gpr _ _ h₂]
    simp only [u₀, State.write, h₁, ↓reduceIte]
  · refine (Frame.sub f fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
    · exact Offset.contains_base _ (d := 8 * m) (k := 8 * (m + 1)) (by omega_using [])
        (by omega_using [ho])
  · show (w.mem.writeW _ _).readW _ 64 = _
    rw [Mem.readW_writeW_sep, hv j hj]
    · exact Offset.sep _ (d := 8 * j) (n := 8) (e := 8 * m) (k := 8)
        (by omega_using [hj]) (by omega_using [ho, hj]) (by omega_using [ho])
    · decide
  · show (w.mem.writeW _ _).readW _ 64 = _
    rw [Mem.readW_writeW_self64]

/-! ## The run from `narrowA` -/

/-- `p - b + d` is `p - (b - d)`, for `d ≤ b`. -/
theorem sub_add_ofNat (p : Addr) {b d : Nat} (h : d ≤ b) :
    p - BitVec.ofNat 64 b + BitVec.ofNat 64 d = p - BitVec.ofNat 64 (b - d) := by
  rw [Offset.sub_ofNat_eq p (show b - d ≤ b by omega_using []), Nat.sub_sub_self h]

/-- The regions of the contract with the buffer, from the state after
`setArgs`: the buffers, the buffer, and the copied stack arguments. -/
def oldRegions (sig : Sig) (e : Elem) (n bytes m : Nat) (s : State) : List (Region × Bool) :=
  (Sig.bufs sig.params (stkArgs m s) ++
    [(⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m), n * e.size⟩, true)]) ++
    [(⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * 0), 8 * (m + 1)⟩, false)]

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the frame's `alloc` and `setArgs`, which may read
and write what the contract with the buffer lets it. -/
def narrowA (sig : Sig) (e : Elem) (n bytes m : Nat) (s : State) : State :=
  (setArgsState bytes m (allocd bytes s)).withRegions
    (((oldRegions sig e n bytes m s).filter (!·.2)).map (·.1))
    (((oldRegions sig e n bytes m s).filter (·.2)).map (·.1))

/-- The sizes `withStackScratchArgs` needs: the frame holds the copies, the
buffer's address and the buffer; the offsets of the copies' loads fit
`ld`'s. -/
abbrev FitsA (m bytes : Nat) (e : Elem) (n : Nat) : Prop :=
  8 + 8 * m + n * e.size ≤ bytes ∧ bytes + 8 * m < 2048 ∧ bytes % 16 = 0

theorem stackArg_withRegions (u : State) (rd wr : List Region) (j : Nat) :
    stackArg (u.withRegions rd wr) j = stackArg u j := rfl

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What the frame's `alloc` and `setArgs` give, from a state satisfying the
contract without the buffer. -/
theorem argsState_run (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    let u := allocd bytes s
    execBlock isa (setArgs bytes m) u = some (setArgsState bytes m u, setArgsTrace bytes u.sp m) ∧
      (setArgsState bytes m u).rd = u.rd ∧ (setArgsState bytes m u).wr = u.wr ∧
      (setArgsState bytes m u).sp = u.sp ∧
      (∀ q, q ≠ .t0 → q ≠ .t1 → (setArgsState bytes m u).gpr q = s.gpr q) ∧
      Frame [⟨u.sp, bytes⟩] s.mem (setArgsState bytes m u).mem ∧
      (∀ j < m, stackArg (setArgsState bytes m u) j = stackArg s j) ∧
      stackArg (setArgsState bytes m u) m = u.sp + BitVec.ofNat 64 (8 + 8 * m) := by
  intro u
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rw [pre_stk hk hl] at hs
  obtain ⟨⟨hal, hst, hfit⟩, hrd, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb0]
  have hu : u.sp = s.sp - BitVec.ofNat 64 bytes := rfl
  have hual : u.sp.toNat % 8 = 0 := by
    rw [hu, toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hal, hb2]
  have hsrc : ∀ j, u.sp + BitVec.ofNat 64 (bytes + 8 * j) = stackArgAddr s j := fun j => by
    rw [hu, stackArgAddr, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  -- The caller's stack arguments hold the sources.
  have hargs : ∀ j < m, InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := fun j hj => by
    have h0 : m ≠ 0 := by omega_using [hj]
    have hmem : (⟨stackArgAddr s 0, 8 * m⟩, false) ∈ allStk sig m s := by
      simp [allStk, argAreaStk, h0]
    have hfit' : s.sp.toNat + 8 * m ≤ 2 ^ 64 := by omega_using [hfit, h0]
    have hc : (⟨stackArgAddr s 0, 8 * m⟩ : Region).Contains (stackArgAddr s j) 8 := by
      rw [stackArgAddr, stackArgAddr]
      exact Offset.contains _ (d := 8 * j) (n := 8) (e := 8 * 0) (k := 8 * m)
        (by omega_using []) (by omega_using [hj]) (by omega_using [hfit', hsb, hb0])
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    show _ ∈ s.rd
    rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j ≤ m, InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * j)) 8 :=
    fun j hj => ⟨_, List.mem_cons_self .., by
      show (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ : Region).Contains _ 8
      exact Offset.contains_base _ (d := 8 * j) (n := 8) (k := bytes)
        (by omega_using [hb0, hj]) (by omega_using [hb0, hb1, hj])⟩
  obtain ⟨hrun, hrd', hwr', hsp', hg, hf, hv, hlast⟩ := setArgs_run (bytes := bytes) (m := m)
    (u := u) hual (by omega_using [hb0, hb1]) (by omega_using [hb0]) (by omega_using [hb1])
    (by omega_using [hb2]) (fun j hj => by rw [hsrc]; exact hargs j hj) hframe
  have hfa : u.mem = s.mem := rfl
  refine ⟨hrun, hrd', hwr', hsp', fun q h₁ h₂ => (hg q h₁ h₂).trans ?_, ?_, fun j hj => ?_, ?_⟩
  · rfl
  · rw [← hfa]
    exact Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hb0])⟩
  · show (setArgsState bytes m u).mem.readW (stackArgAddr (setArgsState bytes m u) j) 64 = _
    rw [stackArgAddr, hsp', hv j hj, hsrc]
    rfl
  · show (setArgsState bytes m u).mem.readW (stackArgAddr (setArgsState bytes m u) m) 64 = _
    rw [stackArgAddr, hsp', hlast]

theorem stkArgs_withScratch (s u : State) (hg : ∀ q, q ≠ .t0 → q ≠ .t1 → u.gpr q = s.gpr q)
    (ha : ∀ j < m, stackArg u j = stackArg s j) :
    stkArgs (m + 1) u = stkArgs m s ++ [stackArg u m] := by
  have hr : argRegs.map u.gpr = argRegs.map s.gpr :=
    List.map_congr_left fun q hq => hg q (by revert q; decide) (by revert q; decide)
  rw [stkArgs, stkArgs, hr, List.range_succ, List.map_append, ← List.append_assoc]
  refine congrArg (· ++ _) (congrArg _ (List.map_congr_left fun j hj => ha j ?_))
  simpa using hj

/-- What `narrowA` keeps of `s`, and what it holds. -/
theorem narrowA_facts (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (narrowA sig e n bytes m s).sp = s.sp - BitVec.ofNat 64 bytes ∧
      (∀ q, q ≠ .t0 → q ≠ .t1 → (narrowA sig e n bytes m s).gpr q = s.gpr q) ∧
      stkArgs (m + 1) (narrowA sig e n bytes m s) =
        stkArgs m s ++ [s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m)] ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩] s.mem (narrowA sig e n bytes m s).mem := by
  obtain ⟨-, -, -, hsp, hg, hf, hargs, hlast⟩ := argsState_run hk hl hb hs
  refine ⟨hsp, hg, ?_, hf⟩
  rw [stkArgs_withScratch (u := narrowA sig e n bytes m s) s (fun q h₁ h₂ => hg q h₁ h₂)
    fun j hj => (stackArg_withRegions _ _ _ j).trans (hargs j hj)]
  exact congrArg (fun x => stkArgs m s ++ [x]) ((stackArg_withRegions _ _ _ _).trans hlast)

/-- The buffers lie outside the frame: `narrowA`'s memory is `s`'s there. -/
theorem narrowA_agree (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (stkArgs m s), ∀ x, b.1.Contains x 1 →
      (narrowA sig e n bytes m s).mem x = s.mem x := by
  obtain ⟨-, -, -, hf⟩ := narrowA_facts hk hl hb hs
  rw [pre_stk hk hl] at hs
  obtain ⟨⟨-, hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb.1]
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega_using [hb.1])]; simp
  intro b hb' x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right
    (Offset.sub_below _ (a := bytes) (n := bytes) (by omega_using []) (by omega_using [])) x hx hc

/-- The regions of the contract with the buffer, in `narrowA`, are
`oldRegions`. -/
theorem allStk_narrowA (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    allStk (sig.withScratch nm e n) (m + 1) (narrowA sig e n bytes m s) =
      oldRegions sig e n bytes m s := by
  obtain ⟨hsp, -, hargs, -⟩ := narrowA_facts hk hl hb hs
  rw [allStk, hargs, argAreaStk, ite_eq_right (by omega_using []),
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _
        (by rw [stkArgs_length]; exact hk.symm), stackArgAddr, hsp]
  rfl

/-- The precondition of the contract without the buffer gives the one with it
in `narrowA`, if the precondition reads memory only within the buffers. -/
theorem narrowA_pre (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre (narrowA sig e n bytes m s) := by
  obtain ⟨hsp, -, hargs, -⟩ := narrowA_facts hk hl hb hs
  have hall := allStk_narrowA (nm := nm) hk hl hb hs
  have hagB := narrowA_agree hk hl hb hs
  have hk' : ((sig.withScratch nm e n).words abi.ptrBits).length = 8 + (m + 1) := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton, hk]; omega_using []
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rw [pre_stk hk hl] at hs
  obtain ⟨⟨hal, hst, -⟩, -, -, hpw, hres, hnw, hpr, hu64⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb0]
  have hlen : (stkArgs m s).length = (sig.words abi.ptrBits).length := by
    rw [stkArgs_length, hk]
  have hlt := s.sp.isLt
  -- Addresses as offsets below `s.sp`.
  have hscr : s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m) =
      s.sp - BitVec.ofNat 64 (bytes - (8 + 8 * m)) := sub_add_ofNat _ (by omega_using [hb0])
  have harea : s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * 0) =
      s.sp - BitVec.ofNat 64 (bytes - 8 * 0) := sub_add_ofNat _ (by omega_using [hb0])
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega_using [hb0])]; simp
  -- The buffers lie outside the frame.
  have hout : ∀ a ∈ Sig.bufs sig.params (stkArgs m s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (Offset.sub_below _ hx hk)
  have hpwB : (Sig.bufs sig.params (stkArgs m s)).Pairwise
      (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
    List.Pairwise.sublist (List.sublist_append_left _ _) hpw
  have hscrD : ∀ a ∈ Sig.bufs sig.params (stkArgs m s), a.1.Disjoint
      ⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m), n * e.size⟩ :=
    fun a ha => by rw [hscr]; exact hout a ha (by omega_using []) (by omega_using [hb0])
  have hareaD : ∀ a ∈ Sig.bufs sig.params (stkArgs m s), a.1.Disjoint
      ⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * 0), 8 * (m + 1)⟩ :=
    fun a ha => by rw [harea]; exact hout a ha (by omega_using []) (by omega_using [hb0])
  have hEal : (s.sp - BitVec.ofNat 64 bytes).toNat % 16 = 0 := by
    rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hal, hb2]
  refine (pre_stk (sig := sig.withScratch nm e n) (m := m + 1)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk'
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [hall, hsp, hargs]
  refine ⟨⟨hEal, .inr ?_, .inr ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hsb]
  · rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hb0, hsb]
  · -- Pairwise disjoint.
    have hsa : (⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m), n * e.size⟩ :
        Region).Disjoint ⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * 0), 8 * (m + 1)⟩ :=
      Offset.disjoint _ (d := 8 + 8 * m) (n := n * e.size) (e := 8 * 0) (k := 8 * (m + 1))
        (.inr (by omega_using [])) (by omega_using [hb0, hsb]) (by omega_using [hb0, hsb])
    simp only [oldRegions, List.pairwise_append, List.pairwise_singleton, List.mem_append,
      List.mem_singleton]
    refine ⟨⟨hpwB, trivial, fun a ha b hb _ => ?_⟩, trivial, fun a ha b hb _ => ?_⟩
    · subst hb; exact hscrD a ha
    · subst hb
      rcases ha with ha | rfl
      · exact hareaD a ha
      · exact hsa
  · -- The reserved stack: the stack below the frame.
    intro r hr a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hr
    rw [stackBelow_pos _ h0, List.mem_singleton] at hr; subst hr
    simp only [oldRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | rfl) | rfl
    · exact (Region.Disjoint.symm (hout a ha (x := stack + bytes) (k := stack + bytes)
        (by omega_using []) (by omega_using []))).sub_left (below_below _ bytes stack)
    · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8 + 8 * m)
        (k := n * e.size) (by omega_using [hb0, hsb]))
    · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8 * 0)
        (k := 8 * (m + 1)) (by omega_using [hb0, hsb]))
  · -- No buffer wraps around.
    intro a ha
    rw [show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m)).toNat + n * e.size ≤ 2 ^ 64
      rw [hscr, toNat_sub_ofNat' (by omega_using [hsb])]
      omega_using [hb0, hsb]
  · -- The precondition, which reads only the buffers, and the alignment of
    -- the `u16`, `u32` and `u64` buffers.
    refine ⟨Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_, ?_⟩
    · exact hpre _ _ _ hlen (fun b hb x hx => (hagB b hb x hx).symm) hpr
    · intro p hp
      rw [show (sig.withScratch nm e n).params = sig.params ++ [(nm, .array true e n)] from rfl,
        Sig.alignedBufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hu64 p hp
      · split at hp
        · simp only [List.mem_singleton] at hp; subst hp
          exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Elem.align_dvd_eight e)
            (Nat.dvd_of_mod_eq_zero (Spill.al8 (by omega_using [hEal]) (by omega_using []))))
        · simp at hp

/-- The public data of the contract without the buffer is public in
`narrowA` for the contract with it. -/
theorem narrowA_pub (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrowA sig e n bytes m s₁)
      (narrowA sig e n bytes m s₂) := by
  have hk' : ((sig.withScratch nm e n).words abi.ptrBits).length = 8 + (m + 1) := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton, hk]; omega_using []
  rw [pubL_stk hk hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  obtain ⟨-, -, a₁, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb h₁
  obtain ⟨-, -, a₂, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb h₂
  have l₁ : (stkArgs m s₁).length = (sig.words abi.ptrBits).length := by rw [stkArgs_length, hk]
  have l₂ : (stkArgs m s₂).length = (sig.words abi.ptrBits).length := by rw [stkArgs_length, hk]
  refine (pubL_stk (sig := sig.withScratch nm e n) (m := m + 1)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk'
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [a₁, a₂, (narrowA_facts (e := e) (n := n) hk hl hb h₁).1,
    (narrowA_facts (e := e) (n := n) hk hl hb h₂).1, hsp]
  refine ⟨⟨rfl, leakAgree_withScratch hleak _ _ l₁ l₂ (narrowA_agree hk hl hb h₁)
    (narrowA_agree hk hl hb h₂) hlk⟩, fun i hi => ?_⟩
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have hps : ((sig.withScratch nm e n).params.flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Sig.withScratch, Param.pubs]
  rw [hps] at hi
  generalize stkArgs m s₁ = v₁ at l₁ hpa ⊢
  generalize stkArgs m s₂ = v₂ at l₂ hpa ⊢
  by_cases hik : i < (sig.words abi.ptrBits).length
  · have hW : (((sig.withScratch nm e n).words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 =
        ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 := by
      rw [Sig.words_withScratch, List.map_append]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [List.length_map]; exact hik)]
    rw [hW]
    simp only [List.getD_eq_getElem?_getD] at hi hpa ⊢
    rw [List.getElem?_append_left (by rw [l₁]; exact hik),
      List.getElem?_append_left (by rw [l₂]; exact hik)]
    rw [List.getElem?_append_left (by rw [lp]; exact hik)] at hi
    exact hpa i hi
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega_using [l₁, hik]),
      List.getElem?_append_right (by omega_using [l₂, hik]), l₁, l₂]

/-- A run of the code from `narrowA s` is a run of `withStackScratchArgs`
from `s`, after `setArgs`'s accesses, which keeps what the calling
convention requires, and whose memory and registers are those of the code's
run. -/
theorem withStackScratchArgs_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowA sig e n bytes m s) t s₃) (ha : abiPreserved (narrowA sig e n bytes m s) s₃) :
    Exec isa (withStackScratchArgs bytes m c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) m ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hrun, hrd', hwr', -, -, -, -, -⟩ := argsState_run hk hl hb hs
  obtain ⟨hsp, hg, -, -⟩ := narrowA_facts hk hl hb hs
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rw [pre_stk hk hl] at hs
  obtain ⟨⟨-, hst, -⟩, hrd, hwr, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb0]
  -- The frame's `alloc`.
  have hpush : isa.push (.alloc bytes) s = some (allocd bytes s) := by
    show push (.alloc bytes) s = some (allocd bytes s)
    unfold push
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega_using [hb0], by omega_using [hb1], hb2,
      by omega_using [hsb]⟩) |>.trans rfl
  -- The regions of `narrowA`: the buffers, and the frame's buffer and copies.
  have hF : ∀ {d k : Nat}, d + k ≤ bytes →
      Covers [⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d, k⟩]
        (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    fun hk => Covers.one ⟨_, List.mem_cons_self .., by
      exact Offset.contains_base _ hk (by omega_using [hk, hb1])⟩
  have hbufR : ∀ a ∈ Sig.bufs sig.params (stkArgs m s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (stkArgs m s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes m s).filter (·.2)).map (·.1))
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (ha | rfl) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · exact hF hb0
    · simp at hf'
  have hcovR : Covers (((oldRegions sig e n bytes m s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (ha | rfl) | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (hF (by omega_using [hb0]))
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowA sig e n bytes m s).withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      setArgsState bytes m (allocd bytes s) by
    rw [narrowA, State.withRegions_withRegions, show s.rd = (allocd bytes s).rd from rfl, ← hrd',
      show ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr = (allocd bytes s).wr from rfl, ← hwr',
      State.withRegions_self]] at hw
  -- The `free`.
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans hsp
  have hpop : isa.pop (.free bytes) (allocd bytes s)
      (s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
        some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions, allocd, hsp₃, List.head?_cons, List.tail_cons,
      show 0 < bytes by omega_using [hb0], show bytes ≤ 4064 by omega_using [hb1], hb2, and_self,
      ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl, ?_⟩, rfl, rfl⟩
  · have h0 : q ≠ .t0 := fun h => by subst h; simp [preserved] at hq
    have h1 : q ≠ .t1 := fun h => by subst h; simp [preserved] at hq
    show s₃.gpr q = s.gpr q
    rw [ha.1 q hq, hg q h0 h1]
  · show s₃.gpr .ra = s.gpr .ra
    rw [ha.2.2, hg .ra (by decide) (by decide)]

/-- Code verified for a function whose arguments fill `a0`–`a7` and `m`
doublewords of stack, and whose last argument, after them on the stack, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratchArgs`), if its precondition,
postcondition and leak read memory only within the function's buffers
(`hpre`, `hpost`, `hleak`, which holds of no leak). -/
theorem Verified.stackScratchArgs {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length = 8 + m) (hb : FitsA m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratchArgs bytes m c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hk' : ((sig.withScratch nm e n).words abi.ptrBits).length = 8 + (m + 1) := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton, hk]; omega_using []
  have hlen : ∀ s, (stkArgs m s).length = (sig.words abi.ptrBits).length := fun s => by
    rw [stkArgs_length, hk]
  -- Every run is the `alloc` and `setArgs`, then the code's run from `narrowA`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowA sig e n bytes m s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrowA sig e n bytes m s) s₃ ∧
      Exec isa (withStackScratchArgs bytes m c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) m ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowA_pre hk hl hb hpre hs)
    exact ⟨t, s₃, he, hq, withStackScratchArgs_run hk hl hb hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stk hk]
    have hq' := (post_stk (sig := sig.withScratch nm e n) (m := m + 1)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, hargs, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb hs
    rw [hargs] at hq'
    rw [hm, hg]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (hlen s)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (hlen s) (narrowA_agree hk hl hb hs) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_stk hk hl).mp hp).1.1,
      hct _ _ _ _ _ _ (narrowA_pre hk hl hb hpre h₁) (narrowA_pre hk hl hb hpre h₂)
        (narrowA_pub hk hl hb h₁ h₂ hp hleak) f₁ f₂]

/-- `withStackScratchArgs`'s code satisfies `spSafe` (no modelled instruction
writes `sp`). -/
theorem withStackScratchArgs_spSafe (bytes m : Nat) (c : Prog isa) :
    (withStackScratchArgs bytes m c).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

end

end VG.RISCV64
