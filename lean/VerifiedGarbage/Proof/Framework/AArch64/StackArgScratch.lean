import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# A scratch buffer on the stack, after stack arguments (AArch64)

`Verified.stackArgScratch`: code verified for a function whose last argument
is a scratch buffer passed on the stack (its contract `Sig.scratchContract`;
the function's other arguments fill the eight argument registers, and `m`
more are on the stack) runs as a function without that argument when
`withStackArgScratch` allocates the buffer in a frame on the stack, with
`bytes` more bytes of stack. The frame holds what the code expects at and
above `sp` on entry: a copy of the `m` stack arguments, then the buffer's
address, then, from the next 16-byte boundary (`bufOff m`), the buffer
(`setArgs`). The return address is in `x30`, which the code keeps, not on
the stack. The code runs from the state after the frame's allocation and
`setArgs`, with the permissions of the contract with the argument
(`narrowS`), and its run there is its run from that state (`Exec.widen`).

The copies are memory the code reads on entry, which the contract without the
argument says nothing of: the precondition, the postcondition and the leak,
if the contract has one, must read memory only within the function's buffers
(`hpre`, `hpost`, `hleak`), which the frame lies outside of. The argument
area is read-only on AArch64 (`abi`), so the copies are too.

The calling convention's precondition, postcondition and public data, with a
leak, for any number of argument words (`pre_args`, `post_args`,
`pub_args`), are here too.
-/

namespace VG.AArch64

open VG.Impl.StackScratch.AArch64

/-! ## The calling convention, with arguments on the stack -/

/-- The number of `sig`'s arguments on the stack. -/
abbrev nStack (sig : Sig) : Nat := (sig.words abi.ptrBits).length - 8

/-- The arguments of a function with signature `sig`: those in registers,
then those on the stack. -/
def allArgs (sig : Sig) (s : State) : List (BitVec 64) :=
  (argRegs.take (sig.words abi.ptrBits).length).map s.gpr ++
    (List.range (nStack sig)).map (stackArg s)

/-- The argument area of `sig`, read-only. -/
def argArea (sig : Sig) (s : State) : List (Region × Bool) :=
  if nStack sig = 0 then [] else [(⟨stackArgAddr s 0, 8 * nStack sig⟩, false)]

/-- The buffers and the argument area of `sig`, and whether each is
writable. -/
def allRegions (sig : Sig) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (allArgs sig s) ++ argArea sig s

/-- The calling convention passes `sig`'s arguments (its stack arguments are
of a layout it accepts). -/
def ArgsOk (sig : Sig) : Prop :=
  abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some (allArgs sig)

theorem ptrBits_eq : abi.ptrBits = 64 := rfl

theorem allArgs_length (sig : Sig) (s : State) :
    (allArgs sig s).length = (sig.words abi.ptrBits).length := by
  simp only [allArgs, List.length_append, List.length_map, List.length_take, List.length_range,
    argRegs, List.length_cons, List.length_nil, nStack, ptrBits_eq]
  omega

/-- The calling convention passes the arguments as `allArgs`, or rejects
the signature. -/
theorem args_cases (sig : Sig) :
    abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = none ∨ ArgsOk sig := by
  unfold ArgsOk
  have hL : ∀ s : State, (argRegs.take (sig.words abi.ptrBits).length).map s.gpr ++
      (List.range (nStack sig)).map (stackArg s) = allArgs sig s := fun _ => rfl
  simp only [abi, List.length_map]
  simp only [nStack, ptrBits_eq] at hL ⊢
  split
  · next h =>
    refine .inr (congrArg some (funext fun s => ?_))
    rw [← hL s]
    have h0 : (sig.words 64).length - 8 = 0 := by
      simp only [argRegs, List.length_cons, List.length_nil] at h; omega
    rw [h0]; simp
  · next h =>
    have htake : ∀ s : State, argRegs.map s.gpr =
        (argRegs.take (sig.words 64).length).map s.gpr := fun s => by
      rw [List.take_of_length_le (by omega)]
    have hs : (fun s => argRegs.map s.gpr ++
        (List.range ((sig.words 64).length - argRegs.length)).map (stackArg s)) = allArgs sig :=
      funext fun s => by rw [htake s, ← hL s]; rfl
    split
    · exact .inr (congrArg some hs)
    · split
      · exact .inr (congrArg some hs)
      · exact .inl rfl

theorem argArea_eq (sig : Sig) (wa : Bool) (s : State) :
    (abi.argArea ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)) = argArea sig s := by
  simp only [abi, argArea, List.length_map, nStack]
  split <;> simp_all [argRegs]

theorem wf_args {sig : Sig} {stack : Nat} {s : State} :
    abi.wf ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) stack s ↔
      ((stack = 0 ∨ stack ≤ s.sp.toNat) ∧ s.sp.toNat + 8 * nStack sig ≤ 2 ^ 64) := by
  have := s.sp.isLt
  simp only [abi, List.length_map, nStack]
  split
  · next h =>
    have h0 : (sig.words 64).length - 8 = 0 := by
      simp only [argRegs, List.length_cons, List.length_nil] at h; omega
    rw [h0]
    cases stack <;> simp <;> omega
  · simp only [argRegs, List.length_cons, List.length_nil]
    cases stack <;> simp

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
  {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The calling convention passes the arguments of a satisfiable contract. -/
theorem argsOk_of_pre {s : State} (hs : (sig.contract abi pre post wa stack leak).pre s) :
    ArgsOk sig := by
  rcases args_cases sig with h | h
  · simp only [Sig.contract, h] at hs
  · exact h

/-- The precondition of a contract. -/
theorem pre_args {s : State} (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pre s ↔
      ((stack = 0 ∨ stack ≤ s.sp.toNat) ∧ s.sp.toNat + 8 * nStack sig ≤ 2 ^ 64) ∧
      s.rd = ((allRegions sig s).filter (!·.2)).map (·.1) ∧
      s.wr = ((allRegions sig s).filter (·.2)).map (·.1) ∧
      (allRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ allRegions sig s, r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (allArgs sig s) s.mem := by
  simp only [Sig.contract]
  rw [hA]
  simp only [argArea_eq, Sig.lists_of_noLists _ _ _ _ hl, List.map_nil, List.append_nil]
  rw [wf_args]
  exact Iff.rfl

/-- The postcondition of a contract. -/
theorem post_args {s s' : State} (hA : ArgsOk sig) :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem s'.mem
        ((s'.gpr .x0).setWidth _) := by
  simp only [Sig.contract]
  rw [hA]
  exact Iff.rfl

/-- The public data of a contract, and what it may leak. -/
theorem pub_args {s₁ s₂ : State} (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.sp = s₂.sp ∧ leakAgree leak (allArgs sig s₁) s₁.mem (allArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((allArgs sig s₁).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((allArgs sig s₂).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  simp only [Sig.contract]
  rw [hA]
  simp only [Sig.descs_of_noLists _ _ _ hl, List.not_mem_nil, false_implies, implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

end

/-! ## The signature with the buffer -/

theorem widths_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) :
    ((sig.withScratch nm e n).words abi.ptrBits).map (·.bits abi.ptrBits) =
      (sig.words abi.ptrBits).map (·.bits abi.ptrBits) ++ [64] := by
  rw [Sig.words_withScratch, List.map_append]
  rfl

theorem firstNarrowStack_append {l : List Nat} (h : firstNarrowStack l = true) :
    firstNarrowStack (l ++ [64]) = true := by
  unfold firstNarrowStack at h ⊢
  split at h
  · simpa [List.all_append] using h
  · exact absurd h (by decide)

/-- The calling convention passes the arguments of `sig` with a buffer after
its stack arguments if it passes those of `sig`. -/
theorem argsOk_withScratch {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    (hk : 8 ≤ (sig.words abi.ptrBits).length) (hA : ArgsOk sig) :
    ArgsOk (sig.withScratch nm e n) := by
  have h8 : argRegs.length = 8 := rfl
  have hk64 : 8 ≤ (sig.words 64).length := hk
  -- The stack arguments of `sig` are of a layout `abi` accepts.
  have hS : (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).drop argRegs.length).all
        (· = 64) = true ∨
      firstNarrowStack (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).drop argRegs.length) =
        true := by
    rcases Nat.eq_or_lt_of_le hk with hk' | hk'
    · refine .inl ?_
      rw [List.drop_eq_nil_of_le (by rw [List.length_map, h8]; omega)]
      rfl
    · unfold ArgsOk at hA
      simp only [abi, List.length_map] at hA
      have hk'' : 8 < (sig.words 64).length := hk'
      split at hA
      · rename_i hc; rw [h8] at hc; omega
      · split at hA
        · exact .inl (by assumption)
        · split at hA
          · exact .inr (by assumption)
          · cases hA
  rcases args_cases (sig.withScratch nm e n) with h | h
  · exfalso
    rw [widths_withScratch] at h
    simp only [abi, List.length_append, List.length_map, List.length_singleton] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h₂ h₃
          simp only [ptrBits_eq] at hS
          rw [List.drop_append_of_le_length (by rw [List.length_map, h8]; omega)] at h₂ h₃
          rcases hS with hS | hS
          · exact h₂ (by rw [List.all_append, hS]; rfl)
          · exact h₃ (firstNarrowStack_append hS)
  · exact h

theorem nStack_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat)
    (hk : 8 ≤ (sig.words abi.ptrBits).length) :
    nStack (sig.withScratch nm e n) = nStack sig + 1 := by
  simp only [nStack, Sig.words_withScratch, List.length_append, List.length_singleton]
  omega

theorem argRegs_take {k : Nat} (hk : 8 ≤ k) : argRegs.take k = argRegs :=
  List.take_of_length_le (by simp only [argRegs, List.length_cons, List.length_nil]; omega)

/-- The arguments of `sig` with a buffer after its stack arguments, from a
state that keeps `s`'s argument registers and stack arguments. -/
theorem allArgs_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat)
    (hk : 8 ≤ (sig.words abi.ptrBits).length) (s u : State)
    (hg : ∀ r ∈ argRegs, u.gpr r = s.gpr r)
    (ha : ∀ j < nStack sig, stackArg u j = stackArg s j) :
    allArgs (sig.withScratch nm e n) u = allArgs sig s ++ [stackArg u (nStack sig)] := by
  have hk' : 8 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append]; omega
  rw [allArgs, allArgs, nStack_withScratch sig nm e n hk, argRegs_take hk, argRegs_take hk',
    List.range_succ, List.map_append, ← List.append_assoc, List.map_congr_left hg]
  refine congrArg (· ++ _) (congrArg _ (List.map_congr_left fun j hj => ha j ?_))
  simpa using hj

/-! ## Instructions -/

theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addSp d imm) s = some (s.write .x d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true]

theorem exec_ldrSp {s : State} {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.ldrSp t off) s = some (s.write .x t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, ho, and_self, ite_true, State.load, h, Option.map_some, Mem.readW]

theorem execBlock_cons_of {i : Instr} {is : List Instr} {s s₁ : State} (h : exec i s = some s₁) :
    execBlock isa (i :: is) s =
      (execBlock isa is s₁).map fun p => (p.1, (addrs i s).map Leak.addr ++ p.2) := by
  simp only [execBlock, isa, h]


/-! ## Copying the stack arguments -/

/-- The stack argument `copyArg bytes j` copies, from `w`. -/
abbrev copyVal (bytes j : Nat) (w : State) : BitVec 64 :=
  w.mem.readW (w.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64

/-- The state after `copyArg bytes j` from `w`. -/
def copyState (bytes j : Nat) (w : State) : State :=
  { w.write .x .x17 (copyVal bytes j w) with
    mem := w.mem.writeW (w.gpr .x16 + BitVec.ofNat 64 (8 * j)) (copyVal bytes j w) }

theorem copyArg_run {bytes j : Nat} {w : State} (ho : bytes % 8 = 0 ∧ bytes + 8 * j < 32768)
    (hr : InRegions (w.rd ++ w.wr) (w.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8)
    (hw : InRegions w.wr (w.gpr .x16 + BitVec.ofNat 64 (8 * j)) 8) :
    execBlock isa (copyArg bytes j) w = some (copyState bytes j w,
      [.addr (w.sp + BitVec.ofNat 64 (bytes + 8 * j)), .addr (w.gpr .x16 + BitVec.ofNat 64 (8 * j))]) := by
  have h16 : (w.write .x .x17 (copyVal bytes j w)).gpr .x16 = w.gpr .x16 :=
    RegUpd.gpr_write_of_ne w .x _ (by decide)
  have h17 : (w.write .x .x17 (copyVal bytes j w)).gpr .x17 = copyVal bytes j w := by
    rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _
  rw [copyArg, execBlock_cons_of (exec_ldrSp ⟨by omega, ho.2⟩ hr),
    execBlock_cons_of (exec_str_x ⟨by omega, by omega⟩ (by rw [h16]; exact hw))]
  simp only [execBlock, Option.map_some, addrs, h16, h17, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

section
variable (bytes j : Nat) (w : State)
@[simp] theorem copyState_sp : (copyState bytes j w).sp = w.sp := rfl
@[simp] theorem copyState_rd : (copyState bytes j w).rd = w.rd := rfl
@[simp] theorem copyState_wr : (copyState bytes j w).wr = w.wr := rfl
@[simp] theorem copyState_v : (copyState bytes j w).v = w.v := rfl
theorem copyState_gpr {r : Reg} (h : r ≠ .x17) : (copyState bytes j w).gpr r = w.gpr r :=
  RegUpd.gpr_write_of_ne w .x _ h
end

/-- The state after copying the first `m` stack arguments from `w`. -/
def copiedState (bytes : Nat) (w : State) : Nat → State
  | 0 => w
  | m + 1 => copyState bytes m (copiedState bytes w m)

section
variable (bytes : Nat) (w : State)
@[simp] theorem copiedState_sp : ∀ m, (copiedState bytes w m).sp = w.sp
  | 0 => rfl
  | m + 1 => copiedState_sp m
@[simp] theorem copiedState_rd : ∀ m, (copiedState bytes w m).rd = w.rd
  | 0 => rfl
  | m + 1 => copiedState_rd m
@[simp] theorem copiedState_wr : ∀ m, (copiedState bytes w m).wr = w.wr
  | 0 => rfl
  | m + 1 => copiedState_wr m
@[simp] theorem copiedState_v : ∀ m, (copiedState bytes w m).v = w.v
  | 0 => rfl
  | m + 1 => copiedState_v m
theorem copiedState_gpr {r : Reg} (h : r ≠ .x17) : ∀ m, (copiedState bytes w m).gpr r = w.gpr r
  | 0 => rfl
  | m + 1 => (copyState_gpr _ _ _ h).trans (copiedState_gpr h m)
end

/-- The addresses copying the first `m` stack arguments accesses, from
`sp = p`. -/
def copyTrace (bytes : Nat) (p : Addr) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j =>
    [.addr (p + BitVec.ofNat 64 (bytes + 8 * j)), .addr (p + BitVec.ofNat 64 (8 * j))]

theorem copies_run {bytes : Nat} {w : State} (h16 : w.gpr .x16 = w.sp) (hb : bytes % 8 = 0) :
    ∀ m, bytes + 8 * m ≤ 32768 →
      (∀ j < m, InRegions (w.rd ++ w.wr) (w.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8) →
      (∀ j < m, InRegions w.wr (w.sp + BitVec.ofNat 64 (8 * j)) 8) →
      execBlock isa ((List.range m).flatMap (copyArg bytes)) w =
        some (copiedState bytes w m, copyTrace bytes w.sp m)
  | 0, _, _, _ => rfl
  | m + 1, hm, hr, hw => by
    have g16 := copiedState_gpr bytes w (r := .x16) (by decide) m
    rw [List.range_succ, List.flatMap_append, execBlock_append,
      copies_run h16 hb m (by omega) (fun j hj => hr j (by omega)) (fun j hj => hw j (by omega))]
    simp only [Option.bind_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [copyArg_run ⟨hb, by omega⟩
      (by rw [copiedState_rd, copiedState_wr, copiedState_sp]; exact hr m (by omega))
      (by rw [copiedState_wr, g16, h16]; exact hw m (by omega))]
    simp only [Option.map_some, copiedState_sp, g16, h16, copyTrace, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-- Copying the first `m` stack arguments writes only within the `m`
destination doublewords (from `sp`), which then hold the sources (from
`sp + bytes`). -/
theorem copiedState_mem {bytes : Nat} {w : State} (h16 : w.gpr .x16 = w.sp) :
    ∀ m, bytes + 8 + 8 * m ≤ 2 ^ 64 → 8 * m ≤ bytes →
      Frame [⟨w.sp, 8 * m⟩] w.mem (copiedState bytes w m).mem ∧
      ∀ j < m, (copiedState bytes w m).mem.readW (w.sp + BitVec.ofNat 64 (8 * j)) 64 =
        w.mem.readW (w.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (w := w) h16 m (by omega) (by omega)
    have g16 := copiedState_gpr bytes w (r := .x16) (by decide) m
    have f' : Frame [⟨w.sp, 8 * (m + 1)⟩] w.mem (copiedState bytes w m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    -- The source of argument `m` is above the first `m` destinations.
    have hsrc : (copiedState bytes w m).mem.readW (w.sp + BitVec.ofNat 64 (bytes + 8 * m)) 64 =
        w.mem.readW (w.sp + BitVec.ofNat 64 (bytes + 8 * m)) 64 := by
      refine f.readW (r := ⟨w.sp + BitVec.ofNat 64 (bytes + 8 * m), 8⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
    have hmem : (copiedState bytes w (m + 1)).mem = (copiedState bytes w m).mem.writeW
        (w.sp + BitVec.ofNat 64 (8 * m))
        ((copiedState bytes w m).mem.readW (w.sp + BitVec.ofNat 64 (bytes + 8 * m)) 64) := by
      show (copiedState bytes w m).mem.writeW ((copiedState bytes w m).gpr .x16 + _) _ = _
      rw [g16, h16, copyVal, copiedState_sp]
    rw [hmem, hsrc]
    refine ⟨f'.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega)), fun j hj => ?_⟩
    rcases Nat.lt_or_ge j m with hj' | hj'
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
        hv j hj']
    · obtain rfl : j = m := by omega
      rw [Mem.readW_writeW_self64]



/-! ## Setting up the arguments -/

theorem bufOff_bounds (m : Nat) : 8 * m + 8 ≤ bufOff m ∧ bufOff m ≤ 8 * m + 16 := by
  simp only [bufOff]; omega

/-- The state after `add x16, sp, #0` from `u`. -/
abbrev baseState (u : State) : State := u.write .x .x16 (u.sp + BitVec.ofNat 64 0)

theorem baseState_x16 (u : State) : (baseState u).gpr .x16 = (baseState u).sp := by
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.sp_write]
  exact BitVec.add_zero _

/-- The state after `setArgs bytes m` from `u`. -/
def setArgsState (bytes m : Nat) (u : State) : State :=
  let w := (copiedState bytes (baseState u) m).write .x .x17
    ((copiedState bytes (baseState u) m).sp + BitVec.ofNat 64 (bufOff m))
  { w with mem := w.mem.writeW (w.gpr .x16 + BitVec.ofNat 64 (8 * m)) (w.gpr .x17) }

/-- The addresses `setArgs bytes m` accesses, from `sp = p`. -/
def setArgsTrace (bytes : Nat) (p : Addr) (m : Nat) : List Leak :=
  copyTrace bytes p m ++ [.addr (p + BitVec.ofNat 64 (8 * m))]

section
variable (bytes m : Nat) (u : State)
@[simp] theorem setArgsState_sp : (setArgsState bytes m u).sp = u.sp := by
  simp only [setArgsState, RegUpd.sp_write, copiedState_sp]
@[simp] theorem setArgsState_rd : (setArgsState bytes m u).rd = u.rd := by
  simp only [setArgsState, RegUpd.rd_write, copiedState_rd]
@[simp] theorem setArgsState_wr : (setArgsState bytes m u).wr = u.wr := by
  simp only [setArgsState, RegUpd.wr_write, copiedState_wr]
@[simp] theorem setArgsState_v : (setArgsState bytes m u).v = u.v := by
  simp only [setArgsState, RegUpd.v_write, copiedState_v]
theorem setArgsState_gpr {q : Reg} (h₁ : q ≠ .x16) (h₂ : q ≠ .x17) :
    (setArgsState bytes m u).gpr q = u.gpr q := by
  show ((copiedState bytes (baseState u) m).write .x .x17 _).gpr q = _
  rw [RegUpd.gpr_write_of_ne _ _ _ h₂, copiedState_gpr _ _ h₂, RegUpd.gpr_write_of_ne _ _ _ h₁]
end

/-- `setArgs`: the stack arguments copied into the frame, the buffer's
address after them; nothing else written, and only `x16` and `x17`
changed. -/
theorem setArgs_run {bytes m : Nat} {u : State} (hb : bytes % 8 = 0) (hbl : bytes < 4096)
    (hbm : bufOff m ≤ bytes)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8)
    (hw : ∀ j ≤ m, InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * j)) 8) :
    execBlock isa (setArgs bytes m) u = some (setArgsState bytes m u, setArgsTrace bytes u.sp m) ∧
      Frame [⟨u.sp, 8 * (m + 1)⟩] u.mem (setArgsState bytes m u).mem ∧
      (∀ j < m, (setArgsState bytes m u).mem.readW (u.sp + BitVec.ofNat 64 (8 * j)) 64 =
        u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64) ∧
      (setArgsState bytes m u).mem.readW (u.sp + BitVec.ofNat 64 (8 * m)) 64 =
        u.sp + BitVec.ofNat 64 (bufOff m) := by
  have hbo := bufOff_bounds m
  have h16 := baseState_x16 u
  have hc := copies_run (bytes := bytes) (w := baseState u) h16 hb m (by omega) hr
    (fun j hj => hw j (by omega))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (w := baseState u) h16 m (by omega) (by omega)
  have g16 : (copiedState bytes (baseState u) m).gpr .x16 = u.sp :=
    (copiedState_gpr bytes _ (by decide) m).trans h16
  -- The last two instructions.
  have e₁ := exec_addSp (s := copiedState bytes (baseState u) m) (d := .x17)
    (show bufOff m < 4096 by omega)
  have e₂ := exec_str_x (s := (copiedState bytes (baseState u) m).write .x .x17
      ((copiedState bytes (baseState u) m).sp + BitVec.ofNat 64 (bufOff m)))
    (t := .x17) (n := .x16) (off := 8 * m) ⟨by omega, by omega⟩
    (by rw [RegUpd.wr_write, copiedState_wr, RegUpd.gpr_write_of_ne _ _ _ (by decide), g16]
        exact hw m (Nat.le_refl _))
  have hx16 : ((copiedState bytes (baseState u) m).write .x .x17
      ((copiedState bytes (baseState u) m).sp + BitVec.ofNat 64 (bufOff m))).gpr .x16 = u.sp := by
    rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), g16]
  have hx17 : ((copiedState bytes (baseState u) m).write .x .x17
      ((copiedState bytes (baseState u) m).sp + BitVec.ofNat 64 (bufOff m))).gpr .x17 =
      u.sp + BitVec.ofNat 64 (bufOff m) := by
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, copiedState_sp]; rfl
  have hmem : (setArgsState bytes m u).mem = (copiedState bytes (baseState u) m).mem.writeW
      (u.sp + BitVec.ofNat 64 (8 * m)) (u.sp + BitVec.ofNat 64 (bufOff m)) := by
    show Mem.writeW _ (_ + _) _ = _
    rw [hx16, hx17]
    rfl
  refine ⟨?_, ?_, fun j hj => ?_, ?_⟩
  · rw [setArgs, execBlock_append, execBlock_cons_of (exec_addSp (by decide)), hc]
    simp only [Option.map_some, Option.bind_some]
    rw [execBlock_cons_of e₁, execBlock_cons_of e₂]
    simp only [execBlock, Option.map_some]
    refine congrArg some (Prod.ext rfl ?_)
    simp only [addrs, hx16, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      RegUpd.sp_write, setArgsTrace]
  · rw [hmem]
    refine (Frame.sub f fun r hr => ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  · rw [hmem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
    exact hv j hj
  · rw [hmem, Mem.readW_writeW_self64]

/-- `withStackArgScratch` writes `sp` only in its frame (no AArch64
instruction writes it). -/
theorem withStackArgScratch_spSafe (bytes m : Nat) (c : Prog isa) :
    (withStackArgScratch bytes m c).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _


/-! ## The run from `narrowS` -/

theorem State.withRegions_of_eq {u : State} {rd wr : List Region} (h₁ : u.rd = rd)
    (h₂ : u.wr = wr) : u.withRegions rd wr = u := by
  subst h₁ h₂; rfl

/-- `p - b + d` is `p - (b - d)`, for `d ≤ b`. -/
theorem sub_add_ofNat (p : Addr) {b d : Nat} (h : d ≤ b) :
    p - BitVec.ofNat 64 b + BitVec.ofNat 64 d = p - BitVec.ofNat 64 (b - d) := by
  rw [Offset.sub_ofNat_eq p (show b - d ≤ b by omega), Nat.sub_sub_self h]

/-- The sizes `withStackArgScratch` needs: the frame, one `alloc` can open,
holds the copies of the `m` stack arguments, the buffer's address and the
buffer. -/
abbrev ArgFits (m bytes : Nat) (e : Elem) (n : Nat) : Prop :=
  bufOff m + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 16 = 0

/-- The regions of the contract with the buffer, from the state after
`setArgs`: the buffers, the buffer, and the copied stack arguments. -/
def oldRegions (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (allArgs sig s) ++
    [(⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (bufOff (nStack sig)), n * e.size⟩, true),
      (⟨s.sp - BitVec.ofNat 64 bytes, 8 * (nStack sig + 1)⟩, false)]

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the frame's allocation and `setArgs`, which may
read and write what the contract with the buffer lets it. -/
def narrowS (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (setArgsState bytes (nStack sig) (allocated bytes s)).withRegions
    (((oldRegions sig e n bytes s).filter (!·.2)).map (·.1))
    (((oldRegions sig e n bytes s).filter (·.2)).map (·.1))

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What `setArgs` gives, from a state satisfying the contract without the
buffer. -/
theorem argsState_run {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hA : ArgsOk sig) (hb : ArgFits (nStack sig) bytes e n) (hl : Sig.noLists sig.params = true) :
    execBlock isa (setArgs bytes (nStack sig)) (allocated bytes s) =
        some (setArgsState bytes (nStack sig) (allocated bytes s),
          setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) (nStack sig)) ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, 8 * (nStack sig + 1)⟩] s.mem
        (setArgsState bytes (nStack sig) (allocated bytes s)).mem ∧
      (∀ j < nStack sig,
        stackArg (setArgsState bytes (nStack sig) (allocated bytes s)) j = stackArg s j) ∧
      stackArg (setArgsState bytes (nStack sig) (allocated bytes s)) (nStack sig) =
        s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (bufOff (nStack sig)) := by
  obtain ⟨hb0, hb1, hb2⟩ := hb
  have hbo := bufOff_bounds (nStack sig)
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  have hsp : (allocated bytes s).sp = s.sp - BitVec.ofNat 64 bytes := rfl
  have hsrc : ∀ j, (allocated bytes s).sp + BitVec.ofNat 64 (bytes + 8 * j) = stackArgAddr s j :=
    fun j => by
      rw [hsp, stackArgAddr, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  -- The caller's stack arguments hold the sources.
  have hargs : ∀ j < nStack sig,
      InRegions ((allocated bytes s).rd ++ (allocated bytes s).wr) (stackArgAddr s j) 8 :=
    fun j hj => by
      have h0 : nStack sig ≠ 0 := by omega
      have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
        simp [allRegions, argArea, h0]
      have hc : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region).Contains (stackArgAddr s j) 8 := by
        simp only [stackArgAddr]
        exact Offset.contains _ (d := 8 * j) (n := 8) (e := 8 * 0) (k := 8 * nStack sig)
          (by omega) (by omega) (by omega)
      refine ⟨_, List.mem_append_left _ ?_, hc⟩
      show _ ∈ s.rd
      rw [hrd]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j ≤ nStack sig,
      InRegions (allocated bytes s).wr ((allocated bytes s).sp + BitVec.ofNat 64 (8 * j)) 8 :=
    fun j hj => ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨hrun, hf, hv, hlast⟩ := setArgs_run (bytes := bytes) (m := nStack sig)
    (u := allocated bytes s) (by omega) hb1 (by omega) (fun j hj => by rw [hsrc]; exact hargs j hj)
    hframe
  refine ⟨hrun, hf, fun j hj => ?_, ?_⟩
  · show (setArgsState bytes (nStack sig) (allocated bytes s)).mem.readW
      ((setArgsState bytes (nStack sig) (allocated bytes s)).sp + BitVec.ofNat 64 (8 * j)) 64 = _
    rw [setArgsState_sp, hv j hj, hsrc]
    rfl
  · show (setArgsState bytes (nStack sig) (allocated bytes s)).mem.readW
      ((setArgsState bytes (nStack sig) (allocated bytes s)).sp +
        BitVec.ofNat 64 (8 * nStack sig)) 64 = _
    rw [setArgsState_sp, hlast]
    rfl

/-- What `narrowS` keeps of `s`, and what it holds. -/
theorem narrowS_facts (hA : ArgsOk sig) (hk : 8 ≤ (sig.words abi.ptrBits).length)
    (hb : ArgFits (nStack sig) bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    (narrowS sig e n bytes s).sp = s.sp - BitVec.ofNat 64 bytes ∧
      (∀ q, q ≠ .x16 → q ≠ .x17 → (narrowS sig e n bytes s).gpr q = s.gpr q) ∧
      (narrowS sig e n bytes s).v = s.v ∧
      allArgs (sig.withScratch nm e n) (narrowS sig e n bytes s) =
        allArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (bufOff (nStack sig))] ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, 8 * (nStack sig + 1)⟩] s.mem
        (narrowS sig e n bytes s).mem := by
  obtain ⟨-, hf, hargs, hlast⟩ := argsState_run hs hA hb hl
  have hg : ∀ q, q ≠ .x16 → q ≠ .x17 → (narrowS sig e n bytes s).gpr q = s.gpr q :=
    fun q h₁ h₂ => setArgsState_gpr _ _ _ h₁ h₂
  have hR : ∀ r ∈ argRegs, r ≠ .x16 ∧ r ≠ .x17 := by decide
  refine ⟨setArgsState_sp _ _ _, hg, setArgsState_v _ _ _, ?_, hf⟩
  rw [allArgs_withScratch sig nm e n hk s _ (fun r hr => hg r (hR r hr).1 (hR r hr).2) hargs]
  exact congrArg (fun x => allArgs sig s ++ [x]) hlast

/-- The regions of the contract with the buffer, in `narrowS`, are
`oldRegions`. -/
theorem allRegions_narrowS (hA : ArgsOk sig) (hk : 8 ≤ (sig.words abi.ptrBits).length)
    (hb : ArgFits (nStack sig) bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    allRegions (sig.withScratch nm e n) (narrowS sig e n bytes s) = oldRegions sig e n bytes s := by
  obtain ⟨hsp, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hA hk hb hs hl
  have hlen := allArgs_length sig s
  rw [allRegions, hargs, argArea, nStack_withScratch sig nm e n hk,
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, oldRegions, List.append_assoc, List.cons_append,
    List.nil_append, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]

/-- The precondition of the contract without the buffer gives the one with it
in `narrowS`, if the precondition reads memory only within the buffers. -/
theorem narrowS_pre (hA : ArgsOk sig) (hk : 8 ≤ (sig.words abi.ptrBits).length)
    (hb : ArgFits (nStack sig) bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre (narrowS sig e n bytes s) := by
  obtain ⟨hrsp, -, -, hargs, hf⟩ := narrowS_facts (nm := nm) hA hk hb hs hl
  have hall := allRegions_narrowS (nm := nm) hA hk hb hs hl
  have hbo := bufOff_bounds (nStack sig)
  obtain ⟨hb0, -, -⟩ := hb
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  have hlt := s.sp.isLt
  have hlen := allArgs_length sig s
  have hscr : s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (bufOff (nStack sig)) =
      s.sp - BitVec.ofNat 64 (bytes - bufOff (nStack sig)) := sub_add_ofNat _ (by omega)
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega)]; simp
  -- The buffers lie outside the frame.
  have hout : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (Offset.sub_below _ hx hk)
  refine (pre_args (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (leak := leak.map (Curry.withScratch abi.ptrBits nm e n sig.params))
    (argsOk_withScratch nm e n hk hA) (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [hall, hrsp, hargs, nStack_withScratch sig nm e n hk]
  refine ⟨⟨.inr ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat' (by omega)]; omega
  · rw [toNat_sub_ofNat' (by omega)]; omega
  · -- Pairwise disjoint.
    simp only [oldRegions]
    rw [List.pairwise_append]
    refine ⟨List.Pairwise.sublist (List.sublist_append_left _ _) hpw, ?_, fun a ha b hb _ => ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        List.Pairwise.nil, and_true, Bool.true_or, forall_const]
      refine ⟨Region.Disjoint.symm ?_, fun _ h => h.elim⟩
      exact Offset.base_disjoint _ (e := bufOff (nStack sig)) (n := n * e.size)
        (k := 8 * (nStack sig + 1)) (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [hscr]; exact hout a ha (by omega) (by omega)
      · exact hout a ha (by omega) (by omega)
  · -- The reserved stack, below the frame.
    intro r hr a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hr
    rw [stackBelow_pos _ h0, List.mem_singleton] at hr; subst hr
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact (Region.Disjoint.symm (hout a ha (x := stack + bytes) (k := stack + bytes)
        (by omega) (by omega))).sub_left (below_below _ bytes stack)
    · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := bufOff (nStack sig))
        (k := n * e.size) (by omega))
    · exact Region.Disjoint.symm (Offset.base_disjoint_below _ (n := stack)
        (k := 8 * (nStack sig + 1)) (by omega))
  · -- No buffer wraps around.
    intro a ha
    rw [show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (bufOff (nStack sig))).toNat +
        n * e.size ≤ 2 ^ 64
      rw [hscr, toNat_sub_ofNat' (by omega)]
      omega
  · -- The precondition, which reads only the buffers.
    refine Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_
    refine hpre _ _ _ hlen (fun b hb x hx => (hf x fun r hr hc => ?_).symm) hpr
    simp only [List.mem_singleton] at hr; subst hr
    exact hout b hb (x := bytes) (k := 8 * (nStack sig + 1)) (by omega) (by omega) x hx hc

/-- The buffers lie outside the frame: `narrowS`'s memory is `s`'s there. -/
theorem narrowS_agree (hA : ArgsOk sig) (hk : 8 ≤ (sig.words abi.ptrBits).length)
    (hb : ArgFits (nStack sig) bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    ∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ x, b.1.Contains x 1 →
      (narrowS sig e n bytes s).mem x = s.mem x := by
  obtain ⟨-, -, -, -, hf⟩ := narrowS_facts (nm := "") hA hk hb hs hl
  have hbo := bufOff_bounds (nStack sig)
  obtain ⟨hb0, -, -⟩ := hb
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega)]; simp
  intro b hb x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb))).sub_right
    (Offset.sub_below _ (a := bytes) (n := 8 * (nStack sig + 1)) (by omega) (by omega)) x hx hc

/-- The public data of the contract without the buffer, and what it may leak,
are public in `narrowS` for the contract with it, if the leak reads memory
only within the buffers. -/
theorem narrowS_pub (hA : ArgsOk sig) (hk : 8 ≤ (sig.words abi.ptrBits).length)
    (hb : ArgFits (nStack sig) bytes e n) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hl : Sig.noLists sig.params = true)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrowS sig e n bytes s₁)
      (narrowS sig e n bytes s₂) := by
  rw [pub_args hA hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  obtain ⟨e₁, -, -, a₁, -⟩ := narrowS_facts (nm := nm) hA hk hb h₁ hl
  obtain ⟨e₂, -, -, a₂, -⟩ := narrowS_facts (nm := nm) hA hk hb h₂ hl
  have l₁ := allArgs_length sig s₁
  have l₂ := allArgs_length sig s₂
  refine (pub_args (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (leak := leak.map (Curry.withScratch abi.ptrBits nm e n sig.params))
    (argsOk_withScratch nm e n hk hA) (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [e₁, e₂, a₁, a₂, hsp]
  refine ⟨⟨rfl, leakAgree_withScratch hleak _ _ l₁ l₂ (narrowS_agree hA hk hb h₁ hl)
    (narrowS_agree hA hk hb h₂ hl) hlk⟩, fun i hi => ?_⟩
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have hps : ((sig.withScratch nm e n).params.flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Sig.withScratch, Param.pubs]
  rw [hps] at hi
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
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), l₁, l₂]

/-- A run of the code from `narrowS s` is a run of `withStackArgScratch`
from `s`, after `setArgs`'s accesses, which keeps what the calling convention
requires, and whose memory and registers are those of the code's run. -/
theorem withStackArgScratch_run {c : Prog isa} (hA : ArgsOk sig)
    (hk : 8 ≤ (sig.words abi.ptrBits).length) (hb : ArgFits (nStack sig) bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowS sig e n bytes s) t s₃)
    (ha : abiPreserved (narrowS sig e n bytes s) s₃) (hl : Sig.noLists sig.params = true) :
    Exec isa (withStackArgScratch bytes (nStack sig) c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) (nStack sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hrun, -, -, -⟩ := argsState_run hs hA hb hl
  obtain ⟨hrsp, hg, hv, -, -⟩ := narrowS_facts (nm := "") hA hk hb hs hl
  have hbo := bufOff_bounds (nStack sig)
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, -⟩, hrd, hwr, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  have hpos : 0 < bytes := by omega
  -- The frame's allocation.
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨hpos, hb1, hb2, by omega⟩
  -- The regions of `narrowS`: the buffers, and the frame's buffer and copies.
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd :=
    fun a ha h => by
      rw [hrd]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr :=
    fun a ha h => by
      rw [hwr]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes s).filter (·.2)).map (·.1))
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · exact Covers.one ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · simp at hf'
  have hcovR : Covers (((oldRegions sig e n bytes s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (Covers.one ⟨_, List.mem_cons_self .., Region.contains_self' (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowS sig e n bytes s).withRegions s.rd
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      setArgsState bytes (nStack sig) (allocated bytes s) by
    rw [narrowS, State.withRegions_withRegions]
    exact State.withRegions_of_eq (setArgsState_rd bytes (nStack sig) (allocated bytes s))
      (setArgsState_wr bytes (nStack sig) (allocated bytes s))] at hw
  -- The frame's release.
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans hrsp
  have hpop : isa.pop (.free bytes) (allocated bytes s)
      (s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions, allocated, hsp₃, List.head?_cons, List.tail_cons, hpos,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  have hP : ∀ q ∈ preserved, q ≠ .x16 ∧ q ≠ .x17 := by decide
  refine ⟨hex, ⟨fun q hq => ?_, rfl, fun q hq => ?_⟩, rfl, rfl⟩
  · show s₃.gpr q = s.gpr q
    rw [ha.1 q hq]
    exact hg q (hP q hq).1 (hP q hq).2
  · show (s₃.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64
    rw [ha.2.2 q hq, hv]

/-- Code verified for a function whose last argument, a scratch buffer of `n`
elements `e`, is passed on the stack after the eight argument registers and
`nStack sig` other stack arguments, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackArgScratch`), if its precondition,
postcondition and leak read memory only within the function's buffers
(`hpre`, `hpost`, `hleak`, which holds of no leak). -/
theorem Verified.stackArgScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 8 ≤ (sig.words abi.ptrBits).length) (hb : ArgFits (nStack sig) bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackArgScratch bytes (nStack sig) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hA : ArgsOk sig := let ⟨_, hs⟩ := hsat; argsOk_of_pre hs
  -- Every run is `setArgs`, then the code's run from `narrowS`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowS sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrowS sig e n bytes s) s₃ ∧
      Exec isa (withStackArgScratch bytes (nStack sig) c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) (nStack sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowS_pre hA hk hb hpre hs hl)
    exact ⟨t, s₃, he, hq, withStackArgScratch_run hA hk hb hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hA]
    have hq' := (post_args (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (leak := leak.map (Curry.withScratch abi.ptrBits nm e n sig.params))
      (argsOk_withScratch nm e n hk hA)).mp hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hA hk hb hs hl
    rw [hargs] at hq'
    rw [hm, hg]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (allArgs_length sig s)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (allArgs_length sig s) (narrowS_agree hA hk hb hs hl) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pub_args hA hl).mp hp).1.1,
      hct _ _ _ _ _ _ (narrowS_pre hA hk hb hpre h₁ hl) (narrowS_pre hA hk hb hpre h₂ hl)
        (narrowS_pub hA hk hb h₁ h₂ hp hl hleak) f₁ f₂]

end

end VG.AArch64
