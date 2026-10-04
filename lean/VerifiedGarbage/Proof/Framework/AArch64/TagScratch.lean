import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TagScratch

/-!
# A tag passed through a buffer on the stack (AArch64)

`Verified.tagScratch`: code verified for a function one of whose parameters,
`q`, is a buffer of working space whose first 16 bytes also carry a tag in or
out (`Sig.tagWork`), runs as a function whose parameter there is a pointer to
the 16-byte tag alone, when `withTagScratch` allocates the buffer in a frame
on the stack, with `bytes` more bytes of stack. The tag pointer may be in an
argument register or on the stack. The frame holds what the code expects at
and above `sp` on entry (a copy of the stack arguments: the return address is
in `x30`), then the tag pointer and the buffer. Before the code, the frame
copies the tag into the buffer and passes the buffer in the tag pointer's
place (`tagSetup`); after it, it copies the buffer's first 16 bytes back to
the tag (`tagOut`). The code runs from the state after `tagSetup`, with the
permissions of its contract (`narrowT`), and its run there is its run from
that state (`Exec.widen`).

The two contracts are related by `Sig.TagFrame`: the inner contract's
precondition, postcondition and leakage, on the arguments with the buffer in
the tag pointer's place, follow from or give the outer ones', for memory that
agrees on the function's other buffers and holds the tag in the buffer
(`TagIn`) and, on return, holds the buffer's first 16 bytes in the tag and is
otherwise the code's (`TagOut`).
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

/-- What a contract's `leak` says of the values and memory of two runs:
nothing, if it has none. -/
def leakAgree {ws : List ArgWord} : Option (Curry ws (Mem → List Nat)) → List (BitVec 64) → Mem →
    List (BitVec 64) → Mem → Prop
  | none, _, _, _, _ => True
  | some f, vs₁, m₁, vs₂, m₂ => Curry.apply ws f vs₁ m₁ = Curry.apply ws f vs₂ m₂

/-- The public data of a contract. -/
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

/-! ## Instructions -/

theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addSp d imm) s = some (s.write .x d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true]

theorem exec_ldrSp {s : State} {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.ldrSp t off) s = some (s.write .x t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, ho, and_self, ite_true, State.load, h, Option.map_some, Mem.readW]

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, and_self, ite_true, Option.bind_some, State.load, h, Option.map_some]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, ho, and_self, ite_true, Option.bind_some, State.store, h]

theorem execBlock_cons_of {i : Instr} {is : List Instr} {s s₁ : State} (h : exec i s = some s₁) :
    execBlock isa (i :: is) s =
      (execBlock isa is s₁).map fun p => (p.1, (addrs i s).map Leak.addr ++ p.2) := by
  simp only [execBlock, isa, h]

/-- Byte `i` of a copied 16 bytes. -/
theorem Mem.write_read_apply (m₀ m : Mem) (w t : Addr) {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (m.write w n (m₀.read t n)) (w + BitVec.ofNat 64 i) = m₀ (t + BitVec.ofNat 64 i) := by
  simp only [Mem.write, Mem.sub_ofNat_toNat w (show i < 2 ^ 64 by omega), hi, ite_true]
  exact Mem.extractLsb'_read m₀ t hi

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

/-! ## The tag -/

/-- The tag pointer where `a` says, from the state after the frame's push of
`bytes`: in its register, or in the caller's stack argument. -/
def tagPtr (bytes : Nat) (a : TagArg) (u : State) : Addr :=
  match a with
  | .reg r => u.gpr r
  | .stack j => u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64

/-- The addresses `loadTagPtr bytes a` accesses, from `sp = p`. -/
def loadTrace (bytes : Nat) (a : TagArg) (p : Addr) : List Leak :=
  match a with
  | .reg _ => []
  | .stack j => [.addr (p + BitVec.ofNat 64 (bytes + 8 * j))]

/-- Where the tag pointer may be: a register `tagSetup` does not use, or one
of the `m` stack arguments. -/
def tagArgOk (m : Nat) : TagArg → Prop
  | .reg r => r ≠ .x16 ∧ r ≠ .x17
  | .stack j => j < m

theorem loadTagPtr_run {bytes m : Nat} {a : TagArg} {w : State} (ha : tagArgOk m a)
    (ho : bytes % 8 = 0 ∧ bytes + 8 * m < 32768)
    (hr : ∀ j < m, InRegions (w.rd ++ w.wr) (w.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8) :
    ∃ w', execBlock isa (loadTagPtr bytes a) w = some (w', loadTrace bytes a w.sp) ∧
      w'.sp = w.sp ∧ w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.v = w.v ∧ w'.mem = w.mem ∧
      (∀ r, r ≠ .x17 → w'.gpr r = w.gpr r) ∧ w'.gpr (tagReg a) = tagPtr bytes a w := by
  cases a with
  | reg r => exact ⟨w, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩
  | stack j =>
    have hj : j < m := ha
    refine ⟨w.write .x .x17 (w.mem.readW (w.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64), ?_, rfl, rfl,
      rfl, rfl, rfl, fun r h => RegUpd.gpr_write_of_ne w .x _ h, ?_⟩
    · rw [loadTagPtr, execBlock_cons_of (exec_ldrSp ⟨by omega, by omega⟩ (hr j hj))]
      rfl
    · rw [tagReg, RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _

/-- The memory after `tagIn m`, from memory `M` with `x16 = p` and the tag
pointer `t`. -/
def tagInMem (m : Nat) (M : Mem) (p t : Addr) : Mem :=
  let M₁ := M.writeW (p + BitVec.ofNat 64 (8 * m)) t
  M₁.write (p + BitVec.ofNat 64 (16 * (m / 2 + 1))) 16 (M₁.read (t + BitVec.ofNat 64 0) 16)

theorem tagIn_run {m : Nat} {r : Reg} {w : State} (hm : 16 * (m / 2 + 1) < 4096)
    (h₁ : InRegions w.wr (w.gpr .x16 + BitVec.ofNat 64 (8 * m)) 8)
    (h₂ : InRegions (w.rd ++ w.wr) (w.gpr r + BitVec.ofNat 64 0) 16)
    (h₃ : InRegions w.wr (w.gpr .x16 + BitVec.ofNat 64 (16 * (m / 2 + 1))) 16) :
    ∃ w', execBlock isa (tagIn m r) w = some (w',
        [.addr (w.gpr .x16 + BitVec.ofNat 64 (8 * m)), .addr (w.gpr r + BitVec.ofNat 64 0),
          .addr (w.gpr .x16 + BitVec.ofNat 64 (16 * (m / 2 + 1)))]) ∧
      w'.sp = w.sp ∧ w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.gpr = w.gpr ∧
      (∀ q, q ≠ .v16 → w'.v q = w.v q) ∧ w'.mem = tagInMem m w.mem (w.gpr .x16) (w.gpr r) := by
  have e₁ := exec_str_x (s := w) (t := r) ⟨by omega, by omega⟩ h₁
  have e₂ := exec_ldrq (s := { w with mem := w.mem.writeW (w.gpr .x16 + BitVec.ofNat 64 (8 * m)) (w.gpr r) })
    (t := .v16) ⟨by omega, by omega⟩ h₂
  have e₃ := exec_strq (s := ({ w with mem := w.mem.writeW (w.gpr .x16 + BitVec.ofNat 64 (8 * m)) (w.gpr r) } :
      State).setV .v16 ((w.mem.writeW (w.gpr .x16 + BitVec.ofNat 64 (8 * m)) (w.gpr r)).read
        (w.gpr r + BitVec.ofNat 64 0) 16)) (t := .v16) ⟨by omega, by omega⟩ h₃
  rw [tagIn, execBlock_cons_of e₁, execBlock_cons_of e₂, execBlock_cons_of e₃]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, fun q hq => RegUpd.v_setV_of_ne _ _ hq, rfl⟩

/-- A doubleword read outside a write. -/
theorem readW_write_sep {m : Mem} {a b : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : Mem.Sep a 8 b n) : (m.write b n v).readW a 64 = m.readW a 64 := by
  simp only [Mem.readW]
  exact congrArg _ (Mem.read_write_sep (n := 64 / 8) h (by decide))

/-- What `tagIn` leaves in memory, if the tag lies outside the saved
pointer: the pointer, and the tag's bytes in the buffer, having written only
the frame up to the buffer's first 16 bytes. -/
theorem tagInMem_facts {m : Nat} {M : Mem} {p t : Addr} (hm : 16 * (m / 2 + 1) + 16 < 2 ^ 64)
    (hd : (⟨t, 16⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 (8 * m), 8⟩) :
    Frame [⟨p + BitVec.ofNat 64 (8 * m), 16 * (m / 2 + 1) + 16 - 8 * m⟩] M (tagInMem m M p t) ∧
      (tagInMem m M p t).readW (p + BitVec.ofNat 64 (8 * m)) 64 = t ∧
      ∀ i < 16, tagInMem m M p t (p + BitVec.ofNat 64 (16 * (m / 2 + 1)) + BitVec.ofNat 64 i) =
        M (t + BitVec.ofNat 64 i) := by
  have hz : t + BitVec.ofNat 64 0 = t := BitVec.add_zero t
  have f₁ : Frame [⟨p + BitVec.ofNat 64 (8 * m), 16 * (m / 2 + 1) + 16 - 8 * m⟩] M
      (M.writeW (p + BitVec.ofNat 64 (8 * m)) t) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains p (d := 8 * m) (n := 64 / 8) (by omega) (by omega) (by omega))
  have ht : ∀ i < 16, (M.writeW (p + BitVec.ofNat 64 (8 * m)) t) (t + BitVec.ofNat 64 i) =
      M (t + BitVec.ofNat 64 i) := fun i hi =>
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) t (Region.contains_self _ _)).bytes
      (R := ⟨t, 16⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
      (show 16 ≤ 2 ^ 64 by decide) hi
  have hs : (M.writeW (p + BitVec.ofNat 64 (8 * m)) t).readW (p + BitVec.ofNat 64 (8 * m)) 64 = t :=
    Mem.readW_writeW_self64 _ _ _
  simp only [tagInMem, hz]
  generalize M.writeW (p + BitVec.ofNat 64 (8 * m)) t = M₁ at f₁ ht hs
  refine ⟨f₁.write (List.mem_singleton_self _) _
      (Offset.contains p (d := 16 * (m / 2 + 1)) (n := 16) (by omega) (by omega) (by omega)), ?_,
    fun i hi => ?_⟩
  · rw [readW_write_sep (Offset.sep p (.inl (by omega)) (by omega) (by omega)), hs]
  · rw [Mem.write_read_apply _ _ _ _ hi (by decide), ht i hi]

/-- The addresses `pointTag m a` accesses, from `sp = p`. -/
def pointTrace (a : TagArg) (p : Addr) : List Leak :=
  match a with
  | .reg _ => []
  | .stack j => [.addr (p + BitVec.ofNat 64 (8 * j))]

/-- `pointTag`, for either place, from a state whose `x16` is `sp`. -/
theorem pointTag_run {m : Nat} {a : TagArg} {w : State} (hm : 16 * (m / 2 + 1) < 4096)
    (ha : tagArgOk m a) (h16 : w.gpr .x16 = w.sp)
    (hF : ∀ j < m, InRegions w.wr (w.sp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ w', execBlock isa (pointTag m a) w = some (w', pointTrace a w.sp) ∧
      w'.sp = w.sp ∧ w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.v = w.v ∧
      (∀ r, r ≠ .x17 → w'.gpr r =
        if a = .reg r then w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) else w.gpr r) ∧
      Frame [⟨w.sp, 8 * m⟩] w.mem w'.mem ∧
      (∀ j < m, w'.mem.readW (w.sp + BitVec.ofNat 64 (8 * j)) 64 =
        if a = .stack j then w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1))
        else w.mem.readW (w.sp + BitVec.ofNat 64 (8 * j)) 64) := by
  cases a with
  | reg r =>
    refine ⟨w.write .x r (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1))), ?_, rfl, rfl, rfl, rfl,
      fun q _ => ?_, Frame.refl _ _, fun j _ => ?_⟩
    · rw [pointTag, execBlock_cons_of (exec_addSp hm)]; rfl
    · rw [RegUpd.gpr_write]
      by_cases hq : q = r
      · subst hq; simp only [↓reduceIte]; exact BitVec.setWidth_eq _
      · simp only [hq, ↓reduceIte, TagArg.reg.injEq, show ¬ r = q from fun h => hq h.symm]
    · simp only [reduceCtorEq, ↓reduceIte]; rfl
  | stack j₀ =>
    have hj₀ : j₀ < m := ha
    have e₁ := exec_addSp (s := w) (d := .x17) hm
    have g₁₆ : (w.write .x .x17 (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)))).gpr .x16 = w.sp := by
      rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), h16]
    have g₁₇ : (w.write .x .x17 (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)))).gpr .x17 =
        w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) := by
      rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _
    have e₂ := exec_str_x (s := w.write .x .x17 (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1))))
      (t := .x17) (n := .x16) (off := 8 * j₀) ⟨by omega, by omega⟩ (by rw [g₁₆]; exact hF j₀ hj₀)
    rw [g₁₆, g₁₇] at e₂
    refine ⟨{ w.write .x .x17 (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1))) with
        mem := w.mem.writeW (w.sp + BitVec.ofNat 64 (8 * j₀)) (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1))) },
      ?_, rfl, rfl, rfl, rfl, fun q hq => ?_, ?_, fun j hj => ?_⟩
    · rw [pointTag, execBlock_cons_of e₁, execBlock_cons_of e₂]
      simp only [execBlock, Option.map_some, addrs, List.map_cons, List.map_nil, List.nil_append, g₁₆]
      rfl
    · show (w.write .x .x17 _).gpr q = _
      rw [RegUpd.gpr_write_of_ne _ _ _ hq]
      simp only [reduceCtorEq, ↓reduceIte]
    · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base w.sp (d := 8 * j₀) (n := 64 / 8) (k := 8 * m) (by omega) (by omega))
    · show (w.mem.writeW _ _).readW _ 64 = _
      by_cases hjj : j = j₀
      · subst hjj; rw [Mem.readW_writeW_self64]; simp
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        simp only [TagArg.stack.injEq, show ¬ j₀ = j from fun h => hjj h.symm, ↓reduceIte]

/-- The addresses `tagSetup bytes m a` accesses, from `sp = p`, for the tag
at `t`. -/
def tagSetupTrace (bytes m : Nat) (a : TagArg) (p t : Addr) : List Leak :=
  copyTrace bytes p m ++ loadTrace bytes a p ++
    [.addr (p + BitVec.ofNat 64 (8 * m)), .addr (t + BitVec.ofNat 64 0),
      .addr (p + BitVec.ofNat 64 (16 * (m / 2 + 1)))] ++ pointTrace a p

/-- The state after `tagSetup bytes m a` from `u`, if it runs. -/
def tagSetupState (bytes m : Nat) (a : TagArg) (u : State) : State :=
  ((execBlock isa (tagSetup bytes m a) u).map Prod.fst).getD u

/-- `tagSetup`, from the state after the frame's push (`u`, whose `sp` is the
frame's base): the stack arguments copied into the frame, the tag pointer
saved after them and the tag copied to the buffer after that, and the
buffer's address in the tag pointer's place; nothing else written, and only
`x16`, `x17`, `v16` and the tag pointer's register changed. -/
theorem tagSetup_run {bytes m : Nat} {a : TagArg} {u : State}
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (m / 2 + 1) + 16 ≤ bytes)
    (hF : (⟨u.sp, bytes⟩ : Region) ∈ u.wr)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 8)
    (ha : tagArgOk m a)
    (htw : (⟨tagPtr bytes a u, 16⟩ : Region) ∈ u.wr)
    (htd : (⟨tagPtr bytes a u, 16⟩ : Region).Disjoint ⟨u.sp, bytes⟩) :
    execBlock isa (tagSetup bytes m a) u =
        some (tagSetupState bytes m a u, tagSetupTrace bytes m a u.sp (tagPtr bytes a u)) ∧
      (tagSetupState bytes m a u).sp = u.sp ∧
      (tagSetupState bytes m a u).rd = u.rd ∧ (tagSetupState bytes m a u).wr = u.wr ∧
      (∀ q, q ≠ .v16 → (tagSetupState bytes m a u).v q = u.v q) ∧
      (∀ r, r ≠ .x16 → r ≠ .x17 → (tagSetupState bytes m a u).gpr r =
        if a = .reg r then u.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) else u.gpr r) ∧
      Frame [⟨u.sp, 16 * (m / 2 + 1) + 16⟩] u.mem (tagSetupState bytes m a u).mem ∧
      (∀ j < m, (tagSetupState bytes m a u).mem.readW (u.sp + BitVec.ofNat 64 (8 * j)) 64 =
        if a = .stack j then u.sp + BitVec.ofNat 64 (16 * (m / 2 + 1))
        else u.mem.readW (u.sp + BitVec.ofNat 64 (bytes + 8 * j)) 64) ∧
      (tagSetupState bytes m a u).mem.readW (u.sp + BitVec.ofNat 64 (8 * m)) 64 =
        tagPtr bytes a u ∧
      ∀ i < 16, (tagSetupState bytes m a u).mem
          (u.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) + BitVec.ofNat 64 i) =
        u.mem (tagPtr bytes a u + BitVec.ofNat 64 i) := by
  obtain ⟨hb16, hb1, hb2⟩ := hb
  have hc8 : ∀ {d k : Nat}, d + k ≤ bytes → InRegions u.wr (u.sp + BitVec.ofNat 64 d) k :=
    fun h => ⟨_, hF, Offset.contains_base _ h (by omega)⟩
  -- `x16 := sp`.
  have e₀ := exec_addSp (s := u) (d := .x16) (imm := 0) (by decide)
  have h0 : u.sp + BitVec.ofNat 64 0 = u.sp := BitVec.add_zero _
  rw [h0] at e₀
  have h16₀ : (u.write .x .x16 u.sp).gpr .x16 = u.sp := by
    rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _
  have g₀ : ∀ r, r ≠ .x16 → (u.write .x .x16 u.sp).gpr r = u.gpr r :=
    fun r h => RegUpd.gpr_write_of_ne _ _ _ h
  generalize hw₀ : u.write .x .x16 u.sp = w₀ at e₀ h16₀ g₀
  have sp₀ : w₀.sp = u.sp := by rw [← hw₀]; rfl
  have rd₀ : w₀.rd = u.rd := by rw [← hw₀]; rfl
  have wr₀ : w₀.wr = u.wr := by rw [← hw₀]; rfl
  have v₀ : w₀.v = u.v := by rw [← hw₀]; rfl
  have mem₀ : w₀.mem = u.mem := by rw [← hw₀]; rfl
  -- The copies.
  have hcp := copies_run (bytes := bytes) (w := w₀) (h16₀.trans sp₀.symm) (by omega) m (by omega)
    (fun j hj => by rw [rd₀, wr₀, sp₀]; exact hr j hj)
    (fun j hj => by rw [wr₀, sp₀]; exact hc8 (by omega))
  obtain ⟨f₁, hv₁⟩ := copiedState_mem (bytes := bytes) (w := w₀) (h16₀.trans sp₀.symm) m
    (by omega) (by omega)
  rw [sp₀, mem₀] at f₁ hv₁
  rw [sp₀] at hcp
  have sp₁ := (copiedState_sp bytes w₀ m).trans sp₀
  have rd₁ := (copiedState_rd bytes w₀ m).trans rd₀
  have wr₁ := (copiedState_wr bytes w₀ m).trans wr₀
  have v₁ := (copiedState_v bytes w₀ m).trans v₀
  have g₁ : ∀ r, r ≠ .x17 → (copiedState bytes w₀ m).gpr r = w₀.gpr r :=
    fun r h => copiedState_gpr bytes w₀ h m
  generalize copiedState bytes w₀ m = w₁ at hcp f₁ hv₁ sp₁ rd₁ wr₁ v₁ g₁
  -- The tag pointer.
  obtain ⟨w₂, hld, sp₂, rd₂, wr₂, v₂, mem₂, g₂, ht₂⟩ := loadTagPtr_run (bytes := bytes) (w := w₁) ha
    ⟨by omega, by omega⟩ (fun j hj => by rw [rd₁, wr₁, sp₁]; exact hr j hj)
  rw [sp₁] at hld
  have ht : tagPtr bytes a w₁ = tagPtr bytes a u := by
    cases a with
    | reg r =>
      obtain ⟨o₁, o₂⟩ := ha
      show w₁.gpr r = u.gpr r
      rw [g₁ r o₂, g₀ r o₁]
    | stack j =>
      have hj : j < m := ha
      show w₁.mem.readW (w₁.sp + _) 64 = u.mem.readW (u.sp + _) 64
      rw [sp₁]
      exact f₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  rw [ht] at ht₂
  generalize tagPtr bytes a u = t at ht₂ htw htd ⊢
  -- Saving the pointer and copying the tag.
  have x16₂ : w₂.gpr .x16 = u.sp := by rw [g₂ _ (by decide), g₁ _ (by decide), h16₀]
  obtain ⟨w₃, hti, sp₃, rd₃, wr₃, g₃, v₃, mem₃⟩ := tagIn_run (m := m) (r := tagReg a) (w := w₂)
    (by omega) (by rw [x16₂, wr₂, wr₁]; exact hc8 (by omega))
    (by rw [ht₂, BitVec.add_zero, rd₂, wr₂, rd₁, wr₁]
        exact ⟨_, List.mem_append_right _ htw, Region.contains_self _ _⟩)
    (by rw [x16₂, wr₂, wr₁]; exact hc8 (by omega))
  rw [x16₂, ht₂] at hti mem₃
  obtain ⟨f₃, hslot, hW⟩ := tagInMem_facts (m := m) (M := w₂.mem) (p := u.sp) (t := t) (by omega)
    (htd.sub_right (Offset.sub_base _ (by omega)))
  rw [← mem₃] at f₃ hslot hW
  -- The tag lies outside the frame.
  have ht₁ : ∀ i < 16, w₂.mem (t + BitVec.ofNat 64 i) = u.mem (t + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [mem₂]
      exact f₁.bytes (R := ⟨t, 16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact htd.sub_right (Region.sub_prefix (by omega))) (show 16 ≤ 2 ^ 64 by decide) hi
  -- Passing the buffer.
  obtain ⟨w₄, hpt, sp₄, rd₄, wr₄, v₄, g₄, f₄, hv₄⟩ := pointTag_run (m := m) (a := a) (w := w₃)
    (by omega) ha (by rw [g₃, x16₂, sp₃, sp₂, sp₁])
    (fun j hj => by rw [wr₃, wr₂, wr₁, sp₃, sp₂, sp₁]; exact hc8 (by omega))
  rw [sp₃, sp₂, sp₁] at hpt g₄ f₄ hv₄
  have hrun : execBlock isa (tagSetup bytes m a) u = some (w₄, tagSetupTrace bytes m a u.sp t) := by
    rw [tagSetup, execBlock_append, execBlock_append, execBlock_append, execBlock_cons_of e₀, hcp]
    simp only [Option.map_some, Option.bind_some, hld, hti, hpt, tagSetupTrace, addrs,
      List.map_nil, List.nil_append, List.append_assoc]
  have hst : tagSetupState bytes m a u = w₄ := by simp [tagSetupState, hrun]
  rw [hst]
  refine ⟨hrun, by rw [sp₄, sp₃, sp₂, sp₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁], fun q hq => ?_, fun r h₁ h₂ => ?_, ?_, fun j hj => ?_, ?_,
    fun i hi => ?_⟩
  · rw [v₄, v₃ q hq, v₂, v₁]
  · rw [g₄ r h₂, g₃, g₂ r h₂, g₁ r h₂, g₀ r h₁]
  · refine (f₁.sub ?_).trans (((by rw [← mem₂]; exact f₃ : Frame _ w₁.mem w₃.mem).sub ?_).trans
      (f₄.sub ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  · rw [hv₄ j hj]
    split
    · rfl
    · rw [f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), mem₂, hv₁ j hj]
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · rw [f₄.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), hslot]
  · rw [f₄.bytes (R := ⟨u.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)), 16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (show 16 ≤ 2 ^ 64 by decide) hi,
      hW i hi, ht₁ i hi]

/-- The memory after `tagOut m`: the 16 bytes of the buffer, from `sp = p`,
copied to the tag at `t`. -/
def tagOutMem (m : Nat) (M : Mem) (p t : Addr) : Mem :=
  M.write (t + BitVec.ofNat 64 0) 16 (M.read (p + BitVec.ofNat 64 (16 * (m / 2 + 1)) + BitVec.ofNat 64 0) 16)

theorem tagOut_run {m : Nat} {w : State} (hm : 16 * (m / 2 + 1) < 4096)
    (h₁ : InRegions (w.rd ++ w.wr) (w.sp + BitVec.ofNat 64 (8 * m)) 8)
    (h₂ : InRegions (w.rd ++ w.wr) (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) + BitVec.ofNat 64 0) 16)
    (h₃ : InRegions w.wr (w.mem.readW (w.sp + BitVec.ofNat 64 (8 * m)) 64 + BitVec.ofNat 64 0) 16) :
    ∃ w', execBlock isa (tagOut m) w = some (w',
        [.addr (w.sp + BitVec.ofNat 64 (8 * m)),
          .addr (w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) + BitVec.ofNat 64 0),
          .addr (w.mem.readW (w.sp + BitVec.ofNat 64 (8 * m)) 64 + BitVec.ofNat 64 0)]) ∧
      w'.sp = w.sp ∧ w'.rd = w.rd ∧ w'.wr = w.wr ∧
      (∀ r, r ≠ .x16 → r ≠ .x17 → w'.gpr r = w.gpr r) ∧ (∀ q, q ≠ .v16 → w'.v q = w.v q) ∧
      w'.mem = tagOutMem m w.mem w.sp (w.mem.readW (w.sp + BitVec.ofNat 64 (8 * m)) 64) := by
  have e₁ := exec_ldrSp (s := w) (t := .x16) ⟨by omega, by omega⟩ h₁
  generalize hT : w.mem.readW (w.sp + BitVec.ofNat 64 (8 * m)) 64 = T at e₁ h₃ ⊢
  have e₂ := exec_addSp (s := w.write .x .x16 T) (d := .x17) (imm := 16 * (m / 2 + 1)) hm
  have g₁₇ : ((w.write .x .x16 T).write .x .x17 ((w.write .x .x16 T).sp +
      BitVec.ofNat 64 (16 * (m / 2 + 1)))).gpr .x17 = w.sp + BitVec.ofNat 64 (16 * (m / 2 + 1)) := by
    rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _
  have g₁₆ : ((w.write .x .x16 T).write .x .x17 ((w.write .x .x16 T).sp +
      BitVec.ofNat 64 (16 * (m / 2 + 1)))).gpr .x16 = T := by
    rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _
  have g₂ : ∀ r, r ≠ .x16 → r ≠ .x17 → ((w.write .x .x16 T).write .x .x17 ((w.write .x .x16 T).sp +
      BitVec.ofNat 64 (16 * (m / 2 + 1)))).gpr r = w.gpr r := fun r h₁ h₂ => by
    rw [RegUpd.gpr_write_of_ne _ _ _ h₂, RegUpd.gpr_write_of_ne _ _ _ h₁]
  generalize hw₂ : (w.write .x .x16 T).write .x .x17 ((w.write .x .x16 T).sp +
      BitVec.ofNat 64 (16 * (m / 2 + 1))) = w₂ at e₂ g₁₇ g₁₆ g₂
  have sp₂ : w₂.sp = w.sp := by rw [← hw₂]; rfl
  have rd₂ : w₂.rd = w.rd := by rw [← hw₂]; rfl
  have wr₂ : w₂.wr = w.wr := by rw [← hw₂]; rfl
  have mem₂ : w₂.mem = w.mem := by rw [← hw₂]; rfl
  have v₂ : w₂.v = w.v := by rw [← hw₂]; rfl
  have e₃ := exec_ldrq (s := w₂) (t := .v16) (n := .x17) (off := 0) ⟨by decide, by decide⟩
    (by rw [g₁₇, rd₂, wr₂]; exact h₂)
  have e₄ := exec_strq (s := w₂.setV .v16 (w₂.mem.read (w₂.gpr .x17 + BitVec.ofNat 64 0) 16))
    (t := .v16) (n := .x16) (off := 0) ⟨by decide, by decide⟩
    (by rw [RegUpd.gpr_setV, g₁₆, RegUpd.wr_setV, wr₂]; exact h₃)
  rw [tagOut, execBlock_cons_of e₁, execBlock_cons_of e₂, execBlock_cons_of e₃, execBlock_cons_of e₄]
  refine ⟨{ w₂.setV .v16 (w₂.mem.read (w₂.gpr .x17 + BitVec.ofNat 64 0) 16) with
      mem := w₂.mem.write (T + BitVec.ofNat 64 0) 16 (w₂.mem.read (w₂.gpr .x17 + BitVec.ofNat 64 0) 16) },
    ?_, sp₂, rd₂, wr₂, g₂, fun q hq => ?_, ?_⟩
  · simp only [execBlock, Option.map_some, addrs, isa, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, RegUpd.gpr_setV, g₁₆, g₁₇]
    rfl
  · show (w₂.setV .v16 _).v q = _
    rw [RegUpd.v_setV_of_ne _ _ hq, v₂]
  · show w₂.mem.write _ 16 _ = _
    rw [mem₂, g₁₇]
    rfl

/-- `tagOut`'s memory is the code's but for the tag, which holds the
buffer's first 16 bytes. -/
theorem tagOutMem_tagOut (m : Nat) (M : Mem) (p t : Addr) :
    TagOut t (p + BitVec.ofNat 64 (16 * (m / 2 + 1))) M (tagOutMem m M p t) := by
  have hz : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := BitVec.add_zero
  refine ⟨fun x hx => ?_, fun i hi => ?_⟩
  · simp only [tagOutMem, hz]
    exact Mem.write_apply fun h => hx (by simp only [Region.Contains]; omega)
  · simp only [tagOutMem, hz]
    exact Mem.write_read_apply _ _ _ _ hi (by decide)

/-! ## The state the code runs from -/

/-- Where argument word `k` of a function is passed: in an argument
register, or on the stack. -/
def tagArgAt (k : Nat) : TagArg := if k < 8 then .reg (argRegs.getD k .x0) else .stack (k - 8)

/-- The word of `sig`'s parameter `q`. -/
abbrev tagWord (sig : Sig) (q : Nat) : Nat := (Sig.psWords (sig.params.take q) abi.ptrBits).length

/-- The buffer's address, from the state `s` on entry. -/
abbrev tagBufAddr (sig : Sig) (bytes : Nat) (s : State) : Addr :=
  s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 * (nStack sig / 2 + 1))

/-- The copy of the stack arguments, read-only, if there are any. -/
def copyArea (sig : Sig) (bytes : Nat) (s : State) : List (Region × Bool) :=
  if nStack sig = 0 then [] else [(⟨s.sp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩, false)]

/-- The regions of the code's contract, from the state `s` on entry: the
buffers, with the working space in the tag's place, and the copy of the
stack arguments. -/
def innerRegions (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) :
    List (Region × Bool) :=
  Sig.bufs (sig.tagWork q nm e n).params
      ((allArgs sig s).set (tagWord sig q) (tagBufAddr sig bytes s)) ++
    copyArea sig bytes s

/-- The state the code runs from, with the permissions of its contract: the
state after the frame's push and `tagSetup`. -/
def narrowT (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).withRegions
    (((innerRegions sig q nm e n bytes s).filter (!·.2)).map (·.1))
    (((innerRegions sig q nm e n bytes s).filter (·.2)).map (·.1))

section
variable (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State)
theorem narrowT_gpr : (narrowT sig q nm e n bytes s).gpr =
    (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).gpr := rfl
theorem narrowT_mem : (narrowT sig q nm e n bytes s).mem =
    (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).mem := rfl
theorem narrowT_sp : (narrowT sig q nm e n bytes s).sp =
    (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).sp := rfl
theorem narrowT_v : (narrowT sig q nm e n bytes s).v =
    (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).v := rfl
end

theorem allArgs_getElem (sig : Sig) (s : State) {i : Nat} (h : i < (allArgs sig s).length) :
    (allArgs sig s)[i] = if i < 8 then s.gpr (argRegs.getD i .x0) else stackArg s (i - 8) := by
  have hL := allArgs_length sig s
  have hA : ((argRegs.take (sig.words abi.ptrBits).length).map s.gpr).length =
      min (sig.words abi.ptrBits).length 8 := by
    simp only [List.length_map, List.length_take, argRegs, List.length_cons, List.length_nil]
  by_cases hi : i < 8
  · simp only [allArgs, List.getElem_append, hA, show i < min (sig.words abi.ptrBits).length 8 by omega,
      dite_true, hi, ite_true, List.getElem_map, List.getElem_take]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < argRegs.length from hi)]
  · simp only [allArgs, List.getElem_append, hA, show ¬ i < min (sig.words abi.ptrBits).length 8 by omega,
      dite_false, hi, ite_false, List.getElem_map, List.getElem_range]
    congr 1
    omega

theorem argRegs_ok : ∀ k < 8, argRegs.getD k .x0 ≠ .x16 ∧ argRegs.getD k .x0 ≠ .x17 ∧
    argRegs.getD k .x0 ∉ preserved ∧ ∀ i < 8, argRegs.getD k .x0 = argRegs.getD i .x0 → k = i := by
  decide

theorem tagArgAt_ok {sig : Sig} {k : Nat} (hlt : k < (sig.words abi.ptrBits).length) :
    tagArgOk (nStack sig) (tagArgAt k) := by
  unfold tagArgAt
  split
  · next h => obtain ⟨h₁, h₂, -⟩ := argRegs_ok k h; exact ⟨h₁, h₂⟩
  · show k - 8 < nStack sig; simp only [nStack]; omega

/-- The tag pointer `tagSetup` reads is argument word `k`. -/
theorem tagPtr_alloc {sig : Sig} {bytes k : Nat} (hlt : k < (sig.words abi.ptrBits).length)
    (s : State) :
    tagPtr bytes (tagArgAt k) (allocated bytes s) = (allArgs sig s).getD k 0 := by
  have hl := allArgs_length sig s
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    allArgs_getElem]
  unfold tagArgAt
  split
  · rfl
  · next h =>
    show s.mem.readW (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (bytes + 8 * (k - 8))) 64 =
      s.mem.readW (stackArgAddr s (k - 8)) 64
    rw [stackArgAddr, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- `tagArgAt k` is no callee-saved register. -/
theorem tagArgAt_ne {k : Nat} {r : Reg} (hr : r ∈ preserved) : tagArgAt k ≠ .reg r := by
  unfold tagArgAt
  split
  · next h =>
    intro e
    exact (argRegs_ok k h).2.2.1 (TagArg.reg.inj e ▸ hr)
  · exact fun e => TagArg.noConfusion e

/-- `tagArgAt k` is register argument `i` exactly if `i` is `k`. -/
theorem tagArgAt_reg {k i : Nat} (hi : i < 8) : tagArgAt k = .reg (argRegs.getD i .x0) ↔ k = i := by
  unfold tagArgAt
  split
  · next h =>
    constructor
    · intro e; exact (argRegs_ok k h).2.2.2 i hi (TagArg.reg.inj e)
    · rintro rfl; rfl
  · next h => exact ⟨fun e => TagArg.noConfusion e, fun e => absurd (by omega : k < 8) h⟩

/-- `tagArgAt k` is stack argument `i - 8` exactly if `i` is `k`, for `8 ≤ i`. -/
theorem tagArgAt_stack {k i : Nat} (hi : 8 ≤ i) : tagArgAt k = .stack (i - 8) ↔ k = i := by
  unfold tagArgAt
  split
  · next h => exact ⟨fun e => TagArg.noConfusion e, fun e => by omega⟩
  · next h =>
    constructor
    · intro e; have := TagArg.stack.inj e; omega
    · rintro rfl; rfl

section
variable {sig : Sig} {q : Nat} {nmT nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {wa : Bool} {stack bytes : Nat}

theorem tagWord_lt (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    tagWord sig q < (sig.words abi.ptrBits).length := by
  rw [Sig.words_split _ hq, List.length_append, List.length_cons]; simp only [tagWord]; omega

theorem allArgs_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) :
    allArgs (sig.tagWork q nm e n) s = allArgs sig s := by
  rw [allArgs, allArgs, nStack, nStack, Sig.words_tagWork _ _ _ _ hq]

theorem argsOk_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig) :
    ArgsOk (sig.tagWork q nm e n) := by
  unfold ArgsOk
  rw [Sig.words_tagWork _ _ _ _ hq, hA]
  exact congrArg some (funext fun s => (allArgs_tagWork hq s).symm)

/-- What the function's precondition says of the frame: it lies below the
stack pointer, within the stack the function may use, and outside its
buffers. -/
theorem pre_frame (hA : ArgsOk sig) (hb0 : 0 < bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    stack + bytes ≤ s.sp.toNat ∧
      ∀ a ∈ allRegions sig s, ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
        a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 x, k⟩ := by
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega)]; simp
  exact ⟨hsb, fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right (Offset.sub_below _ hx hk)⟩

/-- What `tagSetup` gives, from a state satisfying the function's
precondition: the run, from the frame's push; and the state the code runs
from, which keeps what the function must keep, passes the arguments with
the buffer in the tag's place, and holds the tag pointer after the copied
stack arguments and the tag in the buffer, having written only there. -/
theorem narrowT_facts (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig)
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    execBlock isa (tagSetup bytes (nStack sig) (tagArgAt (tagWord sig q))) (allocated bytes s) =
        some (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s),
          tagSetupTrace bytes (nStack sig) (tagArgAt (tagWord sig q))
            (s.sp - BitVec.ofNat 64 bytes) ((allArgs sig s).getD (tagWord sig q) 0)) ∧
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).rd = s.rd ∧
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s)).wr =
        ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr ∧
      (narrowT sig q nm e n bytes s).sp = s.sp - BitVec.ofNat 64 bytes ∧
      (∀ r ∈ preserved, (narrowT sig q nm e n bytes s).gpr r = s.gpr r) ∧
      (∀ x ∈ preservedV, (narrowT sig q nm e n bytes s).v x = s.v x) ∧
      allArgs (sig.tagWork q nm e n) (narrowT sig q nm e n bytes s) =
        (allArgs sig s).set (tagWord sig q) (tagBufAddr sig bytes s) ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, 16 * (nStack sig / 2 + 1) + 16⟩] s.mem
        (narrowT sig q nm e n bytes s).mem ∧
      (narrowT sig q nm e n bytes s).mem.readW
          (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * nStack sig)) 64 =
        (allArgs sig s).getD (tagWord sig q) 0 ∧
      ∀ i < 16, (narrowT sig q nm e n bytes s).mem (tagBufAddr sig bytes s + BitVec.ofNat 64 i) =
        s.mem ((allArgs sig s).getD (tagWord sig q) 0 + BitVec.ofNat 64 i) := by
  have hlt := tagWord_lt hq
  have hlen := allArgs_length sig s
  have hsplit := List.split_at (vs := allArgs sig s) (k := tagWord sig q) (by omega)
  have hl₁ : ((allArgs sig s).take (tagWord sig q)).length =
      (Sig.psWords (sig.params.take q) abi.ptrBits).length := by
    rw [List.length_take_of_le (by omega)]
  have hbufs := Sig.bufs_split abi.ptrBits hq _ ((allArgs sig s).drop (tagWord sig q + 1))
    ((allArgs sig s).getD (tagWord sig q) 0) hl₁
  rw [← hsplit] at hbufs
  have hptr := tagPtr_alloc (bytes := bytes) hlt s
  obtain ⟨hsb, hout⟩ := pre_frame hA (by omega) hs hl
  generalize (allArgs sig s).getD (tagWord sig q) 0 = t at hbufs hptr ⊢
  rw [pre_args hA hl] at hs
  obtain ⟨-, hrd, hwr, -, -, -, -⟩ := hs
  have htb : ((⟨t, 16⟩ : Region), true) ∈ Sig.bufs sig.params (allArgs sig s) := by
    rw [hbufs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have htw : (⟨t, 16⟩ : Region) ∈ s.wr := by
    rw [hwr]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ htb, rfl⟩, rfl⟩
  have htd : (⟨t, 16⟩ : Region).Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :=
    hout _ (List.mem_append_left _ htb) (by omega) (by omega)
  -- The caller's stack arguments hold the sources.
  have hsrc : ∀ j, (allocated bytes s).sp + BitVec.ofNat 64 (bytes + 8 * j) = stackArgAddr s j :=
    fun j => by
      show s.sp - BitVec.ofNat 64 bytes + _ = _
      rw [stackArgAddr, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have hargs : ∀ j < nStack sig,
      InRegions ((allocated bytes s).rd ++ (allocated bytes s).wr) (stackArgAddr s j) 8 := fun j hj => by
    have h0 : ¬ nStack sig = 0 := by omega
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
  obtain ⟨hrun, hsp', hrd', hwr', hv, hg, hf, hcopy, hslot, hW⟩ := tagSetup_run (bytes := bytes)
    (m := nStack sig) (a := tagArgAt (tagWord sig q)) (u := allocated bytes s) hb
    (List.mem_cons_self ..) (fun j hj => by rw [hsrc]; exact hargs j hj)
    (tagArgAt_ok hlt) (by rw [hptr]; exact List.mem_cons_of_mem _ htw) (by rw [hptr]; exact htd)
  rw [hptr] at hrun hslot hW
  have hcs : ∀ r ∈ preserved, r ≠ .x16 ∧ r ≠ .x17 := by decide
  have hcv : ∀ x ∈ preservedV, x ≠ .v16 := by decide
  refine ⟨hrun, hrd', hwr', by rw [narrowT_sp, hsp']; rfl, fun r hr => ?_,
    fun x hx => by rw [narrowT_v]; exact hv x (hcv x hx), ?_, by rw [narrowT_mem]; exact hf,
    by rw [narrowT_mem]; exact hslot, fun i hi => by rw [narrowT_mem]; exact hW i hi⟩
  · obtain ⟨o₁, o₂⟩ := hcs r hr
    rw [narrowT_gpr, hg r o₁ o₂]
    simp only [tagArgAt_ne hr, ↓reduceIte]
    rfl
  · rw [allArgs_tagWork hq]
    have hlenT := allArgs_length sig (narrowT sig q nm e n bytes s)
    apply List.ext_getElem (by rw [hlenT, List.length_set, hlen])
    intro i h₁ h₂
    rw [allArgs_getElem, List.getElem_set, allArgs_getElem]
    by_cases hi : i < 8
    · obtain ⟨o₁, o₂, -, -⟩ := argRegs_ok i hi
      simp only [hi, ↓reduceIte]
      rw [narrowT_gpr, hg _ o₁ o₂]
      simp only [tagArgAt_reg hi]
      rfl
    · have hj : i - 8 < nStack sig := by simp only [nStack]; omega
      simp only [hi, ↓reduceIte]
      rw [stackArg, stackArgAddr, narrowT_mem, narrowT_sp, hsp']
      rw [hcopy (i - 8) hj]
      simp only [tagArgAt_stack (by omega : 8 ≤ i)]
      split
      · rfl
      · rw [hsrc]
        rfl

/-- The arguments and the buffers of the function and of the code: those of
the function around the tag (at `t`), and the code's with the buffer (at
`W`) in its place. -/
theorem tag_bufs (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) (W : Addr) :
    ((allArgs sig s).take (tagWord sig q)).length =
        (Sig.psWords (sig.params.take q) abi.ptrBits).length ∧
      ((allArgs sig s).drop (tagWord sig q + 1)).length =
        (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length ∧
      allArgs sig s = (allArgs sig s).take (tagWord sig q) ++
        (allArgs sig s).getD (tagWord sig q) 0 :: (allArgs sig s).drop (tagWord sig q + 1) ∧
      (allArgs sig s).set (tagWord sig q) W =
        (allArgs sig s).take (tagWord sig q) ++ W :: (allArgs sig s).drop (tagWord sig q + 1) ∧
      Sig.bufs sig.params (allArgs sig s) =
        Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
          (⟨(allArgs sig s).getD (tagWord sig q) 0, 16⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)) ∧
      Sig.bufs (sig.tagWork q nm e n).params ((allArgs sig s).set (tagWord sig q) W) =
        Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
          (⟨W, n * e.size⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)) := by
  have hlt := tagWord_lt hq
  have hlen := allArgs_length sig s
  have hw := Sig.words_split abi.ptrBits hq
  have hl₁ : ((allArgs sig s).take (tagWord sig q)).length =
      (Sig.psWords (sig.params.take q) abi.ptrBits).length := List.length_take_of_le (by omega)
  have hl₂ : ((allArgs sig s).drop (tagWord sig q + 1)).length =
      (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length := by
    rw [List.length_drop, hlen, hw, List.length_append, List.length_cons]; simp only [tagWord]; omega
  have hsplit := List.split_at (vs := allArgs sig s) (k := tagWord sig q) (by omega)
  have hset : (allArgs sig s).set (tagWord sig q) W =
      (allArgs sig s).take (tagWord sig q) ++ W :: (allArgs sig s).drop (tagWord sig q + 1) := by
    rw [List.set_eq_take_append_cons_drop]
    simp only [show tagWord sig q < (allArgs sig s).length by omega, ↓reduceIte]
  refine ⟨hl₁, hl₂, hsplit, hset, ?_, ?_⟩
  · conv => lhs; rw [hsplit]
    exact Sig.bufs_split abi.ptrBits hq _ _ _ hl₁
  · rw [hset]; exact Sig.bufs_tagWork nm e n abi.ptrBits hq _ _ _ hl₁

/-- `p - b + d` is `p - (b - d)`, for `d ≤ b`. -/
theorem sub_add_ofNat (p : Addr) {b d : Nat} (h : d ≤ b) :
    p - BitVec.ofNat 64 b + BitVec.ofNat 64 d = p - BitVec.ofNat 64 (b - d) := by
  rw [Offset.sub_ofNat_eq p (show b - d ≤ b by omega), Nat.sub_sub_self h]

theorem nStack_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    nStack (sig.tagWork q nm e n) = nStack sig := by
  simp only [nStack, Sig.words_tagWork _ _ _ _ hq]

theorem allRegions_narrowT (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig)
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) (hl : Sig.noLists sig.params = true) :
    allRegions (sig.tagWork q nm e n) (narrowT sig q nm e n bytes s) = innerRegions sig q nm e n bytes s := by
  obtain ⟨-, -, -, hsp, -, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hA hb hs hl
  rw [allRegions, hargs, innerRegions]
  congr 1
  rw [argArea, copyArea, nStack_tagWork hq, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]

/-- The relation of `Sig.contract`'s disjointness is symmetric. -/
theorem disj_symm {x y : Region × Bool} (h : (x.2 || y.2) → x.1.Disjoint y.1) :
    (y.2 || x.2) → y.1.Disjoint x.1 :=
  fun hb => (h (by rw [Bool.or_comm]; exact hb)).symm

/-- The function's buffers other than the tag. -/
abbrev otherBufs (sig : Sig) (q : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
    Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1))

theorem otherBufs_mem (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s : State} :
    ∀ b ∈ otherBufs sig q s, b ∈ Sig.bufs sig.params (allArgs sig s) := fun b hb => by
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := "") (e := .u8) (n := 0) hq s 0
  rw [hbO]
  rcases List.mem_append.mp hb with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- The code's precondition holds in `narrowT`, from the function's. -/
theorem narrowT_pre (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig)
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes ∧
      16 * (nStack sig / 2 + 1) + n * e.size ≤ bytes)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pre (narrowT sig q nm e n bytes s) := by
  obtain ⟨hb16, hb1, hb2, hb3⟩ := hb
  obtain ⟨-, -, -, hsp, -, -, hargs, hf, -, hW⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) hq hA ⟨hb16, hb1, hb2⟩ hs hl
  have hall := allRegions_narrowT (nm := nm) (e := e) (n := n) hq hA ⟨hb16, hb1, hb2⟩ hs hl
  obtain ⟨hl₁, hl₂, hsplit, hset, hbO, hbI⟩ :=
    tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBufAddr sig bytes s)
  obtain ⟨hsb, hout⟩ := pre_frame hA (by omega) hs hl
  have hB := otherBufs_mem (s := s) hq
  rw [pre_args hA hl] at hs
  obtain ⟨-, -, -, hpw, -, hnw, hpr⟩ := hs
  have hscr : tagBufAddr sig bytes s =
      s.sp - BitVec.ofNat 64 (bytes - 16 * (nStack sig / 2 + 1)) := sub_add_ofNat _ (by omega)
  have houtB : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes → a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 x, k⟩ :=
    fun a ha => hout a (List.mem_append_left _ ha)
  have hpwB : (otherBufs sig q s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) := by
    rw [allRegions, hbO, List.pairwise_append, List.pairwise_middle disj_symm] at hpw
    exact (List.pairwise_cons.mp hpw.1).2
  have hWB : ∀ b ∈ otherBufs sig q s,
      (⟨tagBufAddr sig bytes s, n * e.size⟩ : Region).Disjoint b.1 := fun b hb => by
    rw [hscr]; exact (houtB b (hB b hb) (by omega) (by omega)).symm
  have hCA : ∀ a ∈ copyArea sig bytes s,
      a = (⟨s.sp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩, false) := fun a ha => by
    unfold copyArea at ha; split at ha
    · simp at ha
    · simpa using ha
  refine (pre_args (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
    (argsOk_tagWork hq hA) (Sig.noLists_tagWork _ _ _ hq hl)).mpr ?_
  rw [hall, hsp, hargs, nStack_tagWork hq]
  refine ⟨⟨.inr ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat' (by omega)]; omega
  · rw [toNat_sub_ofNat' (by omega)]; have := s.sp.isLt; omega
  · -- Pairwise disjoint.
    rw [innerRegions, hbI, List.pairwise_append, List.pairwise_middle disj_symm]
    refine ⟨List.pairwise_cons.mpr ⟨fun b hb _ => hWB b hb, hpwB⟩, ?_, fun a ha b hb _ => ?_⟩
    · unfold copyArea; split <;> simp
    · obtain rfl := hCA b hb
      rcases List.mem_append.mp ha with ha | ha
      · exact houtB a (hB a (List.mem_append_left _ ha)) (by omega) (by omega)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · exact houtB a (hB a (List.mem_append_right _ ha)) (by omega) (by omega)
  · -- The reserved stack below the frame.
    intro r hr a ha
    have hr' : 0 < stack ∧ r = below (s.sp - BitVec.ofNat 64 bytes) stack := by
      rcases Nat.eq_zero_or_pos stack with h0 | h0
      · subst h0; simp [stackBelow] at hr
      · rw [stackBelow_pos _ h0, List.mem_singleton] at hr; exact ⟨h0, hr⟩
    obtain ⟨h0, rfl⟩ := hr'
    have hbuf : ∀ a ∈ Sig.bufs sig.params (allArgs sig s),
        (below (s.sp - BitVec.ofNat 64 bytes) stack).Disjoint a.1 := fun a ha =>
      (Region.Disjoint.symm (houtB a ha (x := stack + bytes) (k := stack + bytes)
        (by omega) (by omega))).sub_left (below_below _ bytes stack)
    rw [innerRegions, hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hbuf a (hB a (List.mem_append_left _ ha))
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact Region.Disjoint.symm (Offset.disjoint_below _ (by omega))
        · exact hbuf a (hB a (List.mem_append_right _ ha))
    · obtain rfl := hCA a ha
      exact Region.Disjoint.symm (Offset.base_disjoint_below _ (by omega))
  · -- No buffer wraps around.
    intro a ha
    rw [hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a (hB a (List.mem_append_left _ ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · show (tagBufAddr sig bytes s).toNat + n * e.size ≤ 2 ^ 64
        rw [hscr, toNat_sub_ofNat' (by omega)]
        have := s.sp.isLt
        omega
      · exact hnw a (hB a (List.mem_append_right _ ha))
  · -- The precondition.
    rw [hset]
    refine ho.pre _ _ _ _ _ _ hl₁ hl₂ ⟨fun b hb x hx => (hf x fun r hr hc => ?_).symm, hW⟩
      (by rw [← hsplit]; exact hpr)
    simp only [List.mem_singleton] at hr; subst hr
    exact houtB b (hB b hb) (x := bytes) (k := 16 * (nStack sig / 2 + 1) + 16) (by omega) (by omega)
      x hx hc

/-- The tag lies outside the other buffers, and the code's memory agrees
with the function's on them and holds the tag in the buffer (`TagIn`). -/
theorem narrowT_tagIn (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig)
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    TagIn (otherBufs sig q s) ((allArgs sig s).getD (tagWord sig q) 0) (tagBufAddr sig bytes s) s.mem
      (narrowT sig q nm e n bytes s).mem ∧
    ∀ b ∈ otherBufs sig q s, b.1.Disjoint ⟨(allArgs sig s).getD (tagWord sig q) 0, 16⟩ := by
  obtain ⟨-, -, -, -, -, -, -, hf, -, hW⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hA hb hs hl
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBufAddr sig bytes s)
  obtain ⟨-, hout⟩ := pre_frame hA (by omega) hs hl
  have hB := otherBufs_mem (s := s) hq
  rw [pre_args hA hl] at hs
  obtain ⟨-, -, -, hpw, -, -, -⟩ := hs
  refine ⟨⟨fun b hb x hx => (hf x fun r hr hc => ?_).symm, hW⟩, fun b hb => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact hout b (List.mem_append_left _ (hB b hb)) (x := bytes)
      (k := 16 * (nStack sig / 2 + 1) + 16) (by omega) (by omega) x hx hc
  · rw [allRegions, hbO, List.pairwise_append, List.pairwise_middle disj_symm] at hpw
    exact (((List.pairwise_cons.mp hpw.1).1 b hb rfl)).symm

theorem getD_set_ne {l : List (BitVec 64)} {k i : Nat} {a : BitVec 64} (h : k ≠ i) :
    (l.set k a).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_self {l : List (BitVec 64)} {k : Nat} {a : BitVec 64} (h : k < l.length) :
    (l.set k a).getD k 0 = a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self h, Option.getD_some]

/-- The function's public data is the code's public data in `narrowT`. -/
theorem narrowT_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig)
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pub
      (narrowT sig q nm e n bytes s₁) (narrowT sig q nm e n bytes s₂) := by
  have hlt := tagWord_lt hq
  rw [pub_args hA hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  obtain ⟨-, -, -, e₁, -, -, a₁, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hA hb h₁ hl
  obtain ⟨-, -, -, e₂, -, -, a₂, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hA hb h₂ hl
  obtain ⟨t₁, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hA hb h₁ hl
  obtain ⟨t₂, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hA hb h₂ hl
  obtain ⟨l₁, l₁', s₁', st₁, -, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s₁ (tagBufAddr sig bytes s₁)
  obtain ⟨l₂, l₂', s₂', st₂, -, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s₂ (tagBufAddr sig bytes s₂)
  have p₁ := ((pre_args hA hl).mp h₁).2.2.2.2.2.2
  have p₂ := ((pre_args hA hl).mp h₂).2.2.2.2.2.2
  rw [s₁'] at p₁
  rw [s₂'] at p₂
  refine (pub_args (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
    (argsOk_tagWork hq hA) (Sig.noLists_tagWork _ _ _ hq hl)).mpr ⟨⟨by rw [e₁, e₂, hsp], ?_⟩,
      fun i hi => ?_⟩
  · rw [a₁, a₂, st₁, st₂]
    have hol := ho.leak
    revert hlk hol
    cases leak <;> cases leakI <;> simp only [leakAgree, imp_self, implies_true, false_implies]
    intro hlk hol
    rw [hol _ _ _ _ _ _ l₁ l₁' t₁ p₁, hol _ _ _ _ _ _ l₂ l₂' t₂ p₂, ← s₁', ← s₂']
    exact hlk
  · rw [Sig.pubs_tagWork _ _ _ hq] at hi
    rw [a₁, a₂, Sig.words_tagWork _ _ _ _ hq]
    by_cases hik : tagWord sig q = i
    · subst hik
      rw [getD_set_self (by rw [allArgs_length]; exact hlt),
        getD_set_self (by rw [allArgs_length]; exact hlt), tagBufAddr, tagBufAddr, hsp]
    · rw [getD_set_ne hik, getD_set_ne hik]
      exact hpa i hi

/-! ## The run -/

/-- The addresses `tagOut m` accesses, from `sp = p`, for the tag at `t`. -/
def tagOutTrace (m : Nat) (p t : Addr) : List Leak :=
  [.addr (p + BitVec.ofNat 64 (8 * m)),
    .addr (p + BitVec.ofNat 64 (16 * (m / 2 + 1)) + BitVec.ofNat 64 0), .addr (t + BitVec.ofNat 64 0)]

/-- The state after `tagOut m` from `u`, if it runs. -/
def tagOutState (m : Nat) (u : State) : State :=
  ((execBlock isa (tagOut m) u).map Prod.fst).getD u

/-- The state `withTagScratch` ends in, from `s`, when its code ends in
`s₃`. -/
def finalT (bytes m : Nat) (s s₃ : State) : State :=
  freed bytes (tagOutState m (s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))

/-- Every region of the code's contract is one of the function's buffers,
the working space, or the copy of the stack arguments. -/
theorem mem_innerRegions (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s : State}
    {a : Region × Bool} (ha : a ∈ innerRegions sig q nm e n bytes s) :
    a ∈ Sig.bufs sig.params (allArgs sig s) ∨ a = (⟨tagBufAddr sig bytes s, n * e.size⟩, true) ∨
      a = (⟨s.sp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩, false) := by
  obtain ⟨-, -, -, -, hbO, hbI⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBufAddr sig bytes s)
  rw [innerRegions, hbI] at ha
  rw [hbO]
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact .inl (List.mem_append_left _ ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact .inr (.inl rfl)
      · exact .inl (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  · unfold copyArea at ha; split at ha
    · simp at ha
    · exact .inr (.inr (by simpa using ha))

/-- A run of the code from `narrowT s` is a run of `withTagScratch` from
`s`, after `tagSetup`'s accesses and before `tagOut`'s, which keeps what the
calling convention requires, and whose memory is the code's with the
buffer's first 16 bytes copied to the tag, and whose `x0` is the code's. -/
theorem withTagScratch_run {c : Prog isa} (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hA : ArgsOk sig)
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes ∧
      16 * (nStack sig / 2 + 1) + n * e.size ≤ bytes)
    (hd : 16 * c.aarch64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowT sig q nm e n bytes s) t s₃)
    (ha : abiPreserved (narrowT sig q nm e n bytes s) s₃) (hl : Sig.noLists sig.params = true) :
    Exec isa (withTagScratch bytes (nStack sig) (tagArgAt (tagWord sig q)) c) s
        (tagSetupTrace bytes (nStack sig) (tagArgAt (tagWord sig q)) (s.sp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0) ++
          (t ++ tagOutTrace (nStack sig) (s.sp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0)))
        (finalT bytes (nStack sig) s s₃) ∧
      abiPreserved s (finalT bytes (nStack sig) s s₃) ∧
      TagOut ((allArgs sig s).getD (tagWord sig q) 0) (tagBufAddr sig bytes s) s₃.mem
        (finalT bytes (nStack sig) s s₃).mem ∧
      (finalT bytes (nStack sig) s s₃).gpr .x0 = s₃.gpr .x0 := by
  obtain ⟨hb16, hb1, hb2, hb3⟩ := hb
  obtain ⟨hrun, hrd', hwr', hsp, hpres, hpresV, -, hf, hslot, -⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) hq hA ⟨hb16, hb1, hb2⟩ hs hl
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBufAddr sig bytes s)
  obtain ⟨hsb, hout⟩ := pre_frame hA (by omega) hs hl
  rw [pre_args hA hl] at hs
  obtain ⟨-, hrd, hwr, -, -, -, -⟩ := hs
  generalize hT : (allArgs sig s).getD (tagWord sig q) 0 = tg at hbO hrun hslot ⊢
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, show 0 < bytes by omega, hb1, hb16, show bytes ≤ s.sp.toNat by omega,
      and_self, ite_true]
    rfl
  have hF : ∀ {d k : Nat}, d + k ≤ bytes →
      Covers [⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d, k⟩]
        (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    fun h => Covers.one ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have htb : ((⟨tg, 16⟩ : Region), true) ∈ Sig.bufs sig.params (allArgs sig s) := by
    rw [hbO]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- The code runs within the function's regions and the frame.
  have hcovW : Covers (((innerRegions sig q nm e n bytes s).filter (·.2)).map (·.1))
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · exact hF (by omega)
    · simp at hf'
  have hcovR : Covers (((innerRegions sig q nm e n bytes s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (Covers.one ⟨_, List.mem_cons_self .., Region.contains_self' (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowT sig q nm e n bytes s).withRegions s.rd
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocated bytes s) by
    rw [narrowT, State.withRegions_withRegions, ← hrd', ← hwr', State.withRegions_self]] at hw
  -- What the code leaves: the tag pointer, and `sp`.
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans hsp
  have hfs := Exec.frameSp he (by omega)
  rw [hsp] at hfs
  have hcode : ∀ {R : Region}, (∀ a ∈ Sig.bufs sig.params (allArgs sig s), R.Disjoint a.1) →
      R.Disjoint ⟨tagBufAddr sig bytes s, n * e.size⟩ →
      R.Disjoint (below (s.sp - BitVec.ofNat 64 bytes) (16 * c.aarch64Depth)) →
      ∀ r ∈ (narrowT sig q nm e n bytes s).wr ++
        [below (s.sp - BitVec.ofNat 64 bytes) (16 * c.aarch64Depth)], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
      rcases mem_innerRegions hq ha with ha | rfl | rfl
      · exact h₁ a ha
      · exact h₂
      · simp at hf'
    · simp only [List.mem_singleton] at hr; subst hr; exact h₃
  have hslot₃ : s₃.mem.readW (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * nStack sig)) 64 =
      tg := by
    rw [hfs.readW (Region.contains_self _ _) (hcode ?_ ?_ ?_) (by decide)]
    · exact hslot
    · intro a ha
      rw [sub_add_ofNat _ (by omega)]
      exact (hout a (List.mem_append_left _ ha) (by omega) (by omega)).symm
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact Offset.disjoint_below _ (by omega)
  -- `tagOut`, with the function's regions and the frame.
  have hz : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := BitVec.add_zero
  have htw : (⟨tg, 16⟩ : Region) ∈ s.wr := hbufW _ htb rfl
  obtain ⟨u₄, hto, sp₄, rd₄, wr₄, g₄, v₄, mem₄⟩ := tagOut_run (m := nStack sig)
    (w := s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) (by omega)
    (by rw [State.withRegions_sp, hsp₃, State.withRegions_rd, State.withRegions_wr]
        exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
          Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [State.withRegions_sp, hsp₃, State.withRegions_rd, State.withRegions_wr, hz]
        exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
          Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [State.withRegions_mem, State.withRegions_sp, hsp₃, hslot₃, hz, State.withRegions_wr]
        exact ⟨_, List.mem_cons_of_mem _ htw, Region.contains_self _ _⟩)
  rw [State.withRegions_mem, State.withRegions_sp, hsp₃, hslot₃] at hto mem₄
  have hst₄ : tagOutState (nStack sig)
      (s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) = u₄ := by
    simp [tagOutState, hto]
  have hfin : finalT bytes (nStack sig) s s₃ = freed bytes u₄ := by rw [finalT, hst₄]
  rw [hfin]
  -- The pop.
  have hsp₄ : u₄.sp = (allocated bytes s).sp := by rw [sp₄, State.withRegions_sp, hsp₃]; rfl
  have hwr₄ : u₄.wr = (allocated bytes s).wr := by rw [wr₄]; rfl
  have hpop : isa.pop (.free bytes) (allocated bytes s) u₄ = some (freed bytes u₄) := by
    simp only [freed, isa, pop, show 0 < bytes by omega, hb1, hb16, hsp₄, hwr₄, allocated,
      List.head?_cons, and_self, ite_true]
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) (Exec.seq hw (Exec.block hto))) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun r hr => ?_, ?_, fun x hx => ?_⟩, ?_, ?_⟩
  · have hcs : ∀ r ∈ preserved, r ≠ .x16 ∧ r ≠ .x17 := by decide
    show u₄.gpr r = s.gpr r
    rw [g₄ r (hcs r hr).1 (hcs r hr).2, State.withRegions_gpr, ha.1 r hr, hpres r hr]
  · show u₄.sp + BitVec.ofNat 64 bytes = s.sp
    rw [hsp₄]
    exact BitVec.sub_add_cancel _ _
  · have hcv : ∀ x ∈ preservedV, x ≠ .v16 := by decide
    show (u₄.v x).extractLsb' 0 64 = _
    rw [v₄ x (hcv x hx), ← hpresV x hx]
    exact ha.2.2 x hx
  · show TagOut tg (tagBufAddr sig bytes s) s₃.mem u₄.mem
    rw [mem₄]
    exact tagOutMem_tagOut _ _ _ _
  · show u₄.gpr .x0 = s₃.gpr .x0
    rw [g₄ .x0 (by decide) (by decide)]
    rfl

/-- The tag pointer is public. -/
theorem tag_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (hA : ArgsOk sig)
    {s₁ s₂ : State} (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂)
    (hl : Sig.noLists sig.params = true) :
    (allArgs sig s₁).getD (tagWord sig q) 0 = (allArgs sig s₂).getD (tagWord sig q) 0 := by
  obtain ⟨-, hpa⟩ := (pub_args hA hl).mp hp
  have hpub : (sig.params.flatMap (·.2.pubs)).getD (tagWord sig q) false = true := by
    conv => lhs; rw [Sig.params_split hq]
    rw [List.flatMap_append, List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Sig.pubs_length _ abi.ptrBits]),
      Sig.pubs_length _ abi.ptrBits]
    simp only [tagWord, Nat.sub_self]
    rfl
  have hw : ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD (tagWord sig q) 64 = 64 := by
    rw [Sig.words_split _ hq, List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_map])]
    simp [ArgWord.bits, abi]
  have h := hpa _ hpub
  rw [hw] at h
  simpa using h

/-- Code verified for a function whose parameter `q` is working space that
also carries a 16-byte tag in its first 16 bytes (`Sig.tagWork`), with
`stack` bytes of stack, is verified for the function whose parameter `q` is
the tag, which allocates the working space in a frame of `bytes` more bytes
of stack (`withTagScratch`), if the two contracts are related by
`Sig.TagFrame`. -/
theorem Verified.tagScratch {c : Prog isa}
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI))
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes ∧
      16 * (nStack sig / 2 + 1) + n * e.size ≤ bytes)
    (hd : 16 * c.aarch64Depth ≤ stack)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withTagScratch bytes (nStack sig) (tagArgAt (tagWord sig q)) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hA : ArgsOk sig := let ⟨_, hs⟩ := hsat; argsOk_of_pre hs
  have hb' : bytes % 16 = 0 ∧ bytes < 4096 ∧ 16 * (nStack sig / 2 + 1) + 16 ≤ bytes :=
    ⟨hb.1, hb.2.1, hb.2.2.1⟩
  -- Every run is `tagSetup`, the code's run from `narrowT`, and `tagOut`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowT sig q nm e n bytes s) t s₃ ∧
      ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).post
        (narrowT sig q nm e n bytes s) s₃ ∧
      Exec isa (withTagScratch bytes (nStack sig) (tagArgAt (tagWord sig q)) c) s
        (tagSetupTrace bytes (nStack sig) (tagArgAt (tagWord sig q)) (s.sp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0) ++
          (t ++ tagOutTrace (nStack sig) (s.sp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0)))
        (finalT bytes (nStack sig) s s₃) ∧
      abiPreserved s (finalT bytes (nStack sig) s s₃) ∧
      TagOut ((allArgs sig s).getD (tagWord sig q) 0) (tagBufAddr sig bytes s) s₃.mem
        (finalT bytes (nStack sig) s s₃).mem ∧
      (finalT bytes (nStack sig) s s₃).gpr .x0 = s₃.gpr .x0 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq'⟩ := hcor _ (narrowT_pre hq hA hb ho hs hl)
    exact ⟨t, s₃, he, hq', withTagScratch_run hq hA hb hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hpost, hex, ha, hto, hx0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hA]
    have hq' := (post_args (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
      (argsOk_tagWork hq hA)).mp hpost
    obtain ⟨-, -, -, -, -, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hA hb' hs hl
    obtain ⟨hl₁, hl₂, hsplit, hset, -, -⟩ :=
      tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBufAddr sig bytes s)
    obtain ⟨hin, hdis⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hA hb' hs hl
    have hpr := ((pre_args hA hl).mp hs).2.2.2.2.2.2
    rw [hsplit] at hpr
    rw [hargs, hset] at hq'
    rw [hx0, hsplit]
    exact ho.post _ _ _ _ _ _ _ _ _ hl₁ hl₂ hin hpr hdis hto hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pub_args hA hl).mp hp).1.1, tag_pub hq hA hp hl,
      hct _ _ _ _ _ _ (narrowT_pre hq hA hb ho h₁ hl) (narrowT_pre hq hA hb ho h₂ hl)
        (narrowT_pub hq hA hb' ho h₁ h₂ hp hl) f₁ f₂]

end

/-- `withTagScratch`'s code satisfies `spSafe` (no AArch64 instruction
writes `sp`). -/
theorem withTagScratch_spSafe (bytes m : Nat) (a : TagArg) (c : Prog isa) :
    (withTagScratch bytes m a c).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

end VG.AArch64
