import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# A scratch buffer on the stack, after stack arguments (x86-64)

`Verified.stackArgScratch`: code verified for a function whose last argument
is a scratch buffer passed on the stack (its contract `Sig.scratchContract`;
the function's other arguments fill the six argument registers, and `m` more
are on the stack) runs as a function without that argument when
`withStackArgScratch` allocates the buffer in a frame on the stack, with
`bytes` more bytes of stack. The frame holds what the code expects at and
above `rsp` on entry: a quadword for its return address, a copy of the `m`
stack arguments, then the buffer's address (`setArgs`). The code runs from
the state after the frame's push and `setArgs`, with the permissions of the
contract with the argument (`narrow`), and its run there is its run from
that state (`Exec.widen`).

The copies are memory the code reads on entry, which the contract without the
argument says nothing of: the precondition and postcondition must read memory
only within the function's buffers (`hpre`, `hpost`), which the frame lies
outside of. The argument area is read-only on x86-64 (`abi`), so the copies
are too.
-/

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-- The arguments of a function with signature `sig`, of at least six words:
the six registers, then those on the stack. -/
def allArgs (sig : Sig) (s : State) : List (BitVec 64) :=
  argRegs.map s.gpr ++ (List.range ((sig.words abi.ptrBits).length - 6)).map (stackArg s)

/-- The argument area of `sig`, read-only. -/
def argArea (sig : Sig) (s : State) : List (Region × Bool) :=
  if (sig.words abi.ptrBits).length - 6 = 0 then []
  else [(⟨stackArgAddr s 0, 8 * ((sig.words abi.ptrBits).length - 6)⟩, false)]

/-- The buffers and the argument area of `sig`, and whether each is
writable. -/
def allRegions (sig : Sig) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (allArgs sig s) ++ argArea sig s

theorem allArgs_length (sig : Sig) (s : State) (hk : 6 ≤ (sig.words abi.ptrBits).length) :
    (allArgs sig s).length = (sig.words abi.ptrBits).length := by
  simp only [allArgs, List.length_append, List.length_map, List.length_range, argRegs,
    List.length_cons, List.length_nil]
  omega

theorem args_some (sig : Sig) (hk : 6 ≤ (sig.words abi.ptrBits).length) :
    abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some (allArgs sig) := by
  simp only [abi, List.length_map]
  split
  · have h6 : (sig.words 64).length = 6 := by
      have : (sig.words 64).length ≤ 6 := by assumption
      have : 6 ≤ (sig.words 64).length := hk
      omega
    congr 1
    funext s
    simp only [allArgs, show abi.ptrBits = 64 from rfl, h6, Nat.sub_self, List.range_zero,
      List.map_nil, List.append_nil]
    rfl
  · rfl

theorem argArea_eq (sig : Sig) (wa : Bool) (s : State) :
    (abi.argArea ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)) = argArea sig s := by
  simp only [abi, argArea, List.length_map]
  split <;> simp_all [argRegs]

theorem wf_args {sig : Sig} {stack : Nat} {s : State} (hk : 6 ≤ (sig.words abi.ptrBits).length) :
    abi.wf ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) stack s ↔
      ((stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) ∧
        ((sig.words abi.ptrBits).length = 6 ∨
          (s.gpr .rsp).toNat + 8 * ((sig.words abi.ptrBits).length - 6 + 1) ≤ 2 ^ 64)) := by
  have hk' : 6 ≤ (sig.words 64).length := hk
  simp only [abi, List.length_map]
  split
  · have h6 : (sig.words 64).length = 6 := by
      have : (sig.words 64).length ≤ argRegs.length := by assumption
      simp only [argRegs, List.length_cons, List.length_nil] at this; omega
    cases stack <;> simp [h6]
  · have h6 : (sig.words 64).length ≠ 6 := by
      have : ¬ (sig.words 64).length ≤ argRegs.length := by assumption
      simp only [argRegs, List.length_cons, List.length_nil] at this; omega
    simp only [h6, false_or, argRegs, List.length_cons, List.length_nil]
    cases stack <;> simp

/-- The precondition of a contract with at least six argument words. -/
theorem pre_args {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pre s ↔
      ((stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) ∧
        ((sig.words abi.ptrBits).length = 6 ∨
          (s.gpr .rsp).toNat + 8 * ((sig.words abi.ptrBits).length - 6 + 1) ≤ 2 ^ 64)) ∧
      s.rd = ((allRegions sig s).filter (!·.2)).map (·.1) ∧
      s.wr = ((allRegions sig s).filter (·.2)).map (·.1) ∧
      (allRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) stack : List Region),
        ∀ a ∈ allRegions sig s, r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (allArgs sig s) s.mem := by
  simp only [Sig.contract]
  rw [args_some sig hk]
  simp only [argArea_eq, Sig.lists_of_noLists _ _ _ _ hl, List.map_nil, List.append_nil]
  rw [wf_args hk]
  exact Iff.rfl

/-- The postcondition of a contract with at least six argument words. -/
theorem post_args {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s s' : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem s'.mem
        ((s'.gpr .rax).setWidth _) := by
  simp only [Sig.contract]
  rw [args_some sig hk]
  exact Iff.rfl

/-- The public data of a contract with at least six argument words, which
leaks nothing. -/
theorem pub_args {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack none).pub s₁ s₂ ↔
      s₁.gpr .rsp = s₂.gpr .rsp ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((allArgs sig s₁).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((allArgs sig s₂).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  simp only [Sig.contract]
  rw [args_some sig hk]
  simp only [Sig.descs_of_noLists _ _ _ hl, List.not_mem_nil, false_implies, implies_true, and_true]
  exact Iff.rfl

/-! ## Copying the stack arguments -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  simp

/-- The state after `copyArg bytes j` from `u`. -/
def copyState (bytes j : Nat) (u : State) : State :=
  { u.setReg .rax (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) with
    mem := u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j))
      (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) }

theorem copyArg_run {bytes j : Nat} {u : State}
    (hr : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8)
    (hw : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8) :
    execBlock isa (copyArg bytes j) u = some (copyState bytes j u,
      [.addr (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)),
        .addr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j))]) := by
  simp only [copyArg, execBlock, isa, exec, readSrc, State.load64, State.ea, ofInt_natCast, hr,
    ite_true, Option.map_some, addrs, srcAddrs]
  simp [copyState, State.setReg, State.store64, hw]

@[simp] theorem copyState_rsp (bytes j : Nat) (u : State) :
    (copyState bytes j u).gpr .rsp = u.gpr .rsp := by
  simp [copyState, State.setReg]
@[simp] theorem copyState_rd (bytes j : Nat) (u : State) : (copyState bytes j u).rd = u.rd := rfl
@[simp] theorem copyState_wr (bytes j : Nat) (u : State) : (copyState bytes j u).wr = u.wr := rfl
@[simp] theorem copyState_mxcsr (bytes j : Nat) (u : State) :
    (copyState bytes j u).mxcsr = u.mxcsr := rfl
theorem copyState_gpr (bytes j : Nat) (u : State) {q : Reg} (h : q ≠ .rax) :
    (copyState bytes j u).gpr q = u.gpr q := by
  simp [copyState, State.setReg, h]

/-- The state after copying the first `m` stack arguments from `u`. -/
def copiedState (bytes : Nat) (u : State) : Nat → State
  | 0 => u
  | m + 1 => copyState bytes m (copiedState bytes u m)

@[simp] theorem copiedState_rsp (bytes : Nat) (u : State) :
    ∀ m, (copiedState bytes u m).gpr .rsp = u.gpr .rsp
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_rsp, copiedState_rsp bytes u m]
@[simp] theorem copiedState_rd (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).rd = u.rd
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_rd, copiedState_rd bytes u m]
@[simp] theorem copiedState_wr (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).wr = u.wr
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_wr, copiedState_wr bytes u m]
@[simp] theorem copiedState_mxcsr (bytes : Nat) (u : State) :
    ∀ m, (copiedState bytes u m).mxcsr = u.mxcsr
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_mxcsr, copiedState_mxcsr bytes u m]
theorem copiedState_gpr (bytes : Nat) (u : State) {q : Reg} (h : q ≠ .rax) :
    ∀ m, (copiedState bytes u m).gpr q = u.gpr q
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_gpr _ _ _ h, copiedState_gpr bytes u h m]

/-- The addresses copying the first `m` stack arguments accesses. -/
def copyTrace (bytes : Nat) (sp : Addr) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j =>
    [.addr (sp + BitVec.ofNat 64 (bytes + 8 + 8 * j)), .addr (sp + BitVec.ofNat 64 (8 + 8 * j))]

theorem copies_run {bytes : Nat} {u : State} :
    ∀ m, (∀ j < m, InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8) →
      (∀ j < m, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8) →
      execBlock isa ((List.range m).flatMap (copyArg bytes)) u =
        some (copiedState bytes u m, copyTrace bytes (u.gpr .rsp) m)
  | 0, _, _ => rfl
  | m + 1, hr, hw => by
    rw [List.range_succ, List.flatMap_append, execBlock_append,
      copies_run m (fun j hj => hr j (by omega)) (fun j hj => hw j (by omega))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [copyArg_run (by simpa using hr m (by omega)) (by simpa using hw m (by omega))]
    simp only [Option.map_some, copiedState, copiedState_rsp, copyTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` stack arguments writes only within the `m`
destination quadwords (from `rsp + 8`), which then hold the sources (from
`rsp + bytes + 8`). -/
theorem copiedState_mem {bytes : Nat} {u : State} :
    ∀ m, bytes + 16 + 8 * m ≤ 2 ^ 64 → 8 * m ≤ bytes →
      Frame [⟨u.gpr .rsp + 8, 8 * m⟩] u.mem (copiedState bytes u m).mem ∧
      ∀ j < m, (copiedState bytes u m).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 64 =
        u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u) m (by omega) (by omega)
    have h8 : u.gpr .rsp + 8 = u.gpr .rsp + BitVec.ofNat 64 8 := rfl
    have hR : Region.Sub ⟨u.gpr .rsp + 8, 8 * m⟩ ⟨u.gpr .rsp + 8, 8 * (m + 1)⟩ :=
      Region.sub_prefix (by omega)
    have f' : Frame [⟨u.gpr .rsp + 8, 8 * (m + 1)⟩] u.mem (copiedState bytes u m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    -- The source of argument `m` is above the first `m` destinations.
    have hsrc : (copiedState bytes u m).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m)) 64 =
        u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m)) 64 := by
      refine f.readW (r := ⟨u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m), 8⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [h8]
      exact Offset.disjoint _ (d := bytes + 8 + 8 * m) (n := 8) (e := 8) (k := 8 * m) (.inr (by omega))
        (by omega) (by omega)
    refine ⟨?_, fun j hj => ?_⟩
    · show Frame _ u.mem ((copiedState bytes u m).mem.writeW _ _)
      rw [copiedState_rsp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      rw [h8]
      exact Offset.contains _ (d := 8 + 8 * m) (e := 8) (k := 8 * (m + 1)) (by omega) (by omega)
        (by omega)
    · show ((copiedState bytes u m).mem.writeW
          ((copiedState bytes u m).gpr .rsp + BitVec.ofNat 64 (8 + 8 * m))
          ((copiedState bytes u m).mem.readW
            ((copiedState bytes u m).gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m)) 64)).readW _ 64 = _
      rw [copiedState_rsp]
      rcases Nat.lt_or_ge j m with hj' | hj'
      · rw [Mem.readW_writeW_sep, hv j hj']
        · exact Offset.sep _ (d := 8 + 8 * j) (n := 8) (e := 8 + 8 * m) (k := 8) (by omega) (by omega)
            (by omega)
        · decide
      · obtain rfl : j = m := by omega
        rw [Mem.readW_writeW_self64, hsrc]

/-- `mov rax, rsp; add rax, 16 + 8m; mov [rsp + 8 + 8m], rax`: pass the buffer. -/
theorem tail_run {m : Nat} {w : State}
    (hw : InRegions w.wr (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 8) (hm : 16 + 8 * m < 2 ^ 31) :
    ∃ w', execBlock isa [.mov .rax (.reg .rsp), .alu .add .rax (.imm (BitVec.ofNat 32 (16 + 8 * m))),
        .store { base := .rsp, disp := ((8 + 8 * m : Nat) : Int) } .rax] w =
        some (w', [.addr (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m))]) ∧
      w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.mxcsr = w.mxcsr ∧ (∀ q, q ≠ .rax → w'.gpr q = w.gpr q) ∧
      w'.mem = w.mem.writeW (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m))
        (w.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)) := by
  have hse : (BitVec.ofNat 32 (16 + 8 * m)).signExtend 64 = BitVec.ofNat 64 (16 + 8 * m) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_signExtend]
    have : (BitVec.ofNat 32 (16 + 8 * m)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp; omega
    simp [this]
    omega
  simp only [execBlock, isa, exec, readSrc, execAlu, Option.map_some, Option.bind_some, addrs,
    srcAddrs, State.store64, State.ea, ofInt_natCast]
  simp [State.setReg, arithFlags, State.setFlags, hw, hse]
  intro q hq; simp [hq]

/-- The addresses `setArgs bytes m` accesses, from `rsp = sp`. -/
def setArgsTrace (bytes : Nat) (sp : Addr) (m : Nat) : List Leak :=
  copyTrace bytes sp m ++ [.addr (sp + BitVec.ofNat 64 (8 + 8 * m))]

/-- The state after `setArgs bytes m` from `u`, if it runs. -/
def setArgsState (bytes m : Nat) (u : State) : State :=
  ((execBlock isa (setArgs bytes m) u).map Prod.fst).getD u

/-- `setArgs`: the stack arguments copied into the frame, the buffer's
address after them; nothing else written, and only `rax` changed. -/
theorem setArgs_run {bytes m : Nat} {u : State}
    (hfit : bytes + 16 + 8 * m ≤ 2 ^ 64) (hb : 8 * m + 8 ≤ bytes)
    (hm : 16 + 8 * m < 2 ^ 31)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8)
    (hw : ∀ j ≤ m, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8) :
    execBlock isa (setArgs bytes m) u = some (setArgsState bytes m u, setArgsTrace bytes (u.gpr .rsp) m) ∧
      (setArgsState bytes m u).rd = u.rd ∧ (setArgsState bytes m u).wr = u.wr ∧
      (setArgsState bytes m u).mxcsr = u.mxcsr ∧
      (∀ q, q ≠ .rax → (setArgsState bytes m u).gpr q = u.gpr q) ∧
      Frame [⟨u.gpr .rsp + 8, 8 * (m + 1)⟩] u.mem (setArgsState bytes m u).mem ∧
      (∀ j < m, (setArgsState bytes m u).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 64 =
        u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) ∧
      (setArgsState bytes m u).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64 =
        u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m) := by
  have hc := copies_run (bytes := bytes) (u := u) m hr (fun j hj => hw j (by omega))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u) m (by omega) (by omega)
  obtain ⟨w', ht, hrd, hwr, hmx, hg, hmem⟩ := tail_run (m := m) (w := copiedState bytes u m)
    (by simpa using hw m (Nat.le_refl _)) hm
  have hrun : execBlock isa (setArgs bytes m) u = some (w', setArgsTrace bytes (u.gpr .rsp) m) := by
    rw [setArgs, execBlock_append, hc]
    simp only [Option.bind_some, ht, Option.map_some, copiedState_rsp, setArgsTrace]
  have hst : setArgsState bytes m u = w' := by simp [setArgsState, hrun]
  rw [hst]
  have h8 : u.gpr .rsp + 8 = u.gpr .rsp + BitVec.ofNat 64 8 := rfl
  refine ⟨hrun, by rw [hrd, copiedState_rd], by rw [hwr, copiedState_wr],
    by rw [hmx, copiedState_mxcsr], fun q hq => ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [hg q hq, copiedState_gpr _ _ hq]
  · rw [hmem, copiedState_rsp]
    refine (Frame.sub f fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · rw [h8]
      exact Offset.contains _ (d := 8 + 8 * m) (e := 8) (k := 8 * (m + 1)) (by omega) (by omega)
        (by omega)
  · rw [hmem, copiedState_rsp, Mem.readW_writeW_sep, hv j hj]
    · exact Offset.sep _ (d := 8 + 8 * j) (n := 8) (e := 8 + 8 * m) (k := 8) (by omega) (by omega)
        (by omega)
    · decide
  · rw [hmem, copiedState_rsp, Mem.readW_writeW_self64]

/-! ## The run from `narrow` -/

/-- The number of `sig`'s arguments on the stack. -/
abbrev nStack (sig : Sig) : Nat := (sig.words abi.ptrBits).length - 6

/-- The regions of the contract with the buffer, from the state after
`setArgs`: the buffers, the buffer, and the copied stack arguments. -/
def oldRegions (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (allArgs sig s) ++
    [(⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig), n * e.size⟩,
        true),
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩, false)]

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the frame's push and `setArgs`, which may read
and write what the contract with the buffer lets it. -/
def narrowS (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (setArgsState bytes (nStack sig) (allocState bytes s)).withRegions
    (((oldRegions sig e n bytes s).filter (!·.2)).map (·.1))
    (((oldRegions sig e n bytes s).filter (·.2)).map (·.1))

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat}

@[simp] theorem allocState_rsp' (bytes : Nat) (s : State) :
    (allocState bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := by
  simp [allocState, State.setReg]

theorem allocState_gpr' (bytes : Nat) (s : State) {q : Reg} (h : q ≠ .rsp) :
    (allocState bytes s).gpr q = s.gpr q := by
  simp [allocState, State.setReg, h]

/-- What `setArgs` gives, from a state satisfying the contract without the
buffer. -/
theorem argsState_run {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096)
    (hl : Sig.noLists sig.params = true) :
    let u := allocState bytes s
    execBlock isa (setArgs bytes (nStack sig)) u =
        some (setArgsState bytes (nStack sig) u, setArgsTrace bytes (u.gpr .rsp) (nStack sig)) ∧
      (setArgsState bytes (nStack sig) u).rd = u.rd ∧ (setArgsState bytes (nStack sig) u).wr = u.wr ∧
      (setArgsState bytes (nStack sig) u).mxcsr = s.mxcsr ∧
      (∀ q, q ≠ .rax → (setArgsState bytes (nStack sig) u).gpr q = u.gpr q) ∧
      Frame [⟨u.gpr .rsp + 8, 8 * (nStack sig + 1)⟩] s.mem (setArgsState bytes (nStack sig) u).mem ∧
      (∀ j < nStack sig, stackArg (setArgsState bytes (nStack sig) u) j = stackArg s j) ∧
      stackArg (setArgsState bytes (nStack sig) u) (nStack sig) =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig) := by
  intro u
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hst, -⟩, hrd, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega
  have hesp : u.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := allocState_rsp' _ _
  have hsrc : ∀ j, u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j) = stackArgAddr s j := fun j => by
    rw [hesp, stackArgAddr, show bytes + 8 + 8 * j = bytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  -- The caller's stack arguments hold the sources.
  have hargs : ∀ j < nStack sig, InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := fun j hj => by
    have h0 : ¬ (sig.words abi.ptrBits).length - 6 = 0 := by simp only [nStack] at hj; omega
    have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, h0]
    have hc : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region).Contains (stackArgAddr s j) 8 := by
      simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8 * (0 + 1)) (k := 8 * nStack sig)
        (by omega) (by omega) (by omega)
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    show _ ∈ s.rd
    rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j ≤ nStack sig, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8 :=
    fun j hj => ⟨_, List.mem_cons_self .., by
      rw [hesp]; exact Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨hrun, hrd', hwr', hmx, hg, hf, hv, hlast⟩ := setArgs_run (bytes := bytes)
    (m := nStack sig) (u := u) (by omega) (by omega) (by omega)
    (fun j hj => by rw [hsrc]; exact hargs j hj) hframe
  have hrsp₂ : (setArgsState bytes (nStack sig) u).gpr .rsp = u.gpr .rsp := hg _ (by decide)
  refine ⟨hrun, hrd', hwr', hmx, hg, hf, fun j hj => ?_, ?_⟩
  · show (setArgsState bytes (nStack sig) u).mem.readW
      ((setArgsState bytes (nStack sig) u).gpr .rsp + BitVec.ofNat 64 (8 * (j + 1))) 64 = _
    rw [hrsp₂, show 8 * (j + 1) = 8 + 8 * j by omega, hv j hj, hsrc]
    rfl
  · show (setArgsState bytes (nStack sig) u).mem.readW
      ((setArgsState bytes (nStack sig) u).gpr .rsp + BitVec.ofNat 64 (8 * (nStack sig + 1))) 64 = _
    rw [hrsp₂, show 8 * (nStack sig + 1) = 8 + 8 * nStack sig by omega, hlast, hesp]

theorem nStack_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat)
    (hk : 6 ≤ (sig.words abi.ptrBits).length) :
    nStack (sig.withScratch nm e n) = nStack sig + 1 := by
  simp only [nStack, Sig.words_withScratch, List.length_append, List.length_singleton]
  omega

theorem stackArg_withRegions (u : State) (rd wr : List Region) (j : Nat) :
    stackArg (u.withRegions rd wr) j = stackArg u j := rfl

theorem argRegs_map_congr {g g' : Reg → BitVec 64} (h : ∀ q, q ≠ .rax → q ≠ .rsp → g q = g' q) :
    argRegs.map g = argRegs.map g' := by
  simp only [argRegs, List.map_cons, List.map_nil]
  rw [h .rdi (by decide) (by decide), h .rsi (by decide) (by decide), h .rdx (by decide) (by decide),
    h .rcx (by decide) (by decide), h .r8 (by decide) (by decide), h .r9 (by decide) (by decide)]

theorem allArgs_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat)
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (s u : State)
    (hg : ∀ q, q ≠ .rax → q ≠ .rsp → u.gpr q = s.gpr q)
    (ha : ∀ j < nStack sig, stackArg u j = stackArg s j) :
    allArgs (sig.withScratch nm e n) u = allArgs sig s ++ [stackArg u (nStack sig)] := by
  have h := nStack_withScratch sig nm e n hk
  simp only [nStack] at h
  rw [allArgs, allArgs, h, List.range_succ, List.map_append, ← List.append_assoc,
    argRegs_map_congr hg]
  refine congrArg (· ++ _) (congrArg _ (List.map_congr_left fun j hj => ha j ?_))
  simpa using hj

/-- What `narrowS` keeps of `s`, and what it holds. -/
theorem narrowS_facts (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) (hl : Sig.noLists sig.params = true) :
    (narrowS sig e n bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes ∧
      (∀ q, q ≠ .rax → q ≠ .rsp → (narrowS sig e n bytes s).gpr q = s.gpr q) ∧
      (narrowS sig e n bytes s).mxcsr = s.mxcsr ∧
      allArgs (sig.withScratch nm e n) (narrowS sig e n bytes s) =
        allArgs sig s ++ [s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig)] ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩]
        s.mem (narrowS sig e n bytes s).mem := by
  obtain ⟨-, -, -, hmx, hg, hf, hargs, hlast⟩ := argsState_run hs hk hb hb1 hl
  have hg' : ∀ q, q ≠ .rax → q ≠ .rsp → (narrowS sig e n bytes s).gpr q = s.gpr q :=
    fun q h₁ h₂ => (hg q h₁).trans (allocState_gpr' _ _ h₂)
  refine ⟨(hg .rsp (by decide)).trans (allocState_rsp' _ _), hg', hmx, ?_, ?_⟩
  · rw [allArgs_withScratch sig nm e n hk s _ hg' fun j hj =>
      (stackArg_withRegions _ _ _ j).trans (hargs j hj)]
    exact congrArg (fun x => allArgs sig s ++ [x])
      ((stackArg_withRegions _ _ _ _).trans hlast)
  · rw [show (narrowS sig e n bytes s).mem =
      (setArgsState bytes (nStack sig) (allocState bytes s)).mem from rfl, ← allocState_rsp']
    exact hf

/-- `p - b + d` is `p - (b - d)`, for `d ≤ b`. -/
theorem sub_add_ofNat (p : Addr) {b d : Nat} (h : d ≤ b) :
    p - BitVec.ofNat 64 b + BitVec.ofNat 64 d = p - BitVec.ofNat 64 (b - d) := by
  rw [Offset.sub_ofNat_eq p (show b - d ≤ b by omega), Nat.sub_sub_self h]

/-- The regions of the contract with the buffer, in `narrowS`, are
`oldRegions`. -/
theorem allRegions_narrowS (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) (hl : Sig.noLists sig.params = true) :
    allRegions (sig.withScratch nm e n) (narrowS sig e n bytes s) = oldRegions sig e n bytes s := by
  obtain ⟨hrsp, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb hb1 hs hl
  have hlen := allArgs_length sig s hk
  have h0 : ((sig.withScratch nm e n).words abi.ptrBits).length - 6 ≠ 0 := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega
  have hm : ((sig.withScratch nm e n).words abi.ptrBits).length - 6 = nStack sig + 1 :=
    nStack_withScratch sig nm e n hk
  rw [allRegions, hargs, argArea, ite_eq_right_of_eq_false _ _ (eq_false h0), hm,
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen]
  simp only [oldRegions, List.append_assoc, List.cons_append, List.nil_append, stackArgAddr, hrsp]
  rfl

/-- The precondition of the contract without the buffer gives the one with it
in `narrowS`, if the precondition reads memory only within the buffers. -/
theorem narrowS_pre (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrowS sig e n bytes s) := by
  obtain ⟨hrsp, -, -, hargs, hf⟩ := narrowS_facts (nm := nm) hk hb hb1 hs hl
  have hall := allRegions_narrowS (nm := nm) hk hb hb1 hs hl
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega
  have hlen := allArgs_length sig s hk
  -- Addresses as offsets below `E`.
  have hscr : s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig) =
      s.gpr .rsp - BitVec.ofNat 64 (bytes - (16 + 8 * nStack sig)) := sub_add_ofNat _ (by omega)
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega)
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  -- The buffers lie outside the frame.
  have hout : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (Offset.sub_below _ hx hk)
  refine (pre_args (sig := sig.withScratch nm e n) (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk'
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [hall, hrsp, hargs]
  refine ⟨⟨.inr ?_, .inr ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by omega)]; omega
  · have hm := nStack_withScratch sig nm e n hk
    have hn : nStack sig = (sig.words abi.ptrBits).length - 6 := rfl
    simp only [nStack] at hm
    rw [toNat_sub_ofNat (by omega), hm]; omega
  · -- Pairwise disjoint.
    simp only [oldRegions]
    rw [List.pairwise_append]
    refine ⟨List.Pairwise.sublist (List.sublist_append_left _ _) hpw, ?_, fun a ha b hb _ => ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        List.Pairwise.nil, and_true, Bool.true_or, forall_const]
      refine ⟨Region.Disjoint.symm ?_, fun _ h => h.elim⟩
      rw [show s.gpr .rsp - BitVec.ofNat 64 bytes + 8 =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 8 from rfl]
      exact Offset.disjoint _ (d := 8) (n := 8 * (nStack sig + 1)) (e := 16 + 8 * nStack sig)
        (k := n * e.size) (.inl (by omega)) (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [hscr]; exact hout a ha (by omega) (by omega)
      · rw [harea]; exact hout a ha (by omega) (by omega)
  · -- The reserved stack: the frame's first quadword and the stack below it.
    intro r hr a ha
    have hr' : r = ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩ ∨
        (0 < stack ∧ r = below (s.gpr .rsp - BitVec.ofNat 64 bytes) stack) := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl rfl
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hr
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
      · exact (Region.Disjoint.symm (hout a ha (x := stack + bytes) (k := stack + bytes)
          (by omega) (by omega))).sub_left (below_below _ bytes stack)
    · rcases hr' with rfl | ⟨h0, rfl⟩
      · exact Offset.base_disjoint _ (e := 16 + 8 * nStack sig) (k := 8) (by omega) (by omega)
      · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 16 + 8 * nStack sig)
          (k := n * e.size) (by omega))
    · rw [show s.gpr .rsp - BitVec.ofNat 64 bytes + 8 =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 8 from rfl]
      rcases hr' with rfl | ⟨h0, rfl⟩
      · exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega)
      · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8)
          (k := 8 * (nStack sig + 1)) (by omega))
  · -- No buffer wraps around.
    intro a ha
    rw [show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig)).toNat +
        n * e.size ≤ 2 ^ 64
      rw [hscr, toNat_sub_ofNat (by omega)]
      have := (s.gpr .rsp).isLt
      omega
  · -- The precondition, which reads only the buffers.
    refine Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_
    refine hpre _ _ _ hlen (fun b hb x hx => (hf x fun r hr hc => ?_).symm) hpr
    simp only [List.mem_singleton] at hr; subst hr
    rw [harea] at hc
    exact hout b hb (x := bytes - 8) (k := 8 * (nStack sig + 1)) (by omega) (by omega) x hx hc

/-- The buffers lie outside the frame: `narrowS`'s memory is `s`'s there. -/
theorem narrowS_agree (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) (hl : Sig.noLists sig.params = true) :
    ∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ x, b.1.Contains x 1 →
      (narrowS sig e n bytes s).mem x = s.mem x := by
  obtain ⟨-, -, -, -, hf⟩ := narrowS_facts (nm := "") hk hb hb1 hs hl
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  intro b hb x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega)
  rw [harea] at hc
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb))).sub_right
    (Offset.sub_below _ (a := bytes - 8) (n := 8 * (nStack sig + 1)) (by omega) (by omega)) x hx hc

/-- The public data of the contract without the buffer is public in
`narrowS` for the contract with it. -/
theorem narrowS_pub (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes)).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes)).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrowS sig e n bytes s₁)
      (narrowS sig e n bytes s₂) := by
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega
  rw [pub_args hk hl] at hp
  obtain ⟨hsp, hpa⟩ := hp
  obtain ⟨e₁, -, -, a₁, -⟩ := narrowS_facts (nm := nm) hk hb hb1 h₁ hl
  obtain ⟨e₂, -, -, a₂, -⟩ := narrowS_facts (nm := nm) hk hb hb1 h₂ hl
  refine (pub_args (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk'
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [e₁, e₂, a₁, a₂, hsp]
  refine ⟨rfl, fun i hi => ?_⟩
  have l₁ := allArgs_length sig s₁ hk
  have l₂ := allArgs_length sig s₂ hk
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
requires, and whose memory and `rax` are those of the code's run. -/
theorem withStackArgScratch_run {c : Prog isa} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsafe : SpSafe c) (hd : c.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowS sig e n bytes s) t s₃) (ha : abiPreserved (narrowS sig e n bytes s) s₃)
    (hl : Sig.noLists sig.params = true) :
    Exec isa (withStackArgScratch bytes (nStack sig) c) s
        (setArgsTrace bytes (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', -, -, -, -, -⟩ := argsState_run hs hk hb hb1 hl
  obtain ⟨hrsp, hg, hmx, -, hf⟩ := narrowS_facts (nm := "") hk hb hb1 hs hl
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hwf, -⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega
  -- The frame's push and `setArgs`.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by omega, hb1, hb2, by omega⟩
  -- The regions of `narrowS`: the buffers, and the frame's buffer and copies.
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨s.gpr .rsp - BitVec.ofNat 64 a, k⟩] (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    fun ha hk => Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ ha hk (by omega)⟩
  have hscr : s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig) =
      s.gpr .rsp - BitVec.ofNat 64 (bytes - (16 + 8 * nStack sig)) := sub_add_ofNat _ (by omega)
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega)
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes s).filter (·.2)).map (·.1))
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega) (by omega)
    · simp at hf'
  have hcovR : Covers (((oldRegions sig e n bytes s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (by rw [harea]; exact hF (by omega) (by omega))
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowS sig e n bytes s).withRegions s.rd
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      setArgsState bytes (nStack sig) (allocState bytes s) by
    rw [narrowS, State.withRegions_withRegions,
      show s.rd = (allocState bytes s).rd from rfl, ← hrd',
      show ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr = (allocState bytes s).wr from rfl,
      ← hwr', State.withRegions_self]] at hw
  -- The pop.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr]
    refine ite_eq_left ⟨by omega, hb1, hb2, ?_, rfl, ?_⟩
    · rw [hrsp₃]; simp [allocState, State.setReg]
    · simp [allocState, State.setReg]
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_rsp'] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, ?_⟩, rfl, ?_⟩
  · -- The callee-saved registers.
    simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .rax := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq, hg q hqa hqs]
  · -- The return address: the code writes only its regions and below `rsp`.
    have hfs := Exec.stackFrame hsafe he (by omega)
    show s₃.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    have hR : ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
        (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun hx hk =>
      (Offset.base_disjoint_below _ (n := stack + bytes) (k := 8) (by omega)).sub_right
        (Offset.sub_below _ hx hk)
    rw [hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [harea]; exact hR (by omega) (by omega))
        (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | rfl | rfl
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha)
        · rw [hscr]; exact hR (by omega) (by omega)
        · rw [harea]; exact hR (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hrsp]
        show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint
          ⟨s.gpr .rsp - BitVec.ofNat 64 bytes - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩
        rw [BitVec.sub_sub, ← BitVec.ofNat_add]
        exact hR (by omega) (by omega)
  · -- MXCSR.
    show s₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [ha.2.2, hmx]
  · simp [popState, State.setReg]

/-- Code verified for a function whose last argument, a scratch buffer of `n`
elements `e`, is passed on the stack after the six argument registers and
`nStack sig` other stack arguments, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackArgScratch`), if its precondition and
postcondition read memory only within the function's buffers (`hpre`,
`hpost`). -/
theorem Verified.stackArgScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withStackArgScratch bytes (nStack sig) c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega
  -- Every run is `setArgs`, then the code's run from `narrowS`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrowS sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrowS sig e n bytes s) s₃ ∧
      Exec isa (withStackArgScratch bytes (nStack sig) c) s
        (setArgsTrace bytes (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowS_pre hk hb.1 hb.2.1 hpre hs hl)
    exact ⟨t, s₃, he, hq, withStackArgScratch_run hk hb hst hsafe hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hk]
    have hq' := (post_args (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb.1 hb.2.1 hs hl
    rw [hargs] at hq'
    rw [hm, hrax]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (allArgs_length sig s hk)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (allArgs_length sig s hk) (narrowS_agree hk hb.1 hb.2.1 hs hl) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pub_args hk hl).mp hp).1,
      hct _ _ _ _ _ _ (narrowS_pre hk hb.1 hb.2.1 hpre h₁ hl) (narrowS_pre hk hb.1 hb.2.1 hpre h₂ hl)
        (narrowS_pub hk hb.1 hb.2.1 h₁ h₂ hp hl) f₁ f₂]

/-- `withStackArgScratch` writes `rsp` only in its frame if its code does. -/
theorem withStackArgScratch_spSafe {bytes m : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratch bytes m c).all (fun i => !isa.writesSp i) = true := by
  have hc : ((List.range m).flatMap (copyArg bytes)).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyArg, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  simp only [withStackArgScratch, setArgs, Code.all, List.all_append, h, hc, Bool.and_true,
    Bool.true_and]
  rfl

end

end VG.X86_64
