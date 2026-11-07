module

public import VerifiedGarbage.Impl.CallWipe.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.CallWipe
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# A call that wipes part of a buffer afterwards (AArch64)

`Verified.callWipe`: a function verified against `sig.contract` with `stack`
bytes of stack, whose arguments are all in registers, one of them (in
`argRegs[i]`) a writable array of `k` elements `e`, is verified against the
same contract with `stack + 32` bytes when called by `callWipe`, which then
zeroes the first `n ≤ k * e.size` bytes of the array with a function verified
against `Spec.Zeroize.zeroizeContract`, and returns the first function's
result; `Verified.callWipe'` adds to the postcondition that those bytes are
zero on return. The same theorem as x86-64's
(`Proof/Framework/X86_64/CallWipe.lean`), with the same hypotheses.

The frame (`allocated 32`) holds the return address, at `sp`, the array's
address, at `sp + 8`, and the first function's result, at `sp + 16`. Each
callee runs from the state after its call with the permissions of its own
contract: the buffers for the first, the `n` bytes for the zeroize function
(`WP.callFV`). The frame is memory the first function's contract reads on
entry, which the caller's says nothing of: the precondition, postcondition
and leak must read the memory on entry only within the function's buffers
(`hpre`, `hpost`, `hleak`). The zeroize function writes the array after the
first function returned: the postcondition must read the memory on return
only within the buffers apart from the array (`hpostOut`), which the
precondition keeps apart from the others (it is writable).

Constant time: the frame's accesses depend on `sp` alone, each callee is
constant time, and the zeroize function's arguments, the array's address and
`n`, are public.
-/

@[expose] public section

namespace VG.AArch64

open VG.Impl.CallWipe.AArch64

/-! ## The frame -/

/-- The address `off` bytes into the frame of `s`'s caller. -/
abbrev slot (s : State) (off : Nat) : Addr := s.sp - BitVec.ofNat 64 32 + BitVec.ofNat 64 off

/-- The state after the frame's allocation and `saveArg r`: the return
address at `sp`, the address in `r` at `sp + 8`. -/
def cwSave (r : Reg) (s : State) : State :=
  { allocated 32 s with
    mem := (s.mem.write (slot s 0) 8 (s.gpr .x30)).write (slot s 8) 8 (s.gpr r) }

@[simp] theorem cwSave_gpr (r : Reg) (s : State) : (cwSave r s).gpr = s.gpr := rfl
@[simp] theorem cwSave_sp (r : Reg) (s : State) : (cwSave r s).sp = s.sp - BitVec.ofNat 64 32 := rfl
@[simp] theorem cwSave_rd (r : Reg) (s : State) : (cwSave r s).rd = s.rd := rfl
@[simp] theorem cwSave_wr (r : Reg) (s : State) :
    (cwSave r s).wr = ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr := rfl
@[simp] theorem cwSave_v (r : Reg) (s : State) : (cwSave r s).v = s.v := rfl

/-- The frame's slot at `off < 32` is in its region. -/
theorem slot_in (s : State) {off : Nat} (h : off + 8 ≤ 32) :
    InRegions (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr) (slot s off) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by omega_using [h])⟩

theorem exec_strSp' {s : State} {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.strSp t off) s = some { s with mem := s.mem.write (s.sp + BitVec.ofNat 64 off) 8 (s.gpr t) } := by
  simp only [reduceExec, ho, and_self, ite_true, State.store, h, State.read, BitVec.setWidth_eq]

theorem exec_ldrSp' {s : State} {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.ldrSp t off) s = some (s.write .x t (s.mem.read (s.sp + BitVec.ofNat 64 off) 8)) := by
  simp only [reduceExec, ho, and_self, ite_true, State.load, h, Option.map_some, BitVec.setWidth_eq]

/-- So is it among all the regions. -/
theorem slot_in' (s : State) (rd : List Region) {off : Nat} (h : off + 8 ≤ 32) :
    InRegions (rd ++ ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr) (slot s off) 8 :=
  ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega_using [h])⟩

theorem saveArg_run (r : Reg) (s : State) :
    execBlock isa (saveArg r) (allocated 32 s) =
      some (cwSave r s, [.addr (slot s 0), .addr (slot s 8)]) := by
  have e₁ : exec (.strSp .x30 0) (allocated 32 s) =
      some { allocated 32 s with mem := s.mem.write (slot s 0) 8 (s.gpr .x30) } :=
    exec_strSp' (s := allocated 32 s) (by decide) (slot_in s (by decide))
  have e₂ : exec (.strSp r 8) { allocated 32 s with mem := s.mem.write (slot s 0) 8 (s.gpr .x30) } =
      some (cwSave r s) :=
    exec_strSp' (s := { allocated 32 s with mem := s.mem.write (slot s 0) 8 (s.gpr .x30) }) (by decide)
      (slot_in s (by decide))
  simp only [saveArg, execBlock, isa, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rfl

/-- A slot as an address below `sp`. -/
theorem slot_eq (s : State) {off : Nat} (h : off ≤ 32) :
    slot s off = s.sp - BitVec.ofNat 64 (32 - off) := by
  rw [Offset.sub_ofNat_eq s.sp (a := 32 - off) (b := 32) (by omega_using []),
    show 32 - (32 - off) = off by omega_using [h]]

/-- The frame's slot at `off` holds the 8 bytes there. -/
theorem slot_contains (s : State) {off : Nat} (h : off + 8 ≤ 32) :
    (below s.sp 32).Contains (slot s off) 8 :=
  Offset.contains_base _ h (by omega_using [h])

/-- The frame's slots are separate. -/
theorem slot_sep (s : State) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 32)
    (hb : b + 8 ≤ 32) : Mem.Sep (slot s a) 8 (slot s b) 8 :=
  Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])

theorem cwSave_read0 (r : Reg) (s : State) : (cwSave r s).mem.read (slot s 0) 8 = s.gpr .x30 := by
  rw [cwSave, Mem.read_write_sep (slot_sep s (a := 0) (b := 8) (.inl (by decide)) (by decide) (by decide)) (by decide),
    read_write_self]

theorem cwSave_read8 (r : Reg) (s : State) : (cwSave r s).mem.read (slot s 8) 8 = s.gpr r := by
  rw [cwSave, read_write_self]

/-- The save writes only the frame, the 32 bytes below `sp`. -/
theorem cwSave_frame (r : Reg) (s : State) : Frame [below s.sp 32] s.mem (cwSave r s).mem :=
  Frame.write (Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (slot_contains s (by decide)))
    (List.mem_singleton_self _) _ (slot_contains s (by decide))

/-! ## The caller's contract -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- Without lists of slices, a function's memory is its buffers. -/
theorem regRegions_noLists (hl : Sig.noLists sig.params = true) (s : State) :
    regRegions sig s = Sig.bufs sig.params (regArgs sig s) := by
  simp only [regRegions, Sig.lists_of_noLists 64 s.mem sig.params _ hl, List.map_nil, List.append_nil]

/-- The precondition of a contract whose arguments are all in registers,
without lists of slices. -/
theorem pre_regs' (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
      s.rd = ((Sig.bufs sig.params (regArgs sig s)).filter (!·.2)).map (·.1) ∧
      s.wr = ((Sig.bufs sig.params (regArgs sig s)).filter (·.2)).map (·.1) ∧
      (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ Sig.bufs sig.params (regArgs sig s), r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (regArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem := by
  rw [pre_regs hk, regRegions_noLists hl]

/-- What the caller's contract gives of the stack. -/
theorem cw_sp (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) : stack + 32 ≤ s.sp.toNat := by
  rw [pre_regs' hk hl] at hs
  rcases hs.1 with h | h <;> omega_using [h]

theorem cw_below (s : State) : below s.sp (stack + 32) ∈ stackBelow s.sp (stack + 32) := by
  rw [stackBelow_pos _ (by omega_using [])]; exact List.mem_singleton_self _

/-- The buffers lie apart from the stack below `sp` that the caller's
contract reserves. -/
theorem cw_out (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ (a n : Nat), n ≤ a → a ≤ stack + 32 →
      b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 a, n⟩ := by
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  intro b hb a n hn ha
  exact (Region.Disjoint.symm (hres _ (cw_below s) b hb)).sub_right
    (Offset.sub_below _ ha (by omega_using [hn, ha]))

/-- So do the writable regions. -/
theorem cw_outW (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    ∀ x ∈ s.wr, ∀ (a n : Nat), n ≤ a → a ≤ stack + 32 → x.Disjoint ⟨s.sp - BitVec.ofNat 64 a, n⟩ := by
  have hout := cw_out hk hl hs
  rw [pre_regs' hk hl] at hs
  intro x hx a n hn ha
  rw [hs.2.2.1] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hout b (List.mem_filter.mp hb).1 a n hn ha

/-- The state the first function runs from, with the permissions of its
contract: after the call. -/
def cwEntry (r : Reg) (s : State) : State := (cwSave r s).callEntry.withRegions s.rd s.wr

theorem cwEntry_gpr (r : Reg) (s : State) {q : Reg} (h : q ∉ linkRegs) : (cwEntry r s).gpr q = s.gpr q := by
  rw [cwEntry, State.withRegions_gpr, State.callEntry_gpr _ h, cwSave_gpr]

@[simp] theorem cwEntry_sp (r : Reg) (s : State) : (cwEntry r s).sp = s.sp - BitVec.ofNat 64 32 := rfl
@[simp] theorem cwEntry_mem (r : Reg) (s : State) : (cwEntry r s).mem = (cwSave r s).mem := rfl
@[simp] theorem cwEntry_rd (r : Reg) (s : State) : (cwEntry r s).rd = s.rd := rfl
@[simp] theorem cwEntry_wr (r : Reg) (s : State) : (cwEntry r s).wr = s.wr := rfl

theorem regArgs_getD' (g : Reg → BitVec 64) {L i : Nat} (hL : L ≤ 8) (hi : i < L) :
    ((argRegs.take L).map g).getD i 0 = g (argRegs.getD i .x0) := by
  have hi8 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega_using [hL, hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hi, ite_true,
    List.getElem?_eq_getElem hi8, Option.map_some, Option.getD_some]

theorem argRegs_not_link : ∀ q ∈ argRegs, q ∉ linkRegs := by decide

theorem regArgs_cwEntry (r : Reg) (s : State) : regArgs sig (cwEntry r s) = regArgs sig s :=
  List.map_congr_left fun q hq => cwEntry_gpr r s (argRegs_not_link q (List.mem_of_mem_take hq))

/-- The entry's memory is the caller's in the buffers. -/
theorem cw_agree (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (r : Reg) {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ x, b.1.Contains x 1 → (cwEntry r s).mem x = s.mem x :=
  fun b hb x hx => cwSave_frame r s x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact cw_out hk hl hs b hb (a := 32) (n := 32) (by decide) (by omega_using []) x hx hc

/-- The caller's precondition gives the first function's at its entry. -/
theorem cw_bodyPre (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {r : Reg} (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cwEntry r s) := by
  have hsb := cw_sp hk hl hs
  have hag := cw_agree hk hl r hs
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  refine (pre_regs' hk hl).mpr ?_
  rw [regArgs_cwEntry, cwEntry_sp, cwEntry_rd, cwEntry_wr]
  refine ⟨.inr ?_, hrd, hwr, hpw, ?_, hnw, ?_⟩
  · rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hsb]
  · intro x hx a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hx
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
      exact (hres _ (cw_below s) a ha).sub_left (below_below _ 32 stack)
  · exact hpre _ _ _ (regArgs_length sig s hk) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- What the run of the first function leaves, from the caller's state `s`. -/
def AfterBody (sig : Sig) (post : sig.Post abi.ptrBits) (r : Reg) (stack : Nat) (s c : State) : Prop :=
  c.rd = s.rd ∧ c.wr = ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr ∧ c.sp = s.sp - BitVec.ofNat 64 32 ∧
  (∀ q ∈ preserved, q ≠ .x30 → c.gpr q = s.gpr q) ∧
  (∀ q ∈ preservedV, (c.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64) ∧
  c.mem.read (slot s 0) 8 = s.gpr .x30 ∧ c.mem.read (slot s 8) 8 = s.gpr r ∧
  Frame (s.wr ++ [below s.sp (stack + 32)]) s.mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem c.mem ((c.gpr .x0).setWidth _)

/-- The frame lies apart from the writable regions and from the stack below it. -/
theorem cw_frameApart (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) {d : Nat} (hd : d ≤ stack) :
    ∀ x ∈ s.wr ++ [below (s.sp - BitVec.ofNat 64 32) d], (below s.sp 32).Disjoint x := by
  have hsb := cw_sp hk hl hs
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (cw_outW hk hl hs x hx (a := 32) (n := 32) (by decide) (by omega_using [])).symm
  · simp only [List.mem_singleton] at hx; subst hx
    exact Offset.base_disjoint_below _ (by omega_using [hd, hsb])

/-- The call of the first function. -/
theorem cw_body_wp {name : String} {body : Prog isa}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {r : Reg}
    (hd : 16 * body.aarch64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    WP isa (.call name body) (cwSave r s) (AfterBody sig post r stack s) := by
  have hsb := cw_sp hk hl hs
  have hag := cw_agree hk hl r hs
  have hap := cw_frameApart hk hl hs hd
  refine WP.callFV (k := sig.contract abi pre post wa stack leak) h.1 (rd := s.rd) (wr := s.wr)
    (cw_bodyPre hk hl hpre hs)
    (Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx))
    (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx) ?_ (by omega_using [hd, hsb])
  intro c hrd hwr hsp hfr hcs hv hq
  rw [cwSave_sp] at hfr hsp
  refine ⟨hrd, hwr, hsp, fun q hq hq30 => (hcs q hq hq30).trans (congrFun (cwSave_gpr r s) q), hv, ?_, ?_, ?_, ?_⟩
  · rw [hfr.read (slot_contains s (by decide)) hap (by decide), cwSave_read0]
  · rw [hfr.read (slot_contains s (by decide)) hap (by decide), cwSave_read8]
  · -- Memory changes only within the writable buffers and the stack below `sp`.
    refine Frame.trans (Frame.sub (cwSave_frame r s) fun x hx => ?_) (Frame.sub hfr fun x hx => ?_)
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        Offset.sub_below _ (by omega_using []) (by omega_using [])⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, List.mem_append_left _ hx, fun _ h => h⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun y hy => below_sub (sp := s.sp) (a := 16 * body.aarch64Depth + 32) (b := stack + 32)
            (by omega_using [hd]) (by omega_using [hd, hsb]) y (below_below _ 32 _ y hy)⟩
  · -- The postcondition, which reads the memory on entry only within the buffers.
    rw [post_regs hk] at hq
    rw [show (cwSave r s).callEntry.withRegions s.rd s.wr = cwEntry r s from rfl, regArgs_cwEntry,
      cwEntry_mem, State.withRegions_mem, State.withRegions_gpr] at hq
    exact hpost _ _ _ _ _ (regArgs_length sig s hk) (fun b hb x hx => hag b hb x hx) hq

/-! ## The zeroize function's arguments -/

/-- The memory after `str x0, [sp, #16]`. -/
abbrev cwZeroMem (c : State) : Mem := c.mem.write (c.sp + BitVec.ofNat 64 16) 8 (c.gpr .x0)

/-- The state after `zeroArgs n`. -/
def cwZero (n : Nat) (c : State) : State :=
  (({ c with mem := cwZeroMem c }).write .x .x0 ((cwZeroMem c).read (c.sp + BitVec.ofNat 64 8) 8)).write .x .x1
    ((BitVec.ofNat 16 n).setWidth 64 <<< (16 * 0))

@[simp] theorem cwZero_mem (n : Nat) (c : State) : (cwZero n c).mem = cwZeroMem c := rfl
@[simp] theorem cwZero_sp (n : Nat) (c : State) : (cwZero n c).sp = c.sp := rfl
@[simp] theorem cwZero_rd (n : Nat) (c : State) : (cwZero n c).rd = c.rd := rfl
@[simp] theorem cwZero_wr (n : Nat) (c : State) : (cwZero n c).wr = c.wr := rfl
@[simp] theorem cwZero_v (n : Nat) (c : State) : (cwZero n c).v = c.v := rfl

theorem cwZero_gpr (n : Nat) (c : State) {q : Reg} (h₀ : q ≠ .x0) (h₁ : q ≠ .x1) :
    (cwZero n c).gpr q = c.gpr q := by
  rw [cwZero, RegUpd.gpr_write_of_ne _ _ _ h₁, RegUpd.gpr_write_of_ne _ _ _ h₀]

theorem cwZero_x0 (n : Nat) (c : State) :
    (cwZero n c).gpr .x0 = c.mem.read (c.sp + BitVec.ofNat 64 8) 8 := by
  rw [cwZero, RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq,
    Mem.read_write_sep (Offset.sep c.sp (d := 8) (n := 8) (e := 16) (k := 8) (.inl (by decide)) (by decide)
      (by decide)) (by decide)]

theorem cwZero_x1 {n : Nat} (hn : n < 2 ^ 16) (c : State) : ((cwZero n c).gpr .x1).toNat = n := by
  rw [cwZero, RegUpd.gpr_write_self, BitVec.setWidth_eq, Nat.mul_zero, BitVec.shiftLeft_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_using [hn])]

theorem zeroArgs_run (n : Nat) {c : State} (hw : InRegions c.wr (c.sp + BitVec.ofNat 64 16) 8)
    (hr : InRegions (c.rd ++ c.wr) (c.sp + BitVec.ofNat 64 8) 8) :
    execBlock isa (zeroArgs n) c =
      some (cwZero n c, [.addr (c.sp + BitVec.ofNat 64 16), .addr (c.sp + BitVec.ofNat 64 8)]) := by
  have e₁ : exec (.strSp .x0 16) c = some { c with mem := cwZeroMem c } := exec_strSp' (by decide) hw
  have e₂ : exec (.ldrSp .x0 8) { c with mem := cwZeroMem c } =
      some (({ c with mem := cwZeroMem c }).write .x .x0 ((cwZeroMem c).read (c.sp + BitVec.ofNat 64 8) 8)) :=
    exec_ldrSp' (s := { c with mem := cwZeroMem c }) (by decide) hr
  simp only [zeroArgs, execBlock, isa, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, reduceExec]
  rfl

/-- What the caller's contract gives of the array: its region is within the
writable ones, and does not wrap. -/
theorem cw_array (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {r : Reg} {e : Elem} {k : Nat} {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s)) :
    (⟨s.gpr r, k * e.size⟩ : Region) ∈ s.wr ∧ (s.gpr r).toNat + k * e.size ≤ 2 ^ 64 := by
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, -, hwr, -, -, hnw, -⟩ := hs
  exact ⟨hwr ▸ List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨harr, rfl⟩, rfl⟩, hnw _ harr⟩

end

/-! ## The zeroize function's contract -/

theorem zeroize_bufs (X : State) :
    Sig.bufs Spec.Zeroize.zeroizeSig.params (regArgs Spec.Zeroize.zeroizeSig X) =
      [(⟨X.gpr .x0, (X.gpr .x1).toNat * 1⟩, true)] := rfl

/-- The zeroize function's precondition, from what it says of the state. -/
theorem zeroize_pre_of {zst n : Nat} {X : State} (hn : (X.gpr .x1).toNat = n)
    (hwf : zst = 0 ∨ zst ≤ X.sp.toNat) (hrd : X.rd = []) (hwr : X.wr = [⟨X.gpr .x0, n⟩])
    (hres : ∀ x ∈ stackBelow X.sp zst, x.Disjoint ⟨X.gpr .x0, n⟩)
    (hb : (X.gpr .x0).toNat + n ≤ 2 ^ 64) :
    (Spec.Zeroize.zeroizeContract abi zst).pre X := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pre_regs' (by decide) (by decide)).mpr ?_
  rw [zeroize_bufs, hn, Nat.mul_one]
  refine ⟨hwf, hrd, hwr, List.pairwise_singleton _ _, fun x hx a ha => ?_, fun a ha => ?_, ?_⟩
  · simp only [List.mem_singleton] at ha; subst ha; exact hres x hx
  · simp only [List.mem_singleton] at ha; subst ha; exact hb
  · rw [Curry.apply_const]; trivial

/-- The zeroize function's postcondition. -/
theorem zeroize_post_iff {zst : Nat} {X Y : State} :
    (Spec.Zeroize.zeroizeContract abi zst).post X Y ↔
      Spec.Zeroize.bytesAt Y.mem (X.gpr .x0) ((X.gpr .x1).setWidth 64).toNat =
        Spec.Zeroize.zeros ((X.gpr .x1).setWidth 64).toNat := Iff.rfl

/-- The zeroize function's public data. -/
theorem zeroize_pub_of {zst : Nat} {X₁ X₂ : State} (hsp : X₁.sp = X₂.sp)
    (h0 : X₁.gpr .x0 = X₂.gpr .x0) (h1 : X₁.gpr .x1 = X₂.gpr .x1) :
    (Spec.Zeroize.zeroizeContract abi zst).pub X₁ X₂ := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pub_regs (by decide)).mpr ⟨⟨hsp, trivial⟩, fun i _ => ?_, ?_⟩
  · show ([X₁.gpr .x0, X₁.gpr .x1].getD i 0).setWidth _ = ([X₂.gpr .x0, X₂.gpr .x1].getD i 0).setWidth _
    rw [h0, h1]
  · intro R hR
    rw [Sig.descs_of_noLists 64 _ _ (by decide)] at hR
    exact absurd hR List.not_mem_nil

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {r : Reg}

theorem cwZero_x0' {s c : State} (hc : AfterBody sig post r stack s c) (n : Nat) :
    (cwZero n c).gpr .x0 = s.gpr r := by
  rw [cwZero_x0, hc.2.2.1]; exact hc.2.2.2.2.2.2.1

/-- The zeroize function's entry state. -/
theorem cwZeroEntry {s c : State} (hc : AfterBody sig post r stack s c) {n : Nat} (hn : n < 2 ^ 16)
    (R : Region) :
    ((cwZero n c).callEntry.withRegions [] [R]).gpr .x0 = s.gpr r ∧
      (((cwZero n c).callEntry.withRegions [] [R]).gpr .x1).toNat = n ∧
      ((cwZero n c).callEntry.withRegions [] [R]).sp = s.sp - BitVec.ofNat 64 32 := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    cwZero_x0' hc, cwZero_x1 hn]
  exact ⟨rfl, rfl, hc.2.2.1⟩

/-- The zeroize function's precondition, at its entry. -/
theorem cw_zeroPre (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n zst : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16) (hzs : zst ≤ stack) (hc : AfterBody sig post r stack s c) :
    (Spec.Zeroize.zeroizeContract abi zst).pre
      ((cwZero n c).callEntry.withRegions [] [⟨s.gpr r, n⟩]) := by
  have hsb := cw_sp hk hl hs
  have hA := cw_out hk hl hs _ harr
  have hnw := (cw_array hk hl hs harr).2
  have hsubA : Region.Sub ⟨s.gpr r, n⟩ ⟨s.gpr r, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨h0, h1, hsp⟩ := cwZeroEntry hc hn16 ⟨s.gpr r, n⟩
  refine zeroize_pre_of h1 (.inr ?_) rfl (by rw [h0]; rfl) ?_ (by rw [h0]; omega_using [hnw, hn])
  · rw [hsp, toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hsb, hzs]
  · rw [hsp, h0]
    intro x hx
    rcases Nat.eq_zero_or_pos zst with hz0 | hz0
    · subst hz0; simp [stackBelow] at hx
    · rw [stackBelow_pos _ hz0, List.mem_singleton] at hx; subst hx
      exact (hA (zst + 32) (zst + 32) (Nat.le_refl _) (by omega_using [hzs])).symm.sub_right hsubA
        |>.sub_left (below_below _ 32 zst)

/-- The zeroize function's public data, at its entry, if the array's
address is public. -/
theorem cw_zeroPub {n zst : Nat} (hn : n < 2 ^ 16) {s₁ s₂ c₁ c₂ : State} (hsp : s₁.sp = s₂.sp)
    (hpp : s₁.gpr r = s₂.gpr r) (hc₁ : AfterBody sig post r stack s₁ c₁)
    (hc₂ : AfterBody sig post r stack s₂ c₂) :
    (Spec.Zeroize.zeroizeContract abi zst).pub ((cwZero n c₁).callEntry.withRegions [] [⟨s₁.gpr r, n⟩])
      ((cwZero n c₂).callEntry.withRegions [] [⟨s₂.gpr r, n⟩]) := by
  obtain ⟨d₁, i₁, p₁⟩ := cwZeroEntry hc₁ hn ⟨s₁.gpr r, n⟩
  obtain ⟨d₂, i₂, p₂⟩ := cwZeroEntry hc₂ hn ⟨s₂.gpr r, n⟩
  exact zeroize_pub_of (by rw [p₁, p₂, hsp]) (by rw [d₁, d₂, hpp])
    (BitVec.eq_of_toNat_eq (by rw [i₁, i₂]))

/-- What the zeroize function's run leaves, from the caller's state `s`: the
first function's, but for the first `n` bytes of the array, which are zero,
and its result, at `sp + 16` of the frame. -/
def AfterZero (sig : Sig) (post : sig.Post abi.ptrBits) (r : Reg) (stack n : Nat) (s e : State) : Prop :=
  ∃ c, AfterBody sig post r stack s c ∧
    e.rd = s.rd ∧ e.wr = ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr ∧ e.sp = s.sp - BitVec.ofNat 64 32 ∧
    (∀ q ∈ preserved, q ≠ .x30 → e.gpr q = s.gpr q) ∧
    (∀ q ∈ preservedV, (e.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64) ∧
    e.mem.read (slot s 0) 8 = s.gpr .x30 ∧ e.mem.read (slot s 16) 8 = c.gpr .x0 ∧
    Frame (s.wr ++ [below s.sp (stack + 32)]) s.mem e.mem ∧
    Frame [⟨s.gpr r, n⟩, below s.sp (stack + 32)] c.mem e.mem ∧
    Spec.Zeroize.bytesAt e.mem (s.gpr r) n = Spec.Zeroize.zeros n

/-- The zeroize function may write only the first `n` bytes of the array. -/
theorem cw_zeroCovers (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hc : AfterBody sig post r stack s c) :
    Covers [⟨s.gpr r, n⟩] (cwZero n c).wr :=
  Covers.one ⟨_, by rw [cwZero_wr, hc.2.1]; exact List.mem_cons_of_mem _ (cw_array hk hl hs harr).1, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn⟩

/-- The frame lies apart from the array and from the stack below it. -/
theorem cw_frameApartZ (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) {d : Nat} (hd : d ≤ stack) :
    ∀ x ∈ [⟨s.gpr r, n⟩] ++ [below (s.sp - BitVec.ofNat 64 32) d], (below s.sp 32).Disjoint x := by
  have hsb := cw_sp hk hl hs
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simp only [List.mem_singleton] at hx; subst hx
    exact (cw_out hk hl hs _ harr (a := 32) (n := 32) (by decide) (by omega_using [])).symm.sub_right
      (Region.sub_prefix hn)
  · simp only [List.mem_singleton] at hx; subst hx
    exact Offset.base_disjoint_below _ (by omega_using [hd, hsb])

/-- The call of the zeroize function. -/
theorem cw_zero_wp {zname : String} {zcode : Prog isa} {zst : Nat}
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hzd : 16 * zcode.aarch64Depth ≤ zst) (hzs : zst ≤ stack)
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16) (hc : AfterBody sig post r stack s c) :
    WP isa (.call zname zcode) (cwZero n c) (AfterZero sig post r stack n s) := by
  have hsb := cw_sp hk hl hs
  obtain ⟨hAw, -⟩ := cw_array hk hl hs harr
  have hsubA : Region.Sub ⟨s.gpr r, n⟩ ⟨s.gpr r, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨hrdc, hwrc, hspc, hcsc, hvc, h0c, -, hfc, -⟩ := id hc
  have hcw := cw_zeroCovers hk hl hs harr hn hc
  have hap := cw_frameApartZ hk hl hs harr hn (d := 16 * zcode.aarch64Depth) (by omega_using [hzd, hzs])
  refine WP.callFV (k := Spec.Zeroize.zeroizeContract abi zst) hz.1 (rd := []) (wr := [⟨s.gpr r, n⟩])
    (cw_zeroPre hk hl hs harr hn hn16 hzs hc) (Covers.right hcw) hcw ?_ (by omega_using [hzd, hzs, hsb])
  intro g hrd hwr hsp hfr hcs hv hq
  rw [cwZero_sp, hspc] at hfr hsp
  -- The result's slot, which `zeroArgs` writes.
  have fD : Frame [below s.sp 32] c.mem (cwZero n c).mem := by
    rw [cwZero_mem, cwZeroMem, hspc]
    exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (slot_contains s (by decide))
  have hbelowZ : Region.Sub (below (s.sp - BitVec.ofNat 64 32) (16 * zcode.aarch64Depth))
      (below s.sp (stack + 32)) := fun y hy =>
    below_sub (sp := s.sp) (a := 16 * zcode.aarch64Depth + 32) (b := stack + 32)
      (by omega_using [hzd, hzs]) (by omega_using [hzd, hzs, hsb]) y (below_below _ 32 _ y hy)
  have hframeSub : Region.Sub (below s.sp 32) (below s.sp (stack + 32)) :=
    below_sub (by omega_using []) (by omega_using [hsb])
  refine ⟨c, hc, by rw [hrd, cwZero_rd, hrdc], by rw [hwr, cwZero_wr, hwrc], hsp,
    fun q hq hq30 => ?_, fun q hq => (hv q hq).trans (hvc q hq), ?_, ?_, ?_, ?_, ?_⟩
  · have hq0 : q ≠ .x0 := fun h => by subst h; simp [preserved] at hq
    have hq1 : q ≠ .x1 := fun h => by subst h; simp [preserved] at hq
    rw [hcs q hq hq30, cwZero_gpr n c hq0 hq1, hcsc q hq hq30]
  · -- The return address, at `sp`, which neither `zeroArgs` nor the zeroize function writes.
    rw [hfr.read (slot_contains s (by decide)) hap (by decide), cwZero_mem, cwZeroMem, hspc,
      Mem.read_write_sep (slot_sep s (a := 0) (b := 16) (.inl (by decide)) (by decide) (by decide))
        (by decide), h0c]
  · -- The result, at `sp + 16`, which the zeroize function does not write.
    rw [hfr.read (slot_contains s (by decide)) hap (by decide), cwZero_mem, cwZeroMem, hspc,
      read_write_self]
  · refine Frame.trans hfc (Frame.trans (Frame.sub fD fun x hx => ?_) (Frame.sub hfr fun x hx => ?_))
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hframeSub⟩
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_left _ hAw, hsubA⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hbelowZ⟩
  · refine Frame.trans (Frame.sub fD fun x hx => ?_) (Frame.sub hfr fun x hx => ?_)
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hframeSub⟩
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hbelowZ⟩
  · -- The zeroize function's postcondition.
    obtain ⟨h0, h1, -⟩ := cwZeroEntry hc hn16 ⟨s.gpr r, n⟩
    rw [zeroize_post_iff, h0, BitVec.setWidth_eq, h1, State.withRegions_mem] at hq
    exact hq

/-! ## The whole call -/

/-- The state after `restore`. -/
def cwRestore (g : State) : State :=
  (g.write .x .x0 (g.mem.read (g.sp + BitVec.ofNat 64 16) 8)).write .x .x30
    (g.mem.read (g.sp + BitVec.ofNat 64 0) 8)

theorem restore_run {g : State} (h16 : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 16) 8)
    (h0 : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 0) 8) :
    execBlock isa restore g =
      some (cwRestore g, [.addr (g.sp + BitVec.ofNat 64 16), .addr (g.sp + BitVec.ofNat 64 0)]) := by
  have e₁ : exec (.ldrSp .x0 16) g = some (g.write .x .x0 (g.mem.read (g.sp + BitVec.ofNat 64 16) 8)) :=
    exec_ldrSp' (by decide) h16
  have e₂ : exec (.ldrSp .x30 0) (g.write .x .x0 (g.mem.read (g.sp + BitVec.ofNat 64 16) 8)) =
      some (cwRestore g) :=
    exec_ldrSp' (s := g.write .x .x0 (g.mem.read (g.sp + BitVec.ofNat 64 16) 8)) (by decide) h0
  simp only [restore, execBlock, isa, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, RegUpd.sp_write]

/-- A run of `callWipe` from the caller's state `s`: it keeps what the
calling convention requires, its postcondition is the first function's if
that reads the memory on return only within the buffers apart from the
array (`hout`), and the first `n` bytes of the array are zero. -/
theorem cw_wp {name zname : String} {body zcode : Prog isa} {zst : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hd : 16 * body.aarch64Depth ≤ stack) (hzd : 16 * zcode.aarch64Depth ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {e : Elem} {k n : Nat} (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x) :
    WP isa (callWipe r n name body zname zcode) s fun g =>
      abiPreserved s g ∧ (sig.contract abi pre post wa (stack + 32) leak).post s g ∧
        Spec.Zeroize.bytesAt g.mem (s.gpr r) n = Spec.Zeroize.zeros n := by
  have hsb := cw_sp hk hl hs
  have hout' := cw_out hk hl hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_using [hsb]) ?_
  refine WP.seq (WP.block ⟨_, saveArg_run r s, ?_⟩)
  refine WP.seq (WP.mono (cw_body_wp h hk hl hd hpre hpost hs) fun c hc => ?_)
  obtain ⟨hrdc, hwrc, hspc, -⟩ := id hc
  refine WP.seq (WP.block ⟨_, zeroArgs_run n (by rw [hwrc, hspc]; exact slot_in s (by decide))
    (by rw [hwrc, hspc]; exact slot_in' s c.rd (by decide)), ?_⟩)
  refine WP.seq (WP.mono (cw_zero_wp hz hzd hzs hk hl hs harr hn hn16 hc) fun g hg => ?_)
  obtain ⟨c', hc', hrdg, hwrg, hspg, hcsg, hvg, h0g, h16g, hfs, hfc, hz0⟩ := hg
  refine WP.block ⟨_, restore_run (by rw [hwrg, hspg]; exact slot_in' s g.rd (by decide))
    (by rw [hwrg, hspg]; exact slot_in' s g.rd (by decide)), ?_⟩
  have hx30 : (cwRestore g).gpr .x30 = s.gpr .x30 := by
    rw [cwRestore, RegUpd.gpr_write_self, BitVec.setWidth_eq, hspg]; exact h0g
  have hx0 : (cwRestore g).gpr .x0 = c'.gpr .x0 := by
    rw [cwRestore, RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq, hspg]
    exact h16g
  refine ⟨⟨fun q hq => ?_, ?_, fun q hq => hvg q hq⟩, ?_, hz0⟩
  · -- The callee-saved registers.
    show (cwRestore g).gpr q = s.gpr q
    by_cases hq30 : q = .x30
    · subst hq30; exact hx30
    · have hq0 : q ≠ .x0 := fun h => by subst h; simp [preserved] at hq
      rw [cwRestore, RegUpd.gpr_write_of_ne _ _ _ hq30, RegUpd.gpr_write_of_ne _ _ _ hq0]
      exact hcsg q hq hq30
  · show (cwRestore g).sp + BitVec.ofNat 64 32 = s.sp
    rw [cwRestore, RegUpd.sp_write, RegUpd.sp_write, hspg, BitVec.sub_add_cancel]
  · -- The postcondition, which reads the memory on return only within the buffers apart from the array.
    rw [post_regs hk]
    show Curry.apply _ post (regArgs sig s) s.mem (cwRestore g).mem (((cwRestore g).gpr .x0).setWidth _)
    rw [hx0]
    refine hout c'.mem _ _ (fun b hb hbA x hx => ?_) hc'.2.2.2.2.2.2.2.2
    refine (hfc x fun R hR hc => ?_).symm
    rcases List.mem_cons.mp hR with rfl | hR
    · exact hbA x hx (Region.sub_prefix hn x hc)
    · simp only [List.mem_singleton] at hR; subst hR
      exact hout' b hb (stack + 32) (stack + 32) (Nat.le_refl _) (Nat.le_refl _) x hx hc

/-- The caller's public data is the first function's at its entry. -/
theorem cw_bodyPub (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (r : Reg) {s₁ s₂ : State} (h₁ : (sig.contract abi pre post wa (stack + 32) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + 32) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + 32) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cwEntry r s₁) (cwEntry r s₂) := by
  rw [pub_regs hk] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa, -⟩ := hp
  rw [regArgs_cwEntry, regArgs_cwEntry, cwEntry_sp, cwEntry_sp, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa, fun R hR => ?_⟩
  · cases leak with
    | none => trivial
    | some f =>
      show Curry.apply _ f (regArgs sig s₁) (cwEntry r s₁).mem =
        Curry.apply _ f (regArgs sig s₂) (cwEntry r s₂).mem
      rw [hleak _ _ _ (regArgs_length sig s₁ hk) (cw_agree hk hl r h₁),
        hleak _ _ _ (regArgs_length sig s₂ hk) (cw_agree hk hl r h₂)]
      exact hlk
  · rw [Sig.descs_of_noLists 64 _ _ hl] at hR
    exact absurd hR List.not_mem_nil

end

/-- Two runs of a block, whose traces agree. -/
theorem RelCT.block_of {P Q : State → State → Prop} {l : List Instr}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ u₁ u₂ t, execBlock isa l s₁ = some (u₁, t) ∧
      execBlock isa l s₂ = some (u₂, t) ∧ Q u₁ u₂) :
    RelCT isa P (.block l) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨u₁, u₂, t, h₁, h₂, hq⟩ := h _ _ hp
  rw [Exec.block_iff, h₁, Option.some.injEq, Prod.mk.injEq] at e₁
  rw [Exec.block_iff, h₂, Option.some.injEq, Prod.mk.injEq] at e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hq⟩

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- Code verified against `sig.contract` with `stack` bytes of stack, for a
function whose arguments are all in registers, the one in `argRegs[i]` a
writable array of `k` elements `e`, is verified with `stack + 32` bytes when
called by `callWipe`, which then zeroes the first `n` bytes of the array with
code verified against `Spec.Zeroize.zeroizeContract` (with `zst ≤ stack`
bytes of stack), against the contract whose postcondition `post'` follows
from the function's and those bytes being zero (`hwiped`). The
precondition, postcondition and leak must read the memory on entry only
within the function's buffers (`hpre`, `hpost`, `hleak`), and the
postcondition the memory on return only within those apart from the array
(`hpostOut`). -/
theorem Verified.callWipe' {post' : sig.Post abi.ptrBits} {name zname : String}
    {body zcode : Prog isa} {zst : Nat} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {k n i : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16)
    (hd : 16 * body.aarch64Depth ≤ stack) (hzd : 16 * zcode.aarch64Depth ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hwiped : ∀ vs m m' x, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) post vs m m' x →
      Spec.Zeroize.bytesAt m' (vs.getD i 0) n = Spec.Zeroize.zeros n →
        Curry.apply (sig.words abi.ptrBits) post' vs m m' x)
    (hsat : ∃ s, (sig.contract abi pre post' wa (stack + 32) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.AArch64.callWipe (argRegs.getD i .x0) n name body zname zcode)
      (sig.contract abi pre post' wa (stack + 32) leak) := by
  subst hi
  have hL : (sig.words abi.ptrBits).length = (ps₁.flatMap fun p => p.2.words 64).length + 1 +
      (ps₂.flatMap fun p => p.2.words 64).length := by
    show (sig.params.flatMap fun p => p.2.words 64).length = _
    rw [hps, List.flatMap_append, List.flatMap_cons]
    simp only [List.length_append, Param.words.eq_2, List.length_cons, List.length_nil]
    omega
  have hiL : (ps₁.flatMap fun p => p.2.words 64).length < (sig.words abi.ptrBits).length := by
    rw [hL]; omega
  generalize hr' : argRegs.getD (ps₁.flatMap fun p => p.2.words 64).length .x0 = r
  have hget : ∀ s : State, (regArgs sig s).getD (ps₁.flatMap fun p => p.2.words 64).length 0 = s.gpr r :=
    fun s => by rw [← hr']; exact regArgs_getD' s.gpr (by omega_using [hk]) hiL
  -- The array, among the buffers.
  have harr : ∀ s : State, (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s) := by
    intro s
    rw [← hget s, hps]
    exact Sig.bufs_mem_array (pb := 64) ps₂ ps₁ (regArgs sig s) (by rw [regArgs_length sig s hk, hL]; omega)
  -- Its address is public.
  have hpubA : ∀ s₁ s₂, (sig.contract abi pre post wa (stack + 32) leak).pub s₁ s₂ → s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ hp
    have hP : (sig.params.flatMap (·.2.pubs)).getD (ps₁.flatMap fun p => p.2.words 64).length false = true := by
      rw [hps]; exact (Sig.pub_array (pb := 64) ps₁ ps₂).1
    have hW : ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD
        (ps₁.flatMap fun p => p.2.words 64).length 64 = 64 := by
      show ((sig.params.flatMap fun p => p.2.words 64).map (·.bits 64)).getD _ 64 = 64
      rw [hps]; exact (Sig.pub_array (pb := 64) ps₁ ps₂).2
    have h2 := congrArg BitVec.toNat (((pub_regs hk).mp hp).2.1 _ hP)
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hW, hget, hget, Nat.mod_eq_of_lt (BitVec.isLt _),
      Nat.mod_eq_of_lt (BitVec.isLt _)] at h2
    exact BitVec.eq_of_toNat_eq h2
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + 32) leak).pre s → ∀ m₁ m₂ x,
      (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    rw [pre_regs' hk hl] at hs
    exact hpostOut _ _ _ _ _ (regArgs_length sig s hk) hs.2.2.2.1 (by rw [hget]; exact hag) hq
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · obtain ⟨t, g, he, habi, hq, hz0⟩ :=
      cw_wp (r := r) h hz hk hl hd hzd hzs hpre hpost hn hn16 hs (harr s) (hout s hs)
    refine ⟨t, g, he, habi, ?_⟩
    rw [post_regs hk] at hq ⊢
    exact hwiped _ _ _ _ (regArgs_length sig s hk) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract abi pre post' wa (stack + 32) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + 32) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + 32) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + 32) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + 32) leak).pre σ₂ := h₂
    have hp' : (sig.contract abi pre post wa (stack + 32) leak).pub σ₁ σ₂ := hp
    have hsp12 : σ₁.sp = σ₂.sp := ((pub_regs hk).mp hp').1.1
    have hpp := hpubA _ _ hp'
    have hcov : ∀ σ : State, Covers (σ.rd ++ σ.wr) ((cwSave r σ).rd ++ (cwSave r σ).wr) ∧
        Covers σ.wr (cwSave r σ).wr := fun σ =>
      ⟨Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx⟩
    refine RelCT.mono (P := fun a b => a = allocated 32 σ₁ ∧ b = allocated 32 σ₂) ?_
      (fun a b hab => hab.2) (fun _ _ h => h)
    -- The return address and the array's address are saved.
    refine RelCT.seq (R := fun a b => a = cwSave r σ₁ ∧ b = cwSave r σ₂)
      (RelCT.block_of fun a b hab => ?_) ?_
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, saveArg_run r σ₁, by rw [saveArg_run r σ₂]; simp only [slot, hsp12], rfl, rfl⟩
    -- The first function.
    refine RelCT.seq (R := fun c₁ c₂ => AfterBody sig post r stack σ₁ c₁ ∧ AfterBody sig post r stack σ₂ c₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterBody sig post r stack σ₁) (F₂ := AfterBody sig post r stack σ₂)
        (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨σ₁.rd, σ₁.wr, σ₂.rd, σ₂.wr, cw_bodyPre hk hl hpre h₁', cw_bodyPre hk hl hpre h₂',
          cw_bodyPub hk hl r h₁' h₂' hp' hleak, (hcov σ₁).1, (hcov σ₁).2, (hcov σ₂).1, (hcov σ₂).2⟩
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨cw_body_wp h hk hl hd hpre hpost h₁', cw_body_wp h hk hl hd hpre hpost h₂'⟩
    -- The zeroize function's arguments.
    refine RelCT.seq (R := fun d₁ d₂ => (∃ c, AfterBody sig post r stack σ₁ c ∧ d₁ = cwZero n c) ∧
      (∃ c, AfterBody sig post r stack σ₂ c ∧ d₂ = cwZero n c)) (RelCT.block_of fun c₁ c₂ hc => ?_) ?_
    · obtain ⟨hc₁, hc₂⟩ := hc
      have w₁ : InRegions c₁.wr (c₁.sp + BitVec.ofNat 64 16) 8 := by
        rw [hc₁.2.1, hc₁.2.2.1]; exact slot_in σ₁ (by decide)
      have r₁ : InRegions (c₁.rd ++ c₁.wr) (c₁.sp + BitVec.ofNat 64 8) 8 := by
        rw [hc₁.2.1, hc₁.2.2.1]; exact slot_in' σ₁ c₁.rd (by decide)
      have w₂ : InRegions c₂.wr (c₂.sp + BitVec.ofNat 64 16) 8 := by
        rw [hc₂.2.1, hc₂.2.2.1]; exact slot_in σ₂ (by decide)
      have r₂ : InRegions (c₂.rd ++ c₂.wr) (c₂.sp + BitVec.ofNat 64 8) 8 := by
        rw [hc₂.2.1, hc₂.2.2.1]; exact slot_in' σ₂ c₂.rd (by decide)
      refine ⟨_, _, _, zeroArgs_run n w₁ r₁, ?_, ⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩
      rw [zeroArgs_run n w₂ r₂, hc₁.2.2.1, hc₂.2.2.1, hsp12]
    -- The zeroize function.
    refine RelCT.seq (R := fun g₁ g₂ => AfterZero sig post r stack n σ₁ g₁ ∧ AfterZero sig post r stack n σ₂ g₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterZero sig post r stack n σ₁) (F₂ := AfterZero sig post r stack n σ₂)
        (RelCT.callEx hz.1 hz.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨[], [⟨σ₁.gpr r, n⟩], [], [⟨σ₂.gpr r, n⟩], cw_zeroPre hk hl h₁' (harr σ₁) hn hn16 hzs hc₁,
          cw_zeroPre hk hl h₂' (harr σ₂) hn hn16 hzs hc₂, cw_zeroPub hn16 hsp12 hpp hc₁ hc₂,
          Covers.right (cw_zeroCovers hk hl h₁' (harr σ₁) hn hc₁), cw_zeroCovers hk hl h₁' (harr σ₁) hn hc₁,
          Covers.right (cw_zeroCovers hk hl h₂' (harr σ₂) hn hc₂), cw_zeroCovers hk hl h₂' (harr σ₂) hn hc₂⟩
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨cw_zero_wp hz hzd hzs hk hl h₁' (harr σ₁) hn hn16 hc₁,
          cw_zero_wp hz hzd hzs hk hl h₂' (harr σ₂) hn hn16 hc₂⟩
    -- The result and the return address are restored.
    · refine RelCT.block_of fun g₁ g₂ hg => ?_
      obtain ⟨⟨c₁, _, -, hw₁, hs₁, -⟩, ⟨c₂, _, -, hw₂, hs₂, -⟩⟩ := hg
      have i₁ : ∀ off, off + 8 ≤ 32 → InRegions (g₁.rd ++ g₁.wr) (g₁.sp + BitVec.ofNat 64 off) 8 :=
        fun off h => by rw [hw₁, hs₁]; exact slot_in' σ₁ g₁.rd h
      have i₂ : ∀ off, off + 8 ≤ 32 → InRegions (g₂.rd ++ g₂.wr) (g₂.sp + BitVec.ofNat 64 off) 8 :=
        fun off h => by rw [hw₂, hs₂]; exact slot_in' σ₂ g₂.rd h
      refine ⟨_, cwRestore g₂, _, restore_run (i₁ 16 (by decide)) (i₁ 0 (by decide)), ?_, trivial⟩
      rw [restore_run (i₂ 16 (by decide)) (i₂ 0 (by decide)), hs₁, hs₂, hsp12]

/-- `Verified.callWipe'`, with the function's postcondition. -/
theorem Verified.callWipe {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {k n i : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16)
    (hd : 16 * body.aarch64Depth ≤ stack) (hzd : 16 * zcode.aarch64Depth ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + 32) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.AArch64.callWipe (argRegs.getD i .x0) n name body zname zcode)
      (sig.contract abi pre post wa (stack + 32) leak) :=
  Verified.callWipe' h hz hk hl hps hi hn hn16 hd hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak

end

end VG.AArch64
