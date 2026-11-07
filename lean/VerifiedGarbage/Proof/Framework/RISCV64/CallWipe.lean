module

public import VerifiedGarbage.Impl.CallWipe.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.CallWipe
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# A call that wipes part of a buffer afterwards (RISC-V)

`Verified.callWipe`: a function verified against `sig.contract` with `stack`
bytes of stack, whose arguments are all in registers, one of them (in
`argRegs[i]`) a writable array of `k` elements `e`, is verified against the
same contract with `stack + 32` bytes when called by `callWipe`, which then
zeroes the first `n ≤ k * e.size` bytes of the array with a function verified
against `Spec.Zeroize.zeroizeContract`, and returns the first function's
result; `Verified.callWipe'` adds to the postcondition that those bytes are
zero on return. The same theorem as AArch64's
(`Proof/Framework/AArch64/CallWipe.lean`), with the same hypotheses.

The frame (`allocd 32`) holds the return address, at `sp`, the array's
address, at `sp + 8`, and the first function's result, at `sp + 16`, each an
aligned doubleword (the contracts keep `sp` 16-byte aligned). Each callee
runs from the state after its call with the permissions of its own contract:
the buffers for the first, the `n` bytes for the zeroize function
(`WP.callAny`). The frame is memory the first function's contract reads on
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

namespace VG.RISCV64

open VG.Impl.CallWipe.RISCV64

/-! ## The frame -/

/-- The address `off` bytes into the frame of `s`'s caller. -/
abbrev slot (s : State) (off : Nat) : Addr := s.sp - BitVec.ofNat 64 32 + BitVec.ofNat 64 off

/-- A slot as `t0 + off`, with `t0` the frame's base. -/
theorem slot_t0 (s : State) (off : Nat) :
    s.sp - BitVec.ofNat 64 32 + BitVec.ofNat 64 0 + BitVec.ofNat 64 off = slot s off := by
  rw [BitVec.add_zero]

/-- The frame's slots are aligned doublewords. -/
theorem slot_aligned {s : State} (hal : s.sp.toNat % 16 = 0) (hsp : 32 ≤ s.sp.toNat) {off : Nat}
    (ho : off % 8 = 0) (h : off + 8 ≤ 32) : (slot s off).toNat % 8 = 0 := by
  have := s.sp.isLt
  rw [slot, BitVec.toNat_add, toNat_sub_ofNat' hsp, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := off) (by omega_using [h]), Nat.mod_eq_of_lt (a := s.sp.toNat - 32 + off) (by omega_using [hsp, h, this])]
  omega_using [hal, ho, hsp]

/-- The frame's slot at `off < 32` is in its region. -/
theorem slot_in (s : State) {off : Nat} (h : off + 8 ≤ 32) :
    InRegions (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr) (slot s off) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by omega_using [h])⟩

/-- So is it among all the regions. -/
theorem slot_in' (s : State) (rd : List Region) {off : Nat} (h : off + 8 ≤ 32) :
    InRegions (rd ++ ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr) (slot s off) 8 :=
  ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega_using [h])⟩

/-- The frame's slot at `off` holds the 8 bytes there. -/
theorem slot_contains (s : State) {off : Nat} (h : off + 8 ≤ 32) :
    (below s.sp 32).Contains (slot s off) 8 :=
  Offset.contains_base _ h (by omega_using [h])

/-- The frame's slots are separate. -/
theorem slot_sep (s : State) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 32)
    (hb : b + 8 ≤ 32) : Mem.Sep (slot s a) 8 (slot s b) 8 :=
  Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])

/-- The state after `addi t0, sp, 0` in the frame: `t0` its base. -/
def cwT0 (s : State) : State := (allocd 32 s).write .t0 (s.sp - BitVec.ofNat 64 32 + BitVec.ofNat 64 0)

theorem cwT0_t0 (s : State) (off : Nat) : (cwT0 s).gpr .t0 + BitVec.ofNat 64 off = slot s off := by
  rw [cwT0, RegUpd.gpr_write_self, slot_t0]

theorem cwT0_gpr (s : State) {q : Reg} (h : q ≠ .t0) : (cwT0 s).gpr q = s.gpr q :=
  RegUpd.gpr_write_of_ne _ _ h

@[simp] theorem cwT0_sp (s : State) : (cwT0 s).sp = s.sp - BitVec.ofNat 64 32 := rfl
@[simp] theorem cwT0_rd (s : State) : (cwT0 s).rd = s.rd := rfl
@[simp] theorem cwT0_wr (s : State) : (cwT0 s).wr = ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr := rfl
@[simp] theorem cwT0_mem (s : State) : (cwT0 s).mem = s.mem := rfl

/-- The state after the frame's allocation and `saveArg r`: `t0` the frame's
base, the return address at `sp`, the address in `r` at `sp + 8`. -/
def cwSave (r : Reg) (s : State) : State :=
  { cwT0 s with mem := (s.mem.writeW (slot s 0) (s.gpr .ra)).writeW (slot s 8) (s.gpr r) }

@[simp] theorem cwSave_sp (r : Reg) (s : State) : (cwSave r s).sp = s.sp - BitVec.ofNat 64 32 := rfl
@[simp] theorem cwSave_rd (r : Reg) (s : State) : (cwSave r s).rd = s.rd := rfl
@[simp] theorem cwSave_wr (r : Reg) (s : State) :
    (cwSave r s).wr = ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr := rfl

theorem cwSave_gpr (r : Reg) (s : State) {q : Reg} (h : q ≠ .t0) : (cwSave r s).gpr q = s.gpr q :=
  cwT0_gpr s h

/-- The state after `sd ra, 0(t0)`. -/
def cwS1 (s : State) : State := { cwT0 s with mem := s.mem.writeW (slot s 0) (s.gpr .ra) }

theorem saveArg_run {r : Reg} (hr : r ≠ .t0) {s : State} (hal : s.sp.toNat % 16 = 0)
    (hsp : 32 ≤ s.sp.toNat) :
    execBlock isa (saveArg r) (allocd 32 s) =
      some (cwSave r s, [.addr (slot s 0), .addr (slot s 8)]) := by
  have e₀ : exec (.addSp .t0 0) (allocd 32 s) = some (cwT0 s) := exec_addSp (by decide)
  have e₁ : exec (.store .d .ra .t0 0) (cwT0 s) = some (cwS1 s) := by
    rw [exec_store_d (by decide) (by rw [cwT0_t0]; exact slot_aligned hal hsp (by decide) (by decide))
      (by rw [cwT0_t0]; exact slot_in s (by decide)), cwT0_t0, cwT0_gpr s (by decide), cwT0_mem]
    rfl
  have e₂ : exec (.store .d r .t0 8) (cwS1 s) = some (cwSave r s) := by
    have ht : (cwS1 s).gpr .t0 + BitVec.ofNat 64 8 = slot s 8 := cwT0_t0 s 8
    rw [exec_store_d (by decide) (by rw [ht]; exact slot_aligned hal hsp (by decide) (by decide))
      (by rw [ht]; exact slot_in s (by decide)), ht]
    show some { cwS1 s with mem := (cwS1 s).mem.writeW (slot s 8) ((cwT0 s).gpr r) } = _
    rw [cwT0_gpr s hr]
    rfl
  simp only [saveArg, execBlock, isa, e₀, e₁, e₂, Option.map_some, addrs, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append]
  rw [cwT0_t0, show (cwS1 s).gpr .t0 + BitVec.ofNat 64 8 = slot s 8 from cwT0_t0 s 8]

theorem cwSave_read0 (r : Reg) (s : State) : (cwSave r s).mem.readW (slot s 0) 64 = s.gpr .ra := by
  show ((s.mem.writeW (slot s 0) (s.gpr .ra)).writeW (slot s 8) (s.gpr r)).readW (slot s 0) 64 = _
  rw [Mem.readW_writeW_sep (slot_sep s (a := 0) (b := 8) (.inl (by decide)) (by decide) (by decide))
    (by decide), Mem.readW_writeW_self64]

theorem cwSave_read8 (r : Reg) (s : State) : (cwSave r s).mem.readW (slot s 8) 64 = s.gpr r := by
  show ((s.mem.writeW (slot s 0) (s.gpr .ra)).writeW (slot s 8) (s.gpr r)).readW (slot s 8) 64 = _
  rw [Mem.readW_writeW_self64]

/-- The save writes only the frame, the 32 bytes below `sp`. -/
theorem cwSave_frame (r : Reg) (s : State) : Frame [below s.sp 32] s.mem (cwSave r s).mem :=
  Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (slot_contains s (by decide)))
    (List.mem_singleton_self _) _ (slot_contains s (by decide))

/-- `sp - 32` is 16-byte aligned. -/
theorem sub32_aligned {sp : Addr} (hal : sp.toNat % 16 = 0) (hsp : 32 ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 32).toNat % 16 = 0 := by
  rw [toNat_sub_ofNat' hsp]; omega_using [hal, hsp]

/-! ## The caller's contract -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `pre_regs`, with any leak: the precondition does not depend on it. -/
theorem pre_regs' (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (s.sp.toNat % 16 = 0 ∧ (stack = 0 ∨ stack ≤ s.sp.toNat)) ∧
      s.rd = ((Sig.bufs sig.params (regArgs sig s)).filter (!·.2)).map (·.1) ∧
      s.wr = ((Sig.bufs sig.params (regArgs sig s)).filter (·.2)).map (·.1) ∧
      (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ Sig.bufs sig.params (regArgs sig s), r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (regArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem ∧
      ∀ p ∈ Sig.alignedBufs sig.params (regArgs sig s), p.1.toNat % p.2 = 0 :=
  pre_regs (post := post) (wa := wa) hk hl

/-- `post_regs`, with any leak. -/
theorem post_regs' (hk : (sig.words abi.ptrBits).length ≤ 8) {s s' : State} :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem s'.mem
        ((s'.gpr .a0).setWidth _) :=
  post_regs (pre := pre) (wa := wa) (stack := stack) hk

/-- What the caller's contract gives of the stack. -/
theorem cw_sp (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    s.sp.toNat % 16 = 0 ∧ stack + 32 ≤ s.sp.toNat := by
  rw [pre_regs' hk hl] at hs
  exact ⟨hs.1.1, by rcases hs.1.2 with h | h <;> omega_using [h]⟩

theorem cw_below (s : State) : below s.sp (stack + 32) ∈ stackBelow s.sp (stack + 32) := by
  rw [stackBelow_pos _ (by omega_using [])]; exact List.mem_singleton_self _

/-- The buffers lie apart from the stack below `sp` that the caller's
contract reserves. -/
theorem cw_out (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ (a n : Nat), n ≤ a → a ≤ stack + 32 →
      b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 a, n⟩ := by
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, -, -, -, hres, -, -, -⟩ := hs
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
  rw [cwEntry, State.withRegions_gpr, State.callEntry_gpr _ h, cwSave_gpr r s (fun h' => h (by subst h'; decide))]

@[simp] theorem cwEntry_sp (r : Reg) (s : State) : (cwEntry r s).sp = s.sp - BitVec.ofNat 64 32 := rfl
@[simp] theorem cwEntry_mem (r : Reg) (s : State) : (cwEntry r s).mem = (cwSave r s).mem := rfl
@[simp] theorem cwEntry_rd (r : Reg) (s : State) : (cwEntry r s).rd = s.rd := rfl
@[simp] theorem cwEntry_wr (r : Reg) (s : State) : (cwEntry r s).wr = s.wr := rfl

theorem argRegs_not_link : ∀ q ∈ argRegs, q ∉ linkRegs := by decide

theorem regArgs_cwEntry (r : Reg) (s : State) : regArgs sig (cwEntry r s) = regArgs sig s :=
  List.map_congr_left fun q hq => cwEntry_gpr r s (argRegs_not_link q (List.mem_of_mem_take hq))

theorem regArgs_getD' (g : Reg → BitVec 64) {L i : Nat} (hL : L ≤ 8) (hi : i < L) :
    ((argRegs.take L).map g).getD i 0 = g (argRegs.getD i .a0) := by
  have hi8 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega_using [hL, hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hi, ite_true,
    List.getElem?_eq_getElem hi8, Option.map_some, Option.getD_some]

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
  obtain ⟨hal, hsb⟩ := cw_sp hk hl hs
  have hag := cw_agree hk hl r hs
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, hrd, hwr, hpw, hres, hnw, hpr, halb⟩ := hs
  refine (pre_regs' hk hl).mpr ?_
  rw [regArgs_cwEntry, cwEntry_sp, cwEntry_rd, cwEntry_wr]
  refine ⟨⟨sub32_aligned hal (by omega_using [hsb]), .inr ?_⟩, hrd, hwr, hpw, ?_, hnw, ?_, halb⟩
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
  (∀ q ∈ preserved, c.gpr q = s.gpr q) ∧
  c.mem.readW (slot s 0) 64 = s.gpr .ra ∧ c.mem.readW (slot s 8) 64 = s.gpr r ∧
  Frame (s.wr ++ [below s.sp (stack + 32)]) s.mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem c.mem ((c.gpr .a0).setWidth _)

/-- The frame lies apart from the writable regions and from the stack below it. -/
theorem cw_frameApart (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) {d : Nat} (hd : d ≤ stack) :
    ∀ x ∈ s.wr ++ [below (s.sp - BitVec.ofNat 64 32) d], (below s.sp 32).Disjoint x := by
  have hsb := (cw_sp hk hl hs).2
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (cw_outW hk hl hs x hx (a := 32) (n := 32) (by decide) (by omega_using [])).symm
  · simp only [List.mem_singleton] at hx; subst hx
    exact Offset.base_disjoint_below _ (by omega_using [hd, hsb])

theorem preserved_ne_t0 : ∀ q ∈ preserved, q ≠ .t0 := by decide

/-- The call of the first function. -/
theorem cw_body_wp {name : String} {body : Prog isa}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {r : Reg}
    (hd : sdepth body ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 32) leak).pre s) :
    WP isa (.call name body) (cwSave r s) (AfterBody sig post r stack s) := by
  have hsb := (cw_sp hk hl hs).2
  have hag := cw_agree hk hl r hs
  have hap := cw_frameApart hk hl hs hd
  refine WP.callAny (k := sig.contract abi pre post wa stack leak) h.1 (rd := s.rd) (wr := s.wr)
    (cw_bodyPre hk hl hpre hs)
    (Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx))
    (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx) ?_ (by omega_using [hd, hsb])
  intro c hrd hwr hsp hfr hcs hq
  rw [cwSave_sp] at hfr hsp
  refine ⟨hrd, hwr, hsp, fun q hq' => (hcs q hq').trans (cwSave_gpr r s (preserved_ne_t0 q hq')), ?_, ?_, ?_, ?_⟩
  · rw [hfr.readW (slot_contains s (by decide)) hap (by decide), cwSave_read0]
  · rw [hfr.readW (slot_contains s (by decide)) hap (by decide), cwSave_read8]
  · -- Memory changes only within the writable buffers and the stack below `sp`.
    refine Frame.trans (Frame.sub (cwSave_frame r s) fun x hx => ?_) (Frame.sub hfr fun x hx => ?_)
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        Offset.sub_below _ (by omega_using []) (by omega_using [])⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, List.mem_append_left _ hx, fun _ h => h⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun y hy =>
          below_sub (sp := s.sp) (a := sdepth body + 32) (b := stack + 32)
            (by omega_using [hd]) (by omega_using [hd, hsb]) y (below_below _ 32 _ y hy)⟩
  · -- The postcondition, which reads the memory on entry only within the buffers.
    rw [post_regs' hk] at hq
    rw [show (cwSave r s).callEntry.withRegions s.rd s.wr = cwEntry r s from rfl, regArgs_cwEntry,
      cwEntry_mem, State.withRegions_mem, State.withRegions_gpr] at hq
    exact hpost _ _ _ _ _ (regArgs_length sig s hk) (fun b hb x hx => hag b hb x hx) hq

/-! ## The zeroize function's arguments -/

/-- The value `lenArg n` leaves in `a1`. -/
def lenVal (n : Nat) : BitVec 64 :=
  if n < 2048 then BitVec.ofInt 64 n else BitVec.ofInt 64 2047 + BitVec.ofInt 64 ((n : Int) - 2047)

theorem lenVal_toNat {n : Nat} (hn : n < 4095) : (lenVal n).toNat = n := by
  unfold lenVal
  split
  · rw [show BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n from BitVec.ofInt_natCast _ _,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  · rename_i h
    rw [show ((n : Int) - 2047) = ((n - 2047 : Nat) : Int) by omega_using [h],
      BitVec.ofInt_natCast, show (2047 : Int) = ((2047 : Nat) : Int) from rfl, BitVec.ofInt_natCast,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
    omega_using [h]

theorem lenArg_run (n : Nat) (hn : n < 4095) (X : State) :
    execBlock isa (lenArg n) X = some (X.write .a1 (lenVal n), []) := by
  unfold lenArg lenVal
  split
  · rename_i h
    simp only [execBlock, isa, exec_li (show imm12 (n : Int) by unfold imm12; omega_using [h]),
      Option.map_some, addrs, List.map_nil, List.nil_append]
  · rename_i h
    simp only [execBlock, isa, exec_li (show imm12 (2047 : Int) by decide),
      exec_addi (show imm12 ((n : Int) - 2047) by unfold imm12; omega_using [h, hn]), Option.map_some,
      addrs, List.map_nil, List.nil_append, RegUpd.gpr_write_self, RegUpd.write_write]

/-- `t0` at `sp`. -/
def cwZ1 (c : State) : State := c.write .t0 (c.sp + BitVec.ofNat 64 0)

theorem cwZ1_t0 (c : State) (off : Nat) : (cwZ1 c).gpr .t0 + BitVec.ofNat 64 off = c.sp + BitVec.ofNat 64 off := by
  rw [cwZ1, RegUpd.gpr_write_self, BitVec.add_zero]

/-- The memory after `sd a0, 16(t0)`. -/
abbrev cwZeroMem (c : State) : Mem := c.mem.writeW (c.sp + BitVec.ofNat 64 16) (c.gpr .a0)

/-- The state after `sd a0, 16(t0)`. -/
def cwZ2 (c : State) : State := { cwZ1 c with mem := cwZeroMem c }

/-- The state after `ld a0, 8(t0)`. -/
def cwZ3 (c : State) : State := (cwZ2 c).write .a0 ((cwZeroMem c).readW (c.sp + BitVec.ofNat 64 8) 64)

/-- The state after `zeroArgs n`. -/
def cwZero (n : Nat) (c : State) : State := (cwZ3 c).write .a1 (lenVal n)

@[simp] theorem cwZero_mem (n : Nat) (c : State) : (cwZero n c).mem = cwZeroMem c := rfl
@[simp] theorem cwZero_sp (n : Nat) (c : State) : (cwZero n c).sp = c.sp := rfl
@[simp] theorem cwZero_rd (n : Nat) (c : State) : (cwZero n c).rd = c.rd := rfl
@[simp] theorem cwZero_wr (n : Nat) (c : State) : (cwZero n c).wr = c.wr := rfl

theorem cwZero_gpr (n : Nat) (c : State) {q : Reg} (h₀ : q ≠ .a0) (h₁ : q ≠ .a1) (ht : q ≠ .t0) :
    (cwZero n c).gpr q = c.gpr q := by
  rw [cwZero, RegUpd.gpr_write_of_ne _ _ h₁, cwZ3, RegUpd.gpr_write_of_ne _ _ h₀]
  exact RegUpd.gpr_write_of_ne _ _ ht

theorem cwZero_a0 (n : Nat) (c : State) :
    (cwZero n c).gpr .a0 = c.mem.readW (c.sp + BitVec.ofNat 64 8) 64 := by
  rw [cwZero, RegUpd.gpr_write_of_ne _ _ (by decide), cwZ3, RegUpd.gpr_write_self, cwZeroMem,
    Mem.readW_writeW_sep (Offset.sep c.sp (d := 8) (n := 8) (e := 16) (k := 8)
      (.inl (by decide)) (by decide) (by decide)) (by decide)]

theorem cwZero_a1 {n : Nat} (hn : n < 4095) (c : State) : ((cwZero n c).gpr .a1).toNat = n := by
  rw [cwZero, RegUpd.gpr_write_self, lenVal_toNat hn]

theorem zeroArgs_run (n : Nat) (hn : n < 4095) {c : State}
    (ha16 : (c.sp + BitVec.ofNat 64 16).toNat % 8 = 0) (ha8 : (c.sp + BitVec.ofNat 64 8).toNat % 8 = 0)
    (hw : InRegions c.wr (c.sp + BitVec.ofNat 64 16) 8)
    (hr : InRegions (c.rd ++ c.wr) (c.sp + BitVec.ofNat 64 8) 8) :
    execBlock isa (zeroArgs n) c =
      some (cwZero n c, [.addr (c.sp + BitVec.ofNat 64 16), .addr (c.sp + BitVec.ofNat 64 8)]) := by
  have e₀ : exec (.addSp .t0 0) c = some (cwZ1 c) := exec_addSp (by decide)
  have e₁ : exec (.store .d .a0 .t0 16) (cwZ1 c) = some (cwZ2 c) := by
    rw [exec_store_d (by decide) (by rw [cwZ1_t0]; exact ha16) (by rw [cwZ1_t0]; exact hw), cwZ1_t0,
      show (cwZ1 c).gpr .a0 = c.gpr .a0 from RegUpd.gpr_write_of_ne _ _ (by decide)]
    rfl
  have e₂ : exec (.load .d .a0 .t0 8) (cwZ2 c) = some (cwZ3 c) := by
    have ht : (cwZ2 c).gpr .t0 + BitVec.ofNat 64 8 = c.sp + BitVec.ofNat 64 8 := cwZ1_t0 c 8
    rw [exec_load_d (by decide) (by rw [ht]; exact ha8) (by rw [ht]; exact hr), ht]
    rfl
  have hz : zeroArgs n = [.addSp .t0 0, .store .d .a0 .t0 16, .load .d .a0 .t0 8] ++ lenArg n := rfl
  rw [hz, execBlock_append]
  simp only [execBlock, isa, e₀, e₁, e₂, Option.map_some, Option.bind_some]
  rw [show execBlock VG.RISCV64.isa (lenArg n) (cwZ3 c) = _ from lenArg_run n hn _]
  simp only [Option.map_some, addrs, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_nil]
  rw [cwZ1_t0, show (cwZ2 c).gpr .t0 + BitVec.ofNat 64 8 = c.sp + BitVec.ofNat 64 8 from cwZ1_t0 c 8]
  rfl

end

end VG.RISCV64
