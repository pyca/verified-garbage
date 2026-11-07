module

public import VerifiedGarbage.Impl.CallWipe.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.CallWipe
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Sig

/-!
# A call that wipes part of a buffer afterwards (x86-64)

`Verified.callWipe`: a function verified against `sig.contract` with `stack`
bytes of stack, whose arguments are all in registers, one of them (in
`argRegs[i]`) a writable array of `k` elements `e`, is verified against the
same contract with `stack + 24` bytes when called by `callWipe`, which then
zeroes the first `n ≤ k * e.size` bytes of the array with a function verified
against `Spec.Zeroize.zeroizeContract`, and returns the first function's
result; `Verified.callWipe'` adds to the postcondition that those bytes are
zero on return.

The frame (`allocState 16`) holds the array's address, at `rsp + 8`, and the
first function's result, at `rsp`. Each callee runs from the state after its
call with the permissions of its own contract: the buffers for the first, the
`n` bytes for the zeroize function (`WP.call_sp_mx`). The frame and the
return addresses are memory the first function's contract reads on entry,
which the caller's says nothing of: the precondition, postcondition and leak
must read the memory on entry only within the function's buffers (`hpre`,
`hpost`, `hleak`). The zeroize function writes the array after the first
function returned: the postcondition must read the memory on return only
within the buffers apart from the array (`hpostOut`), which the precondition
keeps apart from the others (it is writable).

Constant time: the frame's accesses depend on `rsp` alone, each callee is
constant time, and the zeroize function's arguments, the array's address and
`n`, are public.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.CallWipe.X86_64

/-! ## Argument registers -/

theorem argRegs_ne_rsp : ∀ q ∈ argRegs, q ≠ .rsp := by decide

theorem regArgs_congr (sig : Sig) {s s' : State} (h : ∀ q, q ≠ .rsp → s'.gpr q = s.gpr q) :
    regArgs sig s' = regArgs sig s :=
  List.map_congr_left fun q hq => h q (argRegs_ne_rsp q (List.mem_of_mem_take hq))

theorem regArgs_getD (g : Reg → BitVec 64) {L i : Nat} (hL : L ≤ 6) (hi : i < L) :
    ((argRegs.take L).map g).getD i 0 = g (argRegs.getD i .rax) := by
  have hi6 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hi, ite_true,
    List.getElem?_eq_getElem hi6, Option.map_some, Option.getD_some]

/-! ## Contracts whose arguments are all in registers, with a leak -/

/-- The public data of a contract whose arguments are all in registers, and
what it may leak. -/
theorem pubL_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.gpr .rsp = s₂.gpr .rsp ∧ leakAgree leak (regArgs sig s₁) s₁.mem (regArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 6 := hk
    simpa [argRegs] using this
  have hD := fun vs => Sig.descs_of_noLists 64 sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', ite_true, hD, List.not_mem_nil, false_implies,
    implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

/-! ## The blocks -/

theorem ea_rsp8 (s : State) : s.ea { base := .rsp, disp := 8 } = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

theorem ea_rsp0 (s : State) : s.ea { base := .rsp } = s.gpr .rsp := BitVec.add_zero _

theorem sub16_add8 (sp : Addr) : sp - BitVec.ofNat 64 16 + BitVec.ofNat 64 8 = sp - BitVec.ofNat 64 8 :=
  (Offset.sub_ofNat_eq sp (show 8 ≤ 16 by decide)).symm

theorem sub16_sub8 (sp : Addr) : sp - BitVec.ofNat 64 16 - 8 = sp - BitVec.ofNat 64 24 := by
  rw [BitVec.sub_sub]; rfl

theorem allocState16_rsp (s : State) : (allocState 16 s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16 := by
  simp [allocState, State.setReg]

theorem allocState16_gpr (s : State) {q : Reg} (h : q ≠ .rsp) : (allocState 16 s).gpr q = s.gpr q := by
  simp [allocState, State.setReg, h]

/-- The state after the frame's push and `saveArg r`: the address in `r` at
`rsp - 8` on entry. -/
def cwSave (r : Reg) (s : State) : State :=
  { allocState 16 s with mem := s.mem.writeW (s.gpr .rsp - BitVec.ofNat 64 8) (s.gpr r) }

@[simp] theorem cwSave_rd (r : Reg) (s : State) : (cwSave r s).rd = s.rd := rfl
@[simp] theorem cwSave_wr (r : Reg) (s : State) :
    (cwSave r s).wr = ⟨s.gpr .rsp - BitVec.ofNat 64 16, 16⟩ :: s.wr := rfl
@[simp] theorem cwSave_mxcsr (r : Reg) (s : State) : (cwSave r s).mxcsr = s.mxcsr := rfl
theorem cwSave_gpr (r : Reg) (s : State) : (cwSave r s).gpr = (allocState 16 s).gpr := rfl
theorem cwSave_mem (r : Reg) (s : State) :
    (cwSave r s).mem = s.mem.writeW (s.gpr .rsp - BitVec.ofNat 64 8) (s.gpr r) := rfl

theorem saveArg_run {r : Reg} (hr : r ≠ .rsp) (s : State) :
    execBlock isa (saveArg r) (allocState 16 s) =
      some (cwSave r s, [.addr (s.gpr .rsp - BitVec.ofNat 64 8)]) := by
  have hin : InRegions (allocState 16 s).wr (s.gpr .rsp - BitVec.ofNat 64 16 + BitVec.ofNat 64 8) 8 :=
    ⟨_, List.mem_cons_self .., Offset.contains_base _ (by decide) (by decide)⟩
  rw [sub16_add8] at hin
  simp only [saveArg, execBlock, isa, reduceExec, State.store64, ea_rsp8, allocState16_rsp, sub16_add8,
    allocState16_gpr s hr, hin, ite_true, addrs, List.map_cons, List.map_nil, Option.map_some,
    List.append_nil]
  rfl

/-- The state after `zeroArgs n`. -/
def cwZero (n : Nat) (c : State) : State :=
  (({ c with mem := c.mem.writeW (c.gpr .rsp) (c.gpr .rax) }).setReg .rdi
    ((c.mem.writeW (c.gpr .rsp) (c.gpr .rax)).readW (c.gpr .rsp + BitVec.ofNat 64 8) 64)).setReg32 .rsi
    (BitVec.ofNat 32 n)

@[simp] theorem cwZero_rd (n : Nat) (c : State) : (cwZero n c).rd = c.rd := rfl
@[simp] theorem cwZero_wr (n : Nat) (c : State) : (cwZero n c).wr = c.wr := rfl
@[simp] theorem cwZero_mxcsr (n : Nat) (c : State) : (cwZero n c).mxcsr = c.mxcsr := rfl
theorem cwZero_mem (n : Nat) (c : State) : (cwZero n c).mem = c.mem.writeW (c.gpr .rsp) (c.gpr .rax) := rfl
theorem cwZero_gpr (n : Nat) (c : State) {q : Reg} (h₁ : q ≠ .rdi) (h₂ : q ≠ .rsi) :
    (cwZero n c).gpr q = c.gpr q := by
  simp [cwZero, State.setReg32, State.setReg, h₁, h₂]
theorem cwZero_rdi (n : Nat) (c : State) :
    (cwZero n c).gpr .rdi = (c.mem.writeW (c.gpr .rsp) (c.gpr .rax)).readW (c.gpr .rsp + BitVec.ofNat 64 8) 64 := by
  simp [cwZero, State.setReg32, State.setReg]
theorem cwZero_rsi (n : Nat) (c : State) : (cwZero n c).gpr .rsi = (BitVec.ofNat 32 n).setWidth 64 := by
  simp [cwZero, State.setReg32, State.setReg]

theorem zeroArgs_run (n : Nat) {c : State} (hF : ⟨c.gpr .rsp, 16⟩ ∈ c.wr) :
    execBlock isa (zeroArgs n) c =
      some (cwZero n c, [.addr (c.gpr .rsp), .addr (c.gpr .rsp + BitVec.ofNat 64 8)]) := by
  have h0 : InRegions c.wr (c.gpr .rsp) 8 := ⟨_, hF, by simp [Region.Contains]⟩
  have h8 : InRegions ((c.rd ++ c.wr)) (c.gpr .rsp + BitVec.ofNat 64 8) 8 :=
    ⟨_, List.mem_append_right _ hF, Offset.contains_base _ (by decide) (by decide)⟩
  simp only [zeroArgs, execBlock, isa, reduceExec, State.store64, ea_rsp0, ea_rsp8, h0, ite_true,
    Option.map_some, readSrc, State.load64, h8, readSrc32, addrs, srcAddrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rfl

theorem restoreRet_run {e : State} (h : InRegions (e.rd ++ e.wr) (e.gpr .rsp) 8) :
    execBlock isa restoreRet e =
      some (e.setReg .rax (e.mem.readW (e.gpr .rsp) 64), [.addr (e.gpr .rsp)]) := by
  simp only [restoreRet, execBlock, isa, reduceExec, readSrc, State.load64, ea_rsp0, h, ite_true,
    Option.map_some, addrs, srcAddrs, List.map_cons, List.map_nil, List.append_nil]

/-- The state the first function runs from, with the permissions of its
contract: after the call. -/
def cwEntry (r : Reg) (s : State) : State := (cwSave r s).callEntry.withRegions s.rd s.wr

theorem cwEntry_gpr (r : Reg) (s : State) {q : Reg} (h : q ≠ .rsp) : (cwEntry r s).gpr q = s.gpr q := by
  rw [cwEntry, State.withRegions_gpr, State.callEntry_gpr _ h, cwSave_gpr, allocState16_gpr s h]

theorem cwEntry_rsp (r : Reg) (s : State) : (cwEntry r s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 24 := by
  rw [cwEntry, State.withRegions_gpr, State.callEntry_rsp, cwSave_gpr, allocState16_rsp, sub16_sub8]

theorem cwEntry_mem (r : Reg) (s : State) : (cwEntry r s).mem =
    (s.mem.writeW (s.gpr .rsp - BitVec.ofNat 64 8) (s.gpr r)).writeW (s.gpr .rsp - BitVec.ofNat 64 24)
      (s.unknowns 0) := by
  rw [cwEntry, State.withRegions_mem, State.callEntry_mem, cwSave_mem, cwSave_gpr, allocState16_rsp,
    sub16_sub8]
  rfl

/-- The entry writes only the 24 bytes below `rsp`. -/
theorem cwEntry_frame (r : Reg) (s : State) :
    Frame [below (s.gpr .rsp) 24] s.mem (cwEntry r s).mem := by
  rw [cwEntry_mem]
  exact Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
    (Offset.contains_below _ (a := 8) (n := 8) (by decide) (by decide) (by decide)))
    (List.mem_singleton_self _) _ (Offset.contains_below _ (a := 24) (n := 8) (by decide) (by decide) (by decide))

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What the caller's contract gives of the stack. -/
theorem cw_sp (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) : stack + 24 ≤ (s.gpr .rsp).toNat := by
  rw [pre_regs hk hl] at hs
  rcases hs.1 with h | h <;> omega_using [h]

/-- The buffers lie apart from the stack below `rsp` that the caller's
contract reserves. -/
theorem cw_out (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ (a n : Nat), n ≤ a → a ≤ stack + 24 →
      b.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 a, n⟩ := by
  rw [pre_regs hk hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hbelow : below (s.gpr .rsp) (stack + 24) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + 24) : List Region) := by
    rw [stackBelow_pos _ (by omega_using [])]; simp
  intro b hb a n hn ha
  exact (Region.Disjoint.symm (hres _ hbelow b hb)).sub_right
    (Offset.sub_below _ ha (by omega_using [hn, ha]))

/-- So do the writable regions. -/
theorem cw_outW (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) :
    ∀ x ∈ s.wr, ∀ (a n : Nat), n ≤ a → a ≤ stack + 24 → x.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 a, n⟩ := by
  have hout := cw_out hk hl hs
  rw [pre_regs hk hl] at hs
  intro x hx a n hn ha
  rw [hs.2.2.1] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hout b (List.mem_filter.mp hb).1 a n hn ha

/-- The entry's memory is the caller's in the buffers. -/
theorem cw_agree (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    (r : Reg) {s : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ x, b.1.Contains x 1 → (cwEntry r s).mem x = s.mem x :=
  fun b hb x hx => cwEntry_frame r s x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact cw_out hk hl hs b hb (a := 24) (n := 24) (by decide) (by omega_using []) x hx hc

/-- The caller's precondition gives the first function's at its entry. -/
theorem cw_bodyPre (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    {r : Reg} (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cwEntry r s) := by
  have hsb := cw_sp hk hl hs
  have hag := cw_agree hk hl r hs
  have hargs : regArgs sig (cwEntry r s) = regArgs sig s := regArgs_congr sig fun q hq => cwEntry_gpr r s hq
  rw [pre_regs hk hl] at hs
  obtain ⟨-, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hbelow : below (s.gpr .rsp) (stack + 24) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + 24) : List Region) := by
    rw [stackBelow_pos _ (by omega_using [])]; simp
  refine (pre_regs hk hl).mpr ?_
  rw [hargs, cwEntry_rsp]
  refine ⟨.inr ?_, hrd, hwr, hpw, ?_, hnw, ?_⟩
  · rw [toNat_sub_ofNat (by omega_using [hsb])]; omega_using [hsb]
  · intro x hx a ha
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hres _ hbelow a ha).sub_left (Offset.sub_below _ (by omega_using []) (by omega_using []))
    · rcases Nat.eq_zero_or_pos stack with h0 | h0
      · subst h0; simp [stackBelow] at hx
      · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
        exact (hres _ hbelow a ha).sub_left (below_below _ 24 stack)
  · exact hpre _ _ _ (regArgs_length sig s hk) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The caller's public data is the first function's at its entry. -/
theorem cw_bodyPub (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    (r : Reg) {s₁ s₂ : State} (h₁ : (sig.contract abi pre post wa (stack + 24) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + 24) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + 24) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cwEntry r s₁) (cwEntry r s₂) := by
  have a₁ : regArgs sig (cwEntry r s₁) = regArgs sig s₁ := regArgs_congr sig fun q hq => cwEntry_gpr r s₁ hq
  have a₂ : regArgs sig (cwEntry r s₂) = regArgs sig s₂ := regArgs_congr sig fun q hq => cwEntry_gpr r s₂ hq
  rw [pubL_regs hk hl] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  rw [a₁, a₂, cwEntry_rsp, cwEntry_rsp, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa⟩
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ f (regArgs sig s₁) (cwEntry r s₁).mem = Curry.apply _ f (regArgs sig s₂) (cwEntry r s₂).mem
    rw [hleak _ _ _ (regArgs_length sig s₁ hk) (cw_agree hk hl r h₁),
      hleak _ _ _ (regArgs_length sig s₂ hk) (cw_agree hk hl r h₂)]
    exact hlk

/-- What the run of the first function leaves, from the caller's state `s`. -/
def AfterBody (sig : Sig) (post : sig.Post abi.ptrBits) (r : Reg) (stack : Nat) (s c : State) : Prop :=
  c.rd = s.rd ∧ c.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 16, 16⟩ :: s.wr ∧
  (∀ q ∈ calleeSaved, c.gpr q = (allocState 16 s).gpr q) ∧
  c.mem.readW (s.gpr .rsp - BitVec.ofNat 64 8) 64 = s.gpr r ∧
  Frame (s.wr ++ [below (s.gpr .rsp) (stack + 24)]) s.mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem c.mem ((c.gpr .rax).setWidth _) ∧
  c.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- The call of the first function. -/
theorem cw_body_wp {name : String} {body : Prog isa}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) {r : Reg}
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ stack)
    (hst : stack + 32 ≤ 2 ^ 64)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) :
    WP isa (.call name body) (cwSave r s) (AfterBody sig post r stack s) := by
  have hsb := cw_sp hk hl hs
  have hag := cw_agree hk hl r hs
  have hW := cw_outW hk hl hs
  have hargs : regArgs sig (cwEntry r s) = regArgs sig s := regArgs_congr sig fun q hq => cwEntry_gpr r s hq
  refine WP.call_sp_mx (k := sig.contract abi pre post wa stack leak) h.1 (SpSafe.of_all hsp)
    (by omega_using [hd, hst]) (rd := s.rd) (wr := s.wr) (cw_bodyPre hk hl hpre hs)
    (Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx))
    (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx) ?_
  intro c hrd hwr hcs hfr _ ⟨s₂, hm, hg, hq⟩ hmx
  have hB : below ((cwSave r s).gpr .rsp) (body.x86_64Depth + 8) =
      ⟨s.gpr .rsp - BitVec.ofNat 64 (16 + (body.x86_64Depth + 8)), body.x86_64Depth + 8⟩ := by
    rw [cwSave_gpr, allocState16_rsp, below, Offset.sub_sub_ofNat]
  rw [hB] at hfr
  refine ⟨hrd, hwr, fun q hq => (hcs q hq).trans (congrFun (cwSave_gpr r s) q), ?_, ?_, ?_, hmx⟩
  · -- The address, at `rsp - 8`, above the first function's stack.
    rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun x hx => ?_)
      (by decide), cwSave_mem, Mem.readW_writeW_self64]
    rcases List.mem_append.mp hx with hx | hx
    · exact (hW x hx (a := 8) (n := 8) (by decide) (by omega_using [])).symm
    · simp only [List.mem_singleton] at hx; subst hx
      exact fun y h₁ h₂ => Offset.sep_below (s.gpr .rsp) (body.x86_64Depth + 24) (a := 8) (n := 8)
        (b := 16 + (body.x86_64Depth + 8)) (k := body.x86_64Depth + 8) (by omega_using [])
        (by omega_using []) (.inr (by omega_using [])) (by omega_using [hd, hst]) (by omega_using [hd, hst])
        y h₁ h₂
  · -- Memory changes only within the writable buffers and the stack below `rsp`.
    refine Frame.trans (Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
      (Offset.contains_below _ (a := 8) (n := 8) (by omega_using []) (by omega_using [])
        (by omega_using [hst]))) (Frame.sub hfr fun x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, List.mem_append_left _ hx, fun _ h => h⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        Offset.sub_below _ (by omega_using [hd]) (by omega_using [hd])⟩
  · -- The postcondition, which reads the memory on entry only within the buffers.
    rw [post_regs hk, show (cwSave r s).callEntry.withRegions s.rd s.wr = cwEntry r s from rfl, hargs, hm,
      hg .rax (by decide)] at hq
    exact hpost _ _ _ _ _ (regArgs_length sig s hk) hag hq

variable {r : Reg}

theorem calleeSaved_args : ∀ q ∈ calleeSaved, q ≠ .rdi ∧ q ≠ .rsi ∧ q ≠ .rax := by decide

theorem cwZero_rsp {s c : State} (hc : AfterBody sig post r stack s c) (n : Nat) :
    (cwZero n c).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16 := by
  rw [cwZero_gpr n c (by decide) (by decide), hc.2.2.1 .rsp (by decide), allocState16_rsp]

theorem cwZero_rdi' {s c : State} (hc : AfterBody sig post r stack s c) (n : Nat) :
    (cwZero n c).gpr .rdi = s.gpr r := by
  have hrsp : c.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16 := by
    rw [hc.2.2.1 .rsp (by decide), allocState16_rsp]
  rw [cwZero_rdi, hrsp, sub16_add8, Mem.readW_writeW_sep (fun y h₁ h₂ => Offset.sep_below (s.gpr .rsp) 16
    (a := 8) (n := 8) (b := 16) (k := 8) (by decide) (by decide) (.inr (by decide)) (by decide) (by decide)
    y h₁ h₂) (by decide), hc.2.2.2.1]

/-- The zeroize function's arguments, from the state after `zeroArgs`. -/
theorem cwZero_regArgs {X : State} :
    regArgs Spec.Zeroize.zeroizeSig X = [X.gpr .rdi, X.gpr .rsi] := rfl

theorem toNat_setWidth_ofNat32 {n : Nat} (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 n).setWidth 64).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_using [hn])]

/-- What the caller's contract gives of the array: its region is within the
writable ones, apart from the stack below `rsp`. -/
theorem cw_array (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k : Nat} {s : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s)) :
    (⟨s.gpr r, k * e.size⟩ : Region) ∈ s.wr ∧ (s.gpr r).toNat + k * e.size ≤ 2 ^ 64 := by
  rw [pre_regs hk hl] at hs
  obtain ⟨-, -, hwr, -, -, hnw, -⟩ := hs
  exact ⟨hwr ▸ List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨harr, rfl⟩, rfl⟩, hnw _ harr⟩

/-! ## The zeroize function's contract -/

/-- The zeroize function's precondition, from what it says of the state. -/
theorem zeroize_pre_of {zst n : Nat} {X : State} (hn : (X.gpr .rsi).toNat = n)
    (hwf : zst = 0 ∨ zst ≤ (X.gpr .rsp).toNat) (hrd : X.rd = []) (hwr : X.wr = [⟨X.gpr .rdi, n⟩])
    (hres : ∀ x ∈ (⟨X.gpr .rsp, 8⟩ :: stackBelow (X.gpr .rsp) zst : List Region),
      x.Disjoint ⟨X.gpr .rdi, n⟩)
    (hb : (X.gpr .rdi).toNat + n ≤ 2 ^ 64) :
    (Spec.Zeroize.zeroizeContract abi zst).pre X := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pre_regs (by decide) (by decide)).mpr ?_
  have hbz : Sig.bufs Spec.Zeroize.zeroizeSig.params (regArgs Spec.Zeroize.zeroizeSig X) =
      [(⟨X.gpr .rdi, n⟩, true)] := by
    show [((⟨X.gpr .rdi, (X.gpr .rsi).toNat * 1⟩ : Region), true)] = _
    rw [hn, Nat.mul_one]
  rw [hbz]
  refine ⟨hwf, hrd, hwr, List.pairwise_singleton _ _, fun x hx a ha => ?_, fun a ha => ?_, ?_⟩
  · simp only [List.mem_singleton] at ha; subst ha; exact hres x hx
  · simp only [List.mem_singleton] at ha; subst ha; exact hb
  · rw [Curry.apply_const]; trivial

/-- The zeroize function's postcondition. -/
theorem zeroize_post_iff {zst : Nat} {X Y : State} :
    (Spec.Zeroize.zeroizeContract abi zst).post X Y ↔
      Spec.Zeroize.bytesAt Y.mem (X.gpr .rdi) ((X.gpr .rsi).setWidth 64).toNat =
        Spec.Zeroize.zeros ((X.gpr .rsi).setWidth 64).toNat := Iff.rfl

/-- The zeroize function's public data. -/
theorem zeroize_pub_of {zst : Nat} {X₁ X₂ : State} (hsp : X₁.gpr .rsp = X₂.gpr .rsp)
    (hdi : X₁.gpr .rdi = X₂.gpr .rdi) (hsi : X₁.gpr .rsi = X₂.gpr .rsi) :
    (Spec.Zeroize.zeroizeContract abi zst).pub X₁ X₂ := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pub_regs (by decide) (by decide)).mpr ⟨hsp, fun i _ => ?_⟩
  rw [cwZero_regArgs, cwZero_regArgs, hdi, hsi]

/-- The zeroize function's entry state. -/
theorem cwZeroEntry_gpr {s c : State} (hc : AfterBody sig post r stack s c) (n : Nat) (R : Region) :
    ((cwZero n c).callEntry.withRegions [] [R]).gpr .rdi = s.gpr r ∧
      ((cwZero n c).callEntry.withRegions [] [R]).gpr .rsi = (BitVec.ofNat 32 n).setWidth 64 ∧
      ((cwZero n c).callEntry.withRegions [] [R]).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 24 := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_rsp, cwZero_rdi' hc, cwZero_rsi, cwZero_rsp hc, sub16_sub8]
  exact ⟨rfl, rfl, rfl⟩

/-- The zeroize function's precondition, at its entry. -/
theorem cw_zeroPre (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n zst : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hzs : zst ≤ stack) (hc : AfterBody sig post r stack s c) :
    (Spec.Zeroize.zeroizeContract abi zst).pre
      ((cwZero n c).callEntry.withRegions [] [⟨s.gpr r, n⟩]) := by
  have hsb := cw_sp hk hl hs
  have hA := cw_out hk hl hs _ harr
  have hnw := (cw_array hk hl hs harr).2
  have hsubA : Region.Sub ⟨s.gpr r, n⟩ ⟨s.gpr r, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨hdi, hsi, hsp⟩ := cwZeroEntry_gpr hc n ⟨s.gpr r, n⟩
  refine zeroize_pre_of (n := n) (by rw [hsi]; exact toNat_setWidth_ofNat32 hn32) (.inr ?_) rfl
    (by rw [hdi]; rfl) ?_ (by rw [hdi]; omega_using [hnw, hn])
  · rw [hsp, toNat_sub_ofNat (by omega_using [hsb])]; omega_using [hsb, hzs]
  · rw [hsp, hdi]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hA (a := 24) (n := 8) (by decide) (by omega_using [])).symm.sub_right hsubA
    · rcases Nat.eq_zero_or_pos zst with h0 | h0
      · subst h0; simp [stackBelow] at hx
      · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
        rw [below, Offset.sub_sub_ofNat]
        exact (hA (a := 24 + zst) (n := zst) (by omega_using []) (by omega_using [hzs])).symm.sub_right hsubA

/-- The zeroize function's public data, at its entry, if the array's
address is public. -/
theorem cw_zeroPub {n zst : Nat} {s₁ s₂ c₁ c₂ : State} (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hpp : s₁.gpr r = s₂.gpr r) (hc₁ : AfterBody sig post r stack s₁ c₁)
    (hc₂ : AfterBody sig post r stack s₂ c₂) :
    (Spec.Zeroize.zeroizeContract abi zst).pub ((cwZero n c₁).callEntry.withRegions [] [⟨s₁.gpr r, n⟩])
      ((cwZero n c₂).callEntry.withRegions [] [⟨s₂.gpr r, n⟩]) := by
  obtain ⟨d₁, i₁, p₁⟩ := cwZeroEntry_gpr hc₁ n ⟨s₁.gpr r, n⟩
  obtain ⟨d₂, i₂, p₂⟩ := cwZeroEntry_gpr hc₂ n ⟨s₂.gpr r, n⟩
  exact zeroize_pub_of (by rw [p₁, p₂, hsp]) (by rw [d₁, d₂, hpp]) (by rw [i₁, i₂])

/-- What the zeroize function's run leaves, from the caller's state `s`: the
first function's, but for the first `n` bytes of the array, which are zero,
and its result, at `rsp - 16`. -/
def AfterZero (sig : Sig) (post : sig.Post abi.ptrBits) (r : Reg) (stack n : Nat) (s e : State) : Prop :=
  ∃ c, AfterBody sig post r stack s c ∧
    e.rd = s.rd ∧ e.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 16, 16⟩ :: s.wr ∧
    (∀ q ∈ calleeSaved, e.gpr q = (allocState 16 s).gpr q) ∧
    e.mem.readW (s.gpr .rsp - BitVec.ofNat 64 16) 64 = c.gpr .rax ∧
    Frame (s.wr ++ [below (s.gpr .rsp) (stack + 24)]) s.mem e.mem ∧
    Frame [⟨s.gpr r, n⟩, below (s.gpr .rsp) (stack + 24)] c.mem e.mem ∧
    Spec.Zeroize.bytesAt e.mem (s.gpr r) n = Spec.Zeroize.zeros n ∧
    e.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- The zeroize function may write only the first `n` bytes of the array. -/
theorem cw_zeroCovers (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hc : AfterBody sig post r stack s c) :
    Covers [⟨s.gpr r, n⟩] (cwZero n c).wr :=
  Covers.one ⟨_, by rw [cwZero_wr, hc.2.1]; exact List.mem_cons_of_mem _ (cw_array hk hl hs harr).1, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn⟩

/-- The call of the zeroize function. -/
theorem cw_zero_wp {zname : String} {zcode : Prog isa} {zst : Nat}
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hzsp : zcode.all (fun i => !isa.writesSp i) = true) (hzd : zcode.x86_64Depth ≤ zst)
    (hzs : zst ≤ stack) (hst : stack + 32 ≤ 2 ^ 64)
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hc : AfterBody sig post r stack s c) :
    WP isa (.call zname zcode) (cwZero n c) (AfterZero sig post r stack n s) := by
  have hsb := cw_sp hk hl hs
  have hA := cw_out hk hl hs _ harr
  obtain ⟨hAw, -⟩ := cw_array hk hl hs harr
  have hsubA : Region.Sub ⟨s.gpr r, n⟩ ⟨s.gpr r, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨hrdc, hwrc, hcsc, -, hfc, -, hmxc⟩ := id hc
  have hcw := cw_zeroCovers hk hl hs harr hn hc
  refine WP.call_sp_mx (k := Spec.Zeroize.zeroizeContract abi zst) hz.1 (SpSafe.of_all hzsp)
    (by omega_using [hzd, hzs, hst]) (cw_zeroPre hk hl hs harr hn hn32 hzs hc) (Covers.right hcw) hcw ?_
  intro e' hrd hwr hcs hfr _ ⟨s₂, hm, _, hq⟩ hmx
  have hB : below ((cwZero n c).gpr .rsp) (zcode.x86_64Depth + 8) =
      ⟨s.gpr .rsp - BitVec.ofNat 64 (16 + (zcode.x86_64Depth + 8)), zcode.x86_64Depth + 8⟩ := by
    rw [cwZero_rsp hc, below, Offset.sub_sub_ofNat]
  rw [hB] at hfr
  have hcrsp : c.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16 := by
    rw [hcsc .rsp (by decide), allocState16_rsp]
  -- The result's slot, which `zeroArgs` writes.
  have fD : Frame [below (s.gpr .rsp) (stack + 24)] c.mem (cwZero n c).mem := by
    rw [cwZero_mem, hcrsp]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_below _ (a := 16) (n := 8) (by omega_using []) (by omega_using []) (by omega_using [hst]))
  have hbelowZ : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (16 + (zcode.x86_64Depth + 8)), zcode.x86_64Depth + 8⟩
      (below (s.gpr .rsp) (stack + 24)) :=
    Offset.sub_below _ (by omega_using [hzd, hzs]) (by omega_using [hzd, hzs])
  refine ⟨c, hc, by rw [hrd, cwZero_rd, hrdc],
    by rw [hwr, cwZero_wr, hwrc], fun q hq => ?_, ?_, ?_, ?_, ?_, by rw [hmx, cwZero_mxcsr, hmxc]⟩
  · obtain ⟨h₁, h₂, -⟩ := calleeSaved_args q hq
    rw [hcs q hq, cwZero_gpr n c h₁ h₂, hcsc q hq]
  · -- The result, at `rsp - 16`, which the zeroize function does not write.
    rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun x hx => ?_)
      (by decide), cwZero_mem, hcrsp, Mem.readW_writeW_self64]
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact (hA (a := 16) (n := 8) (by decide) (by omega_using [])).symm.sub_right hsubA
    · simp only [List.mem_singleton] at hx; subst hx
      exact fun y h₁ h₂ => Offset.sep_below (s.gpr .rsp) (zcode.x86_64Depth + 24) (a := 16) (n := 8)
        (b := 16 + (zcode.x86_64Depth + 8)) (k := zcode.x86_64Depth + 8) (by omega_using [])
        (by omega_using []) (.inr (by omega_using [])) (by omega_using [hzd, hzs, hst])
        (by omega_using [hzd, hzs, hst]) y h₁ h₂
  · refine Frame.trans hfc (Frame.trans (Frame.mono fD fun x hx => List.mem_append_right _ hx)
      (Frame.sub hfr fun x hx => ?_))
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_left _ hAw, hsubA⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hbelowZ⟩
  · refine Frame.trans (Frame.mono fD fun x hx => ?_) (Frame.sub hfr fun x hx => ?_)
    · simp only [List.mem_singleton] at hx; subst hx
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hbelowZ⟩
  · -- The zeroize function's postcondition.
    obtain ⟨hdi, hsi, -⟩ := cwZeroEntry_gpr hc n ⟨s.gpr r, n⟩
    rw [zeroize_post_iff, hdi, hsi, hm, BitVec.setWidth_eq, toNat_setWidth_ofNat32 hn32] at hq
    exact hq

/-! ## The whole call -/

/-- The return address lies apart from the writable regions. -/
theorem cw_ret (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s) :
    ∀ x ∈ s.wr, Region.Disjoint ⟨s.gpr .rsp, 8⟩ x := by
  rw [pre_regs hk hl] at hs
  obtain ⟨-, -, hwr, -, hres, -, -⟩ := hs
  intro x hx
  rw [hwr] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hres _ (List.mem_cons_self ..) b (List.mem_filter.mp hb).1

/-- A run of `callWipe` from the caller's state `s`: it keeps what the
calling convention requires, its postcondition is the first function's if
that reads the memory on return only within the buffers apart from the
array (`hout`), and the first `n` bytes of the array are zero. -/
theorem cw_wp {name zname : String} {body zcode : Prog isa} {zst : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) (hr : r ≠ .rsp)
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ stack)
    (hzsp : zcode.all (fun i => !isa.writesSp i) = true) (hzd : zcode.x86_64Depth ≤ zst)
    (hzs : zst ≤ stack) (hst : stack + 32 ≤ 2 ^ 64)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {e : Elem} {k n : Nat} (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 24) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x) :
    WP isa (callWipe r n name body zname zcode) s fun g =>
      abiPreserved s g ∧ (sig.contract abi pre post wa (stack + 24) leak).post s g ∧
        Spec.Zeroize.bytesAt g.mem (s.gpr r) n = Spec.Zeroize.zeros n := by
  have hsb := cw_sp hk hl hs
  have hret := cw_ret hk hl hs
  have hout' := cw_out hk hl hs
  refine alloc_frame_ok (by decide) (by omega_using [hsb]) ?_
  refine WP.seq (WP.block ⟨_, saveArg_run hr s, ?_⟩)
  refine WP.seq (WP.mono (cw_body_wp h hk hl hsp hd hst hpre hpost hs) fun c hc => ?_)
  have hcrsp : c.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16 := by
    rw [hc.2.2.1 .rsp (by decide), allocState16_rsp]
  refine WP.seq (WP.block ⟨_, zeroArgs_run n (by rw [hcrsp, hc.2.1]; exact List.mem_cons_self ..), ?_⟩)
  refine WP.seq (WP.mono (cw_zero_wp hz hzsp hzd hzs hst hk hl hs harr hn hn32 hc) fun g hg => ?_)
  obtain ⟨c', hc', -, hwr, hcs, hrax', hfs, hfc, hz0, hmx⟩ := hg
  have hgrsp : g.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16 := by
    rw [hcs .rsp (by decide), allocState16_rsp]
  refine WP.block ⟨_, restoreRet_run ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..),
    by rw [hgrsp]; simp [Region.Contains]⟩, ?_⟩
  refine ⟨by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hgrsp, allocState16_rsp],
    by rw [RegUpd.wr_setReg, hwr]; rfl,
    ⟨fun q hq => ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- The callee-saved registers.
    by_cases hq' : q = .rsp
    · subst hq'
      exact freeState_rsp (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hgrsp, allocState16_rsp])
    · have hqa : q ≠ .rax := (calleeSaved_args q hq).2.2
      simp only [freeState, State.setReg, hq', hqa, ite_false]
      rw [hcs q hq, allocState16_gpr s hq']
  · -- The return address: memory changes only within the writable regions and below `rsp`.
    show g.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    refine hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun x hx => ?_) (by decide)
    rcases List.mem_append.mp hx with hx | hx
    · exact hret x hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact Offset.base_disjoint_below _ (by omega_using [hst])
  · exact hmx
  · -- The postcondition, which reads the memory on return only within the buffers apart from the array.
    rw [post_regs hk]
    have hrax : (freeState 16 (g.setReg .rax (g.mem.readW (g.gpr .rsp) 64))).gpr .rax = c'.gpr .rax := by
      simp only [freeState, State.setReg, show Reg.rax ≠ .rsp by decide, ite_false, ite_true]
      rw [hgrsp, hrax']
    rw [hrax]
    refine hout c'.mem _ _ (fun b hb hbA x hx => ?_) hc'.2.2.2.2.2.1
    refine (hfc x fun R hR hc => ?_).symm
    rcases List.mem_cons.mp hR with rfl | hR
    · exact hbA x hx (Region.sub_prefix hn x hc)
    · simp only [List.mem_singleton] at hR; subst hR
      exact hout' b hb (stack + 24) (stack + 24) (Nat.le_refl _) (Nat.le_refl _) x hx hc
  · exact hz0

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

/-- Code verified against `sig.contract` with `stack` bytes of stack, for a
function whose arguments are all in registers, the one in `argRegs[i]` a
writable array of `k` elements `e`, is verified with `stack + 24` bytes when
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
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hst : stack + 32 ≤ 2 ^ 64)
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ stack)
    (hzsp : zcode.all (fun i => !isa.writesSp i) = true) (hzd : zcode.x86_64Depth ≤ zst)
    (hzs : zst ≤ stack)
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
    (hsat : ∃ s, (sig.contract abi pre post' wa (stack + 24) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.X86_64.callWipe (argRegs.getD i .rax) n name body zname zcode)
      (sig.contract abi pre post' wa (stack + 24) leak) := by
  subst hi
  have hL : (sig.words abi.ptrBits).length = (ps₁.flatMap fun p => p.2.words 64).length + 1 +
      (ps₂.flatMap fun p => p.2.words 64).length := by
    show (sig.params.flatMap fun p => p.2.words 64).length = _
    rw [hps, List.flatMap_append, List.flatMap_cons]
    simp only [List.length_append, Param.words.eq_2, List.length_cons, List.length_nil]
    omega
  have hiL : (ps₁.flatMap fun p => p.2.words 64).length < (sig.words abi.ptrBits).length := by
    rw [hL]; omega
  have hr : argRegs.getD (ps₁.flatMap fun p => p.2.words 64).length .rax ≠ .rsp :=
    (argRegs_scratch _ (by omega_using [hiL, hk])).1
  generalize hr' : argRegs.getD (ps₁.flatMap fun p => p.2.words 64).length .rax = r at hr ⊢
  have hget : ∀ s : State, (regArgs sig s).getD (ps₁.flatMap fun p => p.2.words 64).length 0 = s.gpr r :=
    fun s => by rw [← hr']; exact regArgs_getD s.gpr hk hiL
  -- The array, among the buffers.
  have harr : ∀ s : State, (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s) := by
    intro s
    rw [← hget s, hps]
    exact Sig.bufs_mem_array (pb := 64) ps₂ ps₁ (regArgs sig s) (by rw [regArgs_length sig s hk, hL]; omega)
  -- Its address is public.
  have hpubA : ∀ s₁ s₂, (sig.contract abi pre post wa (stack + 24) leak).pub s₁ s₂ → s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ hp
    have hP : (sig.params.flatMap (·.2.pubs)).getD (ps₁.flatMap fun p => p.2.words 64).length false = true := by
      rw [hps]; exact (Sig.pub_array (pb := 64) ps₁ ps₂).1
    have hW : ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD
        (ps₁.flatMap fun p => p.2.words 64).length 64 = 64 := by
      show ((sig.params.flatMap fun p => p.2.words 64).map (·.bits 64)).getD _ 64 = 64
      rw [hps]; exact (Sig.pub_array (pb := 64) ps₁ ps₂).2
    have h2 := congrArg BitVec.toNat (((pubL_regs hk hl).mp hp).2 _ hP)
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hW, hget, hget, Nat.mod_eq_of_lt (BitVec.isLt _),
      Nat.mod_eq_of_lt (BitVec.isLt _)] at h2
    exact BitVec.eq_of_toNat_eq h2
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + 24) leak).pre s → ∀ m₁ m₂ x,
      (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    rw [pre_regs hk hl] at hs
    exact hpostOut _ _ _ _ _ (regArgs_length sig s hk) hs.2.2.2.1 (by rw [hget]; exact hag) hq
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · obtain ⟨t, g, he, habi, hq, hz0⟩ :=
      cw_wp h hz hk hl hr hsp hd hzsp hzd hzs hst hpre hpost hn hn32 hs (harr s) (hout s hs)
    refine ⟨t, g, he, habi, ?_⟩
    rw [post_regs hk] at hq ⊢
    exact hwiped _ _ _ _ (regArgs_length sig s hk) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract abi pre post' wa (stack + 24) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + 24) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + 24) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + 24) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + 24) leak).pre σ₂ := h₂
    have hp' : (sig.contract abi pre post wa (stack + 24) leak).pub σ₁ σ₂ := hp
    have hsp12 : σ₁.gpr .rsp = σ₂.gpr .rsp := ((pubL_regs hk hl).mp hp').1.1
    have hpp := hpubA _ _ hp'
    have hcov : ∀ σ : State, Covers (σ.rd ++ σ.wr) ((cwSave r σ).rd ++ (cwSave r σ).wr) ∧
        Covers σ.wr (cwSave r σ).wr := fun σ =>
      ⟨Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx⟩
    refine RelCT.mono (P := fun a b => a = allocState 16 σ₁ ∧ b = allocState 16 σ₂) ?_
      (fun a b hab => hab.2) (fun _ _ h => h)
    -- The address is saved.
    refine RelCT.seq (R := fun a b => a = cwSave r σ₁ ∧ b = cwSave r σ₂)
      (RelCT.block_of fun a b hab => ?_) ?_
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, saveArg_run hr σ₁, by rw [saveArg_run hr σ₂, hsp12], rfl, rfl⟩
    -- The first function.
    refine RelCT.seq (R := fun c₁ c₂ => AfterBody sig post r stack σ₁ c₁ ∧ AfterBody sig post r stack σ₂ c₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterBody sig post r stack σ₁) (F₂ := AfterBody sig post r stack σ₂)
        (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨σ₁.rd, σ₁.wr, σ₂.rd, σ₂.wr, cw_bodyPre hk hl hpre h₁', cw_bodyPre hk hl hpre h₂',
          cw_bodyPub hk hl r h₁' h₂' hp' hleak, (hcov σ₁).1, (hcov σ₁).2, (hcov σ₂).1, (hcov σ₂).2,
          by rw [cwSave_gpr, cwSave_gpr, allocState16_rsp, allocState16_rsp, hsp12]⟩
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨cw_body_wp h hk hl hsp hd hst hpre hpost h₁', cw_body_wp h hk hl hsp hd hst hpre hpost h₂'⟩
    -- The zeroize function's arguments.
    refine RelCT.seq (R := fun d₁ d₂ => (∃ c, AfterBody sig post r stack σ₁ c ∧ d₁ = cwZero n c) ∧
      (∃ c, AfterBody sig post r stack σ₂ c ∧ d₂ = cwZero n c)) (RelCT.block_of fun c₁ c₂ hc => ?_) ?_
    · obtain ⟨hc₁, hc₂⟩ := hc
      have e₁ : c₁.gpr .rsp = σ₁.gpr .rsp - BitVec.ofNat 64 16 := by
        rw [hc₁.2.2.1 .rsp (by decide), allocState16_rsp]
      have e₂ : c₂.gpr .rsp = σ₂.gpr .rsp - BitVec.ofNat 64 16 := by
        rw [hc₂.2.2.1 .rsp (by decide), allocState16_rsp]
      refine ⟨_, _, _, zeroArgs_run n (by rw [e₁, hc₁.2.1]; exact List.mem_cons_self ..), ?_,
        ⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩
      rw [zeroArgs_run n (by rw [e₂, hc₂.2.1]; exact List.mem_cons_self ..), e₁, e₂, hsp12]
    -- The zeroize function.
    refine RelCT.seq (R := fun g₁ g₂ => AfterZero sig post r stack n σ₁ g₁ ∧ AfterZero sig post r stack n σ₂ g₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterZero sig post r stack n σ₁) (F₂ := AfterZero sig post r stack n σ₂)
        (RelCT.callEx hz.1 hz.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨[], [⟨σ₁.gpr r, n⟩], [], [⟨σ₂.gpr r, n⟩], cw_zeroPre hk hl h₁' (harr σ₁) hn hn32 hzs hc₁,
          cw_zeroPre hk hl h₂' (harr σ₂) hn hn32 hzs hc₂, cw_zeroPub hsp12 hpp hc₁ hc₂,
          Covers.right (cw_zeroCovers hk hl h₁' (harr σ₁) hn hc₁), cw_zeroCovers hk hl h₁' (harr σ₁) hn hc₁,
          Covers.right (cw_zeroCovers hk hl h₂' (harr σ₂) hn hc₂), cw_zeroCovers hk hl h₂' (harr σ₂) hn hc₂,
          by rw [cwZero_rsp hc₁, cwZero_rsp hc₂, hsp12]⟩
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨cw_zero_wp hz hzsp hzd hzs hst hk hl h₁' (harr σ₁) hn hn32 hc₁,
          cw_zero_wp hz hzsp hzd hzs hst hk hl h₂' (harr σ₂) hn hn32 hc₂⟩
    -- The result is restored.
    · refine RelCT.block_of fun g₁ g₂ hg => ?_
      obtain ⟨⟨c₁, _, _, hw₁, hcs₁, _⟩, ⟨c₂, _, _, hw₂, hcs₂, _⟩⟩ := hg
      have e₁ : g₁.gpr .rsp = σ₁.gpr .rsp - BitVec.ofNat 64 16 := by
        rw [hcs₁ .rsp (by decide), allocState16_rsp]
      have e₂ : g₂.gpr .rsp = σ₂.gpr .rsp - BitVec.ofNat 64 16 := by
        rw [hcs₂ .rsp (by decide), allocState16_rsp]
      have hin : ∀ (g : State) (σ : State), g.wr = ⟨σ.gpr .rsp - BitVec.ofNat 64 16, 16⟩ :: σ.wr →
          g.gpr .rsp = σ.gpr .rsp - BitVec.ofNat 64 16 → InRegions (g.rd ++ g.wr) (g.gpr .rsp) 8 :=
        fun g σ hw he => ⟨_, List.mem_append_right _ (by rw [hw]; exact List.mem_cons_self ..),
          by rw [he]; simp [Region.Contains]⟩
      refine ⟨_, g₂.setReg .rax (g₂.mem.readW (g₂.gpr .rsp) 64), _, restoreRet_run (hin g₁ σ₁ hw₁ e₁), ?_,
        trivial⟩
      rw [restoreRet_run (hin g₂ σ₂ hw₂ e₂), e₁, e₂, hsp12]

/-- `Verified.callWipe'`, with the function's postcondition. -/
theorem Verified.callWipe {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {k n i : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hst : stack + 32 ≤ 2 ^ 64)
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ stack)
    (hzsp : zcode.all (fun i => !isa.writesSp i) = true) (hzd : zcode.x86_64Depth ≤ zst)
    (hzs : zst ≤ stack)
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + 24) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.X86_64.callWipe (argRegs.getD i .rax) n name body zname zcode)
      (sig.contract abi pre post wa (stack + 24) leak) :=
  Verified.callWipe' h hz hk hl hps hi hn hn32 hst hsp hd hzsp hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak

end

/-- `callWipe` writes `rsp` only in its frame and its calls if its callees do
only in their frames. -/
theorem callWipe_spSafe {r : Reg} {n : Nat} {name zname : String} {body zcode : Prog isa}
    (h : body.all (fun i => !isa.writesSp i) = true)
    (hz : zcode.all (fun i => !isa.writesSp i) = true) :
    (Impl.CallWipe.X86_64.callWipe r n name body zname zcode).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.CallWipe.X86_64.callWipe, Code.all, h, hz, Bool.true_and]
  rfl

end VG.X86_64
