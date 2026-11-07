module

public import VerifiedGarbage.Impl.CallWipe.Arm
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.CallWipe
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# A call that wipes part of a buffer afterwards (ARMv7)

`Verified.callWipe`: a function verified against `sig.contract` with `stack`
bytes of stack (`armStack body ≤ stack`), whose arguments are all in
registers (`nsaa sig = 0`), one of them (word `i`, in `r`) a writable array
of `k` elements `e`, is verified against the same contract with
`stack + 16` bytes when called by `callWipe`, which then zeroes the first
`n ≤ k * e.size` bytes of the array with a function verified against
`Spec.Zeroize.zeroizeContract`, and returns the first function's result;
`Verified.callWipe'` adds to the postcondition that those bytes are zero on
return.

`callWipe`'s frame (`push {r4, r5, r6, lr}`, `cwPush`) saves the registers it
uses and the return address: `r4` holds the array's address across the first
call, `r5` and `r6` the first function's result across the second. Each
callee runs from the state after its call with the permissions of its own
contract: the buffers for the first, the `n` bytes for the zeroize function
(`WP.callF`). The frame is memory the first function's contract reads on
entry, which the caller's says nothing of: the precondition, postcondition
and leak must read the memory on entry only within the function's buffers
(`hpre`, `hpost`, `hleak`). The zeroize function writes the array after the
first function returned: the postcondition must read the memory on return
only within the buffers apart from the array (`hpostOut`), which the
precondition keeps apart from the others (it is writable).

Constant time: the frame's accesses depend on the stack pointer alone, each
callee is constant time, and the zeroize function's arguments, the array's
address and `n`, are public.
-/

@[expose] public section

namespace VG.Arm

open VG.Impl.CallWipe.Arm VG.Arm.FrameStack

/-! ## The frame -/

/-- The state after the frame's push. -/
def cwPush (s : State) : State := pushed [.r4, .r5, .r6, .lr] s

@[simp] theorem cwPush_sp (s : State) : (cwPush s).sp = s.sp - BitVec.ofNat 32 16 := rfl
@[simp] theorem cwPush_rd (s : State) : (cwPush s).rd = s.rd := rfl
@[simp] theorem cwPush_wr (s : State) :
    (cwPush s).wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr := rfl
@[simp] theorem cwPush_gpr (s : State) : (cwPush s).gpr = s.gpr := rfl

/-- Four words stored at `p`, at offsets from `State.addr p`. -/
theorem storeWords4 (m : Mem) (p : BitVec 32) (a b c d : BitVec 32) (hp : p.toNat + 16 ≤ 2 ^ 32) :
    storeWords m p [a, b, c, d] =
      (((m.writeW (State.addr p) a).writeW (State.addr p + BitVec.ofNat 64 4) b).writeW
        (State.addr p + BitVec.ofNat 64 8) c).writeW (State.addr p + BitVec.ofNat 64 12) d := by
  have e8 : p + 4 + 4 = p + BitVec.ofNat 32 8 := by
    rw [BitVec.add_assoc]; exact congrArg (p + ·) (by decide)
  have e12 : p + 4 + 4 + 4 = p + BitVec.ofNat 32 12 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (p + ·) (by decide)
  show (((m.writeW (State.addr p) a).writeW (State.addr (p + BitVec.ofNat 32 4)) b).writeW
    (State.addr (p + 4 + 4)) c).writeW (State.addr (p + 4 + 4 + 4)) d = _
  rw [e12, e8, addr_add (by omega), addr_add (by omega), addr_add (by omega)]

/-- What the four words read back as. -/
theorem storeWords4_read (m : Mem) (p : BitVec 32) (a b c d : BitVec 32) (hp : p.toNat + 16 ≤ 2 ^ 32) :
    (storeWords m p [a, b, c, d]).readW (State.addr p) 32 = a ∧
    (storeWords m p [a, b, c, d]).readW (State.addr p + BitVec.ofNat 64 4) 32 = b ∧
    (storeWords m p [a, b, c, d]).readW (State.addr p + BitVec.ofNat 64 8) 32 = c ∧
    (storeWords m p [a, b, c, d]).readW (State.addr p + BitVec.ofNat 64 12) 32 = d := by
  rw [storeWords4 m p a b c d hp]
  have sb : ∀ {e : Nat}, 4 ≤ e → e + 4 ≤ 16 → Mem.Sep (State.addr p) (32 / 8) (State.addr p + BitVec.ofNat 64 e)
      (32 / 8) := fun h₁ h₂ => Offset.sep_base _ h₁ (by omega)
  have so : ∀ {i j : Nat}, i + 4 ≤ j ∨ j + 4 ≤ i → i + 4 ≤ 16 → j + 4 ≤ 16 →
      Mem.Sep (State.addr p + BitVec.ofNat 64 i) (32 / 8) (State.addr p + BitVec.ofNat 64 j) (32 / 8) :=
    fun h h₁ h₂ => Offset.sep _ h (by omega) (by omega)
  have s0 : ∀ {j : Nat}, 4 ≤ j → j + 4 ≤ 16 →
      Mem.Sep (State.addr p + BitVec.ofNat 64 j) (32 / 8) (State.addr p) (32 / 8) := fun {j} h₁ h₂ => by
    have := Offset.sep (State.addr p) (d := j) (e := 0) (n := 4) (k := 4) (.inr (by omega)) (by omega)
      (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (sb (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sb (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sb (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (so (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (so (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (so (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- The registers the frame saves, read back. -/
theorem cwPush_read (s : State) (hsp : 16 ≤ s.sp.toNat) :
    (cwPush s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 16)) 32 = s.gpr .r4 ∧
    (cwPush s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 4) 32 = s.gpr .r5 ∧
    (cwPush s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 8) 32 = s.gpr .r6 ∧
    (cwPush s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 12) 32 = s.gpr .lr :=
  storeWords4_read s.mem _ _ _ _ _ (by
    show (s.sp - BitVec.ofNat 32 16).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat' hsp]; have := s.sp.isLt; omega)

/-- The frame's words, in its region. -/
theorem frame_contains (p : BitVec 32) {k : Nat} (hk : k + 4 ≤ 16) :
    (⟨State.addr p, 16⟩ : Region).Contains (State.addr p + BitVec.ofNat 64 k) 4 :=
  Offset.contains_base _ (by omega) (by omega)

/-! ## The blocks -/

/-- The state after `saveArg r`: the array's address in `r4`. -/
def cwSave (r : Reg) (s : State) : State := (cwPush s).setReg .r4 (s.gpr r)

@[simp] theorem cwSave_sp (r : Reg) (s : State) : (cwSave r s).sp = s.sp - BitVec.ofNat 32 16 := rfl
@[simp] theorem cwSave_rd (r : Reg) (s : State) : (cwSave r s).rd = s.rd := rfl
@[simp] theorem cwSave_wr (r : Reg) (s : State) :
    (cwSave r s).wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr := rfl
theorem cwSave_mem (r : Reg) (s : State) : (cwSave r s).mem = (cwPush s).mem := rfl
theorem cwSave_r4 (r : Reg) (s : State) : (cwSave r s).gpr .r4 = s.gpr r :=
  RegUpd.gpr_setReg_self _ _ _
theorem cwSave_gpr (r : Reg) (s : State) {q : Reg} (h : q ≠ .r4) : (cwSave r s).gpr q = s.gpr q :=
  RegUpd.gpr_setReg_of_ne _ _ h

theorem saveArg_run (r : Reg) (s : State) : execBlock isa (saveArg r) (cwPush s) = some (cwSave r s, []) := by
  simp only [saveArg, mov, execBlock, isa, exec, Op2.eval, Option.map_some, addrs, List.map_nil,
    List.append_nil]
  rfl

/-- `movw r1, #lo16(n); movt r1, #hi16(n)` leaves `n`. -/
theorem movwt {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 16 (n / 2 ^ 16) ++ ((BitVec.ofNat 16 n).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  have key : (n / 2 ^ 16) <<< 16 ||| n % 2 ^ 16 = n := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]; omega
  have e1 : n / 2 ^ 16 % 2 ^ 16 = n / 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e2 : n % 2 ^ 16 % 2 ^ 32 = n % 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e3 : n % 2 ^ 16 % 2 ^ 16 = n % 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e5 : n % 2 ^ 32 = n := Nat.mod_eq_of_lt hn
  simp only [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_zero, e1, e2, e3, e5, key]

/-- The state after `zeroArgs n`: the result in `r5` and `r6`, the array's
address in `r0`, `n` in `r1`. -/
def cwZero (n : Nat) (c : State) : State :=
  (((c.setReg .r5 (c.gpr .r0)).setReg .r6 (c.gpr .r1)).setReg .r0 (c.gpr .r4)).setReg .r1 (BitVec.ofNat 32 n)

@[simp] theorem cwZero_rd (n : Nat) (c : State) : (cwZero n c).rd = c.rd := rfl
@[simp] theorem cwZero_wr (n : Nat) (c : State) : (cwZero n c).wr = c.wr := rfl
@[simp] theorem cwZero_sp (n : Nat) (c : State) : (cwZero n c).sp = c.sp := rfl
theorem cwZero_mem (n : Nat) (c : State) : (cwZero n c).mem = c.mem := rfl
theorem cwZero_r0 (n : Nat) (c : State) : (cwZero n c).gpr .r0 = c.gpr .r4 := by
  rw [cwZero, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self]
theorem cwZero_r1 (n : Nat) (c : State) : (cwZero n c).gpr .r1 = BitVec.ofNat 32 n := by
  rw [cwZero, RegUpd.gpr_setReg_self]
theorem cwZero_r5 (n : Nat) (c : State) : (cwZero n c).gpr .r5 = c.gpr .r0 := by
  rw [cwZero, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide),
    RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self]
theorem cwZero_r6 (n : Nat) (c : State) : (cwZero n c).gpr .r6 = c.gpr .r1 := by
  rw [cwZero, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide),
    RegUpd.gpr_setReg_self]
theorem cwZero_gpr (n : Nat) (c : State) {q : Reg} (h0 : q ≠ .r0) (h1 : q ≠ .r1) (h5 : q ≠ .r5)
    (h6 : q ≠ .r6) : (cwZero n c).gpr q = c.gpr q := by
  rw [cwZero, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h0,
    RegUpd.gpr_setReg_of_ne _ _ h6, RegUpd.gpr_setReg_of_ne _ _ h5]

theorem zeroArgs_run {n : Nat} (hn : n < 2 ^ 32) (c : State) :
    execBlock isa (zeroArgs n) c = some (cwZero n c, []) := by
  simp only [zeroArgs, mov, execBlock, isa, exec, Op2.eval, Option.map_some, addrs, List.map_nil,
    List.append_nil, RegUpd.gpr_setReg_self, movwt hn]
  simp only [cwZero, State.setReg, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1; funext q; by_cases h : q = .r1 <;> simp [h]

/-- The state after `restoreRet`, from `g`: the result in `r0` and `r1`,
`r5`, `r6` and `lr` restored from the frame. -/
def cwRestore (g : State) : State :=
  ((((g.setReg .r0 (g.gpr .r5)).setReg .r1 (g.gpr .r6)).setReg .r5
    (g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 4)) 32)).setReg .r6
    (g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 8)) 32)).setReg .lr
    (g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 12)) 32)

theorem restoreRet_run {g : State} (h : ∀ k ∈ [4, 12, 8], InRegions (g.rd ++ g.wr)
    (State.addr (g.sp + BitVec.ofNat 32 k)) 4) :
    execBlock isa restoreRet g = some (cwRestore g, [.addr (State.addr (g.sp + BitVec.ofNat 32 4)),
      .addr (State.addr (g.sp + BitVec.ofNat 32 8)), .addr (State.addr (g.sp + BitVec.ofNat 32 12))]) := by
  have h4 := h 4 (by decide)
  have h8 := h 8 (by decide)
  have h12 := h 12 (by decide)
  simp only [restoreRet, mov, execBlock, isa, exec, Op2.eval, Option.map_some, addrs, List.map_nil,
    show (4 : Nat) < 4096 by decide, show (8 : Nat) < 4096 by decide,
    show (12 : Nat) < 4096 by decide, ite_true, State.load32, RegUpd.sp_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, h4, h8, h12, List.map_cons, List.nil_append, List.cons_append]
  rfl

/-! ## The stack -/

/-- The stack reserved below `p`, by `abi.reserved`. -/
theorem stackBelow_belowA {p : BitVec 32} {k : Nat} (hk : k ≤ p.toNat) :
    ∀ x ∈ stackBelow (State.addr p) k, x = belowA p k := by
  intro x hx
  cases k with
  | zero => simp [stackBelow] at hx
  | succ k =>
    simp only [stackBelow, List.mem_singleton] at hx
    rw [hx, belowA, addr_sub' hk]

/-- The frame lies apart from the stack its body's callees use. -/
theorem frame_disj_below (sp : BitVec 32) {a : Nat} (h : a + 16 ≤ sp.toNat) :
    Region.Disjoint (belowA sp 16) (belowA (sp - BitVec.ofNat 32 16) a) := by
  show Region.Disjoint ⟨State.addr (sp - BitVec.ofNat 32 16), 16⟩
    ⟨State.addr (sp - BitVec.ofNat 32 16 - BitVec.ofNat 32 a), a⟩
  rw [addr_sub' (k := a) (by rw [sub_toNat' (by omega)]; omega)]
  exact Offset.base_disjoint_below _ (by omega)

theorem cwPush_frame (s : State) (hsp : 16 ≤ s.sp.toNat) :
    Frame [belowA s.sp 16] s.mem (cwPush s).mem := by
  have h := pushed_frameA (rs := [.r4, .r5, .r6, .lr]) (s := s) hsp
  exact h

/-! ## The caller's contract -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- With every argument in a register, the regions are the buffers. -/
theorem allRegions_eq (hN : nsaa sig = 0) (s : State) :
    allRegions sig s = Sig.bufs sig.params (armArgs sig s) := by
  simp only [allRegions, argArea, hN, ite_true, List.append_nil]

/-- What the caller's contract gives of the stack. -/
theorem cw_sp (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) : stack + 16 ≤ s.sp.toNat := by
  rw [pre_arm hl] at hs
  rcases hs.1.1 with h | h <;> omega_using [h]

/-- The stack below the stack pointer that the caller's contract reserves
lies apart from the buffers. -/
theorem cw_res (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (armArgs sig s), (belowA s.sp (stack + 16)).Disjoint b.1 := by
  have hsb := cw_sp hl hs
  rw [pre_arm hl, allRegions_eq hN] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hm : belowA s.sp (stack + 16) ∈ stackBelow (State.addr s.sp) (stack + 16) := by
    show _ ∈ [(⟨State.addr s.sp - BitVec.ofNat 64 (stack + 16), stack + 16⟩ : Region)]
    rw [belowA, addr_sub' hsb]; exact List.mem_singleton_self _
  exact hres _ hm

/-- So do the writable regions. -/
theorem cw_resW (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ x ∈ s.wr, (belowA s.sp (stack + 16)).Disjoint x := by
  have hres := cw_res hN hl hs
  rw [pre_arm hl, allRegions_eq hN] at hs
  intro x hx
  rw [hs.2.2.1] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hres b (List.mem_filter.mp hb).1

/-- The state the first function runs from, with the permissions of its
contract: after the call. -/
def cwEntry (r : Reg) (s : State) : State := (cwSave r s).callEntry.withRegions s.rd s.wr

theorem cwEntry_gpr (r : Reg) (s : State) {q : Reg} (h4 : q ≠ .r4) (h12 : q ≠ .r12) (hlr : q ≠ .lr) :
    (cwEntry r s).gpr q = s.gpr q := by
  have hl : q ∉ linkRegs := by
    simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h12, hlr⟩
  rw [cwEntry, State.withRegions_gpr, State.callEntry_gpr _ hl, cwSave_gpr r s h4]

theorem cwEntry_sp (r : Reg) (s : State) : (cwEntry r s).sp = s.sp - BitVec.ofNat 32 16 := rfl
theorem cwEntry_mem (r : Reg) (s : State) : (cwEntry r s).mem = (cwPush s).mem := rfl

theorem argRegs_ne : ∀ q ∈ argRegs, q ≠ .r4 ∧ q ≠ .r12 ∧ q ≠ .lr := by decide

theorem cwEntry_armArgs (hloc : (locs sig).all (Loc.ok 0) = true) (r : Reg) (s : State) :
    armArgs sig (cwEntry r s) = armArgs sig s :=
  armArgs_congr (m := 0) hloc (fun q hq => let h := argRegs_ne q hq; cwEntry_gpr r s h.1 h.2.1 h.2.2)
    (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-- The entry's memory is the caller's in the buffers. -/
theorem cw_agree (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true) (r : Reg) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (armArgs sig s), ∀ x, b.1.Contains x 1 → (cwEntry r s).mem x = s.mem x := by
  have hsb := cw_sp hl hs
  have hres := cw_res hN hl hs
  intro b hb x hx
  exact cwPush_frame s (by omega_using [hsb]) x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact hres b hb x (belowA_sub (by omega_using []) hsb x hc) hx

/-- The caller's precondition gives the first function's at its entry. -/
theorem cw_bodyPre (hN : nsaa sig = 0) (hloc : (locs sig).all (Loc.ok 0) = true)
    (hl : Sig.noLists sig.params = true) {r : Reg}
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cwEntry r s) := by
  have hsb := cw_sp hl hs
  have hag := cw_agree hN hl r hs
  have hres := cw_res hN hl hs
  rw [pre_arm hl, allRegions_eq hN] at hs
  obtain ⟨-, hrd, hwr, hpw, -, hnw, hpr⟩ := hs
  refine (pre_arm hl).mpr ?_
  rw [allRegions_eq hN, cwEntry_armArgs hloc, cwEntry_sp]
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega_using [hsb])
  refine ⟨⟨.inr (by rw [h16]; omega_using [hsb]), by rw [hN, h16]; have := s.sp.isLt; omega_using [this]⟩,
    hrd, hwr, hpw, fun x hx a ha => ?_, hnw, ?_⟩
  · rw [stackBelow_belowA (by rw [h16]; omega_using [hsb]) x hx]
    exact (hres a ha).sub_left (belowA_inner (by omega_using []) hsb)
  · exact hpre _ _ _ (armArgs_length sig s) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The caller's public data is the first function's at its entry. -/
theorem cw_bodyPub (hN : nsaa sig = 0) (hloc : (locs sig).all (Loc.ok 0) = true)
    (hl : Sig.noLists sig.params = true) (r : Reg) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + 16) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + 16) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + 16) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cwEntry r s₁) (cwEntry r s₂) := by
  rw [pubL_arm hl] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  rw [cwEntry_armArgs hloc, cwEntry_armArgs hloc, cwEntry_sp, cwEntry_sp, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa⟩
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ f (armArgs sig s₁) (cwEntry r s₁).mem = Curry.apply _ f (armArgs sig s₂) (cwEntry r s₂).mem
    rw [hleak _ _ _ (armArgs_length sig s₁) (cw_agree hN hl r h₁),
      hleak _ _ _ (armArgs_length sig s₂) (cw_agree hN hl r h₂)]
    exact hlk

/-- What the run of the first function leaves, from the caller's state `s`. -/
def AfterBody (sig : Sig) (post : sig.Post abi.ptrBits) (r : Reg) (stack : Nat) (s c : State) : Prop :=
  c.rd = s.rd ∧ c.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr ∧
  c.sp = s.sp - BitVec.ofNat 32 16 ∧ c.gpr .r4 = s.gpr r ∧
  (∀ q ∈ preserved, q ≠ .lr → q ≠ .r4 → c.gpr q = s.gpr q) ∧
  Frame (s.wr ++ [belowA (s.sp - BitVec.ofNat 32 16) stack]) (cwPush s).mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem c.mem ((c.gpr .r1 ++ c.gpr .r0).setWidth _)

/-- The call of the first function. -/
theorem cw_body_wp {name : String} {body : Prog isa}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hN : nsaa sig = 0) (hloc : (locs sig).all (Loc.ok 0) = true) (hl : Sig.noLists sig.params = true)
    {r : Reg} (hd : armStack body ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    WP isa (.call name body) (cwSave r s) (AfterBody sig post r stack s) := by
  have hsb := cw_sp hl hs
  have hag := cw_agree hN hl r hs
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega_using [hsb])
  refine WP.callF (k := sig.contract abi pre post wa stack leak) h.1 (rd := s.rd) (wr := s.wr)
    (cw_bodyPre hN hloc hl hpre hs)
    (Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx))
    (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx) (by rw [cwSave_sp, h16]; omega_using [hd, hsb]) ?_
  intro c hrd hwr hsp hfr hcs hq
  refine ⟨hrd, hwr, hsp, by rw [hcs .r4 (by decide) (by decide), cwSave_r4], fun q hq hlr h4 => ?_,
    Frame.belowA_mono hfr hd (by rw [h16]; omega_using [hsb]), ?_⟩
  · rw [hcs q hq hlr, cwSave_gpr r s h4]
  · rw [post_arm, show (cwSave r s).callEntry.withRegions s.rd s.wr = cwEntry r s from rfl,
      cwEntry_armArgs hloc, cwEntry_mem, State.withRegions_mem, State.withRegions_gpr] at hq
    exact hpost _ _ _ _ _ (armArgs_length sig s) hag hq

end

/-! ## The zeroize function's contract -/

theorem zeroize_armArgs (X : State) :
    armArgs Spec.Zeroize.zeroizeSig X = [(X.gpr .r0).setWidth 64, (X.gpr .r1).setWidth 64] := rfl

/-- The zeroize function's precondition, from what it says of the state. -/
theorem zeroize_pre_of {zst n : Nat} {X : State} (hn : ((X.gpr .r1).setWidth 64).toNat = n)
    (hwf : zst = 0 ∨ zst ≤ X.sp.toNat) (hrd : X.rd = []) (hwr : X.wr = [⟨(X.gpr .r0).setWidth 64, n⟩])
    (hres : ∀ x ∈ stackBelow (State.addr X.sp) zst, x.Disjoint ⟨(X.gpr .r0).setWidth 64, n⟩)
    (hb : ((X.gpr .r0).setWidth 64).toNat + n ≤ 2 ^ 32) :
    (Spec.Zeroize.zeroizeContract abi zst).pre X := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pre_arm (by decide)).mpr ?_
  have hbz : allRegions Spec.Zeroize.zeroizeSig X = [(⟨(X.gpr .r0).setWidth 64, n⟩, true)] := by
    rw [allRegions_eq (by decide)]
    show [((⟨(X.gpr .r0).setWidth 64, ((X.gpr .r1).setWidth 64).toNat * 1⟩ : Region), true)] = _
    rw [hn, Nat.mul_one]
  have hbs : Sig.bufs Spec.Zeroize.zeroizeSig.params (armArgs Spec.Zeroize.zeroizeSig X) =
      [(⟨(X.gpr .r0).setWidth 64, n⟩, true)] := by rw [← allRegions_eq (by decide)]; exact hbz
  rw [hbz, hbs]
  refine ⟨⟨hwf, by rw [show nsaa Spec.Zeroize.zeroizeSig = 0 by decide]; exact Nat.le_of_lt X.sp.isLt⟩,
    hrd, hwr, List.pairwise_singleton _ _, fun x hx a ha => ?_, fun a ha => ?_, ?_⟩
  · simp only [List.mem_singleton] at ha; subst ha; exact hres x hx
  · simp only [List.mem_singleton] at ha; subst ha; exact hb
  · rw [Curry.apply_const]; trivial

/-- The zeroize function's postcondition. -/
theorem zeroize_post_iff {zst : Nat} {X Y : State} :
    (Spec.Zeroize.zeroizeContract abi zst).post X Y ↔
      Spec.Zeroize.bytesAt Y.mem ((X.gpr .r0).setWidth 64) (((X.gpr .r1).setWidth 64).setWidth 32).toNat =
        Spec.Zeroize.zeros (((X.gpr .r1).setWidth 64).setWidth 32).toNat := Iff.rfl

/-- The zeroize function's public data. -/
theorem zeroize_pub_of {zst : Nat} {X₁ X₂ : State} (hsp : X₁.sp = X₂.sp)
    (h0 : X₁.gpr .r0 = X₂.gpr .r0) (h1 : X₁.gpr .r1 = X₂.gpr .r1) :
    (Spec.Zeroize.zeroizeContract abi zst).pub X₁ X₂ := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pubL_arm (by decide)).mpr ⟨⟨hsp, trivial⟩, fun i _ => ?_⟩
  rw [zeroize_armArgs, zeroize_armArgs, h0, h1]

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {r : Reg}

/-- What the caller's contract gives of the array: its region is within the
writable ones. -/
theorem cw_array (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k : Nat} {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s)
    (harr : (⟨(s.gpr r).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (armArgs sig s)) :
    (⟨(s.gpr r).setWidth 64, k * e.size⟩ : Region) ∈ s.wr ∧
      ((s.gpr r).setWidth 64).toNat + k * e.size ≤ 2 ^ 32 := by
  rw [pre_arm hl, allRegions_eq hN] at hs
  obtain ⟨-, -, hwr, -, -, hnw, -⟩ := hs
  exact ⟨hwr ▸ List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨harr, rfl⟩, rfl⟩, hnw _ harr⟩

theorem toNat_ofNat32 {n : Nat} (hn : n < 2 ^ 32) : ((BitVec.ofNat 32 n).setWidth 64).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_using [hn])]

/-- The zeroize function's entry state. -/
theorem cwZeroEntry_gpr {s c : State} (hc : AfterBody sig post r stack s c) (n : Nat) (R : Region) :
    ((cwZero n c).callEntry.withRegions [] [R]).gpr .r0 = s.gpr r ∧
      ((cwZero n c).callEntry.withRegions [] [R]).gpr .r1 = BitVec.ofNat 32 n ∧
      ((cwZero n c).callEntry.withRegions [] [R]).sp = s.sp - BitVec.ofNat 32 16 := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    cwZero_r0, cwZero_r1, hc.2.2.2.1]
  exact ⟨rfl, rfl, hc.2.2.1⟩

/-- The zeroize function's precondition, at its entry. -/
theorem cw_zeroPre (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n zst : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s)
    (harr : (⟨(s.gpr r).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (armArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hzs : zst ≤ stack) (hc : AfterBody sig post r stack s c) :
    (Spec.Zeroize.zeroizeContract abi zst).pre
      ((cwZero n c).callEntry.withRegions [] [⟨(s.gpr r).setWidth 64, n⟩]) := by
  have hsb := cw_sp hl hs
  have hA := cw_res hN hl hs _ harr
  have hnw := (cw_array hN hl hs harr).2
  have hsubA : Region.Sub ⟨(s.gpr r).setWidth 64, n⟩ ⟨(s.gpr r).setWidth 64, k * e.size⟩ :=
    Region.sub_prefix hn
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega_using [hsb])
  obtain ⟨hdi, hsi, hsp⟩ := cwZeroEntry_gpr hc n ⟨(s.gpr r).setWidth 64, n⟩
  refine zeroize_pre_of (n := n) (by rw [hsi]; exact toNat_ofNat32 hn32) (.inr ?_) rfl
    (by rw [hdi]; rfl) ?_ (by rw [hdi]; omega_using [hnw, hn])
  · rw [hsp, h16]; omega_using [hsb, hzs]
  · rw [hsp, hdi]
    intro x hx
    rw [stackBelow_belowA (by rw [h16]; omega_using [hsb, hzs]) x hx]
    exact (hA.sub_left (belowA_inner (by omega_using [hzs]) hsb)).sub_right hsubA

/-- The zeroize function's public data, at its entry, if the array's
address is public. -/
theorem cw_zeroPub {n zst : Nat} {s₁ s₂ c₁ c₂ : State} (hsp : s₁.sp = s₂.sp)
    (hpp : s₁.gpr r = s₂.gpr r) (hc₁ : AfterBody sig post r stack s₁ c₁)
    (hc₂ : AfterBody sig post r stack s₂ c₂) :
    (Spec.Zeroize.zeroizeContract abi zst).pub
      ((cwZero n c₁).callEntry.withRegions [] [⟨(s₁.gpr r).setWidth 64, n⟩])
      ((cwZero n c₂).callEntry.withRegions [] [⟨(s₂.gpr r).setWidth 64, n⟩]) := by
  obtain ⟨d₁, i₁, p₁⟩ := cwZeroEntry_gpr hc₁ n ⟨(s₁.gpr r).setWidth 64, n⟩
  obtain ⟨d₂, i₂, p₂⟩ := cwZeroEntry_gpr hc₂ n ⟨(s₂.gpr r).setWidth 64, n⟩
  exact zeroize_pub_of (by rw [p₁, p₂, hsp]) (by rw [d₁, d₂, hpp]) (by rw [i₁, i₂])

/-- What the zeroize function's run leaves, from the caller's state `s`: the
first function's, but for the first `n` bytes of the array, which are zero,
and its result, in `r5` and `r6`. -/
def AfterZero (sig : Sig) (post : sig.Post abi.ptrBits) (r : Reg) (stack n : Nat) (s g : State) : Prop :=
  ∃ c, AfterBody sig post r stack s c ∧
    g.rd = s.rd ∧ g.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr ∧
    g.sp = s.sp - BitVec.ofNat 32 16 ∧ g.gpr .r5 = c.gpr .r0 ∧ g.gpr .r6 = c.gpr .r1 ∧
    (∀ q ∈ preserved, q ≠ .lr → q ≠ .r4 → q ≠ .r5 → q ≠ .r6 → g.gpr q = s.gpr q) ∧
    Frame (s.wr ++ [belowA (s.sp - BitVec.ofNat 32 16) stack]) (cwPush s).mem g.mem ∧
    Frame [⟨(s.gpr r).setWidth 64, n⟩, belowA (s.sp - BitVec.ofNat 32 16) stack] c.mem g.mem ∧
    Spec.Zeroize.bytesAt g.mem ((s.gpr r).setWidth 64) n = Spec.Zeroize.zeros n

/-- The zeroize function may write only the first `n` bytes of the array. -/
theorem cw_zeroCovers (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s)
    (harr : (⟨(s.gpr r).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (armArgs sig s))
    (hn : n ≤ k * e.size) (hc : AfterBody sig post r stack s c) :
    Covers [⟨(s.gpr r).setWidth 64, n⟩] (cwZero n c).wr :=
  Covers.one ⟨_, by rw [cwZero_wr, hc.2.1]; exact List.mem_cons_of_mem _ (cw_array hN hl hs harr).1, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn⟩

theorem preserved_ne : ∀ q ∈ preserved, q ≠ .r0 ∧ q ≠ .r1 ∧ q ≠ .r12 := by decide

/-- The call of the zeroize function. -/
theorem cw_zero_wp {zname : String} {zcode : Prog isa} {zst : Nat}
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack)
    (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s)
    (harr : (⟨(s.gpr r).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (armArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hc : AfterBody sig post r stack s c) :
    WP isa (.call zname zcode) (cwZero n c) (AfterZero sig post r stack n s) := by
  have hsb := cw_sp hl hs
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega_using [hsb])
  obtain ⟨hAw, -⟩ := cw_array hN hl hs harr
  have hsubA : Region.Sub ⟨(s.gpr r).setWidth 64, n⟩ ⟨(s.gpr r).setWidth 64, k * e.size⟩ :=
    Region.sub_prefix hn
  obtain ⟨hrdc, hwrc, hspc, -, hcsc, hfc, -⟩ := id hc
  have hcw := cw_zeroCovers hN hl hs harr hn hc
  refine WP.callF (k := Spec.Zeroize.zeroizeContract abi zst) hz.1
    (cw_zeroPre hN hl hs harr hn hn32 hzs hc) (Covers.right hcw) hcw
    (by rw [cwZero_sp, hspc, h16]; omega_using [hzd, hzs, hsb]) ?_
  intro g hrd hwr hsp hfr hcs hq
  rw [cwZero_sp, hspc, cwZero_mem] at hfr
  have hbz : Region.Sub (belowA (s.sp - BitVec.ofNat 32 16) (armStack zcode))
      (belowA (s.sp - BitVec.ofNat 32 16) stack) :=
    belowA_sub (by omega_using [hzd, hzs]) (by rw [h16]; omega_using [hsb])
  refine ⟨c, hc, by rw [hrd, cwZero_rd, hrdc], by rw [hwr, cwZero_wr, hwrc], by rw [hsp, cwZero_sp, hspc],
    by rw [hcs .r5 (by decide) (by decide), cwZero_r5], by rw [hcs .r6 (by decide) (by decide), cwZero_r6],
    fun q hq hlr h4 h5 h6 => ?_, ?_, ?_, ?_⟩
  · obtain ⟨h0, h1, -⟩ := preserved_ne q hq
    rw [hcs q hq hlr, cwZero_gpr n c h0 h1 h5 h6, hcsc q hq hlr h4]
  · refine Frame.trans hfc (Frame.sub hfr fun x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_left _ hAw, hsubA⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hbz⟩
  · refine Frame.sub hfr fun x hx => ?_
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hbz⟩
  · obtain ⟨hdi, hsi, -⟩ := cwZeroEntry_gpr hc n ⟨(s.gpr r).setWidth 64, n⟩
    rw [zeroize_post_iff, hdi, hsi, State.withRegions_mem, BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32] at hq
    exact hq

end

/-! ## The whole call -/

/-- The state `callWipe` returns in, from the state `g` the zeroize call
leaves: `restoreRet` and the frame's pop. -/
def cwFinal (g : State) : State := popped .r4 16 (cwRestore g)

theorem cwFinal_gpr (g : State) {q : Reg} (h0 : q ≠ .r0) (h1 : q ≠ .r1) (h4 : q ≠ .r4) (h5 : q ≠ .r5)
    (h6 : q ≠ .r6) (hlr : q ≠ .lr) : (cwFinal g).gpr q = g.gpr q := by
  rw [cwFinal, popped_gpr h4, cwRestore, RegUpd.gpr_setReg_of_ne _ _ hlr, RegUpd.gpr_setReg_of_ne _ _ h6,
    RegUpd.gpr_setReg_of_ne _ _ h5, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h0]

theorem cwFinal_regs (g : State) :
    (cwFinal g).gpr .r0 = g.gpr .r5 ∧ (cwFinal g).gpr .r1 = g.gpr .r6 ∧
    (cwFinal g).gpr .r4 = g.mem.readW (State.addr g.sp) 32 ∧
    (cwFinal g).gpr .r5 = g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 4)) 32 ∧
    (cwFinal g).gpr .r6 = g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 8)) 32 ∧
    (cwFinal g).gpr .lr = g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 12)) 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cwFinal, popped_gpr (by decide), cwRestore]
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide),
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide),
      RegUpd.gpr_setReg_self]
  · rw [cwFinal, popped_gpr (by decide), cwRestore]
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide),
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self]
  · simp only [cwFinal, popped, State.setReg, ite_true]; rfl
  · rw [cwFinal, popped_gpr (by decide), cwRestore]
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide),
      RegUpd.gpr_setReg_self]
  · rw [cwFinal, popped_gpr (by decide), cwRestore]
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self]
  · rw [cwFinal, popped_gpr (by decide), cwRestore, RegUpd.gpr_setReg_self]

theorem cwFinal_sp (g : State) : (cwFinal g).sp = g.sp + BitVec.ofNat 32 16 := rfl
theorem cwFinal_mem (g : State) : (cwFinal g).mem = g.mem := rfl

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {r : Reg}

/-- The frame lies apart from what the callees may change. -/
theorem cw_slots (hN : nsaa sig = 0) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ x ∈ s.wr ++ [belowA (s.sp - BitVec.ofNat 32 16) stack], Region.Disjoint (belowA s.sp 16) x := by
  have hsb := cw_sp hl hs
  have hresW := cw_resW hN hl hs
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hresW x hx).sub_left (belowA_sub (by omega_using []) hsb)
  · simp only [List.mem_singleton] at hx; subst hx; exact frame_disj_below s.sp (by omega_using [hsb])

/-- The frame's words, at offsets from the stack pointer after the push. -/
theorem frame_addr {s : State} (hsb : 16 ≤ s.sp.toNat) {k : Nat} (hk : k < 16) :
    State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 k) =
      State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 k :=
  addr_add (by rw [sub_toNat' hsb]; have := s.sp.isLt; omega)

/-- A run of `callWipe` from the caller's state `s`: it keeps what the
calling convention requires, its postcondition is the first function's if
that reads the memory on return only within the buffers apart from the
array (`hout`), and the first `n` bytes of the array are zero. -/
theorem cw_wp {name zname : String} {body zcode : Prog isa} {zst : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hN : nsaa sig = 0) (hloc : (locs sig).all (Loc.ok 0) = true) (hl : Sig.noLists sig.params = true)
    (hd : armStack body ≤ stack) (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {e : Elem} {k n : Nat} (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s)
    (harr : (⟨(s.gpr r).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (armArgs sig s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨(s.gpr r).setWidth 64, k * e.size⟩ → ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₂ x) :
    WP isa (callWipe r n name body zname zcode) s fun G =>
      abiPreserved s G ∧ (sig.contract abi pre post wa (stack + 16) leak).post s G ∧
        Spec.Zeroize.bytesAt G.mem ((s.gpr r).setWidth 64) n = Spec.Zeroize.zeros n := by
  have hsb := cw_sp hl hs
  have hres := cw_res hN hl hs
  have hslots := cw_slots hN hl hs
  have h16 : 16 ≤ s.sp.toNat := by omega_using [hsb]
  refine WP.frame (by decide) (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.seq (WP.block ⟨_, saveArg_run r s, ?_⟩)
  refine WP.seq (WP.mono (cw_body_wp h hN hloc hl hd hpre hpost hs) fun c hc => ?_)
  refine WP.seq (WP.block ⟨_, zeroArgs_run hn32 c, ?_⟩)
  refine WP.seq (WP.mono (cw_zero_wp hz hzd hzs hN hl hs harr hn hn32 hc) fun g hg => ?_)
  obtain ⟨c', hc', -, hwrg, hspg, h5g, h6g, hcsg, hfs, hfc, hz0⟩ := hg
  obtain ⟨r4s, r5s, r6s, lrs⟩ := cwPush_read s h16
  have hrd : ∀ {k : Nat}, k + 4 ≤ 16 →
      g.mem.readW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 k) 32 =
        (cwPush s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 k) 32 :=
    fun hk => hfs.readW (frame_contains _ hk) hslots (by decide)
  have hrd0 : g.mem.readW (State.addr (s.sp - BitVec.ofNat 32 16)) 32 =
      (cwPush s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 16)) 32 := by
    have := @hrd 0 (by decide); rwa [BitVec.add_zero] at this
  have hin : ∀ k ∈ [4, 12, 8], InRegions (g.rd ++ g.wr) (State.addr (g.sp + BitVec.ofNat 32 k)) 4 := by
    intro k hk
    have hk' : k + 4 ≤ 16 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    refine ⟨_, List.mem_append_right _ (by rw [hwrg]; exact List.mem_cons_self ..), ?_⟩
    rw [hspg, frame_addr h16 (by omega)]; exact frame_contains _ hk'
  refine WP.block ⟨_, restoreRet_run hin, ?_⟩
  show abiPreserved s (cwFinal g) ∧ (sig.contract abi pre post wa (stack + 16) leak).post s (cwFinal g) ∧
    Spec.Zeroize.bytesAt (cwFinal g).mem ((s.gpr r).setWidth 64) n = Spec.Zeroize.zeros n
  obtain ⟨f0, f1, f4, f5, f6, flr⟩ := cwFinal_regs g
  refine ⟨⟨fun q hq => ?_, by rw [cwFinal_sp, hspg, BitVec.sub_add_cancel]⟩, ?_, ?_⟩
  · -- The callee-saved registers.
    obtain ⟨h0, h1, -⟩ := preserved_ne q hq
    by_cases hq4 : q = .r4
    · subst hq4; rw [f4, hspg, hrd0, r4s]
    by_cases hq5 : q = .r5
    · subst hq5; rw [f5, hspg, frame_addr h16 (by decide), hrd (by decide), r5s]
    by_cases hq6 : q = .r6
    · subst hq6; rw [f6, hspg, frame_addr h16 (by decide), hrd (by decide), r6s]
    by_cases hqlr : q = .lr
    · subst hqlr; rw [flr, hspg, frame_addr h16 (by decide), hrd (by decide), lrs]
    · rw [cwFinal_gpr g h0 h1 hq4 hq5 hq6 hqlr, hcsg q hq hqlr hq4 hq5 hq6]
  · -- The postcondition, which reads the memory on return only within the buffers apart from the array.
    rw [post_arm, f0, f1, h5g, h6g, cwFinal_mem]
    refine hout c'.mem _ _ (fun b hb hbA x hx => ?_) hc'.2.2.2.2.2.2
    refine (hfc x fun R hR hc => ?_).symm
    rcases List.mem_cons.mp hR with rfl | hR
    · exact hbA x hx (Region.sub_prefix hn x hc)
    · simp only [List.mem_singleton] at hR; subst hR
      exact hres b hb x (belowA_inner (by omega_using []) hsb x hc) hx
  · rw [cwFinal_mem]; exact hz0

end

/-- A call of verified code, narrowed in each run to regions of its own. -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine regionModel.relCT_call hv hct fun s₁ s₂ e₁ e₂ hp h₁ h₂ => ?_
  rw [call_callEntry, Option.some.injEq] at h₁ h₂
  subst h₁ h₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  exact ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, rfl, fun _ _ _ _ _ _ => rfl⟩

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

theorem cwPush_push {s : State} (h : 16 ≤ s.sp.toNat) :
    isa.push (.push [.r4, .r5, .r6, .lr]) s = some (cwPush s) :=
  push_pushed (by decide) (by show 16 ≤ s.sp.toNat; exact h)

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- Code verified against `sig.contract` with `stack` bytes of stack, for a
function whose arguments are all in registers (`hN`, `hloc`), word `i` of
them, in `r`, a writable array of `k` elements `e`, is verified with
`stack + 16` bytes when called by `callWipe`, which then zeroes the first `n`
bytes of the array with code verified against
`Spec.Zeroize.zeroizeContract` (with `zst ≤ stack` bytes of stack), against
the contract whose postcondition `post'` follows from the function's and
those bytes being zero (`hwiped`). Each callee uses no more stack than its
contract gives it (`hd`, `hzd`). The precondition, postcondition and leak
must read the memory on entry only within the function's buffers (`hpre`,
`hpost`, `hleak`), and the postcondition the memory on return only within
those apart from the array (`hpostOut`). -/
theorem Verified.callWipe' {post' : sig.Post abi.ptrBits} {name zname : String}
    {body zcode : Prog isa} {zst : Nat} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {k n i : Nat} {r : Reg}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hN : nsaa sig = 0) (hloc : (locs sig).all (Loc.ok 0) = true) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 32).length)
    (hr : (locs sig).getD i (.reg .r0) = .reg r)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32)
    (hd : armStack body ≤ stack) (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack)
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
    (hsat : ∃ s, (sig.contract abi pre post' wa (stack + 16) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.Arm.callWipe r n name body zname zcode)
      (sig.contract abi pre post' wa (stack + 16) leak) := by
  subst hi
  have hL : (sig.words abi.ptrBits).length = (ps₁.flatMap fun p => p.2.words 32).length + 1 +
      (ps₂.flatMap fun p => p.2.words 32).length := by
    show (sig.params.flatMap fun p => p.2.words 32).length = _
    rw [hps, List.flatMap_append, List.flatMap_cons]
    simp only [List.length_append, Param.words.eq_2, List.length_cons, List.length_nil]
    omega
  have hiL : (ps₁.flatMap fun p => p.2.words 32).length < (locs sig).length := by
    rw [locs, classify_length, widths, List.length_map, hL]; omega
  have hli : (locs sig)[(ps₁.flatMap fun p => p.2.words 32).length] = .reg r := by
    rw [← hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL, Option.getD_some]
  have hget : ∀ s : State, (armArgs sig s).getD (ps₁.flatMap fun p => p.2.words 32).length 0 =
      (s.gpr r).setWidth 64 := fun s => by
    rw [armArgs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiL,
      Option.map_some, Option.getD_some, hli]
    rfl
  -- The array, among the buffers.
  have harr : ∀ s : State, (⟨(s.gpr r).setWidth 64, k * e.size⟩, true) ∈
      Sig.bufs sig.params (armArgs sig s) := by
    intro s
    rw [← hget s, hps]
    exact Sig.bufs_mem_array (pb := 32) ps₂ ps₁ (armArgs sig s)
      (by rw [armArgs_length]; show _ < (sig.words abi.ptrBits).length; rw [hL]; omega)
  -- Its address is public.
  have hpubA : ∀ s₁ s₂, (sig.contract abi pre post wa (stack + 16) leak).pub s₁ s₂ → s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ hp
    have hP : (sig.params.flatMap (·.2.pubs)).getD (ps₁.flatMap fun p => p.2.words 32).length false = true := by
      rw [hps]; exact (Sig.pub_array (pb := 32) ps₁ ps₂).1
    have hW : (widths sig).getD (ps₁.flatMap fun p => p.2.words 32).length 64 = 32 := by
      show ((sig.params.flatMap fun p => p.2.words 32).map (·.bits 32)).getD _ 64 = 32
      rw [hps]; exact (Sig.pub_array (pb := 32) ps₁ ps₂).2
    have h2 := congrArg BitVec.toNat (((pubL_arm hl).mp hp).2 _ hP)
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hW, hget, hget, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (a := (s₁.gpr r).toNat) (by have := (s₁.gpr r).isLt; omega),
      Nat.mod_eq_of_lt (a := (s₂.gpr r).toNat) (by have := (s₂.gpr r).isLt; omega),
      Nat.mod_eq_of_lt (s₁.gpr r).isLt, Nat.mod_eq_of_lt (s₂.gpr r).isLt] at h2
    exact BitVec.eq_of_toNat_eq h2
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + 16) leak).pre s → ∀ m₁ m₂ x,
      (∀ b ∈ Sig.bufs sig.params (armArgs sig s), b.1.Disjoint ⟨(s.gpr r).setWidth 64, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    rw [pre_arm hl, allRegions_eq hN] at hs
    exact hpostOut _ _ _ _ _ (armArgs_length sig s) hs.2.2.2.1 (by rw [hget]; exact hag) hq
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · obtain ⟨t, g, he, habi, hq, hz0⟩ :=
      cw_wp h hz hN hloc hl hd hzd hzs hpre hpost hn hn32 hs (harr s) (hout s hs)
    refine ⟨t, g, he, habi, ?_⟩
    rw [post_arm] at hq ⊢
    exact hwiped _ _ _ _ (armArgs_length sig s) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) ?_
    refine RelCT.mono (P := fun a b => ∃ σ₁ σ₂, ((sig.contract abi pre post' wa (stack + 16) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + 16) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + 16) leak).pub σ₁ σ₂) ∧ a = σ₁ ∧ b = σ₂) ?_
      (fun a b hab => ⟨a, b, hab, rfl, rfl⟩) (fun _ _ h => h)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract abi pre post' wa (stack + 16) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + 16) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + 16) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + 16) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + 16) leak).pre σ₂ := h₂
    have hp' : (sig.contract abi pre post wa (stack + 16) leak).pub σ₁ σ₂ := hp
    have hsp12 : σ₁.sp = σ₂.sp := ((pubL_arm hl).mp hp').1.1
    have hpp := hpubA _ _ hp'
    have hs₁ : 16 ≤ σ₁.sp.toNat := by have := cw_sp hl h₁'; omega_using [this]
    have hs₂ : 16 ≤ σ₂.sp.toNat := by have := cw_sp hl h₂'; omega_using [this]
    have hcov : ∀ σ : State, Covers (σ.rd ++ σ.wr) ((cwSave r σ).rd ++ (cwSave r σ).wr) ∧
        Covers σ.wr (cwSave r σ).wr := fun σ =>
      ⟨Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx⟩
    refine RelCT.mono (P := fun a b => a = σ₁ ∧ b = σ₂) ?_ (fun a b hab => hab.2) (fun _ _ h => h)
    refine RelCT.frame (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact hsp12) ?_
    refine RelCT.mono (P := fun a b => a = cwPush σ₁ ∧ b = cwPush σ₂) ?_ (fun a b hab => ?_)
      (fun _ _ h => h)
    swap
    · obtain ⟨_, _, ⟨rfl, rfl⟩, e₁, e₂⟩ := hab
      rw [cwPush_push hs₁] at e₁
      rw [cwPush_push hs₂] at e₂
      exact ⟨(Option.some.inj e₁).symm, (Option.some.inj e₂).symm⟩
    -- The array's address is kept in `r4`.
    refine RelCT.seq (R := fun a b => a = cwSave r σ₁ ∧ b = cwSave r σ₂)
      (RelCT.block_of fun a b hab => ?_) ?_
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, saveArg_run r σ₁, saveArg_run r σ₂, rfl, rfl⟩
    -- The first function.
    refine RelCT.seq (R := fun c₁ c₂ => AfterBody sig post r stack σ₁ c₁ ∧ AfterBody sig post r stack σ₂ c₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterBody sig post r stack σ₁) (F₂ := AfterBody sig post r stack σ₂)
        (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨σ₁.rd, σ₁.wr, σ₂.rd, σ₂.wr, cw_bodyPre hN hloc hl hpre h₁', cw_bodyPre hN hloc hl hpre h₂',
          cw_bodyPub hN hloc hl r h₁' h₂' hp' hleak, (hcov σ₁).1, (hcov σ₁).2, (hcov σ₂).1, (hcov σ₂).2⟩
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨cw_body_wp h hN hloc hl hd hpre hpost h₁', cw_body_wp h hN hloc hl hd hpre hpost h₂'⟩
    -- The zeroize function's arguments.
    refine RelCT.seq (R := fun d₁ d₂ => (∃ c, AfterBody sig post r stack σ₁ c ∧ d₁ = cwZero n c) ∧
      (∃ c, AfterBody sig post r stack σ₂ c ∧ d₂ = cwZero n c))
      (RelCT.block_of fun c₁ c₂ hc => ⟨_, _, _, zeroArgs_run hn32 c₁, zeroArgs_run hn32 c₂,
        ⟨c₁, hc.1, rfl⟩, ⟨c₂, hc.2, rfl⟩⟩) ?_
    -- The zeroize function.
    refine RelCT.seq (R := fun g₁ g₂ => AfterZero sig post r stack n σ₁ g₁ ∧ AfterZero sig post r stack n σ₂ g₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterZero sig post r stack n σ₁) (F₂ := AfterZero sig post r stack n σ₂)
        (RelCT.callEx hz.1 hz.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨[], [⟨(σ₁.gpr r).setWidth 64, n⟩], [], [⟨(σ₂.gpr r).setWidth 64, n⟩],
          cw_zeroPre hN hl h₁' (harr σ₁) hn hn32 hzs hc₁, cw_zeroPre hN hl h₂' (harr σ₂) hn hn32 hzs hc₂,
          cw_zeroPub hsp12 hpp hc₁ hc₂,
          Covers.right (cw_zeroCovers hN hl h₁' (harr σ₁) hn hc₁), cw_zeroCovers hN hl h₁' (harr σ₁) hn hc₁,
          Covers.right (cw_zeroCovers hN hl h₂' (harr σ₂) hn hc₂), cw_zeroCovers hN hl h₂' (harr σ₂) hn hc₂⟩
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨cw_zero_wp hz hzd hzs hN hl h₁' (harr σ₁) hn hn32 hc₁,
          cw_zero_wp hz hzd hzs hN hl h₂' (harr σ₂) hn hn32 hc₂⟩
    -- The result and the saved registers are restored.
    · refine RelCT.block_of fun g₁ g₂ hg => ?_
      obtain ⟨⟨_, _, _, hw₁, e₁, _⟩, ⟨_, _, _, hw₂, e₂, _⟩⟩ := hg
      have hin : ∀ g σ : State, 16 ≤ σ.sp.toNat →
          g.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr → g.sp = σ.sp - BitVec.ofNat 32 16 →
          ∀ k ∈ [4, 12, 8], InRegions (g.rd ++ g.wr) (State.addr (g.sp + BitVec.ofNat 32 k)) 4 := by
        intro g σ h16 hw he k hk
        have hk' : k + 4 ≤ 16 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
        refine ⟨_, List.mem_append_right _ (by rw [hw]; exact List.mem_cons_self ..), ?_⟩
        rw [he, frame_addr h16 (by omega)]; exact frame_contains _ hk'
      refine ⟨_, cwRestore g₂, _, restoreRet_run (hin g₁ σ₁ hs₁ hw₁ e₁), ?_, trivial⟩
      rw [restoreRet_run (hin g₂ σ₂ hs₂ hw₂ e₂), e₁, e₂, hsp12]

/-- `Verified.callWipe'`, with the function's postcondition. -/
theorem Verified.callWipe {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {k n i : Nat} {r : Reg}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hN : nsaa sig = 0) (hloc : (locs sig).all (Loc.ok 0) = true) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 32).length)
    (hr : (locs sig).getD i (.reg .r0) = .reg r)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32)
    (hd : armStack body ≤ stack) (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack)
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + 16) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.Arm.callWipe r n name body zname zcode)
      (sig.contract abi pre post wa (stack + 16) leak) :=
  Verified.callWipe' h hz hN hloc hl hps hi hr hn hn32 hd hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak

end

/-- The stack `callWipe` and its callees use: its frame, and the larger of
its callees'. -/
theorem armStack_callWipe {r : Reg} {n : Nat} {name zname : String} {body zcode : Prog isa} :
    armStack (Impl.CallWipe.Arm.callWipe r n name body zname zcode) =
      max (armStack body) (armStack zcode) + 16 := by
  simp only [Impl.CallWipe.Arm.callWipe, armStack, Nat.zero_max, Nat.max_zero, List.length_cons,
    List.length_nil]

end VG.Arm
