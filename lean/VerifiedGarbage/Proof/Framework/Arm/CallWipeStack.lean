module

public import VerifiedGarbage.Impl.CallWipe.ArmStack
public import VerifiedGarbage.Proof.Framework.Arm.CallWipe
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
# A call that wipes part of a buffer afterwards, with stack arguments (ARMv7)

`Verified.callWipeStack` is `Verified.callWipe` for a function whose
arguments take `k` words of stack (`nsaa sig = 4 * k`), the array (word `i`)
one of them, at byte offset `off`: verified against `sig.contract` with
`stack` bytes of stack, the function is verified against the same contract
with `stack + 16 + allocSize k` bytes when called by `callWipeStack`;
`Verified.callWipeStack'` adds to the postcondition that the first `n` bytes
of the array are zero on return.

Within `callWipe`'s frame, a frame of `allocSize k` bytes holds a copy of the
caller's stack arguments (`copyArgs`, from `cwsU`): the function runs from
the state after the copy, `cwsV`, with the permissions of its own contract,
which reads its stack arguments in that frame (`cwsEntry`, `cwsRegions`), so
its arguments are its caller's (`cwsEntry_armArgs`). The copy and the frames
lie below the caller's stack pointer, apart from the buffers and from the
caller's stack arguments, which the function's precondition, postcondition
and leak must not read (`hpre`, `hpost`, `hleak`, as for `callWipe`). The
frame is freed before the zeroize function is called, so that call is
`callWipe`'s, but for the array's address, which `r4` holds from the copy.

Constant time: the frames' and the copy's accesses depend on the stack
pointer alone, each callee is constant time, and the zeroize function's
arguments, the array's address and `n`, are public.
-/

@[expose] public section

namespace VG.Arm

open VG.Impl.CallWipe.Arm VG.Impl.CallWipe.ArmStack VG.Impl.StackScratch.Arm VG.Arm.FrameStack

/-! ## The frames -/

/-- The sizes `callWipeStack` needs for `k` words of stack arguments: some,
and the copy's offsets encodable, and the frame's size too. -/
abbrev CwsFits (k : Nat) : Prop :=
  0 < k ∧ allocSize k + 16 + 4 * k ≤ 4096 ∧ encodable (BitVec.ofNat 32 (allocSize k)) = true

theorem CwsFits.size {k : Nat} (h : CwsFits k) :
    (0 < allocSize k ∧ allocSize k < 4096 ∧ allocSize k % 8 = 0 ∧
      encodable (BitVec.ofNat 32 (allocSize k)) = true) ∧ 4 * k ≤ allocSize k := by
  obtain ⟨h0, h1, h2⟩ := h
  have e : allocSize k = 8 * ((k + 1) / 2) := rfl
  exact ⟨⟨by omega, by omega, by omega, h2⟩, by omega⟩

/-- The state the inner frame's body starts in. -/
def cwsU (a : Nat) (s : State) : State := allocated a (cwPush s)

@[simp] theorem cwsU_rd (a : Nat) (s : State) : (cwsU a s).rd = s.rd := rfl
@[simp] theorem cwsU_mem (a : Nat) (s : State) : (cwsU a s).mem = (cwPush s).mem := rfl
@[simp] theorem cwsU_gpr (a : Nat) (s : State) : (cwsU a s).gpr = s.gpr := rfl
theorem cwsU_wr (a : Nat) (s : State) :
    (cwsU a s).wr = belowA (s.sp - BitVec.ofNat 32 16) a ::
      ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr := rfl
theorem cwsU_sp (a : Nat) (s : State) :
    (cwsU a s).sp = s.sp - BitVec.ofNat 32 16 - BitVec.ofNat 32 a := rfl
theorem cwsU_sp' (a : Nat) (s : State) : (cwsU a s).sp = s.sp - BitVec.ofNat 32 (a + 16) := by
  rw [cwsU_sp, BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]

theorem cwsU_toNat {a : Nat} {s : State} (h : a + 16 ≤ s.sp.toNat) :
    (cwsU a s).sp.toNat = s.sp.toNat - (a + 16) := by
  rw [cwsU_sp']; exact sub_toNat' h

/-- The state after `add r12, sp, #0` and the copies. -/
def cwsW (k : Nat) (s : State) : State :=
  copiedState (allocSize k + 16) ((cwsU (allocSize k) s).setReg .r12 (cwsU (allocSize k) s).sp) k

/-- The state after `copyArgs k off`: the array's address, from the copy, in
`r4`. -/
def cwsV (k off : Nat) (s : State) : State :=
  (cwsW k s).setReg .r4 ((cwsW k s).mem.readW (sa (cwsW k s).sp off) 32)

theorem cwsW_sp (k : Nat) (s : State) : (cwsW k s).sp = (cwsU (allocSize k) s).sp := by
  rw [cwsW, copiedState_sp, RegUpd.sp_setReg]
theorem cwsW_rd (k : Nat) (s : State) : (cwsW k s).rd = s.rd := by
  rw [cwsW, copiedState_rd, RegUpd.rd_setReg, cwsU_rd]
theorem cwsW_wr (k : Nat) (s : State) : (cwsW k s).wr = (cwsU (allocSize k) s).wr := by
  rw [cwsW, copiedState_wr, RegUpd.wr_setReg]
theorem cwsW_gpr (k : Nat) (s : State) {q : Reg} (hlr : q ≠ .lr) (h12 : q ≠ .r12) :
    (cwsW k s).gpr q = s.gpr q := by
  rw [cwsW, copiedState_gpr _ _ hlr, RegUpd.gpr_setReg_of_ne _ _ h12, cwsU_gpr]

theorem cwsV_sp (k off : Nat) (s : State) : (cwsV k off s).sp = (cwsU (allocSize k) s).sp := by
  rw [cwsV, RegUpd.sp_setReg, cwsW_sp]
theorem cwsV_rd (k off : Nat) (s : State) : (cwsV k off s).rd = s.rd := by
  rw [cwsV, RegUpd.rd_setReg, cwsW_rd]
theorem cwsV_wr (k off : Nat) (s : State) : (cwsV k off s).wr = (cwsU (allocSize k) s).wr := by
  rw [cwsV, RegUpd.wr_setReg, cwsW_wr]
theorem cwsV_mem (k off : Nat) (s : State) : (cwsV k off s).mem = (cwsW k s).mem := by
  rw [cwsV, RegUpd.mem_setReg]
theorem cwsV_gpr (k off : Nat) (s : State) {q : Reg} (hlr : q ≠ .lr) (h12 : q ≠ .r12) (h4 : q ≠ .r4) :
    (cwsV k off s).gpr q = s.gpr q := by
  rw [cwsV, RegUpd.gpr_setReg_of_ne _ _ h4, cwsW_gpr k s hlr h12]
theorem cwsV_r4 (k off : Nat) (s : State) :
    (cwsV k off s).gpr .r4 = (cwsW k s).mem.readW (sa (cwsU (allocSize k) s).sp off) 32 := by
  rw [cwsV, RegUpd.gpr_setReg_self, cwsW_sp]

theorem addSp0_run (u : State) : execBlock isa [.addSp .r12 0] u = some (u.setReg .r12 u.sp, []) := by
  simp [execBlock, isa, exec, addrs]

/-- The addresses `copyArgs k off` accesses, from the inner frame's stack
pointer `sp`. -/
def cwsTrace (k off : Nat) (sp : BitVec 32) : List Leak :=
  copyTrace (allocSize k + 16) sp k ++ [.addr (sa sp off)]

theorem copyArgs_run {k off : Nat} {s : State} (hk : CwsFits k) (hoff : off + 4 ≤ 4 * k)
    (hsb : allocSize k + 16 ≤ s.sp.toNat)
    (hsrc : ∀ j < k, InRegions s.rd (sa s.sp (4 * j)) 4) :
    execBlock isa (copyArgs k off) (cwsU (allocSize k) s) =
      some (cwsV k off s, cwsTrace k off (cwsU (allocSize k) s).sp) := by
  obtain ⟨-, h4⟩ := hk.size
  obtain ⟨-, hb, -⟩ := hk
  have hU := cwsU_toNat hsb
  have hlt := s.sp.isLt
  have hsrc' : ∀ j, sa (cwsU (allocSize k) s).sp (allocSize k + 16 + 4 * j) = sa s.sp (4 * j) := fun j => by
    rw [cwsU_sp']
    show State.addr _ = State.addr _
    rw [BitVec.ofNat_add (allocSize k + 16) (4 * j), ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have hW : ∀ d, d + 4 ≤ allocSize k →
      (belowA (s.sp - BitVec.ofNat 32 16) (allocSize k)).Contains (sa (cwsU (allocSize k) s).sp d) 4 :=
    fun d hd => by
      rw [sa_eq (by omega)]
      exact Offset.contains_base _ hd (by omega)
  have hc := copies_run (bytes := allocSize k + 16)
    (w := (cwsU (allocSize k) s).setReg .r12 (cwsU (allocSize k) s).sp)
    (by rw [RegUpd.gpr_setReg_self, RegUpd.sp_setReg]) k (by omega)
    (fun j hj => by
      rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.sp_setReg, hsrc', cwsU_rd]
      obtain ⟨r, hr, hcn⟩ := hsrc j hj
      exact ⟨r, List.mem_append_left _ hr, hcn⟩)
    (fun j hj => by
      rw [RegUpd.wr_setReg, RegUpd.sp_setReg, cwsU_wr]
      exact ⟨_, List.mem_cons_self .., hW _ (by omega)⟩)
  have hin : InRegions ((cwsW k s).rd ++ (cwsW k s).wr) (State.addr ((cwsW k s).sp + BitVec.ofNat 32 off)) 4 := by
    rw [cwsW_wr, cwsW_sp, cwsU_wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), hW _ (by omega)⟩
  have hl : execBlock isa [.ldrSp .r4 off] (cwsW k s) =
      some (cwsV k off s, [.addr (sa (cwsW k s).sp off)]) := by
    simp only [execBlock, isa, exec, show off < 4096 by omega, ite_true, State.load32, hin,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil]
    rfl
  rw [copyArgs, execBlock_append, execBlock_append, addSp0_run]
  simp only [Option.bind_some]
  rw [hc]
  simp only [Option.bind_some, Option.map_some]
  rw [show copiedState (allocSize k + 16) ((cwsU (allocSize k) s).setReg .r12 (cwsU (allocSize k) s).sp) k =
    cwsW k s from rfl, hl]
  simp only [Option.map_some, RegUpd.sp_setReg, cwsTrace, List.nil_append, cwsW_sp]

/-- `sa` of the inner frame's stack pointer, above both frames: the caller's
stack arguments. -/
theorem cwsU_sa (k : Nat) (s : State) (j : Nat) :
    sa (cwsU (allocSize k) s).sp (allocSize k + 16 + 4 * j) = sa s.sp (4 * j) := by
  rw [cwsU_sp']
  show State.addr _ = State.addr _
  rw [BitVec.ofNat_add (allocSize k + 16) (4 * j), ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- What the copy leaves in memory: the frames changed, and in the inner
one, the caller's stack arguments. -/
theorem cwsV_facts {k off : Nat} {s : State} (hk : CwsFits k) (hsb : allocSize k + 16 ≤ s.sp.toNat)
    (hfit : s.sp.toNat + 4 * k ≤ 2 ^ 32) :
    Frame [belowA s.sp (allocSize k + 16)] s.mem (cwsV k off s).mem ∧
      Frame [⟨State.addr (cwsU (allocSize k) s).sp, 4 * k⟩] (cwPush s).mem (cwsV k off s).mem ∧
      ∀ j < k, (cwsV k off s).mem.readW (sa (cwsU (allocSize k) s).sp (4 * j)) 32 = stackArg s j := by
  obtain ⟨-, h4⟩ := hk.size
  have hU := cwsU_toNat hsb
  have hlt := s.sp.isLt
  have f0 : Frame [belowA s.sp 16] s.mem (cwPush s).mem := cwPush_frame s (by omega)
  obtain ⟨f1, hv⟩ := copiedState_mem (bytes := allocSize k + 16)
    (w := (cwsU (allocSize k) s).setReg .r12 (cwsU (allocSize k) s).sp) k
    (by rw [RegUpd.sp_setReg]; omega) (by omega)
  rw [RegUpd.sp_setReg, RegUpd.mem_setReg, cwsU_mem] at f1
  simp only [RegUpd.sp_setReg, RegUpd.mem_setReg, cwsU_mem, cwsU_sa] at hv
  have f1' : Frame [⟨State.addr (cwsU (allocSize k) s).sp, 4 * k⟩] (cwPush s).mem (cwsV k off s).mem := by
    rw [cwsV_mem]; exact f1
  refine ⟨Frame.trans (Frame.sub f0 fun r hr => ?_) (Frame.sub f1' fun r hr => ?_), f1', fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, belowA_sub (by omega) hsb⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [cwsU_sp']
    exact Region.sub_prefix (by omega)
  · rw [cwsV_mem]
    refine (hv j hj).trans ?_
    refine f0.readW (r := ⟨sa s.sp (4 * j), 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩
    rw [sa_eq (by omega), addr_sub' (by omega)]
    exact Offset.disjoint_below _ (by omega)

/-- The stack arguments of the caller's that `copyArgs` loads into `r4`. -/
theorem cwsV_r4_eq {k off : Nat} {s : State} (hk : CwsFits k) (hsb : allocSize k + 16 ≤ s.sp.toNat)
    (hfit : s.sp.toNat + 4 * k ≤ 2 ^ 32) (h4 : off % 4 = 0) (hoff : off + 4 ≤ 4 * k) :
    (cwsV k off s).gpr .r4 = stackArg s (off / 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, off = 4 * j := ⟨off / 4, by omega⟩
  rw [cwsV_r4, ← cwsV_mem k (4 * j), Nat.mul_div_cancel_left _ (by decide)]
  exact (cwsV_facts hk hsb hfit).2.2 j (by omega)

/-! ## The caller's contract -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- With `k` words of stack arguments, the regions are the buffers and those
words. -/
theorem allRegions_stack {k : Nat} (hN : nsaa sig = 4 * k) (hk : 0 < k) (s : State) :
    allRegions sig s = Sig.bufs sig.params (armArgs sig s) ++ [(⟨State.addr s.sp, 4 * k⟩, false)] := by
  have h0 : 4 * k ≠ 0 := by omega
  simp [allRegions, argArea, h0, hN, stackArgAddr]

/-- What the caller's contract gives of the stack. -/
theorem cws_sp {T : Nat} (hT : 0 < T) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa T leak).pre s) :
    T ≤ s.sp.toNat ∧ s.sp.toNat + nsaa sig ≤ 2 ^ 32 := by
  rw [pre_arm hl] at hs
  rcases hs.1.1 with h | h
  · omega
  · exact ⟨h, hs.1.2⟩

/-- The stack below the stack pointer that the caller's contract reserves
lies apart from its regions. -/
theorem cws_res {T : Nat} (hT : 0 < T) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa T leak).pre s) :
    ∀ x ∈ allRegions sig s, (belowA s.sp T).Disjoint x.1 := by
  have hsb := (cws_sp hT hl hs).1
  rw [pre_arm hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have hm : belowA s.sp (T' + 1) ∈ stackBelow (State.addr s.sp) (T' + 1) := by
    show _ ∈ [(⟨State.addr s.sp - BitVec.ofNat 64 (T' + 1), T' + 1⟩ : Region)]
    rw [belowA, addr_sub' hsb]; exact List.mem_singleton_self _
  exact hres _ hm

/-- So do the writable regions. -/
theorem cws_resW {T : Nat} (hT : 0 < T) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa T leak).pre s) :
    ∀ x ∈ s.wr, (belowA s.sp T).Disjoint x := by
  have hres := cws_res hT hl hs
  rw [pre_arm hl] at hs
  intro x hx
  rw [hs.2.2.1] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hres b (List.mem_filter.mp hb).1

/-- The caller's stack arguments are readable. -/
theorem cws_src {T k : Nat} (hN : nsaa sig = 4 * k) (hk : 0 < k) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract abi pre post wa T leak).pre s) :
    ∀ j < k, InRegions s.rd (sa s.sp (4 * j)) 4 := by
  rw [pre_arm hl, allRegions_stack hN hk] at hs
  obtain ⟨⟨-, hfit⟩, hrd, -⟩ := hs
  have hlt := s.sp.isLt
  intro j hj
  refine ⟨⟨State.addr s.sp, 4 * k⟩, ?_, ?_⟩
  · rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_singleton_self _),
      rfl⟩, rfl⟩
  · rw [sa_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega)

/-- Each region of the caller's is readable or writable, as it says. -/
theorem cws_mem {T : Nat} (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa T leak).pre s) :
    ∀ x ∈ allRegions sig s, (x.2 = false → x.1 ∈ s.rd) ∧ (x.2 = true → x.1 ∈ s.wr) := by
  rw [pre_arm hl] at hs
  obtain ⟨-, hrd, hwr, -⟩ := hs
  intro x hx
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hrd]; exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp [h]⟩, rfl⟩
  · rw [hwr]; exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, h⟩, rfl⟩

/-! ## The function's entry -/

/-- The regions of the function's contract at its entry: the buffers, and
its stack arguments, in the inner frame. -/
def cwsRegions (sig : Sig) (k : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (armArgs sig s) ++ [(⟨State.addr (cwsU (allocSize k) s).sp, 4 * k⟩, false)]

/-- The state the function runs from, with the permissions of its contract:
after the copy and the call. -/
def cwsEntry (sig : Sig) (k off : Nat) (s : State) : State :=
  (cwsV k off s).callEntry.withRegions (((cwsRegions sig k s).filter (!·.2)).map (·.1))
    (((cwsRegions sig k s).filter (·.2)).map (·.1))

theorem cwsEntry_sp (sig : Sig) (k off : Nat) (s : State) :
    (cwsEntry sig k off s).sp = (cwsU (allocSize k) s).sp := by
  rw [cwsEntry, State.withRegions_sp, State.callEntry_sp, cwsV_sp]
theorem cwsEntry_mem (sig : Sig) (k off : Nat) (s : State) :
    (cwsEntry sig k off s).mem = (cwsV k off s).mem := rfl
theorem cwsEntry_gpr (sig : Sig) (k off : Nat) (s : State) {q : Reg} (h4 : q ≠ .r4) (h12 : q ≠ .r12)
    (hlr : q ≠ .lr) : (cwsEntry sig k off s).gpr q = s.gpr q := by
  have hl : q ∉ linkRegs := by
    simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h12, hlr⟩
  rw [cwsEntry, State.withRegions_gpr, State.callEntry_gpr _ hl, cwsV_gpr k off s hlr h12 h4]

/-- The function's arguments at its entry are its caller's. -/
theorem cwsEntry_armArgs {k off : Nat} (hk : CwsFits k) (hloc : (locs sig).all (Loc.ok (4 * k)) = true)
    {s : State} (hsb : allocSize k + 16 ≤ s.sp.toNat) (hfit : s.sp.toNat + 4 * k ≤ 2 ^ 32) :
    armArgs sig (cwsEntry sig k off s) = armArgs sig s :=
  armArgs_congr hloc
    (fun q hq => let h := argRegs_ne q hq; cwsEntry_gpr sig k off s h.1 h.2.1 h.2.2)
    (fun i hi => by
      show (cwsEntry sig k off s).mem.readW
        (State.addr ((cwsEntry sig k off s).sp + BitVec.ofNat 32 (4 * i))) 32 = _
      rw [cwsEntry_mem, cwsEntry_sp]
      exact (cwsV_facts hk hsb hfit).2.2 i hi)

theorem cwsEntry_allRegions {k off : Nat} (hN : nsaa sig = 4 * k) (hk : CwsFits k)
    (hloc : (locs sig).all (Loc.ok (4 * k)) = true) {s : State} (hsb : allocSize k + 16 ≤ s.sp.toNat)
    (hfit : s.sp.toNat + 4 * k ≤ 2 ^ 32) :
    allRegions sig (cwsEntry sig k off s) = cwsRegions sig k s := by
  rw [allRegions_stack hN hk.1, cwsEntry_armArgs hk hloc hsb hfit, cwsEntry_sp]
  rfl

/-- The function's stack arguments, in the inner frame, among the stack
the caller's contract reserves. -/
theorem cws_argSub {k T : Nat} {s : State} (hsb : T ≤ s.sp.toNat) (hT : allocSize k + 16 ≤ T)
    (h4 : 4 * k ≤ allocSize k) :
    Region.Sub ⟨State.addr (cwsU (allocSize k) s).sp, 4 * k⟩ (belowA s.sp T) := by
  rw [cwsU_sp', addr_sub' (by omega)]
  show Region.Sub _ ⟨State.addr (s.sp - BitVec.ofNat 32 T), T⟩
  rw [addr_sub' hsb]
  exact Offset.sub_below _ hT (by omega)

/-- The entry's memory is the caller's in the buffers. -/
theorem cws_agree {k off : Nat} (hN : nsaa sig = 4 * k) (hk : CwsFits k)
    (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (armArgs sig s), ∀ x, b.1.Contains x 1 →
      (cwsEntry sig k off s).mem x = s.mem x := by
  obtain ⟨hsb, hfit⟩ := cws_sp (by omega) hl hs
  have hres := cws_res (by omega) hl hs
  intro b hb x hx
  exact (cwsV_facts (off := off) hk (by omega) (by omega)).1 x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact hres b (List.mem_append_left _ hb) x (belowA_sub (by omega) hsb x hc) hx

/-- The caller's precondition gives the function's at its entry. -/
theorem cws_bodyPre {k off : Nat} (hN : nsaa sig = 4 * k) (hk : CwsFits k)
    (hloc : (locs sig).all (Loc.ok (4 * k)) = true) (hl : Sig.noLists sig.params = true)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cwsEntry sig k off s) := by
  obtain ⟨hsb, hfit⟩ := cws_sp (by omega) hl hs
  have hres := cws_res (by omega) hl hs
  have hag := cws_agree (off := off) hN hk hl hs
  obtain ⟨-, h4⟩ := hk.size
  have hU := cwsU_toNat (a := allocSize k) (s := s) (by omega)
  have hlt := s.sp.isLt
  rw [pre_arm hl, allRegions_stack hN hk.1] at hs
  obtain ⟨-, -, -, hpw, -, hnw, hpr⟩ := hs
  refine (pre_arm hl).mpr ?_
  rw [cwsEntry_allRegions hN hk hloc (by omega) (by omega), cwsEntry_armArgs hk hloc (by omega) (by omega),
    cwsEntry_sp, hN]
  refine ⟨⟨.inr (by omega), by omega⟩, rfl, rfl, ?_, ?_, hnw, ?_⟩
  · -- The buffers, and the stack arguments apart from them.
    refine List.pairwise_append.mpr ⟨(List.pairwise_append.mp hpw).1, List.pairwise_singleton _ _,
      fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    exact (Region.Disjoint.symm (hres a (List.mem_append_left _ ha))).sub_right
      (cws_argSub hsb (by omega) h4)
  · -- The reserved stack, below the inner frame.
    intro r hr x hx
    rw [stackBelow_belowA (by omega) r hr]
    rcases List.mem_append.mp hx with hx | hx
    · refine (hres x (List.mem_append_left _ hx)).sub_left ?_
      rw [cwsU_sp']
      exact belowA_inner (by omega) hsb
    · simp only [List.mem_singleton] at hx; subst hx
      show Region.Disjoint ⟨State.addr ((cwsU (allocSize k) s).sp - BitVec.ofNat 32 stack), stack⟩ _
      rw [addr_sub' (by omega)]
      exact Region.Disjoint.symm (Offset.base_disjoint_below _ (by omega))
  · exact hpre _ _ _ (armArgs_length sig s) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The caller's public data is the function's at its entry. -/
theorem cws_bodyPub {k off : Nat} (hN : nsaa sig = 4 * k) (hk : CwsFits k)
    (hloc : (locs sig).all (Loc.ok (4 * k)) = true) (hl : Sig.noLists sig.params = true) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cwsEntry sig k off s₁) (cwsEntry sig k off s₂) := by
  obtain ⟨hsb₁, hfit₁⟩ := cws_sp (by omega) hl h₁
  obtain ⟨hsb₂, hfit₂⟩ := cws_sp (by omega) hl h₂
  rw [pubL_arm hl] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  rw [cwsEntry_armArgs hk hloc (by omega) (by omega), cwsEntry_armArgs hk hloc (by omega) (by omega),
    cwsEntry_sp, cwsEntry_sp, cwsU_sp, cwsU_sp, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa⟩
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ f (armArgs sig s₁) (cwsEntry sig k off s₁).mem =
      Curry.apply _ f (armArgs sig s₂) (cwsEntry sig k off s₂).mem
    rw [hleak _ _ _ (armArgs_length sig s₁) (cws_agree hN hk hl h₁),
      hleak _ _ _ (armArgs_length sig s₂) (cws_agree hN hk hl h₂)]
    exact hlk

/-- The function's permissions at its entry are among those of the state
after the copy. -/
theorem cws_bodyCovers {k off : Nat} (hN : nsaa sig = 4 * k) (hk : CwsFits k)
    (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s) :
    Covers ((((cwsRegions sig k s).filter (!·.2)).map (·.1)) ++
        (((cwsRegions sig k s).filter (·.2)).map (·.1))) ((cwsV k off s).rd ++ (cwsV k off s).wr) ∧
      Covers (((cwsRegions sig k s).filter (·.2)).map (·.1)) (cwsV k off s).wr := by
  obtain ⟨-, h4⟩ := hk.size
  have hm := cws_mem hl hs
  rw [allRegions_stack hN hk.1] at hm
  have hB : ∀ x ∈ Sig.bufs sig.params (armArgs sig s), x.2 = true →
      x.1 ∈ (cwsV k off s).wr := fun x hx h => by
    rw [cwsV_wr, cwsU_wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((hm x (List.mem_append_left _ hx)).2 h))
  have hall : ∀ x ∈ cwsRegions sig k s, Covers [x.1] ((cwsV k off s).rd ++ (cwsV k off s).wr) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · cases h2 : x.2
      · exact Covers.left (Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [cwsV_rd]; exact (hm x (List.mem_append_left _ hx)).1 h2)
      · exact Covers.right (Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hB x hx h2)
    · simp only [List.mem_singleton] at hx; subst hx
      refine Covers.right (Covers.one ⟨_, by rw [cwsV_wr, cwsU_wr]; exact List.mem_cons_self .., ?_⟩)
      show (⟨State.addr (cwsU (allocSize k) s).sp, allocSize k⟩ : Region).Contains
        (State.addr (cwsU (allocSize k) s).sp) (4 * k)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h4
  refine ⟨Covers.of_forall fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr <;>
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact hall x (List.mem_filter.mp hx).1
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hx, h2⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hB x hx h2
    · simp only [List.mem_singleton] at hx; subst hx; simp at h2

/-- What the inner frame leaves, from the caller's state `s`: the array's
address `A` in `r4`. -/
def AfterBodyS (sig : Sig) (post : sig.Post abi.ptrBits) (A : BitVec 32) (st : Nat) (s c : State) : Prop :=
  c.rd = s.rd ∧ c.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr ∧
  c.sp = s.sp - BitVec.ofNat 32 16 ∧ c.gpr .r4 = A ∧
  (∀ q ∈ preserved, q ≠ .lr → q ≠ .r4 → c.gpr q = s.gpr q) ∧
  Frame (s.wr ++ [belowA (s.sp - BitVec.ofNat 32 16) st]) (cwPush s).mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem c.mem ((c.gpr .r1 ++ c.gpr .r0).setWidth _)

/-- The inner frame: the copy, and the call of the function. -/
theorem cws_body_wp {name : String} {body : Prog isa} {k off : Nat} {A : BitVec 32}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hN : nsaa sig = 4 * k) (hloc : (locs sig).all (Loc.ok (4 * k)) = true)
    (hl : Sig.noLists sig.params = true) (hk : CwsFits k) (hoff : off + 4 ≤ 4 * k)
    (hd : armStack body ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s)
    (hA : (cwsV k off s).gpr .r4 = A) :
    WP isa (.frame (.alloc (allocSize k)) (.seq (.block (copyArgs k off)) (.call name body))
      (.free (allocSize k))) (cwPush s) (AfterBodyS sig post A (stack + allocSize k) s) := by
  obtain ⟨hsb, hfit⟩ := cws_sp (by omega) hl hs
  obtain ⟨hsz, h4⟩ := hk.size
  have hU := cwsU_toNat (a := allocSize k) (s := s) (by omega)
  have hag := cws_agree (off := off) hN hk hl hs
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  obtain ⟨-, f1, -⟩ := cwsV_facts (off := off) (s := s) hk (by omega) (by omega)
  obtain ⟨hcov, hcovW⟩ := cws_bodyCovers (off := off) hN hk hl hs
  have hm := cws_mem hl hs
  rw [allRegions_stack hN hk.1] at hm
  refine WP.alloc hsz (by rw [cwPush_sp, h16]; omega) ?_
  refine WP.seq (WP.block ⟨_, copyArgs_run hk hoff (by omega) (cws_src hN hk.1 hl hs), ?_⟩)
  refine WP.callF (k := sig.contract abi pre post wa stack leak) h.1 (cws_bodyPre hN hk hloc hl hpre hs)
    hcov hcovW (by rw [cwsV_sp, hU]; omega) ?_
  intro c hrd hwr hsp hfr hcs hq
  have hsub : Region.Sub (belowA (s.sp - BitVec.ofNat 32 16) (allocSize k))
      (belowA (s.sp - BitVec.ofNat 32 16) (stack + allocSize k)) :=
    belowA_sub (by omega) (by rw [h16]; omega)
  refine ⟨by show c.rd = s.rd; rw [hrd, cwsV_rd], by show c.wr.tail = _; rw [hwr, cwsV_wr, cwsU_wr]; rfl,
    by show c.sp + _ = _; rw [hsp, cwsV_sp, cwsU_sp, BitVec.sub_add_cancel],
    by show c.gpr .r4 = A; rw [hcs .r4 (by decide) (by decide), hA], fun q hq hlr h4 => ?_, ?_, ?_⟩
  · obtain ⟨-, -, h12⟩ := preserved_ne q hq
    show c.gpr q = s.gpr q
    rw [hcs q hq hlr, cwsV_gpr k off s hlr h12 h4]
  · -- The copy, the buffers, and the stack below the inner frame.
    refine Frame.trans (Frame.sub f1 fun r hr => ?_) (Frame.sub hfr fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        fun x hx => hsub x (Region.sub_prefix h4 x hx)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
        obtain ⟨hx, h2⟩ := List.mem_filter.mp hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨_, List.mem_append_left _ ((hm x (List.mem_append_left _ hx)).2 h2), fun _ h => h⟩
        · simp only [List.mem_singleton] at hx; subst hx; simp at h2
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [cwsV_sp, cwsU_sp]
        exact belowA_inner (by omega) (by rw [h16]; omega)
  · -- The postcondition, which reads the memory on entry only within the buffers.
    rw [post_arm, show (cwsV k off s).callEntry.withRegions (((cwsRegions sig k s).filter (!·.2)).map (·.1))
        (((cwsRegions sig k s).filter (·.2)).map (·.1)) = cwsEntry sig k off s from rfl,
      cwsEntry_armArgs hk hloc (by omega) (by omega), State.withRegions_mem, State.withRegions_gpr] at hq
    exact hpost _ _ _ _ _ (armArgs_length sig s) hag hq

end

/-! ## The zeroize function -/

section
variable {sig : Sig} {post : sig.Post abi.ptrBits}

/-- The zeroize function's entry state. -/
theorem cwsZeroEntry_gpr {A : BitVec 32} {st : Nat} {s c : State} (hc : AfterBodyS sig post A st s c)
    (n : Nat) (R : Region) :
    ((cwZero n c).callEntry.withRegions [] [R]).gpr .r0 = A ∧
      ((cwZero n c).callEntry.withRegions [] [R]).gpr .r1 = BitVec.ofNat 32 n ∧
      ((cwZero n c).callEntry.withRegions [] [R]).sp = s.sp - BitVec.ofNat 32 16 := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    cwZero_r0, cwZero_r1, hc.2.2.2.1]
  exact ⟨rfl, rfl, hc.2.2.1⟩

/-- The zeroize function's precondition, at its entry: the array lies in
the caller's writable regions, apart from the stack it reserves (`T`
bytes). -/
theorem cws_zeroPre {A : BitVec 32} {K n zst st T : Nat} {s c : State} (hsb : T ≤ s.sp.toNat)
    (hT : st + 16 ≤ T) (hA : (belowA s.sp T).Disjoint ⟨A.setWidth 64, K⟩)
    (hnw : (A.setWidth 64).toNat + K ≤ 2 ^ 32) (hn : n ≤ K) (hn32 : n < 2 ^ 32) (hzs : zst ≤ st)
    (hc : AfterBodyS sig post A st s c) :
    (Spec.Zeroize.zeroizeContract abi zst).pre
      ((cwZero n c).callEntry.withRegions [] [⟨A.setWidth 64, n⟩]) := by
  have hsubA : Region.Sub ⟨A.setWidth 64, n⟩ ⟨A.setWidth 64, K⟩ := Region.sub_prefix hn
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  obtain ⟨hdi, hsi, hsp⟩ := cwsZeroEntry_gpr hc n ⟨A.setWidth 64, n⟩
  refine zeroize_pre_of (n := n) (by rw [hsi]; exact toNat_ofNat32 hn32) (.inr ?_) rfl
    (by rw [hdi]; rfl) ?_ (by rw [hdi]; omega)
  · rw [hsp, h16]; omega
  · rw [hsp, hdi]
    intro x hx
    rw [stackBelow_belowA (by rw [h16]; omega) x hx]
    exact (hA.sub_left (belowA_inner (by omega) hsb)).sub_right hsubA

/-- The zeroize function's public data, at its entry, if the array's
address is public. -/
theorem cws_zeroPub {A₁ A₂ : BitVec 32} {n zst st : Nat} {s₁ s₂ c₁ c₂ : State} (hsp : s₁.sp = s₂.sp)
    (hpp : A₁ = A₂) (hc₁ : AfterBodyS sig post A₁ st s₁ c₁) (hc₂ : AfterBodyS sig post A₂ st s₂ c₂) :
    (Spec.Zeroize.zeroizeContract abi zst).pub
      ((cwZero n c₁).callEntry.withRegions [] [⟨A₁.setWidth 64, n⟩])
      ((cwZero n c₂).callEntry.withRegions [] [⟨A₂.setWidth 64, n⟩]) := by
  obtain ⟨d₁, i₁, p₁⟩ := cwsZeroEntry_gpr hc₁ n ⟨A₁.setWidth 64, n⟩
  obtain ⟨d₂, i₂, p₂⟩ := cwsZeroEntry_gpr hc₂ n ⟨A₂.setWidth 64, n⟩
  exact zeroize_pub_of (by rw [p₁, p₂, hsp]) (by rw [d₁, d₂, hpp]) (by rw [i₁, i₂])

/-- What the zeroize function's run leaves, from the caller's state `s`: the
inner frame's, but for the first `n` bytes of the array, which are zero, and
its result, in `r5` and `r6`. -/
def AfterZeroS (sig : Sig) (post : sig.Post abi.ptrBits) (A : BitVec 32) (st n : Nat) (s g : State) : Prop :=
  ∃ c, AfterBodyS sig post A st s c ∧
    g.rd = s.rd ∧ g.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr ∧
    g.sp = s.sp - BitVec.ofNat 32 16 ∧ g.gpr .r5 = c.gpr .r0 ∧ g.gpr .r6 = c.gpr .r1 ∧
    (∀ q ∈ preserved, q ≠ .lr → q ≠ .r4 → q ≠ .r5 → q ≠ .r6 → g.gpr q = s.gpr q) ∧
    Frame (s.wr ++ [belowA (s.sp - BitVec.ofNat 32 16) st]) (cwPush s).mem g.mem ∧
    Frame [⟨A.setWidth 64, n⟩, belowA (s.sp - BitVec.ofNat 32 16) st] c.mem g.mem ∧
    Spec.Zeroize.bytesAt g.mem (A.setWidth 64) n = Spec.Zeroize.zeros n

/-- The zeroize function may write only the first `n` bytes of the array. -/
theorem cws_zeroCovers {A : BitVec 32} {K n st : Nat} {s c : State}
    (hAw : (⟨A.setWidth 64, K⟩ : Region) ∈ s.wr) (hn : n ≤ K) (hc : AfterBodyS sig post A st s c) :
    Covers [⟨A.setWidth 64, n⟩] (cwZero n c).wr :=
  Covers.one ⟨_, by rw [cwZero_wr, hc.2.1]; exact List.mem_cons_of_mem _ hAw, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn⟩

/-- The call of the zeroize function. -/
theorem cws_zero_wp {zname : String} {zcode : Prog isa} {zst : Nat}
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hzd : armStack zcode ≤ zst) {A : BitVec 32} {K n st T : Nat} {s c : State} (hzs : zst ≤ st)
    (hsb : T ≤ s.sp.toNat) (hT : st + 16 ≤ T) (hAw : (⟨A.setWidth 64, K⟩ : Region) ∈ s.wr)
    (hA : (belowA s.sp T).Disjoint ⟨A.setWidth 64, K⟩) (hnw : (A.setWidth 64).toNat + K ≤ 2 ^ 32)
    (hn : n ≤ K) (hn32 : n < 2 ^ 32) (hc : AfterBodyS sig post A st s c) :
    WP isa (.call zname zcode) (cwZero n c) (AfterZeroS sig post A st n s) := by
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  have hsubA : Region.Sub ⟨A.setWidth 64, n⟩ ⟨A.setWidth 64, K⟩ := Region.sub_prefix hn
  obtain ⟨hrdc, hwrc, hspc, -, hcsc, hfc, -⟩ := id hc
  have hcw := cws_zeroCovers hAw hn hc
  refine WP.callF (k := Spec.Zeroize.zeroizeContract abi zst) hz.1
    (cws_zeroPre hsb hT hA hnw hn hn32 hzs hc) (Covers.right hcw) hcw
    (by rw [cwZero_sp, hspc, h16]; omega) ?_
  intro g hrd hwr hsp hfr hcs hq
  rw [cwZero_sp, hspc, cwZero_mem] at hfr
  have hbz : Region.Sub (belowA (s.sp - BitVec.ofNat 32 16) (armStack zcode))
      (belowA (s.sp - BitVec.ofNat 32 16) st) :=
    belowA_sub (by omega) (by rw [h16]; omega)
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
  · obtain ⟨hdi, hsi, -⟩ := cwsZeroEntry_gpr hc n ⟨A.setWidth 64, n⟩
    rw [zeroize_post_iff, hdi, hsi, State.withRegions_mem, BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32] at hq
    exact hq

end

/-! ## The whole call -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The frame lies apart from what the callees may change. -/
theorem cws_slots {T st : Nat} {s : State} (hsb : T ≤ s.sp.toNat) (hT : st + 16 ≤ T)
    (hresW : ∀ x ∈ s.wr, (belowA s.sp T).Disjoint x) :
    ∀ x ∈ s.wr ++ [belowA (s.sp - BitVec.ofNat 32 16) st], Region.Disjoint (belowA s.sp 16) x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hresW x hx).sub_left (belowA_sub (by omega) hsb)
  · simp only [List.mem_singleton] at hx; subst hx; exact frame_disj_below s.sp (by omega)

/-- A run of `callWipeStack` from the caller's state `s`: it keeps what the
calling convention requires, its postcondition is the function's if that
reads the memory on return only within the buffers apart from the array
(`hout`), and the first `n` bytes of the array, at `A`, are zero. -/
theorem cws_wp {name zname : String} {body zcode : Prog isa} {zst k off : Nat} {A : BitVec 32}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hN : nsaa sig = 4 * k) (hloc : (locs sig).all (Loc.ok (4 * k)) = true)
    (hl : Sig.noLists sig.params = true) (hk : CwsFits k) (hoff : off + 4 ≤ 4 * k)
    (hd : armStack body ≤ stack) (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack + allocSize k)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {e : Elem} {kk n : Nat} (hn : n ≤ kk * e.size) (hn32 : n < 2 ^ 32)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s)
    (hA4 : (cwsV k off s).gpr .r4 = A)
    (harr : (⟨A.setWidth 64, kk * e.size⟩, true) ∈ Sig.bufs sig.params (armArgs sig s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨A.setWidth 64, kk * e.size⟩ → ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₂ x) :
    WP isa (callWipeStack k off n name body zname zcode) s fun G =>
      abiPreserved s G ∧ (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).post s G ∧
        Spec.Zeroize.bytesAt G.mem (A.setWidth 64) n = Spec.Zeroize.zeros n := by
  obtain ⟨hsb, -⟩ := cws_sp (by omega) hl hs
  have hres := cws_res (by omega) hl hs
  have hresW := cws_resW (by omega) hl hs
  have hslots := cws_slots (st := stack + allocSize k) hsb (by omega) hresW
  have hAw := (cws_mem hl hs _ (List.mem_append_left _ harr)).2 rfl
  have hnw : (A.setWidth 64).toNat + kk * e.size ≤ 2 ^ 32 := by
    have hs' := hs
    rw [pre_arm hl] at hs'
    exact hs'.2.2.2.2.2.1 _ harr
  have h16 : 16 ≤ s.sp.toNat := by omega
  refine WP.frame (by decide) (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.seq (WP.mono (cws_body_wp h hN hloc hl hk hoff hd hpre hpost hs hA4) fun c hc => ?_)
  refine WP.seq (WP.block ⟨_, zeroArgs_run hn32 c, ?_⟩)
  refine WP.seq (WP.mono (cws_zero_wp hz hzd hzs hsb (by omega) hAw
    (hres _ (List.mem_append_left _ harr)) hnw hn hn32 hc) fun g hg => ?_)
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
  show abiPreserved s (cwFinal g) ∧
    (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).post s (cwFinal g) ∧
    Spec.Zeroize.bytesAt (cwFinal g).mem (A.setWidth 64) n = Spec.Zeroize.zeros n
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
      exact hres b (List.mem_append_left _ hb) x (belowA_inner (by omega) hsb x hc) hx
  · rw [cwFinal_mem]; exact hz0

end

/-- Two runs of a frame that reserves stack leak the same trace if the runs
of its body do. -/
theorem RelCT.allocFrame {bytes : Nat} {body : Prog isa} {P : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocated bytes s₁ ∧ b = allocated bytes s₂)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea : ∀ {s a : State}, isa.push (.alloc bytes) s = some a → a = allocated bytes s := by
        intro s a h
        simp only [isa, push] at h
        split at h <;> [cases h; cases h]
        rfl
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, ea p₁, ea p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp only [addrs]

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What the caller's contract gives of the array, at `A`: it is writable,
apart from the stack the contract reserves, and does not wrap around. -/
theorem cws_array {T : Nat} (hT : 0 < T) (hl : Sig.noLists sig.params = true) {A : BitVec 32} {K : Nat}
    {s : State} (hs : (sig.contract abi pre post wa T leak).pre s)
    (harr : (⟨A.setWidth 64, K⟩, true) ∈ Sig.bufs sig.params (armArgs sig s)) :
    T ≤ s.sp.toNat ∧ (⟨A.setWidth 64, K⟩ : Region) ∈ s.wr ∧
      (belowA s.sp T).Disjoint ⟨A.setWidth 64, K⟩ ∧ (A.setWidth 64).toNat + K ≤ 2 ^ 32 := by
  refine ⟨(cws_sp hT hl hs).1, (cws_mem hl hs _ (List.mem_append_left _ harr)).2 rfl,
    cws_res hT hl hs _ (List.mem_append_left _ harr), ?_⟩
  rw [pre_arm hl] at hs
  exact hs.2.2.2.2.2.1 _ harr

/-- Code verified against `sig.contract` with `stack` bytes of stack, for a
function whose arguments take `r0`–`r3` and `k` words of stack (`hN`,
`hloc`), word `i` of them, the stack argument at byte offset `off` (`hr`), a
writable array of `kk` elements `e`, is verified with
`stack + 16 + allocSize k` bytes when called by `callWipeStack`, which then
zeroes the first `n` bytes of the array with code verified against
`Spec.Zeroize.zeroizeContract` (with `zst ≤ stack + allocSize k` bytes of
stack), against the contract whose postcondition `post'` follows from the
function's and those bytes being zero (`hwiped`). Each callee uses no more
stack than its contract gives it (`hd`, `hzd`). The precondition,
postcondition and leak must read the memory on entry only within the
function's buffers (`hpre`, `hpost`, `hleak`), and the postcondition the
memory on return only within those apart from the array (`hpostOut`). -/
theorem Verified.callWipeStack' {post' : sig.Post abi.ptrBits} {name zname : String}
    {body zcode : Prog isa} {zst : Nat} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {kk n i k off : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hN : nsaa sig = 4 * k) (hloc : (locs sig).all (Loc.ok (4 * k)) = true)
    (hl : Sig.noLists sig.params = true) (hk : CwsFits k)
    (hps : sig.params = ps₁ ++ (nm, .array true e kk) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 32).length)
    (hr : (locs sig).getD i (.reg .r0) = .stack off 32)
    (hn : n ≤ kk * e.size) (hn32 : n < 2 ^ 32)
    (hd : armStack body ≤ stack) (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack + allocSize k)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, kk * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hwiped : ∀ vs m m' x, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) post vs m m' x →
      Spec.Zeroize.bytesAt m' (vs.getD i 0) n = Spec.Zeroize.zeros n →
        Curry.apply (sig.words abi.ptrBits) post' vs m m' x)
    (hsat : ∃ s, (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (callWipeStack k off n name body zname zcode)
      (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak) := by
  subst hi
  have hL : (sig.words abi.ptrBits).length = (ps₁.flatMap fun p => p.2.words 32).length + 1 +
      (ps₂.flatMap fun p => p.2.words 32).length := by
    show (sig.params.flatMap fun p => p.2.words 32).length = _
    rw [hps, List.flatMap_append, List.flatMap_cons]
    simp only [List.length_append, Param.words.eq_2, List.length_cons, List.length_nil]
    omega
  have hiL : (ps₁.flatMap fun p => p.2.words 32).length < (locs sig).length := by
    rw [locs, classify_length, widths, List.length_map, hL]; omega
  have hli : (locs sig)[(ps₁.flatMap fun p => p.2.words 32).length] = .stack off 32 := by
    rw [← hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL, Option.getD_some]
  -- The array's address is the stack argument at `off`, a whole slot among the first `4k` bytes.
  obtain ⟨hoff4, hoff⟩ : off % 4 = 0 ∧ off + 4 ≤ 4 * k := by
    have := List.all_eq_true.mp hloc _ (List.getElem_mem hiL)
    rw [hli] at this
    simpa [Loc.ok] using this
  have hget : ∀ s : State, (armArgs sig s).getD (ps₁.flatMap fun p => p.2.words 32).length 0 =
      (stackArg s (off / 4)).setWidth 64 := fun s => by
    rw [armArgs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiL,
      Option.map_some, Option.getD_some, hli]
    rfl
  -- The array, among the buffers.
  have harr : ∀ s : State, (⟨(stackArg s (off / 4)).setWidth 64, kk * e.size⟩, true) ∈
      Sig.bufs sig.params (armArgs sig s) := by
    intro s
    rw [← hget s, hps]
    exact Sig.bufs_mem_array (pb := 32) ps₂ ps₁ (armArgs sig s)
      (by rw [armArgs_length]; show _ < (sig.words abi.ptrBits).length; rw [hL]; omega)
  -- Its address is public.
  have hpubA : ∀ s₁ s₂, (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pub s₁ s₂ →
      stackArg s₁ (off / 4) = stackArg s₂ (off / 4) := by
    intro s₁ s₂ hp
    have hP : (sig.params.flatMap (·.2.pubs)).getD (ps₁.flatMap fun p => p.2.words 32).length false = true := by
      rw [hps]; exact (Sig.pub_array (pb := 32) ps₁ ps₂).1
    have hW : (widths sig).getD (ps₁.flatMap fun p => p.2.words 32).length 64 = 32 := by
      show ((sig.params.flatMap fun p => p.2.words 32).map (·.bits 32)).getD _ 64 = 32
      rw [hps]; exact (Sig.pub_array (pb := 32) ps₁ ps₂).2
    have h2 := congrArg BitVec.toNat (((pubL_arm hl).mp hp).2 _ hP)
    have l₁ := (stackArg s₁ (off / 4)).isLt
    have l₂ := (stackArg s₂ (off / 4)).isLt
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hW, hget, hget, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (a := (stackArg s₁ (off / 4)).toNat) (by omega),
      Nat.mod_eq_of_lt (a := (stackArg s₂ (off / 4)).toNat) (by omega),
      Nat.mod_eq_of_lt l₁, Nat.mod_eq_of_lt l₂] at h2
    exact BitVec.eq_of_toNat_eq h2
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s → ∀ m₁ m₂ x,
      (∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨(stackArg s (off / 4)).setWidth 64, kk * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    rw [pre_arm hl] at hs
    have hpw := List.Pairwise.sublist (List.sublist_append_left _ _) hs.2.2.2.1
    exact hpostOut _ _ _ _ _ (armArgs_length sig s) hpw (by rw [hget]; exact hag) hq
  -- `copyArgs` loads it into `r4`.
  have hA4 : ∀ s, (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s →
      (cwsV k off s).gpr .r4 = stackArg s (off / 4) := fun s hs => by
    obtain ⟨hsb, hfit⟩ := cws_sp (by omega) hl hs
    exact cwsV_r4_eq hk (by omega) (by omega) hoff4 hoff
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · obtain ⟨t, g, he, habi, hq, hz0⟩ := cws_wp h hz hN hloc hl hk hoff hd hzd hzs hpre hpost hn hn32 hs
      (hA4 s hs) (harr s) (hout s hs)
    refine ⟨t, g, he, habi, ?_⟩
    rw [post_arm] at hq ⊢
    exact hwiped _ _ _ _ (armArgs_length sig s) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) ?_
    refine RelCT.mono (P := fun a b => ∃ σ₁ σ₂,
        ((sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pub σ₁ σ₂) ∧ a = σ₁ ∧ b = σ₂) ?_
      (fun a b hab => ⟨a, b, hab, rfl, rfl⟩) (fun _ _ h => h)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + 16 + allocSize k) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre σ₂ := h₂
    have hp' : (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pub σ₁ σ₂ := hp
    have hsp12 : σ₁.sp = σ₂.sp := ((pubL_arm hl).mp hp').1.1
    have hpp := hpubA _ _ hp'
    obtain ⟨hs₁, hAw₁, hAd₁, hnw₁⟩ := cws_array (by omega) hl h₁' (harr σ₁)
    obtain ⟨hs₂, hAw₂, hAd₂, hnw₂⟩ := cws_array (by omega) hl h₂' (harr σ₂)
    have hs₁' : 16 ≤ σ₁.sp.toNat := by omega
    have hs₂' : 16 ≤ σ₂.sp.toNat := by omega
    refine RelCT.mono (P := fun a b => a = σ₁ ∧ b = σ₂) ?_ (fun a b hab => hab.2) (fun _ _ h => h)
    refine RelCT.frame (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact hsp12) ?_
    refine RelCT.mono (P := fun a b => a = cwPush σ₁ ∧ b = cwPush σ₂) ?_ (fun a b hab => ?_)
      (fun _ _ h => h)
    swap
    · obtain ⟨_, _, ⟨rfl, rfl⟩, e₁, e₂⟩ := hab
      rw [cwPush_push hs₁'] at e₁
      rw [cwPush_push hs₂'] at e₂
      exact ⟨(Option.some.inj e₁).symm, (Option.some.inj e₂).symm⟩
    -- The inner frame: the copy and the function.
    refine RelCT.seq (R := fun c₁ c₂ =>
        AfterBodyS sig post (stackArg σ₁ (off / 4)) (stack + allocSize k) σ₁ c₁ ∧
        AfterBodyS sig post (stackArg σ₂ (off / 4)) (stack + allocSize k) σ₂ c₂) ?_ ?_
    · refine RelCT.mono (RelCT.wp
        (F₁ := AfterBodyS sig post (stackArg σ₁ (off / 4)) (stack + allocSize k) σ₁)
        (F₂ := AfterBodyS sig post (stackArg σ₂ (off / 4)) (stack + allocSize k) σ₂)
        (RelCT.allocFrame ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · refine RelCT.mono (P := fun a b => a = cwsU (allocSize k) σ₁ ∧ b = cwsU (allocSize k) σ₂) ?_
          (fun a b hab => by obtain ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩ := hab; exact ⟨rfl, rfl⟩) (fun _ _ h => h)
        refine RelCT.seq (R := fun a b => a = cwsV k off σ₁ ∧ b = cwsV k off σ₂)
          (RelCT.block_of fun a b hab => ?_) ?_
        · obtain ⟨rfl, rfl⟩ := hab
          refine ⟨_, _, _, copyArgs_run hk hoff (by omega) (cws_src hN hk.1 hl h₁'), ?_, rfl, rfl⟩
          rw [copyArgs_run hk hoff (by omega) (cws_src hN hk.1 hl h₂'), cwsU_sp, cwsU_sp, hsp12]
        · refine RelCT.callEx h.1 h.2.1 fun a b hab => ?_
          obtain ⟨rfl, rfl⟩ := hab
          obtain ⟨c₁, w₁⟩ := cws_bodyCovers (off := off) hN hk hl h₁'
          obtain ⟨c₂, w₂⟩ := cws_bodyCovers (off := off) hN hk hl h₂'
          exact ⟨_, _, _, _, cws_bodyPre hN hk hloc hl hpre h₁', cws_bodyPre hN hk hloc hl hpre h₂',
            cws_bodyPub hN hk hloc hl h₁' h₂' hp' hleak, c₁, w₁, c₂, w₂⟩
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨cws_body_wp h hN hloc hl hk hoff hd hpre hpost h₁' (hA4 σ₁ h₁'),
          cws_body_wp h hN hloc hl hk hoff hd hpre hpost h₂' (hA4 σ₂ h₂')⟩
    -- The zeroize function's arguments.
    refine RelCT.seq (R := fun d₁ d₂ =>
        (∃ c, AfterBodyS sig post (stackArg σ₁ (off / 4)) (stack + allocSize k) σ₁ c ∧ d₁ = cwZero n c) ∧
        (∃ c, AfterBodyS sig post (stackArg σ₂ (off / 4)) (stack + allocSize k) σ₂ c ∧ d₂ = cwZero n c))
      (RelCT.block_of fun c₁ c₂ hc => ⟨_, _, _, zeroArgs_run hn32 c₁, zeroArgs_run hn32 c₂,
        ⟨c₁, hc.1, rfl⟩, ⟨c₂, hc.2, rfl⟩⟩) ?_
    -- The zeroize function.
    refine RelCT.seq (R := fun g₁ g₂ =>
        AfterZeroS sig post (stackArg σ₁ (off / 4)) (stack + allocSize k) n σ₁ g₁ ∧
        AfterZeroS sig post (stackArg σ₂ (off / 4)) (stack + allocSize k) n σ₂ g₂) ?_ ?_
    · refine RelCT.mono (RelCT.wp
        (F₁ := AfterZeroS sig post (stackArg σ₁ (off / 4)) (stack + allocSize k) n σ₁)
        (F₂ := AfterZeroS sig post (stackArg σ₂ (off / 4)) (stack + allocSize k) n σ₂)
        (RelCT.callEx hz.1 hz.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨[], [⟨(stackArg σ₁ (off / 4)).setWidth 64, n⟩], [], [⟨(stackArg σ₂ (off / 4)).setWidth 64, n⟩],
          cws_zeroPre hs₁ (by omega) hAd₁ hnw₁ hn hn32 hzs hc₁,
          cws_zeroPre hs₂ (by omega) hAd₂ hnw₂ hn hn32 hzs hc₂,
          cws_zeroPub hsp12 hpp hc₁ hc₂,
          Covers.right (cws_zeroCovers hAw₁ hn hc₁), cws_zeroCovers hAw₁ hn hc₁,
          Covers.right (cws_zeroCovers hAw₂ hn hc₂), cws_zeroCovers hAw₂ hn hc₂⟩
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨cws_zero_wp hz hzd hzs hs₁ (by omega) hAw₁ hAd₁ hnw₁ hn hn32 hc₁,
          cws_zero_wp hz hzd hzs hs₂ (by omega) hAw₂ hAd₂ hnw₂ hn hn32 hc₂⟩
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
      refine ⟨_, cwRestore g₂, _, restoreRet_run (hin g₁ σ₁ hs₁' hw₁ e₁), ?_, trivial⟩
      rw [restoreRet_run (hin g₂ σ₂ hs₂' hw₂ e₂), e₁, e₂, hsp12]

/-- `Verified.callWipeStack'`, with the function's postcondition. -/
theorem Verified.callWipeStack {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {kk n i k off : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hN : nsaa sig = 4 * k) (hloc : (locs sig).all (Loc.ok (4 * k)) = true)
    (hl : Sig.noLists sig.params = true) (hk : CwsFits k)
    (hps : sig.params = ps₁ ++ (nm, .array true e kk) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 32).length)
    (hr : (locs sig).getD i (.reg .r0) = .stack off 32)
    (hn : n ≤ kk * e.size) (hn32 : n < 2 ^ 32)
    (hd : armStack body ≤ stack) (hzd : armStack zcode ≤ zst) (hzs : zst ≤ stack + allocSize k)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, kk * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + 16 + allocSize k) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (callWipeStack k off n name body zname zcode)
      (sig.contract abi pre post wa (stack + 16 + allocSize k) leak) :=
  Verified.callWipeStack' h hz hN hloc hl hk hps hi hr hn hn32 hd hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak

end

/-- The stack `callWipeStack` and its callees use: its frames, and the
larger of its callees'. -/
theorem armStack_callWipeStack {k off n : Nat} {name zname : String} {body zcode : Prog isa} :
    armStack (callWipeStack k off n name body zname zcode) =
      max (armStack body + allocSize k) (armStack zcode) + 16 := by
  simp only [callWipeStack, armStack, Nat.zero_max, Nat.max_zero, List.length_cons, List.length_nil]

end VG.Arm
