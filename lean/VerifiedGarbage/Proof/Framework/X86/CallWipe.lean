module

public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.CallWipe
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# A call that wipes part of a buffer afterwards (x86, 32-bit)

`Verified.callWipe`: a function verified against `sig.contract` with `stack`
bytes of stack (`stackUse body ≤ stack`), whose arguments take `m` slots on
the stack, one of them (word `i`, in slot `j`) a writable array of `k`
elements `e`, is verified against the same contract with
`stack + frameSize m + 4` bytes when called by `callWipe`, which then
zeroes the first `n ≤ k * e.size` bytes of the array with a function
verified against `Spec.Zeroize.zeroizeContract`, and returns the first
function's result; `Verified.callWipe'` adds to the postcondition that those
bytes are zero on return.

`callWipe`'s frame (`allocFrame`) holds the callees' arguments at `esp`: a
copy of the caller's for the first (`copyArgs`), then the array's address,
read again from the caller's arguments, and `n` for the zeroize function
(`zeroArgs`); and the first function's result above them across the second
call. Each callee runs from the state after its call with the permissions of
its own contract: the buffers and its arguments for the first, the `n` bytes
and its arguments for the zeroize function (`WP.call`). The copies and the
return addresses are memory the first function's contract reads on entry,
which the caller's says nothing of: the precondition, postcondition and leak
must read the memory on entry only within the function's buffers (`hpre`,
`hpost`, `hleak`). The zeroize function writes the array after the first
function returned: the postcondition must read the memory on return only
within the buffers apart from the array (`hpostOut`), which the precondition
keeps apart from the others (it is writable).

Constant time: the frame's accesses depend on `esp` alone, each callee is
constant time, and the zeroize function's arguments, the array's address and
`n`, are public.
-/

@[expose] public section

namespace VG.X86

open VG.Impl.CallWipe.X86

/-! ## Copying the arguments -/

/-- The state after `copyArg bytes k` from `u`. -/
def cwCopy (bytes k : Nat) (u : State) : State :=
  { u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * k)) 32) with
    mem := u.mem.writeW (addr (u.gpr .esp) (4 * k))
      (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * k)) 32) }

theorem cwCopy_run {bytes k : Nat} {u : State}
    (hr : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * k)) 4)
    (hw : InRegions u.wr (addr (u.gpr .esp) (4 * k)) 4) :
    execBlock isa (copyArg bytes k) u = some (cwCopy bytes k u,
      [.addr (addr (u.gpr .esp) (bytes + 4 + 4 * k)), .addr (addr (u.gpr .esp) (4 * k))]) := by
  have hesp : (u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * k)) 32)).gpr .esp =
      u.gpr .esp := by simp [State.setReg]
  simp only [copyArg, execBlock, isa, exec, readSrc, State.load32, ea_mk, hr, ite_true,
    Option.map_some, addrs, srcAddrs, State.store32, hesp]
  simp [cwCopy, State.setReg, hw]

@[simp] theorem cwCopy_esp (bytes k : Nat) (u : State) : (cwCopy bytes k u).gpr .esp = u.gpr .esp := by
  simp [cwCopy, State.setReg]
@[simp] theorem cwCopy_rd (bytes k : Nat) (u : State) : (cwCopy bytes k u).rd = u.rd := rfl
@[simp] theorem cwCopy_wr (bytes k : Nat) (u : State) : (cwCopy bytes k u).wr = u.wr := rfl
theorem cwCopy_gpr (bytes k : Nat) (u : State) {q : Reg} (h : q ≠ .eax) :
    (cwCopy bytes k u).gpr q = u.gpr q := by
  simp [cwCopy, State.setReg, h]

/-- The state after copying the first `m` argument slots from `u`. -/
def cwCopied (bytes : Nat) (u : State) : Nat → State
  | 0 => u
  | m + 1 => cwCopy bytes m (cwCopied bytes u m)

@[simp] theorem cwCopied_esp (bytes : Nat) (u : State) :
    ∀ m, (cwCopied bytes u m).gpr .esp = u.gpr .esp
  | 0 => rfl
  | m + 1 => by rw [cwCopied, cwCopy_esp, cwCopied_esp bytes u m]
@[simp] theorem cwCopied_rd (bytes : Nat) (u : State) : ∀ m, (cwCopied bytes u m).rd = u.rd
  | 0 => rfl
  | m + 1 => by rw [cwCopied, cwCopy_rd, cwCopied_rd bytes u m]
@[simp] theorem cwCopied_wr (bytes : Nat) (u : State) : ∀ m, (cwCopied bytes u m).wr = u.wr
  | 0 => rfl
  | m + 1 => by rw [cwCopied, cwCopy_wr, cwCopied_wr bytes u m]
theorem cwCopied_gpr (bytes : Nat) (u : State) {q : Reg} (h : q ≠ .eax) :
    ∀ m, (cwCopied bytes u m).gpr q = u.gpr q
  | 0 => rfl
  | m + 1 => by rw [cwCopied, cwCopy_gpr _ _ _ h, cwCopied_gpr bytes u h m]

/-- The addresses copying the first `m` slots accesses. -/
def cwCopyTrace (bytes : Nat) (sp : BitVec 32) (m : Nat) : List Leak :=
  (List.range m).flatMap fun k => [.addr (addr sp (bytes + 4 + 4 * k)), .addr (addr sp (4 * k))]

theorem cwCopies_run {bytes : Nat} {u : State} :
    ∀ m, (∀ k < m, InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * k)) 4) →
      (∀ k < m, InRegions u.wr (addr (u.gpr .esp) (4 * k)) 4) →
      execBlock isa (copyArgs bytes m) u = some (cwCopied bytes u m, cwCopyTrace bytes (u.gpr .esp) m)
  | 0, _, _ => rfl
  | m + 1, hr, hw => by
    rw [copyArgs, List.range_succ, List.flatMap_append, execBlock_append,
      ← copyArgs, cwCopies_run m (fun k hk => hr k (by omega_using [hk])) (fun k hk => hw k (by omega_using [hk]))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [cwCopy_run (by simpa using hr m (by omega_using [])) (by simpa using hw m (by omega_using []))]
    simp only [Option.map_some, cwCopied, cwCopied_esp, cwCopyTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` slots writes only within the `m` destination slots
(from `esp`), which then hold the source slots (from `esp + bytes + 4`). -/
theorem cwCopied_mem {bytes : Nat} {u : State} :
    ∀ m, (u.gpr .esp).toNat + bytes + 4 + 4 * m ≤ 2 ^ 32 → 4 * m ≤ bytes →
      Frame [⟨(u.gpr .esp).setWidth 64, 4 * m⟩] u.mem (cwCopied bytes u m).mem ∧
      ∀ k < m, (cwCopied bytes u m).mem.readW (addr (u.gpr .esp) (4 * k)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * k)) 32
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := cwCopied_mem (bytes := bytes) (u := u) m (by omega_using [hfit]) (by omega_using [hb])
    have hA : ∀ d, d < 4 + bytes + 4 * (m + 1) → addr (u.gpr .esp) d =
        (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun d hd => addr_eq (by omega_using [hfit, hd])
    have hR : Region.Sub ⟨(u.gpr .esp).setWidth 64, 4 * m⟩ ⟨(u.gpr .esp).setWidth 64, 4 * (m + 1)⟩ :=
      Region.sub_prefix (by omega_using [])
    have f' : Frame [⟨(u.gpr .esp).setWidth 64, 4 * (m + 1)⟩] u.mem (cwCopied bytes u m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    -- The source of slot `m` is above the first `m` destinations.
    have hsrc : (cwCopied bytes u m).mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * m)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * m)) 32 := by
      rw [hA _ (by omega_using [])]
      refine f.readW (r := ⟨(u.gpr .esp).setWidth 64 + BitVec.ofNat 64 (bytes + 4 + 4 * m), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      have := Offset.disjoint ((u.gpr .esp).setWidth 64) (d := bytes + 4 + 4 * m) (n := 4) (e := 0)
        (k := 4 * m) (.inr (by omega_using [])) (by omega_using [hfit]) (by omega_using [hfit])
      rwa [BitVec.add_zero] at this
    refine ⟨?_, fun k hk => ?_⟩
    · show Frame _ u.mem ((cwCopied bytes u m).mem.writeW _ _)
      rw [cwCopied_esp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      rw [hA _ (by omega_using [])]
      exact Offset.contains_base _ (d := 4 * m) (k := 4 * (m + 1)) (by omega_using []) (by omega_using [hfit])
    · show ((cwCopied bytes u m).mem.writeW (addr ((cwCopied bytes u m).gpr .esp) (4 * m))
          ((cwCopied bytes u m).mem.readW
            (addr ((cwCopied bytes u m).gpr .esp) (bytes + 4 + 4 * m)) 32)).readW _ 32 = _
      rw [cwCopied_esp]
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [Mem.readW_writeW_sep, hv k hk']
        · rw [hA _ (by omega_using [hk']), hA _ (by omega_using [])]
          exact Offset.sep _ (d := 4 * k) (n := 4) (e := 4 * m) (k := 4) (by omega_using [hk'])
            (by omega_using [hfit, hk']) (by omega_using [hfit])
        · decide
      · obtain rfl : k = m := by omega_using [hk, hk']
        rw [Mem.readW_writeW_self32, hsrc]

/-! ## The other blocks -/

/-- The memory after `zeroArgs m j n`, from `c`: the result saved, then the
buffer's address and `n` as the zeroize function's arguments. -/
def cwZeroMem (m j n : Nat) (c : State) : Mem :=
  let m₂ := (c.mem.writeW (addr (c.gpr .esp) (4 * argWords m)) (c.gpr .eax)).writeW
    (addr (c.gpr .esp) (4 * argWords m + 4)) (c.gpr .edx)
  (m₂.writeW (addr (c.gpr .esp) 0) (m₂.readW (addr (c.gpr .esp) (frameSize m + 4 + 4 * j)) 32)).writeW
    (addr (c.gpr .esp) 4) (BitVec.ofNat 32 n)

/-- The trace of `zeroArgs m j n` from `esp = sp`. -/
def cwZeroTrace (m j : Nat) (sp : BitVec 32) : List Leak :=
  [.addr (addr sp (4 * argWords m)), .addr (addr sp (4 * argWords m + 4)),
    .addr (addr sp (frameSize m + 4 + 4 * j)), .addr (addr sp 0), .addr (addr sp 4)]

theorem zeroArgs_run {m j n : Nat} {c : State}
    (hw : ∀ d ∈ [4 * argWords m, 4 * argWords m + 4, 0, 4], InRegions c.wr (addr (c.gpr .esp) d) 4)
    (hr : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) (frameSize m + 4 + 4 * j)) 4) :
    ∃ w', execBlock isa (zeroArgs m j n) c = some (w', cwZeroTrace m j (c.gpr .esp)) ∧
      w'.rd = c.rd ∧ w'.wr = c.wr ∧ (∀ q, q ≠ .eax → w'.gpr q = c.gpr q) ∧
      w'.gpr .eax = BitVec.ofNat 32 n ∧ w'.mem = cwZeroMem m j n c := by
  have h1 := hw (4 * argWords m) (by simp)
  have h2 := hw (4 * argWords m + 4) (by simp)
  have h3 := hw 0 (by simp)
  have h4 := hw 4 (by simp)
  simp only [zeroArgs, execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, State.store32,
    State.load32, ea_mk]
  simp [State.setReg, h1, h2, h3, h4, hr, cwZeroMem, cwZeroTrace]
  intro q hq; simp [hq]

theorem restoreRet_run {m : Nat} {g : State}
    (hr : ∀ d ∈ [4 * argWords m, 4 * argWords m + 4], InRegions (g.rd ++ g.wr) (addr (g.gpr .esp) d) 4) :
    ∃ w', execBlock isa (restoreRet m) g = some (w', [.addr (addr (g.gpr .esp) (4 * argWords m)),
        .addr (addr (g.gpr .esp) (4 * argWords m + 4))]) ∧
      w'.rd = g.rd ∧ w'.wr = g.wr ∧ w'.mem = g.mem ∧
      (∀ q, q ≠ .eax → q ≠ .edx → w'.gpr q = g.gpr q) ∧
      w'.gpr .eax = g.mem.readW (addr (g.gpr .esp) (4 * argWords m)) 32 ∧
      w'.gpr .edx = g.mem.readW (addr (g.gpr .esp) (4 * argWords m + 4)) 32 := by
  have h1 := hr (4 * argWords m) (by simp)
  have h2 := hr (4 * argWords m + 4) (by simp)
  simp only [restoreRet, execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs,
    State.load32, ea_mk]
  simp [State.setReg, h1, h2]
  intro q h₁ h₂; simp [h₁, h₂]

/-! ## Addresses -/

theorem sub_add_ofNat (E : BitVec 32) (b d : Nat) :
    E - BitVec.ofNat 32 b + BitVec.ofNat 32 (b + d) = E + BitVec.ofNat 32 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem frameSize_ge (m : Nat) : 4 * m + 8 ≤ frameSize m ∧ 16 ≤ frameSize m := by
  simp only [frameSize, argWords]; omega

/-- The arguments of `sig`, from slots that agree. -/
theorem stackArgs_congr (sig : Sig) {s s' : State} (h : ∀ k < slots sig, arg s' k = arg s k) :
    stackArgs sig s' = stackArgs sig s := by
  unfold stackArgs
  refine List.map_congr_left fun p hp => ?_
  have hl := argSlots_lt (widths sig) 0 p hp
  have hw := widths_mem sig p.1 (List.of_mem_zip hp).1
  simp only [Nat.zero_add] at hl
  simp only [argVal]
  rcases hw with hw | hw <;> rw [hw] at hl
  · simp only [hw, show (32 : Nat) ≠ 64 by decide, ite_false]
    rw [h _ (by simp only [slots]; omega_using [hl])]
  · simp only [hw, ite_true]
    rw [h _ (by simp only [slots]; omega_using [hl]), h _ (by simp only [slots]; omega_using [hl])]

/-! ## The frame and the copies -/

/-- The state the first call is made from: the frame allocated, the
arguments copied. -/
def cwW (sig : Sig) (s : State) : State :=
  cwCopied (frameSize (slots sig)) (allocFrame (frameSize (slots sig)) s) (slots sig)

theorem cwW_esp (sig : Sig) (s : State) :
    (cwW sig s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) := by
  rw [cwW, cwCopied_esp, allocFrame_esp]
theorem cwW_gpr (sig : Sig) (s : State) {q : Reg} (h₁ : q ≠ .eax) (h₂ : q ≠ .esp) :
    (cwW sig s).gpr q = s.gpr q := by
  rw [cwW, cwCopied_gpr _ _ h₁, allocFrame_gpr _ _ h₂]
@[simp] theorem cwW_rd (sig : Sig) (s : State) : (cwW sig s).rd = s.rd := by
  rw [cwW, cwCopied_rd, allocFrame_rd]
@[simp] theorem cwW_wr (sig : Sig) (s : State) :
    (cwW sig s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64,
      frameSize (slots sig)⟩ :: s.wr := by
  rw [cwW, cwCopied_wr, allocFrame_wr]

/-- The regions of the first function's contract, at its entry from the
caller's state `s`: the buffers, and its arguments in the frame. -/
def bodyRegions (sig : Sig) (wa : Bool) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (stackArgs sig s) ++
    (if slots sig = 0 then [] else
      [(⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)), 4 * slots sig⟩, wa)])

/-- The state the first function runs from, with the permissions of its
contract: after the call. -/
def cwEntry (sig : Sig) (wa : Bool) (s : State) : State :=
  (cwW sig s).callEntry.withRegions (((bodyRegions sig wa s).filter (!·.2)).map (·.1))
    (((bodyRegions sig wa s).filter (·.2)).map (·.1))

theorem cwEntry_esp (sig : Sig) (wa : Bool) (s : State) :
    (cwEntry sig wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) - 4 := by
  rw [cwEntry, State.withRegions_gpr, State.callEntry_esp, cwW_esp]
theorem cwEntry_gpr (sig : Sig) (wa : Bool) (s : State) {q : Reg} (h₁ : q ≠ .eax) (h₂ : q ≠ .esp) :
    (cwEntry sig wa s).gpr q = s.gpr q := by
  rw [cwEntry, State.withRegions_gpr, State.callEntry_gpr _ h₂, cwW_gpr sig s h₁ h₂]

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The caller's stack: the frame, the first function's return address and
its stack, and the caller's arguments above, without wrapping. -/
theorem cw_sp (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    stack + frameSize (slots sig) + 4 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 4 * slots sig ≤ 2 ^ 32 := by
  rw [pre_stack hl] at hs
  exact hs.1

/-- The reserved stack: the return address, and the stack below `esp`. -/
theorem cw_res (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    ∀ a ∈ allRegions sig wa s,
      (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint a.1 ∧
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + frameSize (slots sig) + 4),
        stack + frameSize (slots sig) + 4⟩ : Region).Disjoint a.1 := by
  rw [pre_stack hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  intro a ha
  refine ⟨hres _ (List.mem_cons_self ..) a ha, hres _ (List.mem_cons_of_mem _ ?_) a ha⟩
  rw [show stack + frameSize (slots sig) + 4 = (stack + frameSize (slots sig) + 3) + 1 by omega]
  exact List.mem_singleton_self _

/-- Each of the caller's regions is one it may access. -/
theorem cw_regions (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    ∀ x ∈ allRegions sig wa s, x.1 ∈ s.rd ++ s.wr ∧ (x.2 = true → x.1 ∈ s.wr) := by
  rw [pre_stack hl] at hs
  obtain ⟨-, hrd, hwr, -⟩ := hs
  intro x hx
  cases h2 : x.2
  · refine ⟨List.mem_append_left _ ?_, fun h => absurd h (by simp)⟩
    rw [hrd]; exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp [h2]⟩, rfl⟩
  · have : x.1 ∈ s.wr := by rw [hwr]; exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, h2⟩, rfl⟩
    exact ⟨List.mem_append_right _ this, fun _ => this⟩

theorem argArea_mem {s : State} (h0 : slots sig ≠ 0) :
    (⟨argAddr s 0, 4 * slots sig⟩, wa) ∈ allRegions sig wa s := by
  simp [allRegions, h0]

theorem bufs_mem {s : State} {b : Region × Bool} (hb : b ∈ Sig.bufs sig.params (stackArgs sig s)) :
    b ∈ allRegions sig wa s := List.mem_append_left _ hb

/-- The copies in the frame are the caller's arguments; the frame's
allocation and the copies change memory only in the copies' slots. -/
theorem cwW_mem (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    execBlock isa (copyArgs (frameSize (slots sig)) (slots sig))
        (allocFrame (frameSize (slots sig)) s) =
      some (cwW sig s, cwCopyTrace (frameSize (slots sig))
        (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) (slots sig)) ∧
    Frame [⟨(s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64, 4 * slots sig⟩]
      s.mem (cwW sig s).mem ∧
    ∀ k < slots sig, (cwW sig s).mem.readW
      (addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) (4 * k)) 32 = arg s k := by
  have ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  have hreg := cw_regions hl hs
  have hE : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).toNat =
      (s.gpr .esp).toNat - frameSize (slots sig) := sub_toNat (by omega_using [hsb])
  have hA : ∀ d, d < frameSize (slots sig) + 4 + 4 * slots sig →
      addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) d =
        (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64 + BitVec.ofNat 64 d :=
    fun d hd => addr_eq (by rw [hE]; omega_using [hsb, hfit, hd])
  have hsrc : ∀ k, addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)))
      (frameSize (slots sig) + 4 + 4 * k) = argAddr s k := fun k => by
    rw [addr, argAddr, show frameSize (slots sig) + 4 + 4 * k = frameSize (slots sig) + (4 + 4 * k) by omega,
      sub_add_ofNat]
  have hargA : ∀ k < slots sig, argAddr s k = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * k) :=
    fun k hk => addr_eq (x := s.gpr .esp) (by omega_using [hfit, hk])
  have hrun := cwCopies_run (bytes := frameSize (slots sig)) (u := allocFrame (frameSize (slots sig)) s)
    (slots sig) (fun k hk => ?_) (fun k hk => ?_)
  rotate_left
  · have h0 : slots sig ≠ 0 := by omega_using [hk]
    refine ⟨⟨argAddr s 0, 4 * slots sig⟩, ?_, ?_⟩
    · rw [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
      rcases List.mem_append.mp (hreg _ (argArea_mem (wa := wa) h0)).1 with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · rw [allocFrame_esp, hsrc, hargA k hk, hargA 0 (by omega_using [hk])]
      exact Offset.contains _ (by omega_using []) (by omega_using [hk]) (by omega_using [hfit])
  · refine ⟨_, List.mem_cons_self .., ?_⟩
    rw [allocFrame_esp, hA _ (by omega_using [hk, hB])]
    exact Offset.contains_base _ (by omega_using [hk, hB]) (by omega_using [hfit, hB, hk])
  obtain ⟨f, hv⟩ := cwCopied_mem (bytes := frameSize (slots sig)) (u := allocFrame (frameSize (slots sig)) s)
    (slots sig) (by rw [allocFrame_esp, hE]; omega_using [hsb, hfit]) (by omega_using [hB])
  rw [allocFrame_esp] at hrun f hv
  refine ⟨hrun, f, fun k hk => ?_⟩
  rw [cwW, hv k hk, allocFrame_mem, hsrc]
  rfl

end

/-! ## The first function's entry -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The caller's regions lie apart from the stack below its `esp` that its
contract reserves. -/
theorem cw_low (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    ∀ a ∈ allRegions sig wa s, ∀ (d n : Nat), n ≤ d → d ≤ stack + frameSize (slots sig) + 4 →
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 d, n⟩ a.1 :=
  fun a ha _ _ hn hd => ((cw_res hl hs) a ha).2.sub_left (Offset.sub_below _ hd (by omega_using [hn, hd]))

theorem cw_esp64 (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)) ∧
      ((cwEntry sig wa s).gpr .esp).setWidth 64 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig) + 4) ∧
      ((cwEntry sig wa s).gpr .esp).toNat = (s.gpr .esp).toNat - (frameSize (slots sig) + 4) := by
  obtain ⟨hsb, -⟩ := cw_sp hl hs
  have e : s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) - 4 =
      s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig) + 4) := by
    rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl
  rw [cwEntry_esp, e]
  exact ⟨Taint.sub_setWidth (by omega_using [hsb]), Taint.sub_setWidth (by omega_using [hsb]),
    sub_toNat (by omega_using [hsb])⟩

/-- The first function's arguments are the caller's. -/
theorem cwEntry_args (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    stackArgs sig (cwEntry sig wa s) = stackArgs sig s := by
  have ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  have hE : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).toNat =
      (s.gpr .esp).toNat - frameSize (slots sig) := sub_toNat (by omega_using [hsb])
  obtain ⟨-, -, hv⟩ := cwW_mem hl hs
  refine stackArgs_congr sig fun k hk => ?_
  rw [cwEntry, arg_withRegions, arg_callEntry (by rw [cwW_esp, hE]; omega_using [hsb, hB])
    (by rw [cwW_esp, hE]; omega_using [hsb, hfit, hB, hk]), cwW_esp]
  exact hv k hk

/-- The first function's regions, at its entry. -/
theorem cwEntry_regions (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    allRegions sig wa (cwEntry sig wa s) = bodyRegions sig wa s := by
  obtain ⟨hsb, -⟩ := cw_sp hl hs
  have hA : argAddr (cwEntry sig wa s) 0 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)) := by
    rw [argAddr, cwEntry_esp, show 4 + 4 * 0 = 4 by rfl,
      show (BitVec.ofNat 32 4 : BitVec 32) = 4 from rfl, BitVec.sub_add_cancel]
    exact Taint.sub_setWidth (by omega_using [hsb])
  rw [allRegions, bodyRegions, cwEntry_args hl hs, hA]

/-- What the frame, the copies and the return address change: the
`frameSize + 4` bytes below `esp`. -/
theorem cwEntry_frame (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    Frame [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig) + 4), frameSize (slots sig) + 4⟩]
      s.mem (cwEntry sig wa s).mem := by
  have ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  obtain ⟨hF, -⟩ := cw_esp64 (wa := wa) hl hs
  obtain ⟨-, f, -⟩ := cwW_mem hl hs
  rw [hF] at f
  have e4 : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) - 4).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig) + 4) := by
    rw [BitVec.sub_sub, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]
    exact Taint.sub_setWidth (by omega_using [hsb])
  show Frame _ s.mem ((cwW sig s).mem.writeW (((cwW sig s).gpr .esp - 4).setWidth 64) _)
  rw [cwW_esp, e4]
  refine Frame.writeW (Frame.sub f fun r hr => ?_) (List.mem_singleton_self _) _
    (Offset.contains_below _ (a := frameSize (slots sig) + 4) (n := 4) (by omega_using []) (by omega_using [hB])
      (by omega_using [hsb, hfit]))
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_below _ (by omega_using []) (by omega_using [hB])⟩

/-- The entry's memory is the caller's in the buffers. -/
theorem cw_agree (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (stackArgs sig s), ∀ x, b.1.Contains x 1 →
      (cwEntry sig wa s).mem x = s.mem x := by
  have hlow := cw_low hl hs
  intro b hb x hx
  exact cwEntry_frame hl hs x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact hlow b (bufs_mem hb) _ _ (by omega_using []) (by omega_using []) x hc hx

end

/-! ## The first call -/

/-- The writable buffers. -/
def wbufs (sig : Sig) (s : State) : List Region :=
  ((Sig.bufs sig.params (stackArgs sig s)).filter (·.2)).map (·.1)

theorem mem_filter_map {L : List (Region × Bool)} {p : Region × Bool → Bool} {x : Region}
    (h : x ∈ (L.filter p).map (·.1)) : ∃ y ∈ L, p y = true ∧ y.1 = x := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
  exact ⟨y, (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2, rfl⟩

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The stack below the first function's arguments lies apart from its
regions. -/
theorem cw_bodyLow (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    ∀ (d n : Nat), n ≤ d → frameSize (slots sig) + n ≤ d → d ≤ stack + frameSize (slots sig) + 4 →
      ∀ a ∈ bodyRegions sig wa s, Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 d, n⟩ a.1 := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  have hE := (s.gpr .esp).isLt
  have hlow := cw_low hl hs
  intro d n hn hd hdT a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hlow a (bufs_mem ha) _ _ hn hdT
  · split at ha
    · simp at ha
    · simp only [List.mem_singleton] at ha; subst ha
      exact below_disjoint _ (stack + frameSize (slots sig) + 4) hdT (by omega_using [])
        (.inl (by omega_using [hd, hdT])) (by omega_using [hsb, hfit, hE, hdT, hn])
        (by omega_using [hsb, hfit, hE, hB])

/-- The caller's precondition gives the first function's at its entry. -/
theorem cw_bodyPre (hl : Sig.noLists sig.params = true)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cwEntry sig wa s) := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  obtain ⟨-, hX64, hXn⟩ := cw_esp64 (wa := wa) hl hs
  have hlow := cw_low hl hs
  have hblow := cw_bodyLow hl hs
  have hag := cw_agree (wa := wa) hl hs
  have hreg := cwEntry_regions (wa := wa) hl hs
  have hargs := cwEntry_args (wa := wa) hl hs
  have hs' := hs
  rw [pre_stack hl] at hs'
  obtain ⟨-, -, -, hpw, -, hnw, hpr⟩ := hs'
  refine (pre_stack hl).mpr ⟨⟨by rw [hXn]; omega_using [hsb], by rw [hXn]; omega_using [hsb, hfit, hB]⟩,
    by rw [hreg]; rfl, by rw [hreg]; rfl, ?_, ?_, by rw [hargs]; exact hnw, ?_⟩
  · rw [hreg, bodyRegions, List.pairwise_append]
    refine ⟨hpw.sublist (List.sublist_append_left _ _), by split <;> simp, fun a ha b hb _ => ?_⟩
    split at hb
    · simp at hb
    · simp only [List.mem_singleton] at hb; subst hb
      exact (hlow a (bufs_mem ha) (frameSize (slots sig)) _ (by omega_using [hB]) (by omega_using [])).symm
  · rw [hreg, hX64, stackBelow_sp']
    intro r hr a ha
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hblow _ _ (by omega_using []) (by omega_using []) (by omega_using []) a ha
    · split at hr
      · simp at hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact hblow _ _ (by omega_using []) (by omega_using []) (by omega_using []) a ha
  · rw [hargs]
    exact hpre _ _ _ (stackArgs_length sig s) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The caller's public data is the first function's at its entry. -/
theorem cw_bodyPub (hl : Sig.noLists sig.params = true) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cwEntry sig wa s₁) (cwEntry sig wa s₂) := by
  rw [pubL_stack hl] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  rw [cwEntry_args hl h₁, cwEntry_args hl h₂, cwEntry_esp, cwEntry_esp, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa⟩
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ f (stackArgs sig s₁) (cwEntry sig wa s₁).mem =
      Curry.apply _ f (stackArgs sig s₂) (cwEntry sig wa s₂).mem
    rw [hleak _ _ _ (stackArgs_length sig s₁) (cw_agree hl h₁),
      hleak _ _ _ (stackArgs_length sig s₂) (cw_agree hl h₂)]
    exact hlk

/-- The first function's regions are among those the call is made with. -/
theorem cw_bodyCovers (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    Covers ((((bodyRegions sig wa s).filter (!·.2)).map (·.1)) ++
        (((bodyRegions sig wa s).filter (·.2)).map (·.1))) ((cwW sig s).rd ++ (cwW sig s).wr) ∧
      Covers (((bodyRegions sig wa s).filter (·.2)).map (·.1)) (cwW sig s).wr := by
  obtain ⟨hsb, -⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  obtain ⟨hF, -⟩ := cw_esp64 (wa := wa) hl hs
  have hreg := cw_regions hl hs
  have hfr : Covers [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)), 4 * slots sig⟩]
      (cwW sig s).wr :=
    Covers.one ⟨_, by rw [cwW_wr, hF]; exact List.mem_cons_self .., by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_using [hB]⟩
  have key : ∀ y ∈ bodyRegions sig wa s, Covers [y.1] ((cwW sig s).rd ++ (cwW sig s).wr) ∧
      (y.2 = true → Covers [y.1] (cwW sig s).wr) := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨h₁, h₂⟩ := hreg y (bufs_mem hy)
      refine ⟨Covers.of_mem fun x hx => ?_, fun h => Covers.of_mem fun x hx => ?_⟩
      · simp only [List.mem_singleton] at hx; subst hx
        rw [cwW_rd, cwW_wr]
        rcases List.mem_append.mp h₁ with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · simp only [List.mem_singleton] at hx; subst hx
        rw [cwW_wr]; exact List.mem_cons_of_mem _ (h₂ h)
    · split at hy
      · simp at hy
      · simp only [List.mem_singleton] at hy; subst hy
        exact ⟨Covers.right hfr, fun _ => hfr⟩
  refine ⟨Covers.of_forall fun x hx => ?_, Covers.of_forall fun x hx => ?_⟩
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, -, rfl⟩ := mem_filter_map hx; exact (key y hy).1
    · obtain ⟨y, hy, -, rfl⟩ := mem_filter_map hx; exact (key y hy).1
  · obtain ⟨y, hy, h2, rfl⟩ := mem_filter_map hx; exact (key y hy).2 h2

/-- What the run of the first function leaves, from the caller's state `s`. -/
def AfterBody (sig : Sig) (post : sig.Post abi.ptrBits) (stack : Nat) (s c : State) : Prop :=
  c.rd = s.rd ∧
  c.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64, frameSize (slots sig)⟩ :: s.wr ∧
  c.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) ∧
  (∀ q ∈ calleeSaved, c.gpr q = s.gpr q ∨ q = .esp) ∧
  Frame (wbufs sig s ++ [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + frameSize (slots sig) + 4),
    stack + frameSize (slots sig) + 4⟩]) s.mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (stackArgs sig s) s.mem c.mem ((c.gpr .edx ++ c.gpr .eax).setWidth _)

end

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The `n` bytes below the frame, in 64 bits. -/
theorem below_frame64 (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) {n : Nat}
    (hn : n ≤ stack + 4) :
    below (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) n =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig) + n), n⟩ := by
  obtain ⟨hsb, -⟩ := cw_sp hl hs
  rw [below, BitVec.sub_sub, ← BitVec.ofNat_add, Taint.sub_setWidth (by omega_using [hsb, hn])]

/-- The call of the first function. -/
theorem cw_body_wp {name : String} {body : Prog isa}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hl : Sig.noLists sig.params = true) (hsp : NoSp body) (hd : stackUse body ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) :
    WP isa (.call name body) (cwW sig s) (AfterBody sig post stack s) := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  obtain ⟨hF, -⟩ := cw_esp64 (wa := wa) hl hs
  have hag := cw_agree (wa := wa) hl hs
  obtain ⟨-, f₀, -⟩ := cwW_mem hl hs
  obtain ⟨hcv, hcw⟩ := cw_bodyCovers (wa := wa) hl hs
  have hE : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).toNat =
      (s.gpr .esp).toNat - frameSize (slots sig) := sub_toNat (by omega_using [hsb])
  refine WP.call (k := sig.contract abi pre post wa stack leak) h.1 hsp
    (by rw [cwW_esp, hE]; omega_using [hd, hsb]) (cw_bodyPre hl hpre hs) hcv hcw ?_
  intro c hrd hwr hcs hfr _ ⟨s₂, hm, hg, hq⟩
  have hesp : c.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) := by
    rw [hcs .esp (by decide), cwW_esp]
  refine ⟨by rw [hrd, cwW_rd], by rw [hwr, cwW_wr], hesp, fun q hq => ?_, ?_, ?_⟩
  · by_cases hq' : q = .esp
    · exact .inr hq'
    · refine .inl ?_
      rw [hcs q hq, cwW_gpr sig s (by intro h; subst h; simp [calleeSaved] at hq) hq']
  · -- Memory changes only within the writable buffers and the stack below `esp`.
    rw [cwW_esp, below_frame64 hl hs (by omega_using [hd])] at hfr
    rw [hF] at f₀
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hfr fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        Offset.sub_below _ (by omega_using []) (by omega_using [hB])⟩
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨y, hy, h2, rfl⟩ := mem_filter_map hr
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y.1, List.mem_append_left _ (List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hy, h2⟩, rfl⟩),
            fun _ h => h⟩
        · split at hy
          · simp at hy
          · simp only [List.mem_singleton] at hy; subst hy
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
              Offset.sub_below _ (by omega_using []) (by omega_using [hB])⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          Offset.sub_below _ (by omega_using [hd]) (by omega_using [hd])⟩
  · -- The postcondition, which reads the memory on entry only within the buffers.
    rw [post_stack, show (cwW sig s).callEntry.withRegions _ _ = cwEntry sig wa s from rfl,
      cwEntry_args hl hs, hm, hg .edx (by decide), hg .eax (by decide)] at hq
    exact hpost _ _ _ _ _ (stackArgs_length sig s) hag hq

end

/-! ## The zeroize function's arguments -/

/-- The state after `zeroArgs m j n` from `c`, if it runs. -/
def cwZeroSt (m j n : Nat) (c : State) : State :=
  ((execBlock isa (zeroArgs m j n) c).map Prod.fst).getD c

theorem zeroArgs_run' {m j n : Nat} {c : State}
    (hw : ∀ d ∈ [4 * argWords m, 4 * argWords m + 4, 0, 4], InRegions c.wr (addr (c.gpr .esp) d) 4)
    (hr : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) (frameSize m + 4 + 4 * j)) 4) :
    execBlock isa (zeroArgs m j n) c = some (cwZeroSt m j n c, cwZeroTrace m j (c.gpr .esp)) ∧
      (cwZeroSt m j n c).rd = c.rd ∧ (cwZeroSt m j n c).wr = c.wr ∧
      (∀ q, q ≠ .eax → (cwZeroSt m j n c).gpr q = c.gpr q) ∧
      (cwZeroSt m j n c).mem = cwZeroMem m j n c := by
  obtain ⟨w', hrun, hrd, hwr, hg, -, hm⟩ := zeroArgs_run (n := n) hw hr
  have e : cwZeroSt m j n c = w' := by simp [cwZeroSt, hrun]
  rw [e]
  exact ⟨hrun, hrd, hwr, hg, hm⟩

/-- What the zeroize function's arguments and the saved result read back as. -/
theorem cwZeroMem_reads {m j n : Nat} {c : State} (hj : j < m)
    (hfit : (c.gpr .esp).toNat + frameSize m + 4 + 4 * m ≤ 2 ^ 32) :
    (cwZeroMem m j n c).readW (addr (c.gpr .esp) 0) 32 =
        c.mem.readW (addr (c.gpr .esp) (frameSize m + 4 + 4 * j)) 32 ∧
      (cwZeroMem m j n c).readW (addr (c.gpr .esp) 4) 32 = BitVec.ofNat 32 n ∧
      (cwZeroMem m j n c).readW (addr (c.gpr .esp) (4 * argWords m)) 32 = c.gpr .eax ∧
      (cwZeroMem m j n c).readW (addr (c.gpr .esp) (4 * argWords m + 4)) 32 = c.gpr .edx := by
  have hB := frameSize_ge m
  have hW : 2 ≤ argWords m := by simp only [argWords]; omega
  have hFs : frameSize m = 4 * argWords m + 8 := rfl
  have hA : ∀ d, d < frameSize m + 4 + 4 * m → addr (c.gpr .esp) d =
      (c.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun d hd => addr_eq (by omega_using [hfit, hd])
  have sp : ∀ {a b : Nat}, a + 4 ≤ b ∨ b + 4 ≤ a → a < frameSize m + 4 + 4 * m → b < frameSize m + 4 + 4 * m →
      Mem.Sep (addr (c.gpr .esp) a) (32 / 8) (addr (c.gpr .esp) b) (32 / 8) := fun h ha hb => by
    rw [hA _ ha, hA _ hb]
    exact Offset.sep _ h (by omega_using [hfit, ha]) (by omega_using [hfit, hb])
  have h0 : (0 : Nat) < frameSize m + 4 + 4 * m := by omega_using []
  have h4 : (4 : Nat) < frameSize m + 4 + 4 * m := by omega_using [hB]
  have hM : 4 * argWords m < frameSize m + 4 + 4 * m := by omega_using [hFs]
  have hM4 : 4 * argWords m + 4 < frameSize m + 4 + 4 * m := by omega_using [hFs]
  have hJ : frameSize m + 4 + 4 * j < frameSize m + 4 + 4 * m := by omega_using [hj]
  simp only [cwZeroMem]
  refine ⟨?_, Mem.readW_writeW_self32 _ _ _, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (sp (.inl (by omega_using [])) h0 h4) (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_sep (sp (.inr (by omega_using [hFs])) hJ hM4) (by decide),
      Mem.readW_writeW_sep (sp (.inr (by omega_using [hFs])) hJ hM) (by decide)]
  · rw [Mem.readW_writeW_sep (sp (.inr (by omega_using [hW])) hM h4) (by decide),
      Mem.readW_writeW_sep (sp (.inr (by omega_using [hW])) hM h0) (by decide),
      Mem.readW_writeW_sep (sp (.inl (by omega_using [])) hM hM4) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sp (.inr (by omega_using [hW])) hM4 h4) (by decide),
      Mem.readW_writeW_sep (sp (.inr (by omega_using [hW])) hM4 h0) (by decide), Mem.readW_writeW_self32]

/-! ## The zeroize function's contract -/

theorem zeroize_stackArgs (X : State) :
    stackArgs Spec.Zeroize.zeroizeSig X = [(arg X 0).setWidth 64, (arg X 1).setWidth 64] := rfl

theorem zeroize_regions (X : State) : allRegions Spec.Zeroize.zeroizeSig false X =
    [(⟨(arg X 0).setWidth 64, ((arg X 1).setWidth 64).toNat * 1⟩, true), (⟨argAddr X 0, 8⟩, false)] := rfl

/-- The zeroize function's precondition, from what it says of the state. -/
theorem zeroize_pre_of {zst n : Nat} {X : State} (hn : ((arg X 1).setWidth 64).toNat = n)
    (hwf : zst ≤ (X.gpr .esp).toNat ∧ (X.gpr .esp).toNat + 4 + 4 * 2 ≤ 2 ^ 32)
    (hrd : X.rd = [⟨argAddr X 0, 8⟩]) (hwr : X.wr = [⟨(arg X 0).setWidth 64, n⟩])
    (hd : (⟨(arg X 0).setWidth 64, n⟩ : Region).Disjoint ⟨argAddr X 0, 8⟩)
    (hres : ∀ x ∈ (⟨(X.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((X.gpr .esp).setWidth 64) zst : List Region),
      x.Disjoint ⟨(arg X 0).setWidth 64, n⟩ ∧ x.Disjoint ⟨argAddr X 0, 8⟩)
    (hb : ((arg X 0).setWidth 64).toNat + n ≤ 2 ^ 32) :
    (Spec.Zeroize.zeroizeContract abi zst).pre X := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pre_stack (by decide)).mpr ?_
  have hz : allRegions Spec.Zeroize.zeroizeSig false X =
      [(⟨(arg X 0).setWidth 64, n⟩, true), (⟨argAddr X 0, 8⟩, false)] := by
    rw [zeroize_regions, hn, Nat.mul_one]
  have hbz : Sig.bufs Spec.Zeroize.zeroizeSig.params (stackArgs Spec.Zeroize.zeroizeSig X) =
      [(⟨(arg X 0).setWidth 64, n⟩, true)] := by
    show [((⟨(arg X 0).setWidth 64, ((arg X 1).setWidth 64).toNat * 1⟩ : Region), true)] = _
    rw [hn, Nat.mul_one]
  rw [hz, hbz, show slots Spec.Zeroize.zeroizeSig = 2 by decide]
  refine ⟨hwf, by rw [hrd]; rfl, by rw [hwr]; rfl, ?_, fun x hx a ha => ?_, fun a ha => ?_, ?_⟩
  · exact List.pairwise_cons.mpr ⟨fun b hb _ => by
      simp only [List.mem_singleton] at hb; subst hb; exact hd, List.pairwise_singleton _ _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact (hres x hx).1
    · exact (hres x hx).2
  · simp only [List.mem_singleton] at ha; subst ha; exact hb
  · rw [Curry.apply_const]; trivial

/-- The zeroize function's postcondition. -/
theorem zeroize_post_iff {zst : Nat} {X Y : State} :
    (Spec.Zeroize.zeroizeContract abi zst).post X Y ↔
      Spec.Zeroize.bytesAt Y.mem ((arg X 0).setWidth 64) (((arg X 1).setWidth 64).setWidth 32).toNat =
        Spec.Zeroize.zeros (((arg X 1).setWidth 64).setWidth 32).toNat := Iff.rfl

/-- The zeroize function's public data. -/
theorem zeroize_pub_of {zst : Nat} {X₁ X₂ : State} (hsp : X₁.gpr .esp = X₂.gpr .esp)
    (h0 : arg X₁ 0 = arg X₂ 0) (h1 : arg X₁ 1 = arg X₂ 1) :
    (Spec.Zeroize.zeroizeContract abi zst).pub X₁ X₂ := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pubL_stack (by decide)).mpr ⟨⟨hsp, trivial⟩, fun i _ => ?_⟩
  rw [zeroize_stackArgs, zeroize_stackArgs, h0, h1]

/-! ## The zeroize call -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The frame's words, and the caller's arguments, from a state with the
frame's stack pointer and regions. -/
theorem cw_in (hl : Sig.noLists sig.params = true) {s t : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hrd : t.rd = s.rd)
    (hwr : t.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64, frameSize (slots sig)⟩ :: s.wr)
    (hsp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) :
    (∀ d, d + 4 ≤ frameSize (slots sig) → InRegions t.wr (addr (t.gpr .esp) d) 4) ∧
    (∀ k < slots sig, InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (frameSize (slots sig) + 4 + 4 * k)) 4) := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hreg := cw_regions hl hs
  have hE : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).toNat =
      (s.gpr .esp).toNat - frameSize (slots sig) := sub_toNat (by omega_using [hsb])
  refine ⟨fun d hd => ⟨_, by rw [hwr]; exact List.mem_cons_self .., ?_⟩, fun k hk => ?_⟩
  · rw [hsp, addr_eq (by rw [hE]; omega_using [hsb, hfit, hd])]
    exact Offset.contains_base _ hd (by omega_using [hd, hsb, hfit])
  · have h0 : slots sig ≠ 0 := by omega_using [hk]
    refine ⟨⟨argAddr s 0, 4 * slots sig⟩, ?_, ?_⟩
    · rw [hrd, hwr, List.mem_append, List.mem_cons]
      rcases List.mem_append.mp (hreg _ (argArea_mem (wa := wa) h0)).1 with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · rw [hsp, addr, show frameSize (slots sig) + 4 + 4 * k = frameSize (slots sig) + (4 + 4 * k) by omega,
        sub_add_ofNat, ← addr, argAddr, ← addr, addr_eq (by omega_using [hfit, hk]),
        addr_eq (x := s.gpr .esp) (by omega_using [hfit, hk])]
      exact Offset.contains _ (by omega_using []) (by omega_using [hk]) (by omega_using [hfit])

/-- The caller's argument `k`, which the first function cannot write. -/
theorem cw_argRead (hl : Sig.noLists sig.params = true) {s c : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hc : AfterBody sig post stack s c) {k : Nat} (hk : k < slots sig) :
    c.mem.readW (argAddr s k) 32 = arg s k := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have h0 : slots sig ≠ 0 := by omega_using [hk]
  have hs' := hs
  rw [pre_stack hl] at hs'
  obtain ⟨-, -, -, hpw, -, -, -⟩ := hs'
  have hA : ∀ d, d < 4 + 4 * slots sig → (s.gpr .esp + BitVec.ofNat 32 d).setWidth 64 =
      (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun d hd => addr_eq (by omega_using [hfit, hd])
  have hak : argAddr s k = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * k) := hA _ (by omega_using [hk])
  have ha0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := hA 4 (by omega_using [hk])
  have hsub : Region.Sub ⟨argAddr s k, 4⟩ ⟨argAddr s 0, 4 * slots sig⟩ := by
    rw [hak, ha0]; exact Offset.sub _ (by omega_using []) (by omega_using [hk])
  refine hc.2.2.2.2.1.readW (r := ⟨argAddr s k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨y, hy, h2, rfl⟩ := mem_filter_map hr
    have := (List.pairwise_append.mp hpw).2.2 y hy (⟨argAddr s 0, 4 * slots sig⟩, wa) (by simp [h0])
      (by rw [h2]; rfl)
    exact this.symm.sub_left hsub
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hak]
    exact Offset.disjoint_below _ (by omega_using [hfit, hsb, hk])

end

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The state the zeroize function runs from, with the permissions of its
contract: its arguments in the frame, and the first `n` bytes of the array. -/
def cwZEntry (sig : Sig) (j n : Nat) (s c : State) : State :=
  (cwZeroSt (slots sig) j n c).callEntry.withRegions
    [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)), 8⟩] [⟨(arg s j).setWidth 64, n⟩]

/-- `zeroArgs` and the zeroize function's entry. -/
theorem cw_zeroArgs (hl : Sig.noLists sig.params = true) {s c : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hc : AfterBody sig post stack s c) {j n : Nat} (hj : j < slots sig) :
    execBlock isa (zeroArgs (slots sig) j n) c =
        some (cwZeroSt (slots sig) j n c, cwZeroTrace (slots sig) j
          (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)))) ∧
      (cwZeroSt (slots sig) j n c).rd = s.rd ∧
      (cwZeroSt (slots sig) j n c).wr =
        ⟨(s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64, frameSize (slots sig)⟩ :: s.wr ∧
      (cwZeroSt (slots sig) j n c).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) ∧
      (∀ q, q ≠ .eax → (cwZeroSt (slots sig) j n c).gpr q = c.gpr q) ∧
      (cwZeroSt (slots sig) j n c).mem = cwZeroMem (slots sig) j n c ∧
      (cwZEntry sig j n s c).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) - 4 ∧
      arg (cwZEntry sig j n s c) 0 = arg s j ∧ arg (cwZEntry sig j n s c) 1 = BitVec.ofNat 32 n ∧
      argAddr (cwZEntry sig j n s c) 0 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)) := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  obtain ⟨hrdc, hwrc, hspc, -⟩ := id hc
  obtain ⟨hin, harg⟩ := cw_in hl hs hrdc hwrc hspc
  have hE : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).toNat =
      (s.gpr .esp).toNat - frameSize (slots sig) := sub_toNat (by omega_using [hsb])
  have hFs : frameSize (slots sig) = 4 * argWords (slots sig) + 8 := rfl
  obtain ⟨hrun, hrd, hwr, hg, hm⟩ := zeroArgs_run' (n := n) (fun d hd => hin d (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd, hFs])) (harg j hj)
  rw [hspc] at hrun
  have hesp : (cwZeroSt (slots sig) j n c).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) := by
    rw [hg .esp (by decide), hspc]
  obtain ⟨r0, r1, -, -⟩ := cwZeroMem_reads (m := slots sig) (j := j) (n := n) (c := c) hj
    (by rw [hspc, hE]; omega_using [hsb, hfit])
  have hsrc : addr (c.gpr .esp) (frameSize (slots sig) + 4 + 4 * j) = argAddr s j := by
    rw [hspc, addr, show frameSize (slots sig) + 4 + 4 * j = frameSize (slots sig) + (4 + 4 * j) by omega,
      sub_add_ofNat]; rfl
  have harg' : ∀ q, arg (cwZEntry sig j n s c) q =
      (cwZeroSt (slots sig) j n c).mem.readW (addr (c.gpr .esp) (4 * q)) 32 ∨ q > 1 := by
    intro q
    by_cases hq : q ≤ 1
    · refine .inl ?_
      rw [cwZEntry, arg_withRegions, arg_callEntry (by rw [hesp, hE]; omega_using [hsb, hB])
        (by rw [hesp, hE]; omega_using [hsb, hfit, hB, hq]), hesp, hspc]
      rfl
    · exact .inr (by omega_using [hq])
  refine ⟨hrun, by rw [hrd, hrdc], by rw [hwr, hwrc], hesp, hg, hm, ?_, ?_, ?_, ?_⟩
  · rw [cwZEntry, State.withRegions_gpr, State.callEntry_esp, hesp]
  · rcases harg' 0 with h | h
    · rw [h, hm, show 4 * 0 = 0 from rfl, r0, hsrc, cw_argRead hl hs hc hj]
    · omega_using [h]
  · rcases harg' 1 with h | h
    · rw [h, hm, show 4 * 1 = 4 from rfl, r1]
    · omega_using [h]
  · rw [argAddr, cwZEntry, State.withRegions_gpr, State.callEntry_esp, hesp, show 4 + 4 * 0 = 4 by rfl,
      show (BitVec.ofNat 32 4 : BitVec 32) = 4 from rfl, BitVec.sub_add_cancel]
    exact Taint.sub_setWidth (by omega_using [hsb])

end

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

theorem toNat_ofNat32 {n : Nat} (hn : n < 2 ^ 32) : ((BitVec.ofNat 32 n).setWidth 64).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_using [hn])]

/-- What the caller's contract gives of the array: its region is within the
writable ones. -/
theorem cw_array (hl : Sig.noLists sig.params = true) {e : Elem} {k : Nat} {s : State} {p : Addr}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (harr : (⟨p, k * e.size⟩, true) ∈ Sig.bufs sig.params (stackArgs sig s)) :
    (⟨p, k * e.size⟩ : Region) ∈ s.wr ∧ (⟨p, k * e.size⟩ : Region) ∈ wbufs sig s ∧
      p.toNat + k * e.size ≤ 2 ^ 32 := by
  have hreg := cw_regions hl hs
  rw [pre_stack hl] at hs
  obtain ⟨-, -, -, -, -, hnw, -⟩ := hs
  exact ⟨(hreg _ (bufs_mem harr)).2 rfl, List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨harr, rfl⟩, rfl⟩,
    hnw _ harr⟩

/-- The zeroize function's precondition, at its entry. -/
theorem cw_zeroPre (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n zst j : Nat} {s c : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hj : j < slots sig)
    (harr : (⟨(arg s j).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (stackArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hzs : zst ≤ stack) (hc : AfterBody sig post stack s c) :
    (Spec.Zeroize.zeroizeContract abi zst).pre (cwZEntry sig j n s c) := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  have hE := (s.gpr .esp).isLt
  have hA := cw_low hl hs _ (bufs_mem harr)
  have hnw := (cw_array hl hs harr).2.2
  have hsubA : Region.Sub ⟨(arg s j).setWidth 64, n⟩ ⟨(arg s j).setWidth 64, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨-, -, -, -, -, -, hzsp, h0, h1, hza⟩ := cw_zeroArgs (n := n) hl hs hc hj
  have e4 : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) - 4) =
      s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig) + 4) := by
    rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl
  have hz64 : ((cwZEntry sig j n s c).gpr .esp).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig) + 4) := by
    rw [hzsp, e4]; exact Taint.sub_setWidth (by omega_using [hsb])
  have hzn : ((cwZEntry sig j n s c).gpr .esp).toNat = (s.gpr .esp).toNat - (frameSize (slots sig) + 4) := by
    rw [hzsp, e4]; exact sub_toNat (by omega_using [hsb])
  have hlo : ∀ {d nn : Nat}, nn ≤ d → frameSize (slots sig) + nn ≤ d → d ≤ stack + frameSize (slots sig) + 4 →
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 d, nn⟩ ⟨(arg s j).setWidth 64, n⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 d, nn⟩
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)), 8⟩ := fun hnn hd hdT =>
    ⟨(hA _ _ hnn hdT).sub_right hsubA, below_disjoint _ (stack + frameSize (slots sig) + 4) hdT (by omega_using [])
      (.inl (by omega_using [hd, hdT])) (by omega_using [hsb, hfit, hE, hdT, hnn])
      (by omega_using [hsb, hfit, hE, hB])⟩
  refine zeroize_pre_of (n := n) (by rw [h1]; exact toNat_ofNat32 hn32)
    ⟨by rw [hzn]; omega_using [hsb, hzs], by rw [hzn]; omega_using [hsb, hfit, hB]⟩
    (by rw [hza]; rfl) (by rw [h0]; rfl) ?_ ?_ (by rw [h0]; omega_using [hnw, hn])
  · rw [h0, hza]
    exact ((hA (frameSize (slots sig)) 8 (by omega_using [hB]) (by omega_using [])).sub_right hsubA).symm
  · rw [h0, hza, hz64, stackBelow_sp']
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hlo (by omega_using []) (by omega_using []) (by omega_using [])
    · split at hx
      · simp at hx
      · simp only [List.mem_singleton] at hx; subst hx
        exact hlo (by omega_using []) (by omega_using []) (by omega_using [hzs])

/-- The zeroize function's public data, at its entry, if the array's
address is public. -/
theorem cw_zeroPub (hl : Sig.noLists sig.params = true) {n j : Nat} {zst : Nat} {s₁ s₂ c₁ c₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s₂)
    (hj : j < slots sig) (hsp : s₁.gpr .esp = s₂.gpr .esp) (hpp : arg s₁ j = arg s₂ j)
    (hc₁ : AfterBody sig post stack s₁ c₁) (hc₂ : AfterBody sig post stack s₂ c₂) :
    (Spec.Zeroize.zeroizeContract abi zst).pub (cwZEntry sig j n s₁ c₁) (cwZEntry sig j n s₂ c₂) := by
  obtain ⟨-, -, -, -, -, -, p₁, a₁, b₁, -⟩ := cw_zeroArgs (n := n) hl h₁ hc₁ hj
  obtain ⟨-, -, -, -, -, -, p₂, a₂, b₂, -⟩ := cw_zeroArgs (n := n) hl h₂ hc₂ hj
  exact zeroize_pub_of (by rw [p₁, p₂, hsp]) (by rw [a₁, a₂, hpp]) (by rw [b₁, b₂])

/-- The zeroize function's regions are among those of the state its call is
made from. -/
theorem cw_zeroCovers (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n j : Nat} {s c : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hj : j < slots sig)
    (harr : (⟨(arg s j).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (stackArgs sig s))
    (hn : n ≤ k * e.size) (hc : AfterBody sig post stack s c) :
    Covers ([⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig)), 8⟩] ++
        [⟨(arg s j).setWidth 64, n⟩])
      ((cwZeroSt (slots sig) j n c).rd ++ (cwZeroSt (slots sig) j n c).wr) ∧
      Covers [⟨(arg s j).setWidth 64, n⟩] (cwZeroSt (slots sig) j n c).wr := by
  obtain ⟨hsb, -⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  obtain ⟨hF, -⟩ := cw_esp64 (wa := wa) hl hs
  obtain ⟨-, -, hwr, -⟩ := cw_zeroArgs (n := n) hl hs hc hj
  have hA := (cw_array hl hs harr).1
  have hw : Covers [⟨(arg s j).setWidth 64, n⟩] (cwZeroSt (slots sig) j n c).wr :=
    Covers.one ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ hA, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn⟩
  refine ⟨Covers.append_left (Covers.right (Covers.one ⟨_, by rw [hwr]; exact List.mem_cons_self .., by
    rw [hF]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_using [hB]⟩))
    (Covers.right hw), hw⟩

/-- What the zeroize function's run leaves, from the caller's state `s`: the
first function's, but for the first `n` bytes of the array, which are zero;
its result is in the frame. -/
def AfterZero (sig : Sig) (post : sig.Post abi.ptrBits) (stack j n : Nat) (s g : State) : Prop :=
  ∃ c, AfterBody sig post stack s c ∧
    g.rd = s.rd ∧
    g.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64, frameSize (slots sig)⟩ :: s.wr ∧
    g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) ∧
    (∀ q ∈ calleeSaved, g.gpr q = s.gpr q ∨ q = .esp) ∧
    g.mem.readW (addr (g.gpr .esp) (4 * argWords (slots sig))) 32 = c.gpr .eax ∧
    g.mem.readW (addr (g.gpr .esp) (4 * argWords (slots sig) + 4)) 32 = c.gpr .edx ∧
    Frame (wbufs sig s ++ [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + frameSize (slots sig) + 4),
      stack + frameSize (slots sig) + 4⟩]) s.mem g.mem ∧
    Frame [⟨(arg s j).setWidth 64, n⟩, ⟨(s.gpr .esp).setWidth 64 -
      BitVec.ofNat 64 (stack + frameSize (slots sig) + 4), stack + frameSize (slots sig) + 4⟩] c.mem g.mem ∧
    Spec.Zeroize.bytesAt g.mem ((arg s j).setWidth 64) n = Spec.Zeroize.zeros n

end

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The frame's word at `d`, as the `frameSize - d` bytes below `esp`. -/
theorem frame_word (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s) {d : Nat}
    (hd : d + 4 ≤ frameSize (slots sig)) :
    addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) d =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (frameSize (slots sig) - d) := by
  obtain ⟨hsb, -⟩ := cw_sp hl hs
  exact sub_add_setWidth (by omega_using [hd]) (by omega_using [hsb])

/-- The call of the zeroize function. -/
theorem cw_zero_wp {zname : String} {zcode : Prog isa} {zst : Nat}
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hzsp : NoSp zcode) (hzd : stackUse zcode ≤ zst) (hzs : zst ≤ stack)
    (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n j : Nat} {s c : State}
    (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hj : j < slots sig)
    (harr : (⟨(arg s j).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (stackArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hc : AfterBody sig post stack s c) :
    WP isa (.call zname zcode) (cwZeroSt (slots sig) j n c) (AfterZero sig post stack j n s) := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB := frameSize_ge (slots sig)
  have hFs : frameSize (slots sig) = 4 * argWords (slots sig) + 8 := rfl
  have hE := (s.gpr .esp).isLt
  have hEn : (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).toNat =
      (s.gpr .esp).toNat - frameSize (slots sig) := sub_toNat (by omega_using [hsb])
  have hA := cw_low hl hs _ (bufs_mem harr)
  obtain ⟨hAw, hAb, -⟩ := cw_array hl hs harr
  have hsubA : Region.Sub ⟨(arg s j).setWidth 64, n⟩ ⟨(arg s j).setWidth 64, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨-, hrdz, hwrz, hspz, hgz, hmz, -, h0, h1, -⟩ := cw_zeroArgs (n := n) hl hs hc hj
  obtain ⟨hcv, hcw⟩ := cw_zeroCovers hl hs hj harr hn hc
  obtain ⟨hrdc, hwrc, hspc, hcsc, hfc, -⟩ := id hc
  obtain ⟨-, -, rA, rD⟩ := cwZeroMem_reads (m := slots sig) (j := j) (n := n) (c := c) hj
    (by rw [hspc, hEn]; omega_using [hsb, hfit])
  rw [hspc] at rA rD
  have hBl : ∀ {d : Nat}, d + 4 ≤ frameSize (slots sig) →
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + frameSize (slots sig) + 4),
        stack + frameSize (slots sig) + 4⟩ : Region).Contains
        (addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) d) 4 := fun hd => by
    rw [frame_word hl hs hd]
    exact Offset.contains_below _ (by omega_using [hd]) (by omega_using [hd]) (by omega_using [hsb, hE])
  -- `zeroArgs` writes only in the frame.
  have fz : Frame [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + frameSize (slots sig) + 4),
      stack + frameSize (slots sig) + 4⟩] c.mem (cwZeroSt (slots sig) j n c).mem := by
    rw [hmz, cwZeroMem, hspc]
    exact Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (hBl (by omega_using [hFs]))) (List.mem_singleton_self _) _ (hBl (by omega_using [hFs])))
      (List.mem_singleton_self _) _ (hBl (by omega_using [hB]))) (List.mem_singleton_self _) _
      (hBl (by omega_using [hB]))
  refine WP.call (k := Spec.Zeroize.zeroizeContract abi zst) hz.1 hzsp
    (by rw [hspz, hEn]; omega_using [hsb, hzd, hzs]) (cw_zeroPre hl hs hj harr hn hn32 hzs hc) hcv hcw ?_
  intro g hrd hwr hcs hfr _ ⟨Y, hm, _, hq⟩
  rw [hspz, below_frame64 hl hs (by omega_using [hzd, hzs])] at hfr
  have hgesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) := by
    rw [hcs .esp (by decide), hspz]
  -- The result's slots, which the zeroize function does not write.
  have hslot : ∀ {d : Nat}, frameSize (slots sig) - 8 ≤ d → d + 4 ≤ frameSize (slots sig) →
      g.mem.readW (addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) d) 32 =
        (cwZeroSt (slots sig) j n c).mem.readW (addr (s.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))) d) 32 :=
    fun hd₁ hd₂ => by
      rw [frame_word hl hs hd₂]
      refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact (hA _ _ (by omega_using [hd₂]) (by omega_using [hd₂])).sub_right hsubA
      · simp only [List.mem_singleton] at hr; subst hr
        exact below_disjoint _ (stack + frameSize (slots sig) + 4) (by omega_using [hd₂])
          (by omega_using [hzd, hzs]) (.inr (by omega_using [hd₁, hd₂, hzd, hzs]))
          (by omega_using [hsb, hE]) (by omega_using [hsb, hE, hzd, hzs])
  have hsub : ∀ r ∈ [⟨(arg s j).setWidth 64, n⟩] ++ [⟨(s.gpr .esp).setWidth 64 -
      BitVec.ofNat 64 (frameSize (slots sig) + (stackUse zcode + 4)), stackUse zcode + 4⟩],
      Region.Sub r ⟨(arg s j).setWidth 64, n⟩ ∨
        Region.Sub r ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + frameSize (slots sig) + 4),
          stack + frameSize (slots sig) + 4⟩ := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact .inl fun _ h => h
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inr (Offset.sub_below _ (by omega_using [hzd, hzs]) (by omega_using [hzd, hzs]))
  refine ⟨c, hc, by rw [hrd, hrdz], by rw [hwr, hwrz], hgesp, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hq' : q = .esp
    · exact .inr hq'
    · rw [hcs q hq, hgz q (by intro h; subst h; simp [calleeSaved] at hq)]
      exact hcsc q hq
  · rw [hgesp, hslot (by omega_using [hFs]) (by omega_using [hFs]), hmz, rA]
  · rw [hgesp, hslot (by omega_using [hFs]) (by omega_using [hFs]), hmz, rD]
  · refine Frame.trans hfc (Frame.trans (Frame.mono fz fun x hx => List.mem_append_right _ hx)
      (Frame.sub hfr fun r hr => ?_))
    rcases hsub r hr with h | h
    · exact ⟨_, List.mem_append_left _ hAb, fun x hx => hsubA x (h x hx)⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩
  · refine Frame.trans (Frame.mono fz fun x hx => List.mem_cons_of_mem _ hx) (Frame.sub hfr fun r hr => ?_)
    rcases hsub r hr with h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩
  · rw [zeroize_post_iff, show (cwZeroSt (slots sig) j n c).callEntry.withRegions _ _ = cwZEntry sig j n s c from rfl,
      h0, h1, hm, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn32] at hq
    exact hq

end

/-! ## The whole call -/

/-- `callWipe`'s frame body writes `esp` only if its callees do. -/
theorem cw_main_noSp {m j n : Nat} {name zname : String} {body zcode : Prog isa}
    (hsp : NoSp body) (hzsp : NoSp zcode) :
    NoSp (.seq (.block (copyArgs (frameSize m) m)) (.seq (.call name body) (.seq (.block (zeroArgs m j n))
      (.seq (.call zname zcode) (.block (restoreRet m))))) : Prog isa) := by
  intro i hi
  simp only [instrs, List.mem_append] at hi
  rcases hi with hi | hi | hi | hi | hi
  · simp only [copyArgs, copyArg, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨_, -, rfl | rfl⟩ := hi <;> rfl
  · exact hsp i hi
  · simp only [zeroArgs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · exact hzsp i hi
  · simp only [restoreRet, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

/-- `callWipe` writes `esp` only in its frame and its calls, if its callees
do only in their frames. -/
theorem callWipe_noSp {m j n : Nat} {name zname : String} {body zcode : Prog isa}
    (hsp : NoSp body) (hzsp : NoSp zcode) : NoSp (callWipe m j n name body zname zcode) := by
  intro i hi
  simp only [callWipe, instrs, List.mem_cons, List.mem_append] at hi
  rcases hi with (rfl | hi) | hi
  · rfl
  · exact cw_main_noSp (name := name) (zname := zname) hsp hzsp i (by simp only [instrs, List.mem_append]; exact hi)
  · simp only [List.not_mem_nil, or_false] at hi; subst hi; rfl

/-- The stack `callWipe` and its callees use: its frame, and the larger of
its callees' with their return addresses. -/
theorem stackUse_callWipe {m j n : Nat} {name zname : String} {body zcode : Prog isa} :
    stackUse (callWipe m j n name body zname zcode) =
      max (stackUse body + 4) (stackUse zcode + 4) + frameSize m := by
  simp only [callWipe, stackUse, frameBytes, Nat.zero_max, Nat.max_zero]

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- A run of `callWipe` from the caller's state `s`: it keeps what the
calling convention requires, its postcondition is the first function's if
that reads the memory on return only within the buffers apart from the
array (`hout`), and the first `n` bytes of the array are zero. -/
theorem cw_wp {name zname : String} {body zcode : Prog isa} {zst : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hl : Sig.noLists sig.params = true) (hsp : NoSp body) (hd : stackUse body ≤ stack)
    (hzsp : NoSp zcode) (hzd : stackUse zcode ≤ zst) (hzs : zst ≤ stack)
    (hB : frameSize (slots sig) < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {e : Elem} {k n j : Nat} (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32)
    {s : State} (hs : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hj : j < slots sig)
    (harr : (⟨(arg s j).setWidth 64, k * e.size⟩, true) ∈ Sig.bufs sig.params (stackArgs sig s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (stackArgs sig s),
        b.1.Disjoint ⟨(arg s j).setWidth 64, k * e.size⟩ → ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (stackArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (stackArgs sig s) s.mem m₂ x) :
    WP isa (callWipe (slots sig) j n name body zname zcode) s fun G =>
      abiPreserved s G ∧ (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).post s G ∧
        Spec.Zeroize.bytesAt G.mem ((arg s j).setWidth 64) n = Spec.Zeroize.zeros n := by
  obtain ⟨hsb, hfit⟩ := cw_sp hl hs
  have hB' := frameSize_ge (slots sig)
  have hE := (s.gpr .esp).isLt
  have hlow := cw_low hl hs
  have hres := cw_res hl hs
  refine WP.frameAlloc (by omega_using [hB']) hB (by simp only [frameSize]; omega) (by omega_using [hsb])
    (cw_main_noSp hsp hzsp) ?_
  refine WP.seq (WP.block ⟨_, (cwW_mem hl hs).1, ?_⟩)
  refine WP.seq (WP.mono (cw_body_wp h hl hsp hd hpre hpost hs) fun c hc => ?_)
  refine WP.seq (WP.block ⟨_, (cw_zeroArgs (n := n) hl hs hc hj).1, ?_⟩)
  refine WP.seq (WP.mono (cw_zero_wp hz hzsp hzd hzs hl hs hj harr hn hn32 hc) fun g hg => ?_)
  obtain ⟨c', hc', hrdg, hwrg, hspg, hcsg, hra, hrd', hfs, hfc, hz0⟩ := hg
  obtain ⟨hin, -⟩ := cw_in hl hs hrdg hwrg hspg
  have hFs : frameSize (slots sig) = 4 * argWords (slots sig) + 8 := rfl
  obtain ⟨w, hrun, -, -, hmw, hgw, heax, hedx⟩ := restoreRet_run (m := slots sig) (g := g) fun d hd =>
    let ⟨r, hr, hc⟩ := hin d (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd, hFs])
    ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.block ⟨_, hrun, ?_⟩
  show abiPreserved s (freed (frameSize (slots sig)) w) ∧
    (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).post s (freed (frameSize (slots sig)) w) ∧
    Spec.Zeroize.bytesAt (freed (frameSize (slots sig)) w).mem ((arg s j).setWidth 64) n = Spec.Zeroize.zeros n
  refine ⟨⟨fun q hq => ?_, ?_⟩, ?_, by rw [freed_mem, hmw]; exact hz0⟩
  · -- The callee-saved registers.
    by_cases hq' : q = .esp
    · subst hq'
      rw [freed_esp, hgw .esp (by decide) (by decide), hspg, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ hq', hgw q (by intro h; subst h; simp [calleeSaved] at hq)
        (by intro h; subst h; simp [calleeSaved] at hq)]
      exact (hcsg q hq).resolve_right hq'
  · -- The return address: memory changes only within the writable buffers and below `esp`.
    rw [freed_mem, hmw]
    refine hfs.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨y, hy, -, rfl⟩ := mem_filter_map hr
      exact (hres y (bufs_mem hy)).1
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint_below _ (by omega_using [hsb, hE])
  · -- The postcondition, which reads the memory on return only within the buffers apart from the array.
    rw [post_stack, freed_gpr _ _ (by decide), freed_gpr _ _ (by decide), heax, hedx, hra, hrd', freed_mem, hmw]
    refine hout c'.mem _ _ (fun b hb hbA x hx => ?_) hc'.2.2.2.2.2
    refine (hfc x fun R hR hcR => ?_).symm
    rcases List.mem_cons.mp hR with rfl | hR
    · exact hbA x hx (Region.sub_prefix hn x hcR)
    · simp only [List.mem_singleton] at hR; subst hR
      exact hlow b (bufs_mem hb) _ _ (Nat.le_refl _) (Nat.le_refl _) x hcR hx

end

/-- A call of verified code, narrowed in each run to regions of its own. -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .esp = s₂.gpr .esp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine regionModel.relCT_call hv hct fun s₁ s₂ e₁ e₂ hp h₁ h₂ => ?_
  rw [call_callEntry, Option.some.injEq] at h₁ h₂
  subst h₁ h₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP _ _ hp
  refine ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, by simp only [hsp],
    fun _ _ _ _ r₁ r₂ => ?_⟩
  have q₁ := (ret_gpr r₁ .esp).1
  have q₂ := (ret_gpr r₂ .esp).1
  simp only [State.callEntry_esp] at q₁ q₂
  simp only [q₁, q₂, hsp]

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
function whose arguments take `slots sig` slots on the stack, word `i` of
them, in slot `j`, a writable array of `k` elements `e`, is verified with
`stack + frameSize (slots sig) + 4` bytes when called by `callWipe`, which
then zeroes the first `n` bytes of the array with code verified against
`Spec.Zeroize.zeroizeContract` (with `zst ≤ stack` bytes of stack), against
the contract whose postcondition `post'` follows from the function's and
those bytes being zero (`hwiped`). Each callee writes `esp` only in its
frames and uses no more stack than its contract gives it (`hsp`, `hd`,
`hzsp`, `hzd`). The precondition, postcondition and leak must read the
memory on entry only within the function's buffers (`hpre`, `hpost`,
`hleak`), and the postcondition the memory on return only within those
apart from the array (`hpostOut`). -/
theorem Verified.callWipe' {post' : sig.Post abi.ptrBits} {name zname : String}
    {body zcode : Prog isa} {zst : Nat} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {k n i j : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 32).length)
    (hj : j = (argSlots (widths sig) 0).getD i 0)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hB : frameSize (slots sig) < 4096)
    (hsp : NoSp body) (hd : stackUse body ≤ stack)
    (hzsp : NoSp zcode) (hzd : stackUse zcode ≤ zst) (hzs : zst ≤ stack)
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
    (hsat : ∃ s, (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.X86.callWipe (slots sig) j n name body zname zcode)
      (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak) := by
  subst hi hj
  have hL : (sig.words abi.ptrBits).length = (ps₁.flatMap fun p => p.2.words 32).length + 1 +
      (ps₂.flatMap fun p => p.2.words 32).length := by
    show (sig.params.flatMap fun p => p.2.words 32).length = _
    rw [hps, List.flatMap_append, List.flatMap_cons]
    simp only [List.length_append, Param.words.eq_2, List.length_cons, List.length_nil]
    omega
  generalize hI : (ps₁.flatMap fun p => p.2.words 32).length = I at hL hpostOut hwiped ⊢
  have hwl : (widths sig).length = (sig.words abi.ptrBits).length := List.length_map _
  have hal : (argSlots (widths sig) 0).length = (sig.words abi.ptrBits).length := by
    rw [argSlots_length, hwl]
  have hiw : I < (widths sig).length := by rw [hwl, hL]; omega
  have hia : I < (argSlots (widths sig) 0).length := by rw [hal, hL]; omega
  have hW : (widths sig).getD I 64 = 32 := by
    show ((sig.params.flatMap fun p => p.2.words 32).map (·.bits 32)).getD _ 64 = 32
    rw [hps, ← hI]; exact (Sig.pub_array (pb := 32) ps₁ ps₂).2
  have hW' : (widths sig)[I] = 32 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiw, Option.getD_some] at hW; exact hW
  generalize hJ : (argSlots (widths sig) 0).getD I 0 = j
  have hJ' : (argSlots (widths sig) 0)[I] = j := by
    rw [← hJ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia, Option.getD_some]
  have hlz : I < ((widths sig).zip (argSlots (widths sig) 0)).length := by rw [List.length_zip]; omega
  have hzip : ((widths sig).zip (argSlots (widths sig) 0))[I]'hlz = (32, j) := by
    rw [List.getElem_zip, hW', hJ']
  have hjs : j < slots sig := by
    have := argSlots_lt (widths sig) 0 _ (List.getElem_mem hlz)
    rw [hzip] at this
    simp only [Nat.zero_add] at this
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
  have hget : ∀ s : State, (stackArgs sig s).getD I 0 = (arg s j).setWidth 64 := fun s => by
    rw [stackArgs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hlz, Option.map_some, Option.getD_some, hzip]
    simp only [argVal, show (32 : Nat) ≠ 64 by decide, ite_false]
  -- The array, among the buffers.
  have harr : ∀ s : State, (⟨(arg s j).setWidth 64, k * e.size⟩, true) ∈
      Sig.bufs sig.params (stackArgs sig s) := by
    intro s
    rw [← hget s, hps, ← hI]
    exact Sig.bufs_mem_array (pb := 32) ps₂ ps₁ (stackArgs sig s)
      (by rw [stackArgs_length, hI]; show _ < (sig.words abi.ptrBits).length; rw [hL]; omega)
  -- Its address is public.
  have hpubA : ∀ s₁ s₂, (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pub s₁ s₂ →
      arg s₁ j = arg s₂ j := by
    intro s₁ s₂ hp
    have hP : (sig.params.flatMap (·.2.pubs)).getD I false = true := by
      rw [hps, ← hI]; exact (Sig.pub_array (pb := 32) ps₁ ps₂).1
    have h2 := congrArg BitVec.toNat (((pubL_stack hl).mp hp).2 _ hP)
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hW, hget, hget, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (a := (arg s₁ j).toNat) (by have := (arg s₁ j).isLt; omega),
      Nat.mod_eq_of_lt (a := (arg s₂ j).toNat) (by have := (arg s₂ j).isLt; omega),
      Nat.mod_eq_of_lt (arg s₁ j).isLt, Nat.mod_eq_of_lt (arg s₂ j).isLt] at h2
    exact BitVec.eq_of_toNat_eq h2
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s → ∀ m₁ m₂ x,
      (∀ b ∈ Sig.bufs sig.params (stackArgs sig s), b.1.Disjoint ⟨(arg s j).setWidth 64, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (stackArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (stackArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    rw [pre_stack hl] at hs
    exact hpostOut _ _ _ _ _ (stackArgs_length sig s) (hs.2.2.2.1.sublist (List.sublist_append_left _ _))
      (by rw [hget]; exact hag) hq
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · obtain ⟨t, g, he, habi, hq, hz0⟩ :=
      cw_wp h hz hl hsp hd hzsp hzd hzs hB hpre hpost hn hn32 hs hjs (harr s) (hout s hs)
    refine ⟨t, g, he, habi, ?_⟩
    rw [post_stack] at hq ⊢
    exact hwiped _ _ _ _ (stackArgs_length sig s) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) ?_
    refine RelCT.mono (P := fun a b => ∃ σ₁ σ₂,
        ((sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pub σ₁ σ₂) ∧ a = σ₁ ∧ b = σ₂) ?_
      (fun a b hab => ⟨a, b, hab, rfl, rfl⟩) (fun _ _ h => h)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + frameSize (slots sig) + 4) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre σ₂ := h₂
    have hp' : (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pub σ₁ σ₂ := hp
    have hsp12 : σ₁.gpr .esp = σ₂.gpr .esp := ((pubL_stack hl).mp hp').1.1
    have hpp := hpubA _ _ hp'
    refine RelCT.mono (P := fun a b => a = σ₁ ∧ b = σ₂) ?_ (fun a b hab => hab.2) (fun _ _ h => h)
    refine RelCT.frameAlloc (R := fun _ _ => True) ?_
    refine RelCT.mono (P := fun a b => a = allocFrame (frameSize (slots sig)) σ₁ ∧
      b = allocFrame (frameSize (slots sig)) σ₂) ?_
      (fun a b hab => by obtain ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩ := hab; exact ⟨rfl, rfl⟩) (fun _ _ h => h)
    -- The arguments are copied.
    refine RelCT.seq (R := fun a b => a = cwW sig σ₁ ∧ b = cwW sig σ₂)
      (RelCT.block_of fun a b hab => ?_) ?_
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, (cwW_mem hl h₁').1, by rw [(cwW_mem hl h₂').1, hsp12], rfl, rfl⟩
    -- The first function.
    refine RelCT.seq (R := fun c₁ c₂ => AfterBody sig post stack σ₁ c₁ ∧ AfterBody sig post stack σ₂ c₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterBody sig post stack σ₁) (F₂ := AfterBody sig post stack σ₂)
        (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨rfl, rfl⟩ := hab
        obtain ⟨c₁, w₁⟩ := cw_bodyCovers (wa := wa) hl h₁'
        obtain ⟨c₂, w₂⟩ := cw_bodyCovers (wa := wa) hl h₂'
        exact ⟨_, _, _, _, cw_bodyPre hl hpre h₁', cw_bodyPre hl hpre h₂', cw_bodyPub hl h₁' h₂' hp' hleak,
          c₁, w₁, c₂, w₂, by rw [cwW_esp, cwW_esp, hsp12]⟩
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨cw_body_wp h hl hsp hd hpre hpost h₁', cw_body_wp h hl hsp hd hpre hpost h₂'⟩
    -- The zeroize function's arguments.
    refine RelCT.seq (R := fun d₁ d₂ => (∃ c, AfterBody sig post stack σ₁ c ∧ d₁ = cwZeroSt (slots sig) j n c) ∧
      (∃ c, AfterBody sig post stack σ₂ c ∧ d₂ = cwZeroSt (slots sig) j n c))
      (RelCT.block_of fun c₁ c₂ hc => ⟨_, _, _, (cw_zeroArgs (n := n) hl h₁' hc.1 hjs).1,
        by rw [(cw_zeroArgs (n := n) hl h₂' hc.2 hjs).1, hsp12], ⟨c₁, hc.1, rfl⟩, ⟨c₂, hc.2, rfl⟩⟩) ?_
    -- The zeroize function.
    refine RelCT.seq (R := fun g₁ g₂ => AfterZero sig post stack j n σ₁ g₁ ∧ AfterZero sig post stack j n σ₂ g₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterZero sig post stack j n σ₁) (F₂ := AfterZero sig post stack j n σ₂)
        (RelCT.callEx hz.1 hz.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        obtain ⟨v₁, x₁⟩ := cw_zeroCovers hl h₁' hjs (harr σ₁) hn hc₁
        obtain ⟨v₂, x₂⟩ := cw_zeroCovers hl h₂' hjs (harr σ₂) hn hc₂
        obtain ⟨-, -, -, e₁, -⟩ := cw_zeroArgs (n := n) hl h₁' hc₁ hjs
        obtain ⟨-, -, -, e₂, -⟩ := cw_zeroArgs (n := n) hl h₂' hc₂ hjs
        exact ⟨_, _, _, _, cw_zeroPre hl h₁' hjs (harr σ₁) hn hn32 hzs hc₁,
          cw_zeroPre hl h₂' hjs (harr σ₂) hn hn32 hzs hc₂, cw_zeroPub hl h₁' h₂' hjs hsp12 hpp hc₁ hc₂,
          v₁, x₁, v₂, x₂, by rw [e₁, e₂, hsp12]⟩
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨cw_zero_wp hz hzsp hzd hzs hl h₁' hjs (harr σ₁) hn hn32 hc₁,
          cw_zero_wp hz hzsp hzd hzs hl h₂' hjs (harr σ₂) hn hn32 hc₂⟩
    -- The result is restored.
    · refine RelCT.block_of fun g₁ g₂ hg => ?_
      obtain ⟨⟨_, _, r₁, w₁, e₁, _⟩, ⟨_, _, r₂, w₂, e₂, _⟩⟩ := hg
      have hFs : frameSize (slots sig) = 4 * argWords (slots sig) + 8 := rfl
      have hin : ∀ (σ g : State),
          (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre σ →
          g.rd = σ.rd →
          g.wr = ⟨(σ.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig))).setWidth 64, frameSize (slots sig)⟩ ::
            σ.wr → g.gpr .esp = σ.gpr .esp - BitVec.ofNat 32 (frameSize (slots sig)) →
          ∀ d ∈ [4 * argWords (slots sig), 4 * argWords (slots sig) + 4],
            InRegions (g.rd ++ g.wr) (addr (g.gpr .esp) d) 4 := fun σ g hσ hr hw he d hd =>
        let ⟨r, hr', hc⟩ := (cw_in hl hσ hr hw he).1 d (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd, hFs])
        ⟨r, List.mem_append_right _ hr', hc⟩
      obtain ⟨u₁, hu₁, -⟩ := restoreRet_run (hin σ₁ g₁ h₁' r₁ w₁ e₁)
      obtain ⟨u₂, hu₂, -⟩ := restoreRet_run (hin σ₂ g₂ h₂' r₂ w₂ e₂)
      exact ⟨u₁, u₂, _, hu₁, by rw [hu₂, e₁, e₂, hsp12], trivial⟩

/-- `Verified.callWipe'`, with the function's postcondition. -/
theorem Verified.callWipe {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {k n i j : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 32).length)
    (hj : j = (argSlots (widths sig) 0).getD i 0)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hB : frameSize (slots sig) < 4096)
    (hsp : NoSp body) (hd : stackUse body ≤ stack)
    (hzsp : NoSp zcode) (hzd : stackUse zcode ≤ zst) (hzs : zst ≤ stack)
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.X86.callWipe (slots sig) j n name body zname zcode)
      (sig.contract abi pre post wa (stack + frameSize (slots sig) + 4) leak) :=
  Verified.callWipe' h hz hl hps hi hj hn hn32 hB hsp hd hzsp hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak

end

end VG.X86
