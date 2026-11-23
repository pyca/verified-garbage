module

public import VerifiedGarbage.Impl.ViaMm.X86
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.AllocFrame

/-!
# Calling a function with its stack arguments copied (x86, 32-bit)

`Verified.callCopy`: `callCopy k name core` (`Impl/ViaMm/X86.lean`) copies
its caller's `k` argument slots into the bottom of a frame of its own
(`copyTo`), so that `core`, which it then calls, finds them at its own `esp`,
as a function called by its caller would. Code verified against a contract is
verified so, with `4 k + 4` more bytes of stack: `core` runs from the state
after the call, with the permissions of its contract (the caller's buffers,
and the copies in place of the caller's argument area), and its run there is
its run from that state (`WP.call`).
-/

@[expose] public section

namespace VG.X86

open VG.Impl.ViaMm.X86 VG.Impl.StackScratch.X86

/-! ## The copies -/

/-- The state after `copyTo bytes j` from `u`. -/
def copyToState (bytes j : Nat) (u : State) : State :=
  { u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32) with
    mem := u.mem.writeW (addr (u.gpr .esp) (4 * j))
      (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32) }

theorem copyTo_run {bytes j : Nat} {u : State}
    (hr : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 4)
    (hw : InRegions u.wr (addr (u.gpr .esp) (4 * j)) 4) :
    execBlock isa (copyTo bytes j) u = some (copyToState bytes j u,
      [.addr (addr (u.gpr .esp) (bytes + 4 + 4 * j)), .addr (addr (u.gpr .esp) (4 * j))]) := by
  have hesp : (u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32)).gpr .esp =
      u.gpr .esp := by simp [State.setReg]
  simp only [copyTo, execBlock, isa, exec, readSrc, State.load32, ea_mk, hr, ite_true,
    Option.map_some, addrs, srcAddrs, State.store32, hesp]
  simp [copyToState, State.setReg, hw]

@[simp] theorem copyToState_esp (bytes j : Nat) (u : State) : (copyToState bytes j u).gpr .esp = u.gpr .esp := by
  simp [copyToState, State.setReg]
@[simp] theorem copyToState_rd (bytes j : Nat) (u : State) : (copyToState bytes j u).rd = u.rd := rfl
@[simp] theorem copyToState_wr (bytes j : Nat) (u : State) : (copyToState bytes j u).wr = u.wr := rfl
@[simp] theorem copyToState_syms (bytes j : Nat) (u : State) : (copyToState bytes j u).syms = u.syms := rfl
@[simp] theorem copyToState_mm (bytes j : Nat) (u : State) : (copyToState bytes j u).mm = u.mm := rfl
@[simp] theorem copyToState_mmx (bytes j : Nat) (u : State) : (copyToState bytes j u).mmx = u.mmx := rfl
@[simp] theorem copyToState_unknowns (bytes j : Nat) (u : State) :
    (copyToState bytes j u).unknowns = u.unknowns := rfl
theorem copyToState_gpr (bytes j : Nat) (u : State) {q : Reg} (h : q ≠ .eax) :
    (copyToState bytes j u).gpr q = u.gpr q := by
  simp [copyToState, State.setReg, h]

/-- The state after copying the first `m` argument slots from `u`. -/
def copiedTo (bytes : Nat) (u : State) : Nat → State
  | 0 => u
  | m + 1 => copyToState bytes m (copiedTo bytes u m)

@[simp] theorem copiedTo_esp (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).gpr .esp = u.gpr .esp
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_esp, copiedTo_esp bytes u m]
@[simp] theorem copiedTo_rd (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).rd = u.rd
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_rd, copiedTo_rd bytes u m]
@[simp] theorem copiedTo_wr (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).wr = u.wr
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_wr, copiedTo_wr bytes u m]
@[simp] theorem copiedTo_syms (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).syms = u.syms
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_syms, copiedTo_syms bytes u m]
@[simp] theorem copiedTo_mm (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).mm = u.mm
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_mm, copiedTo_mm bytes u m]
@[simp] theorem copiedTo_mmx (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).mmx = u.mmx
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_mmx, copiedTo_mmx bytes u m]
@[simp] theorem copiedTo_unknowns (bytes : Nat) (u : State) : ∀ m, (copiedTo bytes u m).unknowns = u.unknowns
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_unknowns, copiedTo_unknowns bytes u m]
theorem copiedTo_gpr (bytes : Nat) (u : State) {q : Reg} (h : q ≠ .eax) :
    ∀ m, (copiedTo bytes u m).gpr q = u.gpr q
  | 0 => rfl
  | m + 1 => by rw [copiedTo, copyToState_gpr _ _ _ h, copiedTo_gpr bytes u h m]

/-- The addresses copying the first `m` slots accesses. -/
def copyToTrace (bytes : Nat) (sp : BitVec 32) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j => [.addr (addr sp (bytes + 4 + 4 * j)), .addr (addr sp (4 * j))]

theorem copiesTo_run {bytes : Nat} {u : State} :
    ∀ m, (∀ j < m, InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 4) →
      (∀ j < m, InRegions u.wr (addr (u.gpr .esp) (4 * j)) 4) →
      execBlock isa ((List.range m).flatMap (copyTo bytes)) u =
        some (copiedTo bytes u m, copyToTrace bytes (u.gpr .esp) m)
  | 0, _, _ => rfl
  | m + 1, hr, hw => by
    rw [List.range_succ, List.flatMap_append, execBlock_append,
      copiesTo_run m (fun j hj => hr j (by omega_using [hj])) (fun j hj => hw j (by omega_using [hj]))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [copyTo_run (by simpa using hr m (by omega_using [])) (by simpa using hw m (by omega_using []))]
    simp only [Option.map_some, copiedTo, copiedTo_esp, copyToTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` slots writes only within the `m` destination slots
(from `esp`), which then hold the source slots (from `esp + bytes + 4`). -/
theorem copiedTo_mem {bytes : Nat} {u : State} :
    ∀ m, (u.gpr .esp).toNat + bytes + 4 + 4 * m ≤ 2 ^ 32 → 4 * m ≤ bytes →
      Frame [⟨(u.gpr .esp).setWidth 64, 4 * m⟩] u.mem (copiedTo bytes u m).mem ∧
      ∀ j < m, (copiedTo bytes u m).mem.readW (addr (u.gpr .esp) (4 * j)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedTo_mem (bytes := bytes) (u := u) m (by omega_using [hfit]) (by omega_using [hb])
    have hA : ∀ d, d < 4 + bytes + 4 * (m + 1) → addr (u.gpr .esp) d =
        (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun d hd => addr_eq (by omega_using [hfit, hd])
    have hR : Region.Sub ⟨(u.gpr .esp).setWidth 64, 4 * m⟩ ⟨(u.gpr .esp).setWidth 64, 4 * (m + 1)⟩ :=
      Region.sub_prefix (by omega_using [])
    have f' : Frame [⟨(u.gpr .esp).setWidth 64, 4 * (m + 1)⟩] u.mem (copiedTo bytes u m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    have hsrc : (copiedTo bytes u m).mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * m)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * m)) 32 := by
      rw [hA _ (by omega_using [])]
      refine f.readW (r := ⟨(u.gpr .esp).setWidth 64 + BitVec.ofNat 64 (bytes + 4 + 4 * m), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_using [hb]) (by omega_using [hfit])
    refine ⟨?_, fun j hj => ?_⟩
    · show Frame _ u.mem ((copiedTo bytes u m).mem.writeW _ _)
      rw [copiedTo_esp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      rw [hA _ (by omega_using [])]
      exact Offset.contains_base _ (d := 4 * m) (n := 4) (k := 4 * (m + 1)) (by omega_using []) (by omega_using [hfit])
    · show ((copiedTo bytes u m).mem.writeW (addr ((copiedTo bytes u m).gpr .esp) (4 * m))
          ((copiedTo bytes u m).mem.readW
            (addr ((copiedTo bytes u m).gpr .esp) (bytes + 4 + 4 * m)) 32)).readW _ 32 = _
      rw [copiedTo_esp]
      rcases Nat.lt_or_ge j m with hj' | hj'
      · rw [Mem.readW_writeW_sep, hv j hj']
        · rw [hA _ (by omega_using [hj']), hA _ (by omega_using [])]
          exact Offset.sep _ (d := 4 * j) (n := 4) (e := 4 * m) (k := 4) (by omega_using [hj']) (by omega_using [hfit, hj'])
            (by omega_using [hfit])
        · decide
      · obtain rfl : j = m := by omega_using [hj, hj']
        rw [Mem.readW_writeW_self32, hsrc]

/-! ## The function's entry -/

/-- The arguments of `sig` are those of a state whose argument slots hold the
same words. -/
theorem stackArgs_congr (sig : Sig) {s s₀ : State} (h : ∀ j < slots sig, arg s j = arg s₀ j) :
    stackArgs sig s = stackArgs sig s₀ := by
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

/-- The bytes of the frame of the copies. -/
abbrev cBytes (sig : Sig) : Nat := 4 * slots sig

/-- The state after the frame's allocation and the copies. -/
abbrev cCopied (sig : Sig) (s : State) : State :=
  copiedTo (cBytes sig) (allocState (cBytes sig) s) (slots sig)

/-- The function's entry: the state the call leaves, with the permissions of
its contract. -/
def cEntry (sig : Sig) (wa : Bool) (s : State) : State :=
  (cCopied sig s).callEntry.withRegions
    (((allRegionsL sig wa (cCopied sig s).callEntry).filter (!·.2)).map (·.1))
    (((allRegionsL sig wa (cCopied sig s).callEntry).filter (·.2)).map (·.1))

@[simp] theorem cCopied_esp (sig : Sig) (s : State) :
    (cCopied sig s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (cBytes sig) := by
  rw [copiedTo_esp, allocState_esp]
@[simp] theorem cCopied_rd (sig : Sig) (s : State) : (cCopied sig s).rd = s.rd := by
  rw [copiedTo_rd, allocState_rd]
@[simp] theorem cCopied_wr (sig : Sig) (s : State) :
    (cCopied sig s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 (cBytes sig)).setWidth 64, cBytes sig⟩ :: s.wr := by
  rw [copiedTo_wr, allocState_wr]
@[simp] theorem cCopied_syms (sig : Sig) (s : State) : (cCopied sig s).syms = s.syms := by
  rw [copiedTo_syms]; rfl
@[simp] theorem cCopied_mm (sig : Sig) (s : State) : (cCopied sig s).mm = s.mm := by
  rw [copiedTo_mm]; rfl
@[simp] theorem cCopied_mmx (sig : Sig) (s : State) : (cCopied sig s).mmx = s.mmx := by
  rw [copiedTo_mmx]; rfl
theorem cCopied_gpr (sig : Sig) (s : State) {q : Reg} (h₁ : q ≠ .eax) (h₂ : q ≠ .esp) :
    (cCopied sig s).gpr q = s.gpr q := by
  rw [copiedTo_gpr _ _ h₁, allocState_gpr _ _ h₂]

@[simp] theorem cEntry_esp (sig : Sig) (wa : Bool) (s : State) :
    (cEntry sig wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (cBytes sig) - 4 := by
  rw [cEntry, State.withRegions_gpr, State.callEntry_esp, cCopied_esp]
@[simp] theorem cEntry_mem (sig : Sig) (wa : Bool) (s : State) :
    (cEntry sig wa s).mem = (cCopied sig s).callEntry.mem := rfl
@[simp] theorem cEntry_syms (sig : Sig) (wa : Bool) (s : State) : (cEntry sig wa s).syms = s.syms := by
  rw [cEntry, State.withRegions_syms]; exact cCopied_syms sig s
@[simp] theorem cEntry_mm (sig : Sig) (wa : Bool) (s : State) : (cEntry sig wa s).mm = s.mm :=
  cCopied_mm sig s
@[simp] theorem cEntry_mmx (sig : Sig) (wa : Bool) (s : State) : (cEntry sig wa s).mmx = s.mmx :=
  cCopied_mmx sig s
theorem cEntry_gpr (sig : Sig) (wa : Bool) (s : State) {q : Reg} (h₁ : q ≠ .eax) (h₂ : q ≠ .esp) :
    (cEntry sig wa s).gpr q = s.gpr q := by
  rw [cEntry, State.withRegions_gpr, State.callEntry_gpr _ h₂, cCopied_gpr sig s h₁ h₂]

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What the caller's precondition gives the copies: the run of the block,
the copies' memory, and the arguments the function finds. -/
theorem copies_facts {s : State}
    (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    execBlock isa ((List.range (slots sig)).flatMap (copyTo (cBytes sig))) (allocState (cBytes sig) s) =
        some (cCopied sig s, copyToTrace (cBytes sig) (s.gpr .esp - BitVec.ofNat 32 (cBytes sig)) (slots sig)) ∧
      Frame [below (s.gpr .esp) (cBytes sig + 4)] s.mem (cCopied sig s).callEntry.mem ∧
      (∀ j < slots sig, arg (cCopied sig s).callEntry j = arg s j) ∧
      stack + cBytes sig + 4 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 4 * slots sig ≤ 2 ^ 32 ∧
      Frame [below (s.gpr .esp) (cBytes sig + 4)] s.mem (cCopied sig s).mem := by
  rw [pre_stackL] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, -, -, -⟩ := hs
  have hB : cBytes sig = 4 * slots sig := rfl
  let u := allocState (cBytes sig) s
  have hE : (u.gpr .esp).toNat = (s.gpr .esp).toNat - cBytes sig := by
    simp only [u, allocState_esp]; exact sub_toNat (by omega_using [hst])
  have hesp : u.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (cBytes sig) := allocState_esp _ _
  have hsrc : ∀ j, addr (u.gpr .esp) (cBytes sig + 4 + 4 * j) = argAddr s j := fun j => by
    simp only [u, allocState_esp, addr, argAddr]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [show cBytes sig + 4 + 4 * j = cBytes sig + (4 + 4 * j) by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  have hargs : ∀ j < slots sig, InRegions (u.rd ++ u.wr) (argAddr s j) 4 := fun j hj => by
    have hmem : (⟨argAddr s 0, 4 * slots sig⟩, wa) ∈ allRegionsL sig wa s := by
      simp [allRegionsL, show slots sig ≠ 0 by omega_using [hj]]
    have hc : (⟨argAddr s 0, 4 * slots sig⟩ : Region).Contains (argAddr s j) 4 := by
      show (⟨addr (s.gpr .esp) (4 + 4 * 0), 4 * slots sig⟩ : Region).Contains
        (addr (s.gpr .esp) (4 + 4 * j)) 4
      rw [addr_eq (x := s.gpr .esp) (k := 4 + 4 * 0) (by omega_using [hfit, hj]),
        addr_eq (x := s.gpr .esp) (k := 4 + 4 * j) (by omega_using [hfit, hj])]
      exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by omega_using [hfit])
    cases wa with
    | false =>
      refine ⟨_, List.mem_append_left _ ?_, hc⟩
      simp only [u, allocState_rd, hrd]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
    | true =>
      refine ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), hc⟩
      rw [hwr]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j < slots sig, InRegions u.wr (addr (u.gpr .esp) (4 * j)) 4 := fun j hj => by
    refine ⟨_, List.mem_cons_self .., ?_⟩
    have h₁ : (s.gpr .esp - BitVec.ofNat 32 (cBytes sig)).toNat = (s.gpr .esp).toNat - cBytes sig :=
      sub_toNat (by omega_using [hst])
    rw [hesp, addr_eq (x := s.gpr .esp - BitVec.ofNat 32 (cBytes sig)) (k := 4 * j) (by rw [h₁]; omega_using [hB, hst, hj])]
    exact Offset.contains_base _ (by omega_using [hB, hj]) (by omega_using [hfit, hj])
  have hrun := copiesTo_run (bytes := cBytes sig) (u := u) (slots sig) (fun j hj => by rw [hsrc]; exact hargs j hj) hframe
  obtain ⟨f, hv⟩ := copiedTo_mem (bytes := cBytes sig) (u := u) (slots sig) (by rw [hE]; omega_using [hst, hfit])
    (by omega_using [hB])
  have hc4 : 4 ≤ ((cCopied sig s).gpr .esp).toNat := by
    rw [cCopied_esp, sub_toNat (by omega_using [hst])]; omega_using [hst]
  have f₁ : Frame [below (s.gpr .esp) (cBytes sig + 4)] s.mem (cCopied sig s).mem :=
    f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hesp, below]
      rw [Taint.sub_setWidth (by omega_using [hst]), Taint.sub_setWidth (by omega_using [hst])]
      exact Offset.sub_below _ (by omega_using [hB]) (by omega_using [hB])
  refine ⟨by rw [hrun, hesp], ?_, fun j hj => ?_, by omega_using [hst], hfit, f₁⟩
  · -- The copies and the return address are below `esp`.
    rw [State.callEntry_mem]
    refine f₁.writeW (List.mem_singleton_self _) _ ?_
    rw [cCopied_esp, show s.gpr .esp - BitVec.ofNat 32 (cBytes sig) - 4 = s.gpr .esp - BitVec.ofNat 32 (cBytes sig + 4) by
      rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl]
    exact below_top (Nat.le_refl _) (by omega_using [hst]) (by omega_using [])
  · rw [arg_callEntry hc4 (by rw [cCopied_esp, sub_toNat (by omega_using [hst])]; omega_using [hst, hfit, hj, hB])]
    rw [cCopied_esp, ← hesp]
    exact (hv j hj).trans (by rw [hsrc]; rfl)

/-- The function's arguments are the caller's. -/
theorem c_args {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    stackArgs sig (cCopied sig s).callEntry = stackArgs sig s :=
  stackArgs_congr sig (copies_facts hs).2.2.1

/-- The copies and the return address are in the stack below the caller's
`esp` that its contract reserves, apart from its buffers and lists. -/
theorem c_out {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    ∀ a ∈ bufRegions sig s, ∀ {x k : Nat}, x ≤ stack + cBytes sig + 4 →
      stack + cBytes sig + 4 - x + k ≤ stack + cBytes sig + 4 →
      a.1.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := by
  rw [pre_stackL] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + cBytes sig + 4), stack + cBytes sig + 4⟩ :
      Region) ∈ (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + cBytes sig + 4) :
        List Region) := by
    rw [show stack + cBytes sig + 4 = (stack + cBytes sig + 3) + 1 by omega_using []]; simp [stackBelow]
  intro a ha x k hx hk
  exact (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
    (Offset.sub_below _ hx hk)

/-- The function's memory is the caller's in its buffers and lists. -/
theorem c_agree {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    ∀ a ∈ bufRegions sig s, ∀ x, a.1.Contains x 1 → (cCopied sig s).callEntry.mem x = s.mem x := by
  obtain ⟨-, hf, -, hst, -, -⟩ := copies_facts hs
  have hout := c_out hs
  intro a ha x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have e : below (s.gpr .esp) (cBytes sig + 4) =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig + 4), cBytes sig + 4⟩ := by
    simp only [below]; rw [Taint.sub_setWidth (by omega_using [hst])]
  rw [e] at hc
  exact hout a ha (by omega_using []) (by omega_using []) x hx hc

/-- The function's lists of slices are the caller's. -/
theorem c_lists {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    Sig.lists abi.ptrBits (cCopied sig s).callEntry.mem sig.params (stackArgs sig s) =
      Sig.lists abi.ptrBits s.mem sig.params (stackArgs sig s) :=
  (Sig.lists_eq_of_agree _ fun r hr x hx =>
    (c_agree hs (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm).symm

/-- The function's buffers and lists are the caller's. -/
theorem c_bufRegions {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    bufRegions sig (cCopied sig s).callEntry = bufRegions sig s := by
  rw [bufRegions, bufRegions, c_args hs, c_lists hs]

/-- The function's argument area: the copies, at the bottom of the frame. -/
theorem c_argAddr0 {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    argAddr (cCopied sig s).callEntry 0 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig) := by
  obtain ⟨-, -, -, hst, -, -⟩ := copies_facts hs
  rw [argAddr_callEntry, cCopied_esp, Nat.mul_zero, BitVec.add_zero, Taint.sub_setWidth (by omega_using [hst])]

/-- The function's regions: the caller's buffers and lists, and the copies. -/
theorem c_regions (h0 : 0 < slots sig) {s : State}
    (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    allRegionsL sig wa (cCopied sig s).callEntry =
      bufRegions sig s ++ [(⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig), cBytes sig⟩, wa)] := by
  rw [allRegionsL, c_bufRegions hs, c_argAddr0 hs]
  simp only [show slots sig ≠ 0 by omega_using [h0], ite_false]

theorem cEntry_regions (sig : Sig) (wa : Bool) (s : State) :
    allRegionsL sig wa (cEntry sig wa s) = allRegionsL sig wa (cCopied sig s).callEntry := rfl

/-- **The caller's precondition gives the function's at its entry.** -/
theorem c_bodyPre (h0 : 0 < slots sig)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cEntry sig wa s) := by
  have hout := c_out hs
  have hag := c_agree hs
  have hreg := c_regions h0 hs
  have hargs := c_args hs
  have hlists := c_lists hs
  obtain ⟨-, -, -, hst, -, -⟩ := copies_facts hs
  have hs' := hs
  rw [pre_stackL] at hs'
  obtain ⟨⟨-, hfit⟩, -, -, hpw, -, hnw, hpr⟩ := hs'
  have hB : cBytes sig = 4 * slots sig := rfl
  have hCe : (cEntry sig wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (cBytes sig + 4) := by
    rw [cEntry_esp, BitVec.ofNat_add, BitVec.sub_sub]; rfl
  have hCn : ((cEntry sig wa s).gpr .esp).toNat = (s.gpr .esp).toNat - (cBytes sig + 4) := by
    rw [hCe, sub_toNat (by omega_using [hst])]
  refine pre_stackL.mpr ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hCn]; omega_using [hst]
  · rw [hCn]; omega_using [hst, hfit, hB]
  · rw [cEntry_regions, hreg]
    have hpwB : (bufRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
      List.Pairwise.sublist (List.sublist_append_left _ _) hpw
    refine List.pairwise_append.mpr ⟨hpwB, List.pairwise_singleton _ _, fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    exact hout a ha (by omega_using []) (by omega_using [])
  · intro r hr a ha
    rw [cEntry_regions, hreg] at ha
    have hC : ((cEntry sig wa s).gpr .esp).setWidth 64 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig + 4) := by
      rw [hCe, Taint.sub_setWidth (by omega_using [hst])]
    rw [hC] at hr
    simp only [List.mem_cons, stackBelow_sp'] at hr
    have hr' : r = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig + 4), 4⟩ ∨
        (stack ≠ 0 ∧ r = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig + 4 + stack), stack⟩) := by
      rcases hr with rfl | hr
      · exact .inl rfl
      · by_cases hz : stack = 0
        · simp [hz] at hr
        · simp only [hz, ite_false, List.mem_singleton] at hr; exact .inr ⟨hz, hr⟩
    rcases List.mem_append.mp ha with ha | ha
    · rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega_using []) (by omega_using []))
      · exact Region.Disjoint.symm (hout a ha (by omega_using []) (by omega_using []))
    · simp only [List.mem_singleton] at ha; subst ha
      rcases hr' with rfl | ⟨-, rfl⟩
      · exact below_disjoint _ (stack + cBytes sig + 4) (a := cBytes sig + 4) (n := 4) (b := cBytes sig)
          (k := cBytes sig) (by omega_using []) (by omega_using []) (.inl (by omega_using [])) (by omega_using [hst])
          (by omega_using [hst])
      · exact below_disjoint _ (stack + cBytes sig + 4) (a := cBytes sig + 4 + stack) (n := stack)
          (b := cBytes sig) (k := cBytes sig) (by omega_using []) (by omega_using []) (.inl (by omega_using []))
          (by omega_using [hst]) (by omega_using [hst])
  · intro a ha
    rw [show bufRegions sig (cEntry sig wa s) = bufRegions sig (cCopied sig s).callEntry from rfl,
      c_bufRegions hs] at ha
    exact hnw a ha
  · show Curry.apply (sig.words abi.ptrBits) pre (stackArgs sig (cCopied sig s).callEntry)
      (cCopied sig s).callEntry.mem
    rw [hargs]
    exact hpre _ _ _ (stackArgs_length sig s) (fun b hb x hx => (hag b (List.mem_append_left _ hb) x hx).symm)
      (fun r hr x hx => (hag (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm) hpr

/-- The function's regions are within the caller's and the frame. -/
theorem c_covers (h0 : 0 < slots sig) {s : State}
    (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s) :
    Covers ((((allRegionsL sig wa (cCopied sig s).callEntry).filter (!·.2)).map (·.1)) ++
        (((allRegionsL sig wa (cCopied sig s).callEntry).filter (·.2)).map (·.1)))
        ((cCopied sig s).rd ++ (cCopied sig s).wr) ∧
      Covers (((allRegionsL sig wa (cCopied sig s).callEntry).filter (·.2)).map (·.1)) (cCopied sig s).wr := by
  have hreg := c_regions h0 hs
  obtain ⟨-, -, -, hst, -, -⟩ := copies_facts hs
  have hs' := hs
  rw [pre_stackL] at hs'
  obtain ⟨-, hrd, hwr, -, -, -, -⟩ := hs'
  have hframe : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig), cBytes sig⟩ : Region) ∈
      (cCopied sig s).wr := by
    rw [cCopied_wr, Taint.sub_setWidth (by omega_using [hst])]; exact List.mem_cons_self ..
  have hbuf : ∀ a ∈ bufRegions sig s, (a.2 = false → a.1 ∈ s.rd) ∧ (a.2 = true → a.1 ∈ s.wr) := by
    intro a ha
    have ha' : a ∈ allRegionsL sig wa s := List.mem_append_left _ ha
    refine ⟨fun hf => ?_, fun ht => ?_⟩
    · rw [hrd]; exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha', by simp [hf]⟩, rfl⟩
    · rw [hwr]; exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha', ht⟩, rfl⟩
  rw [hreg]
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr <;> obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr <;>
      obtain ⟨ha, hf⟩ := List.mem_filter.mp ha <;> rcases List.mem_append.mp ha with ha | ha
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hf
      exact List.mem_append_left _ (by rw [cCopied_rd]; exact (hbuf a ha).1 hf)
    · simp only [List.mem_singleton] at ha; subst ha; exact List.mem_append_right _ hframe
    · exact List.mem_append_right _ (by rw [cCopied_wr]; exact List.mem_cons_of_mem _ ((hbuf a ha).2 hf))
    · simp only [List.mem_singleton] at ha; subst ha; exact List.mem_append_right _ hframe
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [cCopied_wr]; exact List.mem_cons_of_mem _ ((hbuf a ha).2 hf)
    · simp only [List.mem_singleton] at ha; subst ha; exact hframe

/-- What the run of `callCopy` leaves, from the caller's state `s`. -/
def AfterC (sig : Sig) (wa : Bool) (stack : Nat) (kc : Contract isa) (s s' : State) : Prop :=
  s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    Frame (s.wr ++ [below (s.gpr .esp) (stack + cBytes sig + 4)]) s.mem s'.mem ∧
    ∃ s₂ : State, (∀ x, ¬ (below (s.gpr .esp) (cBytes sig)).Contains x 1 → s₂.mem x = s'.mem x) ∧
      (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧ kc.post (cEntry sig wa s) s₂

/-- **The run of `callCopy`**, from a caller's state whose precondition holds,
for code verified against a contract `kc` whose precondition holds at its
entry (`hentry`). -/
theorem c_run {name : String} {core : Prog isa} {kc : Contract isa}
    (hv : ∀ s, kc.pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ kc.post s s')
    (hsp : NoSp core) (hd : stackUse core ≤ stack) (h0 : 0 < slots sig) (hB : cBytes sig < 4096)
    {s : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s)
    (hentry : kc.pre (cEntry sig wa s)) :
    WP isa (callCopy (slots sig) name core) s (AfterC sig wa stack kc s) := by
  obtain ⟨hrun, -, -, hst, -, f₁⟩ := copies_facts hs
  obtain ⟨hcov, hcovw⟩ := c_covers h0 hs
  have hreg := c_regions h0 hs
  have hs' := hs
  rw [pre_stackL] at hs'
  obtain ⟨-, hrd, hwr, -, hres, -, -⟩ := hs'
  have hB4 : cBytes sig = 4 * slots sig := rfl
  have hcE : ((cCopied sig s).gpr .esp).toNat = (s.gpr .esp).toNat - cBytes sig := by
    rw [cCopied_esp, sub_toNat (by omega_using [hst, hB4])]
  -- The frame's regions, as regions below `esp`.
  have hsubB : ∀ {k : Nat}, k ≤ stack + cBytes sig + 4 → Region.Sub (below (s.gpr .esp) k)
      (below (s.gpr .esp) (stack + cBytes sig + 4)) := fun hk => below_sub hk (by omega_using [hst, hB4])
  have hsubC : Region.Sub (below ((cCopied sig s).gpr .esp) (stackUse core + 4))
      (below (s.gpr .esp) (stack + cBytes sig + 4)) := by
    rw [cCopied_esp]; exact below_inner (by omega_using [hd, hB4]) (by omega_using [hst, hB4])
  have harea : Region.Sub ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig), cBytes sig⟩
      (below (s.gpr .esp) (stack + cBytes sig + 4)) := by
    have e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig), cBytes sig⟩ : Region) =
        below (s.gpr .esp) (cBytes sig) := by
      simp only [below]; rw [Taint.sub_setWidth (by omega_using [hst, hB4])]
    rw [e]; exact hsubB (by omega_using [hB4])
  have hwrL : ∀ r ∈ ((allRegionsL sig wa (cCopied sig s).callEntry).filter (·.2)).map (·.1),
      r ∈ s.wr ∨ Region.Sub r (below (s.gpr .esp) (stack + cBytes sig + 4)) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
    rw [hreg] at ha
    rcases List.mem_append.mp ha with ha | ha
    · refine .inl ?_
      rw [hwr]; exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, hf⟩, rfl⟩
    · simp only [List.mem_singleton] at ha; subst ha; exact .inr harea
  unfold callCopy
  refine WP.frameAlloc (by omega_using [h0, hB4]) hB (by omega_using [hB4]) (by omega_using [hst, hB4])
    (fun i hi => ?_) ?_
  · simp only [instrs, List.mem_append, List.mem_flatMap, List.mem_range] at hi
    rcases hi with ⟨j, -, hj⟩ | hi
    · simp only [copyTo, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
    · exact hsp i hi
  refine WP.seq ⟨_, _, Exec.block hrun, ?_⟩
  refine WP.call hv hsp (by rw [hcE]; omega_using [hst, hd, hB4]) hentry hcov hcovw ?_
  intro s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, hg₂, hpost₂⟩ m u hfm
  refine ⟨by show s'.rd = s.rd; rw [hrd', cCopied_rd], by show s'.wr.tail = s.wr; rw [hwr', cCopied_wr]; rfl,
    fun r hr => ?_, ?_, ⟨s₂, ?_, ?_, hpost₂⟩⟩
  · by_cases he : r = .esp
    · subst he
      show (freed (cBytes sig) s').gpr .esp = _
      rw [freed_esp, hcs .esp hr, cCopied_esp, BitVec.sub_add_cancel]
    · show (freed (cBytes sig) s').gpr r = _
      rw [freed_gpr _ _ he, hcs r hr, cCopied_gpr sig s (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) he]
  · intro x hx
    have hnot : ∀ R, Region.Sub R (below (s.gpr .esp) (stack + cBytes sig + 4)) → ¬ R.Contains x 1 :=
      fun R hR hc => hx _ (List.mem_append_right _ (List.mem_singleton_self _)) (hR x hc)
    show m x = s.mem x
    rw [hfm x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnot _ (hsubB (by omega_using [hB4])))]
    rw [hfr x (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rcases hwrL r hr with hr | hr
        · exact hx r (List.mem_append_left _ hr)
        · exact hnot r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact hnot _ hsubC)]
    exact f₁ x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnot _ (hsubB (by omega_using [hB4])))
  · intro x hx
    show s₂.mem x = m x
    rw [hm₂, hfm x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx)]
  · intro r hr
    show s₂.gpr r = (freed (cBytes sig) s').gpr r
    rw [freed_gpr _ _ hr, hg₂ r hr]

/-- **What a run of `callCopy` leaks**: the copies' addresses, the call's and
the return's, which are functions of `esp`, and what the function's run from
its entry, with its contract's permissions, leaks. -/
theorem c_trace {name : String} {core : Prog isa} {kc : Contract isa}
    (hv : ∀ s, kc.pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ kc.post s s')
    (h0 : 0 < slots sig) {s s' : State} {t : List Leak}
    (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s)
    (hentry : kc.pre (cEntry sig wa s)) (e : Exec isa (callCopy (slots sig) name core) s t s') :
    ∃ tc sν, Exec isa core (cEntry sig wa s) tc sν ∧
      t = copyToTrace (cBytes sig) (s.gpr .esp - BitVec.ofNat 32 (cBytes sig)) (slots sig) ++
        ([.addr (((cCopied sig s).gpr .esp - 4).setWidth 64)] ++ tc ++
          [.addr (((cCopied sig s).gpr .esp - 4).setWidth 64)]) := by
  obtain ⟨hrun, -, -, -, -, -⟩ := copies_facts hs
  obtain ⟨hcov, hcovw⟩ := c_covers h0 hs
  obtain ⟨tν, sν, eν, habi, -⟩ := hv _ hentry
  -- The function's run from the call, widened to the caller's permissions.
  have ew := Exec.widen eν (rd := (cCopied sig s).rd) (wr := (cCopied sig s).wr)
    (by simpa [cEntry] using hcov) (by simpa [cEntry] using hcovw)
  rw [cEntry, State.withRegions_withRegions,
    show (cCopied sig s).callEntry.withRegions (cCopied sig s).rd (cCopied sig s).wr = (cCopied sig s).callEntry
      from rfl] at ew
  unfold callCopy at e
  cases e with
  | frame hp eb hq =>
    rw [alloc_some hp] at eb
    cases eb with
    | seq eblk ecall =>
      cases eblk with
      | block hb =>
        rw [show allocFrame (cBytes sig) s = allocState (cBytes sig) s from rfl, hrun, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        cases ecall with
        | call hc ec hr =>
          rw [call_callEntry, Option.some.injEq] at hc
          subst hc
          obtain ⟨rfl, rfl⟩ := Exec.det ec ew
          have hsp : (sν.withRegions (cCopied sig s).rd (cCopied sig s).wr).gpr .esp =
              (cCopied sig s).gpr .esp - 4 := by
            rw [State.withRegions_gpr, habi.1 .esp (by simp [calleeSaved])]
            show (cCopied sig s).callEntry.gpr .esp = _
            rw [State.callEntry_esp]
          refine ⟨_, _, eν, ?_⟩
          simp only [addrs, List.map_nil, List.nil_append, List.append_nil, List.map_cons, hsp]

/-- The caller's public data is the function's at its entry. -/
theorem c_pub {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cEntry sig wa s₁) (cEntry sig wa s₂) := by
  rw [pubL_stackL] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa, hdesc⟩ := hp
  have hag₁ := c_agree h₁
  have hag₂ := c_agree h₂
  have ha₁ : stackArgs sig (cEntry sig wa s₁) = stackArgs sig s₁ := c_args h₁
  have ha₂ : stackArgs sig (cEntry sig wa s₂) = stackArgs sig s₂ := c_args h₂
  have hm₁ : (cEntry sig wa s₁).mem = (cCopied sig s₁).callEntry.mem := rfl
  have hm₂ : (cEntry sig wa s₂).mem = (cCopied sig s₂).callEntry.mem := rfl
  refine pubL_stackL.mpr ⟨⟨by rw [cEntry_esp, cEntry_esp, hsp], ?_⟩, ?_, ?_⟩
  · rw [ha₁, ha₂, hm₁, hm₂]
    cases leak with
    | none => trivial
    | some f =>
      show Curry.apply _ f (stackArgs sig s₁) (cCopied sig s₁).callEntry.mem =
        Curry.apply _ f (stackArgs sig s₂) (cCopied sig s₂).callEntry.mem
      have hl := stackArgs_length sig s₁
      have hl₂ := stackArgs_length sig s₂
      rw [← hleak _ _ _ hl (fun b hb x hx => (hag₁ b (List.mem_append_left _ hb) x hx).symm)
          (fun r hr x hx => (hag₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm),
        ← hleak _ _ _ hl₂ (fun b hb x hx => (hag₂ b (List.mem_append_left _ hb) x hx).symm)
          (fun r hr x hx => (hag₂ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm)]
      exact hlk
  · rw [ha₁, ha₂]; exact hpa
  · rw [ha₁, hm₁, hm₂]
    intro r hr i hi
    have hx : r.Contains (r.base + BitVec.ofNat 64 i) 1 := Region.contains_ofNat r.base hi
    have hr₁ : r ∈ Sig.lists abi.ptrBits s₁.mem sig.params (stackArgs sig s₁) := Sig.descs_sub_lists _ _ _ _ r hr
    rw [hag₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr₁, rfl⟩)) _ hx, hdesc r hr i hi]
    obtain ⟨-, f₂, -, -, -, -⟩ := copies_facts h₂
    obtain ⟨-, -, -, hst₁, -, -⟩ := copies_facts h₁
    refine (f₂ _ fun q hq hc => ?_).symm
    simp only [List.mem_singleton] at hq; subst hq
    rw [← hsp] at hc
    have e : below (s₁.gpr .esp) (cBytes sig + 4) =
        ⟨(s₁.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig + 4), cBytes sig + 4⟩ := by
      simp only [below]; rw [Taint.sub_setWidth (by omega_using [hst₁])]
    rw [e] at hc
    exact c_out h₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr₁, rfl⟩))
      (by omega_using []) (by omega_using []) _ hx hc

/-- **What the run of `callCopy` leaves meets the caller's contract**, from
the function's postcondition, if the postcondition reads memory only within
the buffers (`hpost`), and the memory on return only within them where the
precondition holds (`hpostOut`). -/
theorem c_post {kc : Contract isa}
    (hkc : ∀ x y, kc.post x y → (sig.contract abi pre post wa stack leak).post x y)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    {s s' : State} (hs : (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s)
    (hA : AfterC sig wa stack kc s s') :
    abiPreserved s s' ∧ (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).post s s' := by
  obtain ⟨-, -, hcs, hfr, s₂, hm₂, hg₂, hpost₂⟩ := hA
  have hag := c_agree hs
  have hout := c_out hs
  have hargs : stackArgs sig (cEntry sig wa s) = stackArgs sig s := c_args hs
  obtain ⟨-, -, -, hst, -, -⟩ := copies_facts hs
  have hs' := hs
  rw [pre_stackL] at hs'
  obtain ⟨-, -, hwr, -, hres, -, hpr⟩ := hs'
  have hp := post_stack.mp (hkc _ _ hpost₂)
  rw [hargs] at hp
  have hl := stackArgs_length sig s
  refine ⟨⟨hcs, ?_⟩, post_stack.mpr ?_⟩
  · refine hfr.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rw [hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hres _ (List.mem_cons_self ..) a (List.mem_filter.mp ha).1
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [below]; rw [Taint.sub_setWidth (by omega_using [hst])]
      exact Offset.base_disjoint_below _ (by omega_using [hst])
  · rw [show s'.gpr .edx = s₂.gpr .edx from (hg₂ .edx (by decide)).symm,
      show s'.gpr .eax = s₂.gpr .eax from (hg₂ .eax (by decide)).symm]
    have h1 := hpost _ _ _ _ _ hl (fun b hb x hx => hag b (List.mem_append_left _ hb) x hx) hp
    refine hpostOut _ _ _ _ _ hl hpr (fun b hb x hx => ?_) h1
    refine hm₂ x fun hc => ?_
    have e : below (s.gpr .esp) (cBytes sig) =
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (cBytes sig), cBytes sig⟩ := by
      simp only [below]; rw [Taint.sub_setWidth (by omega_using [hst])]
    rw [e] at hc
    exact hout b (List.mem_append_left _ hb) (by omega_using []) (by omega_using []) x hx hc

/-- **A function called with its stack arguments copied**: code verified
against `kc` is verified against `k` called by `callCopy`, if `k`'s
precondition is a contract's with `cBytes sig + 4` more bytes of stack
(`hk`), and gives `kc`'s at the function's entry (`hentry`), its public data
`kc`'s there (`hpub`), and its postcondition follows from what the run
leaves (`hpostK`). -/
theorem Verified.callCopyG {name : String} {core : Prog isa} {kc k : Contract isa}
    (h : Verified target core kc) (h0 : 0 < slots sig) (hB : cBytes sig < 4096) (hsp : NoSp core)
    (hd : stackUse core ≤ stack)
    (hk : ∀ s, k.pre s → (sig.contract abi pre post wa (stack + cBytes sig + 4) leak).pre s)
    (hentry : ∀ s, k.pre s → kc.pre (cEntry sig wa s))
    (hpub : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ →
      kc.pub (cEntry sig wa s₁) (cEntry sig wa s₂) ∧ s₁.gpr .esp = s₂.gpr .esp)
    (hpostK : ∀ s s', k.pre s → AfterC sig wa stack kc s s' → abiPreserved s s' ∧ k.post s s')
    (hsat : ∃ s, k.pre s) :
    Verified target (callCopy (slots sig) name core) k := by
  obtain ⟨hok, hct, -⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', e, hA⟩ := c_run hok hsp hd h0 hB (hk s hs) (hentry s hs)
    exact ⟨t, s', e, hpostK s s' hs hA⟩
  · obtain ⟨tc₁, _, eν₁, rfl⟩ := c_trace hok h0 (hk _ h₁) (hentry _ h₁) e₁
    obtain ⟨tc₂, _, eν₂, rfl⟩ := c_trace hok h0 (hk _ h₂) (hentry _ h₂) e₂
    obtain ⟨hpc, hsp⟩ := hpub _ _ h₁ h₂ hp
    rw [hct _ _ _ _ _ _ (hentry _ h₁) (hentry _ h₂) hpc eν₁ eν₂, cCopied_esp, cCopied_esp, hsp]

end

end VG.X86
