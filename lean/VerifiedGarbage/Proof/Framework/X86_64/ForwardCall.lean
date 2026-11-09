module

public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Impl.ForwardCall.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A call that forwards a function's stack arguments (x86-64)

`Verified.forward`: a function verified against `sig.contract` with `stack`
bytes of stack, whose arguments fill the six argument registers and
`nStack sig` more on the stack, is verified against the same contract with
`stack + bytes + 8` bytes when called by `forward`, which copies the stack
arguments to the bottom of a frame of `bytes` bytes and calls it: the callee,
entered 8 bytes below the frame, finds its stack arguments there, and the
argument registers as they are. The callee runs from the state after the
call with the permissions of its own contract (`narrowF`), which are the
caller's buffers and lists of slices and the copies, read only.

The copies and the return address are memory the callee's contract reads on
entry, which the caller's says nothing of: the precondition, postcondition
and leak must read memory only within the function's buffers and its lists
of slices (`hpre`, `hpost`, `hleak`), which the frame lies outside of.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64 VG.Impl.ForwardCall.X86_64

/-! ## Copying the stack arguments down -/

/-- The state after `copyDown bytes j` from `u`. -/
def copyDState (bytes j : Nat) (u : State) : State :=
  { u.setReg .rax (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) with
    mem := u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 * j))
      (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) }

theorem copyDown_run {bytes j : Nat} {u : State}
    (hr : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8)
    (hw : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 8) :
    execBlock isa (copyDown bytes j) u = some (copyDState bytes j u,
      [.addr (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)),
        .addr (u.gpr .rsp + BitVec.ofNat 64 (8 * j))]) := by
  simp only [copyDown, execBlock, isa, exec, readSrc, State.load64, State.ea, ofInt_natCast, hr,
    ite_true, Option.map_some, addrs, srcAddrs]
  simp [copyDState, State.setReg, State.store64, hw]

@[simp] theorem copyDState_rsp (bytes j : Nat) (u : State) :
    (copyDState bytes j u).gpr .rsp = u.gpr .rsp := by
  simp [copyDState, State.setReg]
@[simp] theorem copyDState_rd (bytes j : Nat) (u : State) : (copyDState bytes j u).rd = u.rd := rfl
@[simp] theorem copyDState_wr (bytes j : Nat) (u : State) : (copyDState bytes j u).wr = u.wr := rfl
@[simp] theorem copyDState_mxcsr (bytes j : Nat) (u : State) :
    (copyDState bytes j u).mxcsr = u.mxcsr := rfl
@[simp] theorem copyDState_unknowns (bytes j : Nat) (u : State) :
    (copyDState bytes j u).unknowns = u.unknowns := rfl
theorem copyDState_gpr (bytes j : Nat) (u : State) {q : Reg} (h : q ≠ .rax) :
    (copyDState bytes j u).gpr q = u.gpr q := by
  simp [copyDState, State.setReg, h]

/-- The state after copying the first `m` stack arguments down from `u`. -/
def copiedD (bytes : Nat) (u : State) : Nat → State
  | 0 => u
  | m + 1 => copyDState bytes m (copiedD bytes u m)

@[simp] theorem copiedD_rsp (bytes : Nat) (u : State) :
    ∀ m, (copiedD bytes u m).gpr .rsp = u.gpr .rsp
  | 0 => rfl
  | m + 1 => by rw [copiedD, copyDState_rsp, copiedD_rsp bytes u m]
@[simp] theorem copiedD_rd (bytes : Nat) (u : State) : ∀ m, (copiedD bytes u m).rd = u.rd
  | 0 => rfl
  | m + 1 => by rw [copiedD, copyDState_rd, copiedD_rd bytes u m]
@[simp] theorem copiedD_wr (bytes : Nat) (u : State) : ∀ m, (copiedD bytes u m).wr = u.wr
  | 0 => rfl
  | m + 1 => by rw [copiedD, copyDState_wr, copiedD_wr bytes u m]
@[simp] theorem copiedD_mxcsr (bytes : Nat) (u : State) :
    ∀ m, (copiedD bytes u m).mxcsr = u.mxcsr
  | 0 => rfl
  | m + 1 => by rw [copiedD, copyDState_mxcsr, copiedD_mxcsr bytes u m]
@[simp] theorem copiedD_unknowns (bytes : Nat) (u : State) :
    ∀ m, (copiedD bytes u m).unknowns = u.unknowns
  | 0 => rfl
  | m + 1 => by rw [copiedD, copyDState_unknowns, copiedD_unknowns bytes u m]
theorem copiedD_gpr (bytes : Nat) (u : State) {q : Reg} (h : q ≠ .rax) :
    ∀ m, (copiedD bytes u m).gpr q = u.gpr q
  | 0 => rfl
  | m + 1 => by rw [copiedD, copyDState_gpr _ _ _ h, copiedD_gpr bytes u h m]

/-- The addresses copying the first `m` stack arguments down accesses. -/
def copyDTrace (bytes : Nat) (sp : Addr) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j =>
    [.addr (sp + BitVec.ofNat 64 (bytes + 8 + 8 * j)), .addr (sp + BitVec.ofNat 64 (8 * j))]

theorem copiesD_run {bytes : Nat} {u : State} :
    ∀ m, (∀ j < m, InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8) →
      (∀ j < m, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 8) →
      execBlock isa (copies bytes m) u = some (copiedD bytes u m, copyDTrace bytes (u.gpr .rsp) m)
  | 0, _, _ => rfl
  | m + 1, hr, hw => by
    rw [copies, List.range_succ, List.flatMap_append, execBlock_append, ← copies,
      copiesD_run m (fun j hj => hr j (by omega_using [hj])) (fun j hj => hw j (by omega_using [hj]))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [copyDown_run (by simpa using hr m (by omega_using [])) (by simpa using hw m (by omega_using []))]
    simp only [Option.map_some, copiedD, copiedD_rsp, copyDTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` stack arguments down writes only within the `m`
destination quadwords (from `rsp`), which then hold the sources (from
`rsp + bytes + 8`). -/
theorem copiedD_mem {bytes : Nat} {u : State} :
    ∀ m, bytes + 8 + 8 * m ≤ 2 ^ 64 → 8 * m ≤ bytes →
      Frame [⟨u.gpr .rsp, 8 * m⟩] u.mem (copiedD bytes u m).mem ∧
      ∀ j < m, (copiedD bytes u m).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 64 =
        u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedD_mem (bytes := bytes) (u := u) m (by omega_using [hfit]) (by omega_using [hb])
    have hR : Region.Sub ⟨u.gpr .rsp, 8 * m⟩ ⟨u.gpr .rsp, 8 * (m + 1)⟩ :=
      Region.sub_prefix (by omega_using [])
    have f' : Frame [⟨u.gpr .rsp, 8 * (m + 1)⟩] u.mem (copiedD bytes u m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    -- The source of argument `m` is above the first `m` destinations.
    have hsrc : (copiedD bytes u m).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m)) 64 =
        u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m)) 64 := by
      refine f.readW (r := ⟨u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m), 8⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (d := bytes + 8 + 8 * m) (n := 8) (k := 8 * m) (by omega_using [hb])
        (by omega_using [hfit])
    refine ⟨?_, fun j hj => ?_⟩
    · show Frame _ u.mem ((copiedD bytes u m).mem.writeW _ _)
      rw [copiedD_rsp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      exact Offset.contains_base _ (d := 8 * m) (n := 8) (k := 8 * (m + 1)) (by omega_using [])
        (by omega_using [hfit])
    · show ((copiedD bytes u m).mem.writeW
          ((copiedD bytes u m).gpr .rsp + BitVec.ofNat 64 (8 * m))
          ((copiedD bytes u m).mem.readW
            ((copiedD bytes u m).gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * m)) 64)).readW _ 64 = _
      rw [copiedD_rsp]
      rcases Nat.lt_or_ge j m with hj' | hj'
      · rw [Mem.readW_writeW_sep, hv j hj']
        · exact Offset.sep _ (d := 8 * j) (n := 8) (e := 8 * m) (k := 8) (by omega_using [hj'])
            (by omega_using [hfit, hj']) (by omega_using [hfit])
        · decide
      · obtain rfl : j = m := by omega_using [hj, hj']
        rw [Mem.readW_writeW_self64, hsrc]

/-! ## The callee's entry -/

/-- `F - 8 + 8 (j + 1)` is `F + 8 j`. -/
theorem sub8_add_succ (F : Addr) (j : Nat) :
    F - 8 + BitVec.ofNat 64 (8 * (j + 1)) = F + BitVec.ofNat 64 (8 * j) := by
  rw [show 8 * (j + 1) = 8 + 8 * j by omega_using [], BitVec.ofNat_add,
    show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The state after the frame's push and the copies. -/
def fwdState (sig : Sig) (bytes : Nat) (s : State) : State :=
  copiedD bytes (allocState bytes s) (nStack sig)

/-- The regions of the callee's contract: the buffers and the lists of
slices, and the copies of the stack arguments, read only. -/
def fwdRegions (sig : Sig) (bytes : Nat) (s : State) : List (Region × Bool) :=
  bufRegions sig s ++ [(⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩, false)]

/-- The state the callee runs from, with the permissions of its contract. -/
def narrowF (sig : Sig) (bytes : Nat) (s : State) : State :=
  (fwdState sig bytes s).callEntry.withRegions
    (((fwdRegions sig bytes s).filter (!·.2)).map (·.1))
    (((fwdRegions sig bytes s).filter (·.2)).map (·.1))

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What the copies give, from a state satisfying the caller's contract. -/
theorem fwdState_run {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s)
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096) :
    let u := allocState bytes s
    execBlock isa (copies bytes (nStack sig)) u =
        some (fwdState sig bytes s, copyDTrace bytes (u.gpr .rsp) (nStack sig)) ∧
      (fwdState sig bytes s).rd = u.rd ∧ (fwdState sig bytes s).wr = u.wr ∧
      (fwdState sig bytes s).mxcsr = s.mxcsr ∧ (fwdState sig bytes s).unknowns = s.unknowns ∧
      (∀ q, q ≠ .rax → (fwdState sig bytes s).gpr q = u.gpr q) ∧
      Frame [⟨u.gpr .rsp, 8 * nStack sig⟩] s.mem (fwdState sig bytes s).mem ∧
      (∀ j < nStack sig, (fwdState sig bytes s).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 64 =
        stackArg s j) := by
  intro u
  rw [pre_args hk] at hs
  obtain ⟨⟨hst, -⟩, hrd, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega_using [h]
  have hesp : u.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := allocState_rsp' _ _
  have hsrc : ∀ j, u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j) = stackArgAddr s j := fun j => by
    rw [hesp, stackArgAddr, show bytes + 8 + 8 * j = bytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  -- The caller's stack arguments hold the sources.
  have hargs : ∀ j < nStack sig, InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := fun j hj => by
    have h0 : ¬ (sig.words abi.ptrBits).length - 6 = 0 := by simp only [nStack] at hj; omega_using [hj]
    have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, h0]
    have hc : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region).Contains (stackArgAddr s j) 8 := by
      simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8 * (0 + 1)) (k := 8 * nStack sig)
        (by omega_using []) (by omega_using [hj]) (by omega_using [hb, hsb])
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    show _ ∈ s.rd
    rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j < nStack sig, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 8 :=
    fun j hj => ⟨_, List.mem_cons_self .., by
      rw [hesp]; exact Offset.contains_base _ (by omega_using [hb, hj]) (by omega_using [hb, hsb, hj])⟩
  have hrun := copiesD_run (bytes := bytes) (u := u) (nStack sig) (fun j hj => by rw [hsrc]; exact hargs j hj)
    hframe
  obtain ⟨hf, hv⟩ := copiedD_mem (bytes := bytes) (u := u) (nStack sig) (by omega_using [hb, hb1])
    (by omega_using [hb])
  refine ⟨hrun, copiedD_rd .., copiedD_wr .., copiedD_mxcsr .., copiedD_unknowns .., fun q hq =>
    copiedD_gpr _ _ hq _, hf, fun j hj => ?_⟩
  rw [fwdState, hv j hj, hsrc]
  rfl

/-- What `narrowF` keeps of `s`, and what it holds. -/
theorem narrowF_facts (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    (narrowF sig bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 ∧
      (∀ q, q ≠ .rax → q ≠ .rsp → (narrowF sig bytes s).gpr q = s.gpr q) ∧
      (narrowF sig bytes s).mxcsr = s.mxcsr ∧
      allArgs sig (narrowF sig bytes s) = allArgs sig s ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, 8 * nStack sig + 8⟩]
        s.mem (narrowF sig bytes s).mem := by
  obtain ⟨-, -, -, hmx, -, hg, hf, hv⟩ := fwdState_run hs hk hb hb1
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by
    rw [pre_args hk] at hs; rcases hs.1.1 with h | h <;> omega_using [h]
  have hrsp : (fwdState sig bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (hg .rsp (by decide)).trans (allocState_rsp' _ _)
  have hg' : ∀ q, q ≠ .rax → q ≠ .rsp → (narrowF sig bytes s).gpr q = s.gpr q := fun q h₁ h₂ => by
    rw [narrowF, State.withRegions_gpr, State.callEntry_gpr _ h₂, hg q h₁, allocState_gpr' _ _ h₂]
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  -- The return address lies below the copies.
  have hsepR : ∀ j < nStack sig, Mem.Sep (s.gpr .rsp - BitVec.ofNat 64 bytes - 8) 8
      (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
    have := Offset.sep_base (s.gpr .rsp - BitVec.ofNat 64 bytes - 8) (n := 8) (e := 8 + 8 * j) (k := 8)
      (by omega_using []) (by omega_using [hj, hb, hb1])
    rwa [BitVec.ofNat_add, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, ← BitVec.add_assoc,
      BitVec.sub_add_cancel] at this
  refine ⟨by rw [narrowF, State.withRegions_gpr, State.callEntry_rsp, hrsp], hg',
    by rw [narrowF, State.withRegions]; exact hmx, ?_, ?_⟩
  · rw [allArgs, allArgs, argRegs_map_congr hg']
    refine congrArg _ (List.map_congr_left fun j hj => ?_)
    have hj' : j < nStack sig := by simpa using hj
    show (narrowF sig bytes s).mem.readW
      ((narrowF sig bytes s).gpr .rsp + BitVec.ofNat 64 (8 * (j + 1))) 64 = _
    rw [narrowF, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_mem,
      hrsp, sub8_add_succ, Mem.readW_writeW_sep (fun x h₁ h₂ => hsepR j hj' x h₂ h₁) (by decide), ← allocState_rsp',
      hv j hj']
  · rw [narrowF, State.withRegions_mem, State.callEntry_mem, hrsp]
    refine Frame.writeW (Frame.sub hf fun r hr => ?_) (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [allocState_rsp', hF]
      exact Offset.sub_below _ (a := bytes) (b := bytes + 8) (by omega_using []) (by omega_using [])
    · exact Offset.contains_base _ (d := 0) (n := 8) (k := 8 * nStack sig + 8) (by omega_using [])
        (by omega_using []) |> fun h => by simpa using h

/-- The buffers and the lists of slices lie apart from the caller's stack
below `rsp`, which its contract reserves. -/
theorem fwd_out (hk : 6 ≤ (sig.words abi.ptrBits).length) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ a ∈ bufRegions sig s, ∀ {x k : Nat}, x ≤ stack + bytes + 8 →
      stack + bytes + 8 - x + k ≤ stack + bytes + 8 →
      a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := by
  rw [pre_args hk] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hbelow : below (s.gpr .rsp) (stack + bytes + 8) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes + 8) : List Region) := by
    rw [stackBelow_pos _ (by omega_using [])]; simp
  intro a ha _ _ hx hk'
  exact (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
    (Offset.sub_below _ hx hk')

/-- The buffers and the lists of slices lie outside what the forwarding
writes: `narrowF`'s memory is `s`'s there. -/
theorem narrowF_agreeL (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ b ∈ bufRegions sig s, ∀ x, b.1.Contains x 1 → (narrowF sig bytes s).mem x = s.mem x := by
  obtain ⟨-, -, -, -, hf⟩ := narrowF_facts hk hb hb1 hs
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  intro b hb' x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  rw [hF] at hc
  exact fwd_out hk hs b hb' (x := bytes + 8) (k := 8 * nStack sig + 8) (by omega_using [])
    (by omega_using [hb]) x hx hc

theorem narrowF_agree (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ x, b.1.Contains x 1 →
      (narrowF sig bytes s).mem x = s.mem x :=
  fun b hb' => narrowF_agreeL hk hb hb1 hs b (List.mem_append_left _ hb')

theorem narrowF_agreeLists (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ r ∈ Sig.lists 64 s.mem sig.params (allArgs sig s), ∀ x, r.Contains x 1 →
      (narrowF sig bytes s).mem x = s.mem x :=
  fun r hr => narrowF_agreeL hk hb hb1 hs (r, false)
    (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))

theorem narrowF_lists (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    Sig.lists 64 (narrowF sig bytes s).mem sig.params (allArgs sig s) =
      Sig.lists 64 s.mem sig.params (allArgs sig s) :=
  (Sig.lists_eq_of_agree 64 fun r hr x hx => (narrowF_agreeLists hk hb hb1 hs r hr x hx).symm).symm

theorem bufRegions_narrowF (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    bufRegions sig (narrowF sig bytes s) = bufRegions sig s := by
  obtain ⟨-, -, -, hargs, -⟩ := narrowF_facts hk hb hb1 hs
  rw [bufRegions, bufRegions, hargs]
  exact congrArg (_ ++ ·) (congrArg _ (narrowF_lists hk hb hb1 hs))

/-- The regions of the callee's contract, in `narrowF`, are `fwdRegions`. -/
theorem allRegions_narrowF (hk : 6 ≤ (sig.words abi.ptrBits).length) (hm : 0 < nStack sig)
    (hb : 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    allRegions sig (narrowF sig bytes s) = fwdRegions sig bytes s := by
  obtain ⟨hrsp, -, -, -, -⟩ := narrowF_facts hk hb hb1 hs
  have h0 : (sig.words abi.ptrBits).length - 6 ≠ 0 := by simp only [nStack] at hm; omega_using [hm]
  rw [allRegions, bufRegions_narrowF hk hb hb1 hs, argArea, ite_eq_right_of_eq_false _ _ (eq_false h0)]
  simp only [fwdRegions, stackArgAddr, hrsp]
  rw [sub8_add_succ]
  simp

/-- The caller's precondition gives the callee's in `narrowF`, if the
precondition reads memory only within the buffers and the lists of slices. -/
theorem narrowF_pre (hk : 6 ≤ (sig.words abi.ptrBits).length) (hm : 0 < nStack sig)
    (hb : 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (narrowF sig bytes s) := by
  obtain ⟨hrsp, -, -, hargs, -⟩ := narrowF_facts hk hb hb1 hs
  have hall := allRegions_narrowF hk hm hb hb1 hs
  have hbuf := bufRegions_narrowF hk hb hb1 hs
  have hagB := narrowF_agree hk hb hb1 hs
  have hagL := narrowF_agreeLists hk hb hb1 hs
  have hout := fwd_out hk hs
  rw [pre_args hk] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, -, hnw, hpr⟩ := hs
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega_using [h]
  have hlen := allArgs_length sig s hk
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  have hpwB : (bufRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
    List.Pairwise.sublist (List.sublist_append_left _ _) hpw
  have hareaD : ∀ a ∈ bufRegions sig s, a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩ :=
    fun a ha => hout a ha (by omega_using []) (by omega_using [hb])
  refine (pre_args hk).mpr ?_
  rw [hall, hbuf, hrsp, hargs, hF]
  refine ⟨⟨.inr ?_, .inr ?_⟩, rfl, rfl, ?_, ?_, hnw, ?_⟩
  · rw [toNat_sub_ofNat (by omega_using [hsb])]; omega_using [hsb]
  · have hn : nStack sig = (sig.words abi.ptrBits).length - 6 := rfl
    rw [toNat_sub_ofNat (by omega_using [hsb])]; omega_using [hb, hsb, hn]
  · -- Pairwise disjoint.
    simp only [fwdRegions, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
    exact ⟨hpwB, trivial, fun a ha b hb' _ => by subst hb'; exact hareaD a ha⟩
  · -- The reserved stack: the return address and the stack below it.
    intro r hr a ha
    have hr' : r = ⟨s.gpr .rsp - BitVec.ofNat 64 (bytes + 8), 8⟩ ∨
        (0 < stack ∧ r = below (s.gpr .rsp - BitVec.ofNat 64 (bytes + 8)) stack) := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl rfl
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hr
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    simp only [fwdRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega_using []) (by omega_using []))
      · refine (Region.Disjoint.symm (hout a ha (x := stack + bytes + 8) (k := stack + bytes + 8)
          (by omega_using []) (by omega_using []))).sub_left ?_
        have := below_below (s.gpr .rsp) (bytes + 8) stack
        rwa [show stack + (bytes + 8) = stack + bytes + 8 by omega_using []] at this
    · have hA : s.gpr .rsp - BitVec.ofNat 64 bytes =
          s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) + BitVec.ofNat 64 8 := by
        rw [← hF, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, BitVec.sub_add_cancel]
      rcases hr' with rfl | ⟨h0, rfl⟩
      · show Region.Disjoint ⟨_, 8⟩ ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩
        rw [hA]
        exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega_using [hb, hb1])
      · show Region.Disjoint (below _ stack) ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩
        rw [hA]
        exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8)
          (k := 8 * nStack sig) (by omega_using [hb, hb1, hsb]))
  · -- The precondition, which reads only the buffers and the lists.
    exact hpre _ _ _ hlen (fun b hb' x hx => (hagB b hb' x hx).symm)
      (fun r hr x hx => (hagL r hr x hx).symm) hpr

/-- The caller's public data is the callee's, in `narrowF`. -/
theorem narrowF_pub (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * nStack sig ≤ bytes)
    (hb1 : bytes < 4096) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes + 8) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    (sig.contract abi pre post wa stack leak).pub (narrowF sig bytes s₁) (narrowF sig bytes s₂) := by
  rw [pubL_args hk] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa, hdesc⟩ := hp
  obtain ⟨e₁, -, -, a₁, -⟩ := narrowF_facts hk hb hb1 h₁
  obtain ⟨e₂, -, -, a₂, f₂⟩ := narrowF_facts hk hb hb1 h₂
  have l₁ := allArgs_length sig s₁ hk
  refine (pubL_args hk).mpr ?_
  rw [e₁, e₂, a₁, a₂, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa, fun r hr i hi => ?_⟩
  · cases leak with
    | none => trivial
    | some f =>
      have hL₁ : ∀ r ∈ Sig.lists abi.ptrBits (narrowF sig bytes s₁).mem sig.params (allArgs sig s₁),
          ∀ x, r.Contains x 1 → (narrowF sig bytes s₁).mem x = s₁.mem x := fun r hr =>
        narrowF_agreeLists hk hb hb1 h₁ r ((narrowF_lists hk hb hb1 h₁) ▸ hr)
      have hL₂ : ∀ r ∈ Sig.lists abi.ptrBits (narrowF sig bytes s₂).mem sig.params (allArgs sig s₂),
          ∀ x, r.Contains x 1 → (narrowF sig bytes s₂).mem x = s₂.mem x := fun r hr =>
        narrowF_agreeLists hk hb hb1 h₂ r ((narrowF_lists hk hb hb1 h₂) ▸ hr)
      show Curry.apply _ f (allArgs sig s₁) (narrowF sig bytes s₁).mem =
        Curry.apply _ f (allArgs sig s₂) (narrowF sig bytes s₂).mem
      rw [hleak _ _ _ l₁ (narrowF_agree hk hb hb1 h₁) hL₁,
        hleak _ _ _ (allArgs_length sig s₂ hk) (narrowF_agree hk hb hb1 h₂) hL₂]
      exact hlk
  · have hx : r.Contains (r.base + BitVec.ofNat 64 i) 1 := Region.contains_ofNat r.base hi
    have hr₁ : r ∈ Sig.lists 64 s₁.mem sig.params (allArgs sig s₁) := Sig.descs_sub_lists 64 _ _ _ r hr
    rw [narrowF_agreeLists hk hb hb1 h₁ r hr₁ _ hx, hdesc r hr i hi]
    refine (f₂ _ fun q hq hc => ?_).symm
    simp only [List.mem_singleton] at hq; subst hq
    rw [← hsp, show s₁.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s₁.gpr .rsp - BitVec.ofNat 64 (bytes + 8) by
      rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl] at hc
    exact fwd_out hk h₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr₁, rfl⟩))
      (x := bytes + 8) (k := 8 * nStack sig + 8) (by omega_using []) (by omega_using [hb]) _ hx hc

/-- The addresses `forward` accesses, from `rsp = sp`, around its callee's `t`. -/
def fwdTrace (bytes m : Nat) (sp : Addr) (t : List Leak) : List Leak :=
  copyDTrace bytes (sp - BitVec.ofNat 64 bytes) m ++
    ([.addr (sp - BitVec.ofNat 64 bytes - 8)] ++ t ++ [.addr (sp - BitVec.ofNat 64 bytes - 8)])

/-- The state `forward` returns in, after the callee's `s₃`. -/
def fwdFinal (bytes : Nat) (s s₃ : State) : State :=
  { ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp
      (s₃.gpr .rsp + 8)).setReg .rsp (s₃.gpr .rsp + 8 + BitVec.ofNat 64 bytes) with wr := s.wr }

/-- A run of the callee from `narrowF s` is a run of `forward` from `s`,
which keeps what the calling convention requires, and whose memory and `rax`
are the callee's. -/
theorem forward_run {name : String} {body : Prog isa} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hm : 0 < nStack sig) (hb : 8 * nStack sig ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 16 ≤ 2 ^ 64) (hsafe : SpSafe body) (hd : body.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa body (narrowF sig bytes s) t s₃) (ha : abiPreserved (narrowF sig bytes s) s₃) :
    Exec isa (forward bytes (nStack sig) name body) s (fwdTrace bytes (nStack sig) (s.gpr .rsp) t)
        (fwdFinal bytes s s₃) ∧
      abiPreserved s (fwdFinal bytes s s₃) ∧ (fwdFinal bytes s s₃).mem = s₃.mem ∧
      (fwdFinal bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', -, -, hgw, hfw, -⟩ := fwdState_run hs hk hb hb1
  obtain ⟨hrsp, hg, hmx, -, hf⟩ := narrowF_facts hk hb hb1 hs
  have hout := fwd_out hk hs
  rw [pre_args hk] at hs
  obtain ⟨⟨hwf, -⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_using [h]
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  let w := fwdState sig bytes s
  have hwrsp : w.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (hgw .rsp (by decide)).trans (allocState_rsp' _ _)
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by omega_using [hb, hm], hb1, hb2, by omega_using [hsb]⟩
  -- The callee's regions are within the caller's and the frame.
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
      by simp [h]⟩, rfl⟩
  have hlistR : ∀ a ∈ (Sig.lists 64 s.mem sig.params (allArgs sig s)).map (fun r => (r, false)),
      a.1 ∈ s.rd := fun a ha => by
    rw [hrd]
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_right _ ha),
      rfl⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), h⟩,
      rfl⟩
  have hcovW : Covers (((fwdRegions sig bytes s).filter (·.2)).map (·.1)) w.wr := by
    rw [hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  have hcovR : Covers (((fwdRegions sig bytes s).filter (!·.2)).map (·.1)) (w.rd ++ w.wr) := by
    rw [hrd', hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hlistR a ha)
    · exact Covers.right (Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ (a := bytes)
        (b := bytes) (Nat.le_refl _) (by omega_using [hb]) (by omega_using [hb1])⟩)
  have hw := Exec.widen he (rd := w.rd) (wr := w.wr) (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowF sig bytes s).withRegions w.rd w.wr = w.callEntry from rfl,
    show w.rd = s.rd from hrd', show w.wr = (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) from hwr'] at hw
  -- The return.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hret : isa.ret w.callEntry (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)) := by
    simp only [isa, ret, State.withRegions_gpr, State.withRegions_mem]
    refine ite_eq_left ⟨by rw [hrsp₃, State.callEntry_rsp, hwrsp], ?_⟩
    have := ha.2.1
    rw [hrsp₃]
    simp only [narrowF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp] at this
    rw [State.callEntry_rsp, hwrsp]
    rw [hwrsp] at this
    exact this
  -- The pop.
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8))) = some (fwdFinal bytes s s₃) := by
    have h4 : ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)).gpr .rsp =
        (allocState bytes s).gpr .rsp := by
      simp only [State.setReg, ite_true, hrsp₃, allocState_rsp', BitVec.sub_add_cancel]
    have h5 : ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)).wr = (allocState bytes s).wr := by
      rfl
    have h6 : (allocState bytes s).wr.head? = some ⟨(allocState bytes s).gpr .rsp, bytes⟩ := by
      simp [allocState, State.setReg]
    simp only [isa, pop]
    rw [ite_eq_left ⟨by omega_using [hb, hm], hb1, hb2, h4, h5, h6⟩]
    simp only [fwdFinal, State.setReg, State.withRegions, ite_true]
    rfl
  have hex : Exec isa (forward bytes (nStack sig) name body) s _ _ :=
    Exec.frame hpush (Exec.seq (Exec.block hrun) (Exec.call (name := name) (call_callEntry w) hw hret)) hpop
  have hwrsp' : (fwdState sig bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := hwrsp
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_rsp',
    List.map_cons, State.withRegions_gpr, hrsp₃, hwrsp'] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, ?_⟩, rfl, ?_⟩
  · -- The callee-saved registers.
    simp only [fwdFinal, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃]
      rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .rax := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq, hg q hqa hqs]
  · -- The return address: the callee writes only its regions and below its `rsp`.
    have hfs := Exec.stackFrame hsafe he (by omega_using [hd, hst])
    show s₃.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    have hR : ∀ {x k : Nat}, x ≤ stack + bytes + 8 → stack + bytes + 8 - x + k ≤ stack + bytes + 8 →
        (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun hx hk' =>
      (Offset.base_disjoint_below _ (n := stack + bytes + 8) (k := 8) (by omega_using [hst])).sub_right
        (Offset.sub_below _ hx hk')
    rw [hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hF]
        exact hR (by omega_using []) (by omega_using [hb])) (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        simp only [fwdRegions, List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha)
        · simp at hf'
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hrsp, hF]
        show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint
          ⟨s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) - BitVec.ofNat 64 body.x86_64Depth, body.x86_64Depth⟩
        rw [BitVec.sub_sub, ← BitVec.ofNat_add]
        exact hR (by omega_using [hd]) (by omega_using [hd])
  · -- MXCSR.
    show s₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [ha.2.2, hmx]
  · simp [fwdFinal, State.setReg]


/-- Code verified against `sig.contract` with `stack` bytes of stack, for a
function whose arguments fill the six argument registers and `nStack sig`
more on the stack, is verified against the same contract with
`stack + bytes + 8` bytes when called by `forward` with its stack arguments
forwarded, if its precondition, postcondition and leak read memory only
within the function's buffers and its lists of slices. -/
theorem Verified.forward {name : String} {body : Prog isa}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hm : 0 < nStack sig)
    (hb : 8 * nStack sig ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 16 ≤ 2 ^ 64)
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.ForwardCall.X86_64.forward bytes (nStack sig) name body)
      (sig.contract abi pre post wa (stack + bytes + 8) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hb0 := hb.1
  have hb1 := hb.2.1
  -- Every run is the copies, then the call of the callee's run from `narrowF`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s → ∃ t s₃,
      Exec isa body (narrowF sig bytes s) t s₃ ∧
      (sig.contract abi pre post wa stack leak).post (narrowF sig bytes s) s₃ ∧
      Exec isa (Impl.ForwardCall.X86_64.forward bytes (nStack sig) name body) s (fwdTrace bytes (nStack sig) (s.gpr .rsp) t)
        (fwdFinal bytes s s₃) ∧
      abiPreserved s (fwdFinal bytes s s₃) ∧ (fwdFinal bytes s s₃).mem = s₃.mem ∧
      (fwdFinal bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowF_pre hk hm hb0 hb1 hpre hs)
    exact ⟨t, s₃, he, hq, forward_run hk hm hb hst hsafe hd hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hmem, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hk]
    rw [post_args hk] at hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowF_facts hk hb0 hb1 hs
    rw [hargs] at hq
    rw [hmem, hrax]
    exact hpost _ _ _ _ _ (allArgs_length sig s hk) (narrowF_agree hk hb0 hb1 hs)
      (fun r hr x hx => narrowF_agreeLists hk hb0 hb1 hs r ((narrowF_lists hk hb0 hb1 hs) ▸ hr) x hx) hq
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_args hk).mp hp).1.1,
      hct _ _ _ _ _ _ (narrowF_pre hk hm hb0 hb1 hpre h₁) (narrowF_pre hk hm hb0 hb1 hpre h₂)
        (narrowF_pub hk hb0 hb1 h₁ h₂ hp hleak) f₁ f₂]

/-- `forward` writes `rsp` only in its frame and its call if its callee does
only in its frames. -/
theorem forward_spSafe {bytes m : Nat} {name : String} {body : Prog isa}
    (h : body.all (fun i => !isa.writesSp i) = true) :
    (forward bytes m name body).all (fun i => !isa.writesSp i) = true := by
  have hc : (copies bytes m).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyDown, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  simp only [forward, Code.all, hc, h, Bool.and_true]
  rfl

end

end VG.X86_64
