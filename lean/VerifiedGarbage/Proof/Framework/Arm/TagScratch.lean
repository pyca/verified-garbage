import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.TagScratch

/-!
# A tag passed through a buffer on the stack (ARMv7)

`Verified.tagScratch`: code verified for a function one of whose arguments,
at word `k` (parameter `q`), is a buffer of working space whose first 16
bytes also carry a tag in or out (its contract `(sig.tagWork …).contract`),
runs as a function whose argument there is a pointer to the 16-byte tag alone
(`sig.contract`), when `withTagScratch` allocates the buffer in a frame on the
stack, with `bytes` more bytes of stack. AAPCS passes the tag pointer in
stack slot `j`, which no other argument uses, and the others in `r0`–`r3`
and the `m` slots of stack arguments (`TagLayout`, decidable for the
signature at hand).

The frame holds what the code expects at and above `sp` on entry, a copy of
the stack arguments, then the saved `lr` and, at `sp + off`, the buffer.
Before the code, the frame copies the tag into the buffer and passes the
buffer in the copy of slot `j` (`tagSetup`); after it, it reloads the tag
pointer from the caller's slot, which the code cannot write, and copies the
buffer's first 16 bytes back to the tag (`tagOut`). The code runs from the
state after `tagSetup`, with the permissions of its contract (`narrowT`), and
its run there is its run from that state (`Exec.widen`); it changes memory
only within the regions it may write and the `armStack c` bytes below its
stack pointer (`Exec.frameSp`, for code whose frames fit in its `stack`), so
the caller's slot survives it.

The two contracts are related by `Sig.TagFrame` (see
`Proof/Framework/TagScratch.lean`).
-/

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

/-! ## Copying words -/

/-- Byte `i` of a copied word. -/
theorem Mem.writeW_readW_apply32 (m₀ m : Mem) (w t : Addr) {i : Nat} (hi : i < 4) :
    (m.writeW w (m₀.readW t 32)) (w + BitVec.ofNat 64 i) = m₀ (t + BitVec.ofNat 64 i) := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat w (show i < 2 ^ 64 by omega),
    show i < 32 / 8 by omega, ite_true, Mem.readW, show 32 / 8 = 4 from rfl]
  rw [show (BitVec.setWidth (8 * 4) (BitVec.setWidth 32 (Mem.read m₀ t 4))) = Mem.read m₀ t 4 by
    simp]
  exact Mem.extractLsb'_read m₀ t hi

/-- The memory after copying the first `n` words at `src` to `dst`, one at a
time. -/
def copyWords (M : Mem) (dst src : Addr) : Nat → Mem
  | 0 => M
  | n + 1 => (copyWords M dst src n).writeW (dst + BitVec.ofNat 64 (4 * n))
      ((copyWords M dst src n).readW (src + BitVec.ofNat 64 (4 * n)) 32)

/-- Copying `n` words between separate places writes only the destination,
which then holds the source's bytes. -/
theorem copyWords_facts {M : Mem} {dst src : Addr} :
    ∀ n, 4 * n < 2 ^ 32 → (⟨src, 4 * n⟩ : Region).Disjoint ⟨dst, 4 * n⟩ →
      Frame [⟨dst, 4 * n⟩] M (copyWords M dst src n) ∧
      ∀ i < 4 * n, copyWords M dst src n (dst + BitVec.ofNat 64 i) = M (src + BitVec.ofNat 64 i)
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, hd => by
    obtain ⟨f, hv⟩ := copyWords_facts (M := M) (dst := dst) (src := src) n (by omega)
      ((hd.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
    have hsrc : (copyWords M dst src n).readW (src + BitVec.ofNat 64 (4 * n)) 32 =
        M.readW (src + BitVec.ofNat 64 (4 * n)) 32 :=
      f.readW (r := ⟨src + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hd.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega)))
        (by decide)
    refine ⟨?_, fun i hi => ?_⟩
    · show Frame _ M ((copyWords M dst src n).writeW _ _)
      refine (Frame.sub f fun r hr => ?_).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · show ((copyWords M dst src n).writeW _ _) _ = _
      rcases Nat.lt_or_ge i (4 * n) with h | h
      · rw [Mem.writeW, Mem.write_apply (Offset.sep dst (d := i) (n := 1) (e := 4 * n) (k := 4) (.inl (by omega))
            (by omega) (by omega) _ (by rw [BitVec.sub_self]; decide)), hv i h]
      · have ha : dst + BitVec.ofNat 64 i = dst + BitVec.ofNat 64 (4 * n) + BitVec.ofNat 64 (i - 4 * n) := by
          rw [Offset.add_add]; congr 2; omega
        have hb : src + BitVec.ofNat 64 (4 * n) + BitVec.ofNat 64 (i - 4 * n) =
            src + BitVec.ofNat 64 i := by
          rw [Offset.add_add]; congr 2; omega
        rw [ha, hsrc, Mem.writeW_readW_apply32 _ _ _ _ (by omega), hb]

/-! ## The blocks -/

/-- The tag pointer in the caller's stack slot `j`, from the frame's base
`sp`. -/
abbrev slotPtr (bytes j : Nat) (w : State) : BitVec 32 := w.mem.readW (sa w.sp (bytes + 4 * j)) 32

/-- The state after `tagWordIn bytes j off k` from `w`. -/
def tagInStep (bytes j off k : Nat) (w : State) : State :=
  { w.setReg .lr (w.mem.readW (State.addr (slotPtr bytes j w + BitVec.ofNat 32 (4 * k))) 32) with
    mem := w.mem.writeW (sa w.sp (off + 4 * k))
      (w.mem.readW (State.addr (slotPtr bytes j w + BitVec.ofNat 32 (4 * k))) 32) }

theorem tagWordIn_run {bytes j off k : Nat} {w : State} (hr12 : w.gpr .r12 = w.sp)
    (h₁ : bytes + 4 * j < 4096) (h₂ : 4 * k < 4096) (h₃ : off + 4 * k < 4096)
    (hs : InRegions (w.rd ++ w.wr) (sa w.sp (bytes + 4 * j)) 4)
    (ht : InRegions (w.rd ++ w.wr) (State.addr (slotPtr bytes j w + BitVec.ofNat 32 (4 * k))) 4)
    (hw : InRegions w.wr (sa w.sp (off + 4 * k)) 4) :
    execBlock isa (tagWordIn bytes j off k) w = some (tagInStep bytes j off k w,
      [.addr (sa w.sp (bytes + 4 * j)),
        .addr (State.addr (slotPtr bytes j w + BitVec.ofNat 32 (4 * k))),
        .addr (sa w.sp (off + 4 * k))]) := by
  simp only [tagWordIn, execBlock, isa, exec, h₁, h₂, h₃, ite_true, State.load32, hs,
    Option.map_some, addrs, State.store32]
  simp [State.setReg, hr12, ht, hw, tagInStep]
  funext q
  by_cases hq : q = .lr <;> simp [hq, slotPtr]

@[simp] theorem tagInStep_sp (bytes j off k : Nat) (w : State) : (tagInStep bytes j off k w).sp = w.sp := rfl
@[simp] theorem tagInStep_rd (bytes j off k : Nat) (w : State) : (tagInStep bytes j off k w).rd = w.rd := rfl
@[simp] theorem tagInStep_wr (bytes j off k : Nat) (w : State) : (tagInStep bytes j off k w).wr = w.wr := rfl
theorem tagInStep_gpr (bytes j off k : Nat) (w : State) {q : Reg} (h : q ≠ .lr) :
    (tagInStep bytes j off k w).gpr q = w.gpr q := by
  simp [tagInStep, State.setReg, h]

/-- The state after copying the first `n` words of the tag from `w`. -/
def tagInStates (bytes j off : Nat) (w : State) : Nat → State
  | 0 => w
  | n + 1 => tagInStep bytes j off n (tagInStates bytes j off w n)

@[simp] theorem tagInStates_sp (bytes j off : Nat) (w : State) :
    ∀ n, (tagInStates bytes j off w n).sp = w.sp
  | 0 => rfl
  | n + 1 => by rw [tagInStates, tagInStep_sp, tagInStates_sp bytes j off w n]
@[simp] theorem tagInStates_rd (bytes j off : Nat) (w : State) :
    ∀ n, (tagInStates bytes j off w n).rd = w.rd
  | 0 => rfl
  | n + 1 => by rw [tagInStates, tagInStep_rd, tagInStates_rd bytes j off w n]
@[simp] theorem tagInStates_wr (bytes j off : Nat) (w : State) :
    ∀ n, (tagInStates bytes j off w n).wr = w.wr
  | 0 => rfl
  | n + 1 => by rw [tagInStates, tagInStep_wr, tagInStates_wr bytes j off w n]
theorem tagInStates_gpr (bytes j off : Nat) (w : State) {q : Reg} (h : q ≠ .lr) :
    ∀ n, (tagInStates bytes j off w n).gpr q = w.gpr q
  | 0 => rfl
  | n + 1 => by rw [tagInStates, tagInStep_gpr _ _ _ _ _ h, tagInStates_gpr bytes j off w h n]

/-- The addresses copying the first `n` words of the tag (at `t`) accesses,
from `sp`. -/
def tagInTrace (bytes j off : Nat) (sp t : BitVec 32) (n : Nat) : List Leak :=
  (List.range n).flatMap fun k =>
    [.addr (sa sp (bytes + 4 * j)), .addr (State.addr (t + BitVec.ofNat 32 (4 * k))),
      .addr (sa sp (off + 4 * k))]

/-- Copying the tag's words, from the pointer `t` in the caller's slot (at
`S`) to the buffer at `D`, separate from the slot and from the tag (at
`T`). -/
theorem tagIns_run {bytes j off : Nat} {w : State} {t : BitVec 32} {D T : Addr}
    (hr12 : w.gpr .r12 = w.sp) (h₁ : bytes + 4 * j < 4096) (h₃ : off + 12 < 4096)
    (hD : ∀ k < 4, sa w.sp (off + 4 * k) = D + BitVec.ofNat 64 (4 * k))
    (hT : ∀ k < 4, State.addr (t + BitVec.ofNat 32 (4 * k)) = T + BitVec.ofNat 64 (4 * k))
    (hslot : slotPtr bytes j w = t)
    (hsd : (⟨sa w.sp (bytes + 4 * j), 4⟩ : Region).Disjoint ⟨D, 16⟩)
    (htd : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16⟩)
    (hs : InRegions (w.rd ++ w.wr) (sa w.sp (bytes + 4 * j)) 4)
    (ht : ∀ k < 4, InRegions (w.rd ++ w.wr) (T + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ k < 4, InRegions w.wr (D + BitVec.ofNat 64 (4 * k)) 4) :
    ∀ n ≤ 4, execBlock isa ((List.range n).flatMap (tagWordIn bytes j off)) w =
        some (tagInStates bytes j off w n, tagInTrace bytes j off w.sp t n) ∧
      (tagInStates bytes j off w n).mem = copyWords w.mem D T n
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨hrun, hmem⟩ := tagIns_run hr12 h₁ h₃ hD hT hslot hsd htd hs ht hw n (by omega)
    obtain ⟨f, -⟩ := copyWords_facts (M := w.mem) (dst := D) (src := T) n (by omega)
      ((htd.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
    have hslot' : slotPtr bytes j (tagInStates bytes j off w n) = t := by
      simp only [slotPtr, tagInStates_sp]
      rw [hmem, f.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsd.sub_right (Region.sub_prefix (by omega))) (by decide)]
      exact hslot
    have hstep := tagWordIn_run (bytes := bytes) (j := j) (off := off) (k := n)
      (w := tagInStates bytes j off w n)
      (by rw [tagInStates_gpr _ _ _ _ (by decide), tagInStates_sp]; exact hr12) h₁ (by omega)
      (by omega) (by simpa using hs)
      (by
        rw [hslot', hT n (by omega), tagInStates_rd, tagInStates_wr]; exact ht n (by omega))
      (by rw [tagInStates_sp, hD n (by omega), tagInStates_wr]; exact hw n (by omega))
    refine ⟨?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, execBlock_append, hrun]
      simp only [Option.bind_some, List.flatMap_singleton]
      rw [hstep]
      simp only [Option.map_some, tagInStates, tagInStates_sp, hslot', tagInTrace, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
    · show (tagInStates bytes j off w n).mem.writeW _ _ = _
      rw [hslot', tagInStates_sp, hD n (by omega), hT n (by omega), hmem]
      rfl

/-- The state after `tagWordOut off k` from `w`. -/
def tagOutStep (off k : Nat) (w : State) : State :=
  { w.setReg .r2 (w.mem.readW (sa w.sp (off + 4 * k)) 32) with
    mem := w.mem.writeW (State.addr (w.gpr .r12 + BitVec.ofNat 32 (4 * k)))
      (w.mem.readW (sa w.sp (off + 4 * k)) 32) }

theorem tagWordOut_run {off k : Nat} {w : State} (h₂ : 4 * k < 4096) (h₃ : off + 4 * k < 4096)
    (hr : InRegions (w.rd ++ w.wr) (sa w.sp (off + 4 * k)) 4)
    (hw : InRegions w.wr (State.addr (w.gpr .r12 + BitVec.ofNat 32 (4 * k))) 4) :
    execBlock isa (tagWordOut off k) w = some (tagOutStep off k w,
      [.addr (sa w.sp (off + 4 * k)), .addr (State.addr (w.gpr .r12 + BitVec.ofNat 32 (4 * k)))]) := by
  simp only [tagWordOut, execBlock, isa, exec, h₂, h₃, ite_true, State.load32, hr,
    Option.map_some, addrs, State.store32]
  simp [State.setReg, hw, tagOutStep]

@[simp] theorem tagOutStep_sp (off k : Nat) (w : State) : (tagOutStep off k w).sp = w.sp := rfl
@[simp] theorem tagOutStep_rd (off k : Nat) (w : State) : (tagOutStep off k w).rd = w.rd := rfl
@[simp] theorem tagOutStep_wr (off k : Nat) (w : State) : (tagOutStep off k w).wr = w.wr := rfl
theorem tagOutStep_gpr (off k : Nat) (w : State) {q : Reg} (h : q ≠ .r2) :
    (tagOutStep off k w).gpr q = w.gpr q := by
  simp [tagOutStep, State.setReg, h]

/-- The state after copying the first `n` words of the buffer back from `w`. -/
def tagOutStates (off : Nat) (w : State) : Nat → State
  | 0 => w
  | n + 1 => tagOutStep off n (tagOutStates off w n)

@[simp] theorem tagOutStates_sp (off : Nat) (w : State) : ∀ n, (tagOutStates off w n).sp = w.sp
  | 0 => rfl
  | n + 1 => by rw [tagOutStates, tagOutStep_sp, tagOutStates_sp off w n]
@[simp] theorem tagOutStates_rd (off : Nat) (w : State) : ∀ n, (tagOutStates off w n).rd = w.rd
  | 0 => rfl
  | n + 1 => by rw [tagOutStates, tagOutStep_rd, tagOutStates_rd off w n]
@[simp] theorem tagOutStates_wr (off : Nat) (w : State) : ∀ n, (tagOutStates off w n).wr = w.wr
  | 0 => rfl
  | n + 1 => by rw [tagOutStates, tagOutStep_wr, tagOutStates_wr off w n]
theorem tagOutStates_gpr (off : Nat) (w : State) {q : Reg} (h : q ≠ .r2) :
    ∀ n, (tagOutStates off w n).gpr q = w.gpr q
  | 0 => rfl
  | n + 1 => by rw [tagOutStates, tagOutStep_gpr _ _ _ h, tagOutStates_gpr off w h n]

/-- The addresses copying the first `n` words of the buffer back to the tag
(at `t`) accesses, from `sp`. -/
def tagOutTrace (off : Nat) (sp t : BitVec 32) (n : Nat) : List Leak :=
  (List.range n).flatMap fun k =>
    [.addr (sa sp (off + 4 * k)), .addr (State.addr (t + BitVec.ofNat 32 (4 * k)))]

/-- Copying the buffer's words (at `D`) back to the tag (at `T`, its pointer
in `r12`). -/
theorem tagOuts_run {off : Nat} {w : State} {D T : Addr} (h₃ : off + 12 < 4096)
    (hD : ∀ k < 4, sa w.sp (off + 4 * k) = D + BitVec.ofNat 64 (4 * k))
    (hT : ∀ k < 4, State.addr (w.gpr .r12 + BitVec.ofNat 32 (4 * k)) = T + BitVec.ofNat 64 (4 * k))
    (htd : (⟨D, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (hr : ∀ k < 4, InRegions (w.rd ++ w.wr) (D + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ k < 4, InRegions w.wr (T + BitVec.ofNat 64 (4 * k)) 4) :
    ∀ n ≤ 4, execBlock isa ((List.range n).flatMap (tagWordOut off)) w =
        some (tagOutStates off w n, tagOutTrace off w.sp (w.gpr .r12) n) ∧
      (tagOutStates off w n).mem = copyWords w.mem T D n
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨hrun, hmem⟩ := tagOuts_run h₃ hD hT htd hr hw n (by omega)
    have hr12 : (tagOutStates off w n).gpr .r12 = w.gpr .r12 := tagOutStates_gpr _ _ (by decide) n
    have hstep := tagWordOut_run (off := off) (k := n) (w := tagOutStates off w n) (by omega)
      (by omega)
      (by
        rw [tagOutStates_sp, hD n (by omega), tagOutStates_rd, tagOutStates_wr]; exact hr n (by omega))
      (by rw [hr12, hT n (by omega), tagOutStates_wr]; exact hw n (by omega))
    refine ⟨?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, execBlock_append, hrun]
      simp only [Option.bind_some, List.flatMap_singleton]
      rw [hstep]
      simp only [Option.map_some, tagOutStates, tagOutStates_sp, hr12, tagOutTrace,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    · show (tagOutStates off w n).mem.writeW _ _ = _
      rw [hr12, tagOutStates_sp, hD n (by omega), hT n (by omega), hmem]
      rfl

/-- The addresses `tagOut bytes j off` accesses, from `sp`, for the tag at
`t`. -/
def tagOutAll (bytes j off : Nat) (sp t : BitVec 32) : List Leak :=
  .addr (sa sp (bytes + 4 * j)) :: tagOutTrace off sp t 4

/-- `tagOut`: the tag pointer from the caller's slot, and the buffer's first
16 bytes (at `D`) copied to the tag (at `T`). -/
theorem tagOut_run {bytes j off : Nat} {w : State} {D T : Addr} (h₁ : bytes + 4 * j < 4096)
    (h₃ : off + 12 < 4096) (hs : InRegions (w.rd ++ w.wr) (sa w.sp (bytes + 4 * j)) 4)
    (hD : ∀ k < 4, sa w.sp (off + 4 * k) = D + BitVec.ofNat 64 (4 * k))
    (hT : ∀ k < 4, State.addr (slotPtr bytes j w + BitVec.ofNat 32 (4 * k)) =
      T + BitVec.ofNat 64 (4 * k))
    (htd : (⟨D, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (hr : ∀ k < 4, InRegions (w.rd ++ w.wr) (D + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ k < 4, InRegions w.wr (T + BitVec.ofNat 64 (4 * k)) 4) :
    ∃ w', execBlock isa (tagOut bytes j off) w =
        some (w', tagOutAll bytes j off w.sp (slotPtr bytes j w)) ∧
      w'.sp = w.sp ∧ w'.rd = w.rd ∧ w'.wr = w.wr ∧
      (∀ q, q ≠ .r2 → q ≠ .r12 → w'.gpr q = w.gpr q) ∧ w'.mem = copyWords w.mem T D 4 := by
  have hld : execBlock isa [.ldrSp .r12 (bytes + 4 * j)] w =
      some (w.setReg .r12 (slotPtr bytes j w), [.addr (sa w.sp (bytes + 4 * j))]) := by
    simp only [execBlock, isa, exec, h₁, ite_true, State.load32, hs, Option.map_some, addrs]
    rfl
  obtain ⟨hrun, hmem⟩ := tagOuts_run (off := off) (w := w.setReg .r12 (slotPtr bytes j w))
    (D := D) (T := T) h₃ hD (by simpa [State.setReg] using hT) htd hr hw 4 (Nat.le_refl _)
  refine ⟨tagOutStates off (w.setReg .r12 (slotPtr bytes j w)) 4, ?_, by simp [State.setReg],
    by simp [State.setReg], by simp [State.setReg], fun q h₂ h₁₂ => ?_, hmem⟩
  · rw [show tagOut bytes j off = [.ldrSp .r12 (bytes + 4 * j)] ++
        (List.range 4).flatMap (tagWordOut off) from rfl, execBlock_append, hld]
    simp only [Option.bind_some, hrun, Option.map_some, tagOutAll]
    simp [State.setReg]
  · rw [tagOutStates_gpr _ _ h₂]
    simp [State.setReg, h₁₂]

/-- `add lr, sp, #off; str lr, [r12, #4j]; ldr lr, [sp, #4m + 4]`: pass the
buffer in the copy of slot `j`, and restore `lr`. -/
theorem point_run {j off m : Nat} {w : State} (hr12 : w.gpr .r12 = w.sp) (hoff : off < 256)
    (hj : 4 * j < 4096) (hm : 4 * m + 4 < 4096)
    (hw : InRegions w.wr (sa w.sp (4 * j)) 4) (hr : InRegions (w.rd ++ w.wr) (sa w.sp (4 * m + 4)) 4) :
    ∃ w', execBlock isa [.addSp .lr off, .str .lr .r12 (4 * j), .ldrSp .lr (4 * m + 4)] w =
        some (w', [.addr (sa w.sp (4 * j)), .addr (sa w.sp (4 * m + 4))]) ∧
      w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.sp = w.sp ∧ (∀ q, q ≠ .lr → w'.gpr q = w.gpr q) ∧
      w'.mem = w.mem.writeW (sa w.sp (4 * j)) (w.sp + BitVec.ofNat 32 off) ∧
      w'.gpr .lr = w'.mem.readW (sa w.sp (4 * m + 4)) 32 := by
  simp only [execBlock, isa, exec, hoff, hj, hm, ite_true, Option.map_some, addrs, State.store32,
    State.load32]
  simp [State.setReg, hr12, hw, hr]
  intro q hq; simp [hq]

/-- The addresses `tagSetup bytes m j off` accesses, from `sp`, for the tag
at `t`. -/
def tagSetupTrace (bytes m j off : Nat) (sp t : BitVec 32) : List Leak :=
  [.addr (sa sp (4 * m + 4))] ++ copyTrace bytes sp m ++ tagInTrace bytes j off sp t 4 ++
    [.addr (sa sp (4 * j)), .addr (sa sp (4 * m + 4))]

/-- The state after `tagSetup bytes m j off` from `u`, if it runs. -/
def tagSetupState (bytes m j off : Nat) (u : State) : State :=
  ((execBlock isa (tagSetup bytes m j off) u).map Prod.fst).getD u

/-- `tagSetup`, from the state after the frame's push (`u`, whose `sp` is
the frame's base): the stack argument slots copied into the frame, the tag
(from the pointer `t` in the caller's slot `j`) copied to the buffer at
`sp + off`, and the buffer's address in the copy of slot `j`; nothing
written outside the frame, and only `r12` changed. -/
theorem tagSetup_run {bytes m j off : Nat} {u : State}
    (hfit : u.sp.toNat + bytes + 4 * m ≤ 2 ^ 32) (hj : j < m) (hb : 4 * m + 8 ≤ off)
    (hb' : off + 16 ≤ bytes) (hoff : off < 256) (ho : bytes + 4 * m ≤ 4096)
    (hr : ∀ i < m, InRegions (u.rd ++ u.wr) (sa u.sp (bytes + 4 * i)) 4)
    (hfr : ⟨State.addr u.sp, bytes⟩ ∈ u.wr)
    (ht16 : (slotPtr bytes j u).toNat + 16 ≤ 2 ^ 32)
    (ht : ∀ k < 4, InRegions (u.rd ++ u.wr) (State.addr (slotPtr bytes j u) + BitVec.ofNat 64 (4 * k)) 4)
    (htd : (⟨State.addr (slotPtr bytes j u), 16⟩ : Region).Disjoint ⟨State.addr u.sp, bytes⟩) :
    execBlock isa (tagSetup bytes m j off) u =
        some (tagSetupState bytes m j off u, tagSetupTrace bytes m j off u.sp (slotPtr bytes j u)) ∧
      (tagSetupState bytes m j off u).rd = u.rd ∧ (tagSetupState bytes m j off u).wr = u.wr ∧
      (tagSetupState bytes m j off u).sp = u.sp ∧
      (∀ q, q ≠ .r12 → (tagSetupState bytes m j off u).gpr q = u.gpr q) ∧
      Frame [⟨State.addr u.sp, bytes⟩] u.mem (tagSetupState bytes m j off u).mem ∧
      (∀ i < m, (tagSetupState bytes m j off u).mem.readW (sa u.sp (4 * i)) 32 =
        if i = j then u.sp + BitVec.ofNat 32 off else u.mem.readW (sa u.sp (bytes + 4 * i)) 32) ∧
      ∀ i < 16, (tagSetupState bytes m j off u).mem
          (State.addr u.sp + BitVec.ofNat 64 off + BitVec.ofNat 64 i) =
        u.mem (State.addr (slotPtr bytes j u) + BitVec.ofNat 64 i) := by
  generalize hP : State.addr u.sp = Pa at hfr htd
  have hA : ∀ d, d < bytes + 4 * m → sa u.sp d = Pa + BitVec.ofNat 64 d :=
    fun d hd => by rw [← hP]; exact sa_eq (by omega)
  have hW : ∀ d, d + 4 ≤ bytes → InRegions u.wr (sa u.sp d) 4 := fun d hd =>
    ⟨_, hfr, by rw [hA d (by omega)]; exact Offset.contains_base _ hd (by omega)⟩
  have hsep : ∀ d e, d + 4 ≤ e ∨ e + 4 ≤ d → d < bytes + 4 * m → e < bytes + 4 * m →
      Mem.Sep (sa u.sp d) (32 / 8) (sa u.sp e) (32 / 8) := fun d e h hd he => by
    rw [hA d hd, hA e he]; exact Offset.sep _ h (by omega) (by omega)
  -- Saving `lr` and copying the arguments.
  have hh := head_run (u := u) (m := m) (by omega) (hW _ (by omega))
  have hc := copies_run (bytes := bytes) (w := savedState m u) (savedState_r12 m u) m ho
    (fun i hi => by simpa using hr i hi) (fun i hi => by simpa using hW (4 * i) (by omega))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (w := savedState m u) m (by simpa using hfit)
    (by omega)
  simp only [savedState_sp] at f hv
  rw [hP] at f
  have f₀ : Frame [⟨Pa, bytes⟩] u.mem (savedState m u).mem :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by rw [hA _ (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
  have f₁ : Frame [⟨Pa, bytes⟩] u.mem (copiedState bytes (savedState m u) m).mem :=
    f₀.trans (Frame.sub f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  have hlr₁ : (copiedState bytes (savedState m u) m).mem.readW (sa u.sp (4 * m + 4)) 32 = u.gpr .lr := by
    rw [f.readW (r := ⟨sa u.sp (4 * m + 4), 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact Mem.readW_writeW_self32 _ _ _
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hA _ (by omega)]
      exact Offset.disjoint_base _ (by omega) (by omega)
  have hv₁ : ∀ i < m, (copiedState bytes (savedState m u) m).mem.readW (sa u.sp (4 * i)) 32 =
      u.mem.readW (sa u.sp (bytes + 4 * i)) 32 := fun i hi => by
    rw [hv i hi]
    show (u.mem.writeW (sa u.sp (4 * m + 4)) (u.gpr .lr)).readW _ 32 = _
    rw [Mem.readW_writeW_sep (hsep _ _ (by omega) (by omega) (by omega)) (by decide)]
  have hslot₁ : slotPtr bytes j (copiedState bytes (savedState m u) m) = slotPtr bytes j u := by
    simp only [slotPtr, copiedState_sp, savedState_sp]
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hA _ (by omega)]; exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have e₁ : (copiedState bytes (savedState m u) m).sp = u.sp := by simp
  have r₁ : (copiedState bytes (savedState m u) m).rd = u.rd := by simp
  have wr₁ : (copiedState bytes (savedState m u) m).wr = u.wr := by simp
  have g₁ : ∀ q, q ≠ .lr → q ≠ .r12 → (copiedState bytes (savedState m u) m).gpr q = u.gpr q :=
    fun q h₁ h₂ => by rw [copiedState_gpr _ _ h₁, savedState_gpr _ _ h₂]
  have g₁₂ : (copiedState bytes (savedState m u) m).gpr .r12 = u.sp := by
    rw [copiedState_gpr _ _ (by decide), savedState_r12]
  generalize copiedState bytes (savedState m u) m = w₁ at hc f₁ hlr₁ hv₁ hslot₁ e₁ r₁ wr₁ g₁ g₁₂
  generalize hts : slotPtr bytes j u = t at ht16 ht htd hslot₁ ⊢
  -- The tag.
  have hD : ∀ k < 4, sa w₁.sp (off + 4 * k) = Pa + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) :=
    fun k hk => by rw [e₁, hA _ (by omega), Offset.add_add]
  have hT : ∀ k < 4, State.addr (t + BitVec.ofNat 32 (4 * k)) =
      State.addr t + BitVec.ofNat 64 (4 * k) := fun k hk => addr_add (by omega)
  have hbuf : ∀ {d n : Nat}, off ≤ d → d + n ≤ off + 16 →
      Region.Sub ⟨Pa + BitVec.ofNat 64 d, n⟩ ⟨Pa + BitVec.ofNat 64 off, 16⟩ :=
    fun h₁ h₂ => Offset.sub _ h₁ h₂
  have hbufF : Region.Sub ⟨Pa + BitVec.ofNat 64 off, 16⟩ ⟨Pa, bytes⟩ := Offset.sub_base _ (by omega)
  obtain ⟨hti, htm⟩ := tagIns_run (bytes := bytes) (j := j) (off := off) (w := w₁) (t := t)
    (D := Pa + BitVec.ofNat 64 off) (T := State.addr t) (by rw [g₁₂, e₁]) (by omega) (by omega)
    hD hT hslot₁
    (by rw [e₁, hA _ (by omega)]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega))
    (htd.sub_right hbufF) (by rw [r₁, wr₁, e₁]; exact hr j hj) (by rw [r₁, wr₁]; exact ht)
    (fun k hk => by
      rw [wr₁, Offset.add_add]
      exact ⟨_, hfr, Offset.contains_base _ (by omega) (by omega)⟩) 4 (Nat.le_refl _)
  obtain ⟨fc, hcw⟩ := copyWords_facts (M := w₁.mem) (dst := Pa + BitVec.ofNat 64 off)
    (src := State.addr t) 4 (by decide) (htd.sub_right hbufF)
  rw [← htm] at fc hcw
  have e₂ : (tagInStates bytes j off w₁ 4).sp = u.sp := by rw [tagInStates_sp, e₁]
  have r₂ : (tagInStates bytes j off w₁ 4).rd = u.rd := by rw [tagInStates_rd, r₁]
  have wr₂ : (tagInStates bytes j off w₁ 4).wr = u.wr := by rw [tagInStates_wr, wr₁]
  have g₂ : ∀ q, q ≠ .lr → (tagInStates bytes j off w₁ 4).gpr q = w₁.gpr q :=
    fun q h => tagInStates_gpr _ _ _ _ h 4
  have hlr₂ : (tagInStates bytes j off w₁ 4).mem.readW (sa u.sp (4 * m + 4)) 32 = u.gpr .lr := by
    rw [fc.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hA _ (by omega)]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      (by decide), hlr₁]
  have hv₂ : ∀ i < m, (tagInStates bytes j off w₁ 4).mem.readW (sa u.sp (4 * i)) 32 =
      u.mem.readW (sa u.sp (bytes + 4 * i)) 32 := fun i hi => by
    rw [fc.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hA _ (by omega)]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      (by decide), hv₁ i hi]
  generalize tagInStates bytes j off w₁ 4 = w₂ at hti fc hcw e₂ r₂ wr₂ g₂ hlr₂ hv₂
  -- Passing the buffer, and restoring `lr`.
  obtain ⟨w₃, hpt, r₃, wr₃, e₃, g₃, hm₃, hlr₃⟩ := point_run (j := j) (off := off) (m := m) (w := w₂)
    (by rw [g₂ _ (by decide), g₁₂, e₂]) hoff (by omega) (by omega)
    (by rw [wr₂, e₂]; exact hW _ (by omega))
    (by rw [r₂, wr₂, e₂]; exact ⟨_, List.mem_append_right _ hfr, by
      rw [hA _ (by omega)]; exact Offset.contains_base _ (by omega) (by omega)⟩)
  rw [e₂] at hpt hm₃ hlr₃
  have hrun : execBlock isa (tagSetup bytes m j off) u =
      some (w₃, tagSetupTrace bytes m j off u.sp t) := by
    rw [tagSetup, execBlock_append, execBlock_append, execBlock_append, hh]
    simp only [Option.bind_some, Option.map_some, hc, savedState_sp]
    rw [hti]
    simp only [Option.bind_some, Option.map_some, e₁]
    rw [hpt]
    simp only [Option.map_some, tagSetupTrace, List.append_assoc, List.cons_append,
      List.nil_append]
  have hst : tagSetupState bytes m j off u = w₃ := by simp [tagSetupState, hrun]
  rw [hst]
  have hjs : ∀ {i : Nat}, i < m → i ≠ j → Mem.Sep (sa u.sp (4 * i)) (32 / 8) (sa u.sp (4 * j)) (32 / 8) :=
    fun hi hij => hsep _ _ (by omega) (by omega) (by omega)
  refine ⟨hrun, r₃.trans r₂, wr₃.trans wr₂, e₃.trans e₂, fun q hq => ?_, ?_, fun i hi => ?_,
    fun i hi => ?_⟩
  · by_cases hql : q = .lr
    · subst hql; rw [hlr₃, hm₃, Mem.readW_writeW_sep (hsep _ _ (by omega) (by omega) (by omega))
        (by decide), hlr₂]
    · rw [g₃ q hql, g₂ q hql, g₁ q hql hq]
  · rw [hm₃]
    refine (f₁.trans (Frame.sub fc fun r hr => ?_)).writeW (List.mem_singleton_self _) _
      (by rw [hA _ (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, hbufF⟩
  · rw [hm₃]
    split
    · next h => subst h; rw [Mem.readW_writeW_self32]
    · next h => rw [Mem.readW_writeW_sep (hjs hi h) (by decide), hv₂ i hi]
  · rw [hm₃, Mem.writeW, Mem.write_apply, hcw i hi, f₁.bytes (R := ⟨State.addr t, 16⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact htd)
      (show 16 ≤ 2 ^ 64 by decide) hi]
    rw [hA _ (by omega)]
    exact Offset.sep Pa (d := off + i) (n := 1) (e := 4 * j) (k := 4) (.inr (by omega)) (by omega)
      (by omega) _ (by rw [Offset.add_add, BitVec.sub_self]; decide)

/-! ## Where the arguments are -/

/-- `l` does not use stack slot `j`. -/
def Loc.slotFree (j : Nat) : Loc → Bool
  | .stack off b => decide (off / 4 ≠ j) && (decide (b ≠ 64) || decide (off / 4 + 1 ≠ j))
  | _ => true

/-- An argument in a register `s'` keeps, or in slots other than `j` of which
it holds a copy, has the same value in both. -/
theorem Loc.val_congr_ne {N j : Nat} {s s' : State} (hr : ∀ r ∈ argRegs, s'.gpr r = s.gpr r)
    (hs : ∀ i, 4 * i + 4 ≤ N → i ≠ j → stackArg s' i = stackArg s i) :
    ∀ l : Loc, l.ok N = true → l.slotFree j = true → l.val s' = l.val s
  | .reg r, h, _ => by
    simp only [Loc.ok, decide_eq_true_eq] at h
    simp only [Loc.val, hr r h]
  | .pair lo hi, h, _ => by
    simp only [Loc.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Loc.val, hr lo h.1, hr hi h.2]
  | .stack off b, h, hf => by
    simp only [Loc.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Loc.slotFree, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
    obtain ⟨h4, hN⟩ := h
    by_cases hb : b = 64
    · subst hb
      simp only [ite_true] at hN
      simp only [Loc.val]
      rw [hs (off / 4) (by omega) hf.1, hs (off / 4 + 1) (by omega) (by omega)]
    · simp only [hb, ite_false] at hN
      have hv : ∀ t : State, Loc.val t (.stack off b) = (stackArg t (off / 4)).setWidth 64 := by
        intro t; unfold Loc.val; split <;> simp_all
      rw [hv, hv, hs (off / 4) (by omega) hf.1]

/-- The argument word of `sig`'s parameter `q`. -/
abbrev tagWord (sig : Sig) (q : Nat) : Nat := (Sig.psWords (sig.params.take q) abi.ptrBits).length

/-- Where AAPCS passes the arguments of `sig`, for `withTagScratch` with the
tag pointer, parameter `q`, in stack slot `j`: the stack arguments take `m`
slots, every argument is in `r0`–`r3` or among them, the tag pointer is a
word in slot `j`, and no other argument uses that slot. -/
abbrev TagLayout (sig : Sig) (q m j : Nat) : Prop :=
  nsaa sig = 4 * m ∧ (locs sig).all (Loc.ok (4 * m)) = true ∧
    (locs sig)[tagWord sig q]? = some (.stack (4 * j) 32) ∧
    ((locs sig).eraseIdx (tagWord sig q)).all (Loc.slotFree j) = true

/-- The sizes `withTagScratch` needs: the frame holds the copies, the saved
`lr` and the buffer at `off`, which holds the tag; the offsets are
encodable. -/
abbrev TagFits (m off bytes : Nat) (e : Elem) (n : Nat) : Prop :=
  4 * m + 8 ≤ off ∧ off + 16 ≤ bytes ∧ off + n * e.size ≤ bytes ∧ off < 256 ∧ bytes < 4096 ∧
    bytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 bytes) = true ∧ bytes + 4 * m ≤ 4096

theorem widths_tagWork {sig : Sig} {q : Nat} {p : String × Param} (nm : String) (e : Elem)
    (n : Nat) (hq : sig.params[q]? = some p) (hp : ∃ nmT w eT nT, p = (nmT, .array w eT nT)) :
    widths (sig.tagWork q nm e n) = widths sig := by
  obtain ⟨nmT, w, eT, nT, rfl⟩ := hp
  rw [widths, widths, Sig.words_tagWork _ _ _ _ hq]

/-- The arguments of a state that keeps `r0`–`r3` and the stack slots but
`j`, which holds `w`. -/
theorem armArgs_tagSet {sig : Sig} {q m j : Nat} (hlay : TagLayout sig q m j) {s s' : State}
    {w : BitVec 32} (hr : ∀ r ∈ argRegs, s'.gpr r = s.gpr r)
    (hs : ∀ i < m, i ≠ j → stackArg s' i = stackArg s i) (hw : stackArg s' j = w) :
    (locs sig).map (Loc.val s') = (armArgs sig s).set (tagWord sig q) (State.addr w) := by
  obtain ⟨-, hloc, htag, hfree⟩ := hlay
  apply List.ext_getElem (by rw [List.length_map, List.length_set, armArgs, List.length_map])
  intro i h₁ h₂
  rw [List.getElem_map, List.getElem_set]
  by_cases h : tagWord sig q = i
  · simp only [h, ↓reduceIte]
    obtain ⟨_, htag'⟩ := List.getElem?_eq_some_iff.mp htag
    have e : (locs sig)[i]'(by simpa using h₁) = .stack (4 * j) 32 := by
      simp only [← h]; exact htag'
    rw [e]
    simp only [Loc.val, show (4 * j) / 4 = j by omega, hw]
    rfl
  · simp only [h, ↓reduceIte]
    simp only [armArgs, List.getElem_map]
    have hl : (locs sig)[i]'(by simpa using h₁) ∈ locs sig := List.getElem_mem _
    have hi : (locs sig)[i]'(by simpa using h₁) ∈ (locs sig).eraseIdx (tagWord sig q) :=
      List.mem_eraseIdx_iff_getElem.mpr ⟨i, by simpa using h₁, fun e => h e.symm, rfl⟩
    exact Loc.val_congr_ne hr (fun i hi hij => hs i (by omega) hij) _
      (List.all_eq_true.mp hloc _ hl) (List.all_eq_true.mp hfree _ hi)

/-- The tag pointer's slot is among the `m`. -/
theorem TagLayout.j_lt {sig : Sig} {q m j : Nat} (hlay : TagLayout sig q m j) : j < m := by
  obtain ⟨-, hloc, htag, -⟩ := hlay
  have hm := List.mem_of_getElem? htag
  have := List.all_eq_true.mp hloc _ hm
  simp [Loc.ok] at this
  omega

/-- The tag pointer is the value of slot `j`. -/
theorem TagLayout.getD {sig : Sig} {q m j : Nat} (hlay : TagLayout sig q m j) (s : State) :
    (armArgs sig s).getD (tagWord sig q) 0 = State.addr (stackArg s j) := by
  obtain ⟨-, -, htag, -⟩ := hlay
  rw [armArgs, List.getD_eq_getElem?_getD, List.getElem?_map, htag]
  simp only [Option.map_some, Option.getD_some, Loc.val, show (4 * j) / 4 = j by omega]
  rfl

/-! ## The state the code runs from -/

/-- The buffer's address, from the state `s` on entry. -/
abbrev tagBuf (bytes off : Nat) (s : State) : Addr := sa (s.sp - BitVec.ofNat 32 bytes) off

/-- The regions of the code's contract, from the state `s` on entry: the
buffers, with the working space in the tag's place, and the copy of the
stack arguments, read-only. -/
def innerRegions (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes m off : Nat) (s : State) :
    List (Region × Bool) :=
  Sig.bufs (sig.tagWork q nm e n).params ((armArgs sig s).set (tagWord sig q) (tagBuf bytes off s)) ++
    [(⟨State.addr (s.sp - BitVec.ofNat 32 bytes), 4 * m⟩, false)]

/-- The state the code runs from, with the permissions of its contract: the
state after the frame's push and `tagSetup`. -/
def narrowT (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes m j off : Nat) (s : State) :
    State :=
  (tagSetupState bytes m j off (allocState bytes s)).withRegions
    (((innerRegions sig q nm e n bytes m off s).filter (!·.2)).map (·.1))
    (((innerRegions sig q nm e n bytes m off s).filter (·.2)).map (·.1))

theorem narrowT_mem (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes m j off : Nat) (s : State) :
    (narrowT sig q nm e n bytes m j off s).mem = (tagSetupState bytes m j off (allocState bytes s)).mem :=
  rfl

/-- The caller's stack slot `i`, from the frame's base. -/
theorem sa_alloc (bytes i : Nat) (s : State) :
    sa (allocState bytes s).sp (bytes + 4 * i) = stackArgAddr s i := by
  simp only [allocState_sp, sa, stackArgAddr]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem slotPtr_alloc (bytes j : Nat) (s : State) : slotPtr bytes j (allocState bytes s) = stackArg s j := by
  rw [slotPtr, sa_alloc]; rfl

theorem toNat_addr (x : BitVec 32) : (State.addr x).toNat = x.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

section
variable {sig : Sig} {q : Nat} {nmT nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {wa : Bool}
  {stack bytes m j off : Nat}

theorem tagWord_lt (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) :
    tagWord sig q < (armArgs sig s).length := by
  rw [armArgs_length]
  have := Sig.words_split abi.ptrBits hq
  simp only [Sig.words] at this
  rw [this, List.length_append, List.length_cons]; simp only [tagWord]; omega

/-- The arguments and the buffers of the function and of the code: those of
the function around the tag (at `t`), and the code's with the buffer (at
`W`) in its place. -/
theorem tag_bufs (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) (W : Addr) :
    ((armArgs sig s).take (tagWord sig q)).length =
        (Sig.psWords (sig.params.take q) abi.ptrBits).length ∧
      ((armArgs sig s).drop (tagWord sig q + 1)).length =
        (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length ∧
      armArgs sig s = (armArgs sig s).take (tagWord sig q) ++
        (armArgs sig s).getD (tagWord sig q) 0 :: (armArgs sig s).drop (tagWord sig q + 1) ∧
      (armArgs sig s).set (tagWord sig q) W =
        (armArgs sig s).take (tagWord sig q) ++ W :: (armArgs sig s).drop (tagWord sig q + 1) ∧
      Sig.bufs sig.params (armArgs sig s) =
        Sig.bufs (sig.params.take q) ((armArgs sig s).take (tagWord sig q)) ++
          (⟨(armArgs sig s).getD (tagWord sig q) 0, 16⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) ((armArgs sig s).drop (tagWord sig q + 1)) ∧
      Sig.bufs (sig.tagWork q nm e n).params ((armArgs sig s).set (tagWord sig q) W) =
        Sig.bufs (sig.params.take q) ((armArgs sig s).take (tagWord sig q)) ++
          (⟨W, n * e.size⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) ((armArgs sig s).drop (tagWord sig q + 1)) := by
  have hlt := tagWord_lt hq s
  have hlen := armArgs_length sig s
  have hw := Sig.words_split abi.ptrBits hq
  simp only [Sig.words] at hw
  have hl₁ : ((armArgs sig s).take (tagWord sig q)).length =
      (Sig.psWords (sig.params.take q) abi.ptrBits).length := List.length_take_of_le (by omega)
  have hl₂ : ((armArgs sig s).drop (tagWord sig q + 1)).length =
      (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length := by
    rw [List.length_drop, hlen, hw, List.length_append, List.length_cons]; simp only [tagWord]; omega
  have hsplit := List.split_at (vs := armArgs sig s) (k := tagWord sig q) hlt
  have hset : (armArgs sig s).set (tagWord sig q) W =
      (armArgs sig s).take (tagWord sig q) ++ W :: (armArgs sig s).drop (tagWord sig q + 1) := by
    rw [List.set_eq_take_append_cons_drop]
    simp only [hlt, ↓reduceIte]
  refine ⟨hl₁, hl₂, hsplit, hset, ?_, ?_⟩
  · conv => lhs; rw [hsplit]
    exact Sig.bufs_split abi.ptrBits hq _ _ _ hl₁
  · rw [hset]; exact Sig.bufs_tagWork nm e n abi.ptrBits hq _ _ _ hl₁

/-- The stack below the stack pointer, of `stack + bytes` bytes. -/
theorem mem_stackBelow (E : Addr) {k : Nat} (h : 0 < k) :
    (⟨E - BitVec.ofNat 64 k, k⟩ : Region) ∈ stackBelow E k := by
  rw [show k = (k - 1) + 1 by omega]; simp [stackBelow]

/-- What `tagSetup` gives, from a state satisfying the function's
precondition: the run, from the frame's push; and the state the code runs
from, which keeps what the function must keep, passes the arguments with
the buffer in the tag's place, holds the tag in the buffer, and has written
only in the frame. -/
theorem narrowT_facts (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    execBlock isa (tagSetup bytes m j off) (allocState bytes s) =
        some (tagSetupState bytes m j off (allocState bytes s),
          tagSetupTrace bytes m j off (s.sp - BitVec.ofNat 32 bytes) (stackArg s j)) ∧
      (tagSetupState bytes m j off (allocState bytes s)).rd = (allocState bytes s).rd ∧
      (tagSetupState bytes m j off (allocState bytes s)).wr = (allocState bytes s).wr ∧
      (narrowT sig q nm e n bytes m j off s).sp = s.sp - BitVec.ofNat 32 bytes ∧
      (∀ r, r ≠ .r12 → (narrowT sig q nm e n bytes m j off s).gpr r = s.gpr r) ∧
      armArgs (sig.tagWork q nm e n) (narrowT sig q nm e n bytes m j off s) =
        (armArgs sig s).set (tagWord sig q) (tagBuf bytes off s) ∧
      Frame [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩] s.mem
        (narrowT sig q nm e n bytes m j off s).mem ∧
      ∀ i < 16, (narrowT sig q nm e n bytes m j off s).mem (tagBuf bytes off s + BitVec.ofNat 64 i) =
        s.mem (State.addr (stackArg s j) + BitVec.ofNat 64 i) := by
  have hj := hlay.j_lt
  have hgetD := hlay.getD s
  have hN := hlay.1
  obtain ⟨hb1, hb2, -, hoff, -, -, -, ho⟩ := hb
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s 0
  rw [hgetD] at hbO
  rw [pre_arm hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, hres, hnw, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hP : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hbelow := mem_stackBelow (State.addr s.sp) (k := stack + bytes) (by omega)
  have htb : ((⟨State.addr (stackArg s j), 16⟩ : Region), true) ∈ Sig.bufs sig.params (armArgs sig s) := by
    rw [hbO]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have htw : (⟨State.addr (stackArg s j), 16⟩ : Region) ∈ s.wr := by
    rw [hwr]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ htb, rfl⟩, rfl⟩
  have htd : (⟨State.addr (stackArg s j), 16⟩ : Region).Disjoint
      ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ := by
    rw [hP]
    exact (Region.Disjoint.symm (hres _ hbelow _ (List.mem_append_left _ htb))).sub_right
      (Offset.sub_below _ (by omega) (by omega))
  have ht16 : (stackArg s j).toNat + 16 ≤ 2 ^ 32 := by
    have := hnw _ htb
    simp only [toNat_addr] at this
    exact this
  -- The caller's stack arguments are readable.
  have hargs : ∀ i < m, InRegions ((allocState bytes s).rd ++ (allocState bytes s).wr)
      (sa (allocState bytes s).sp (bytes + 4 * i)) 4 := fun i hi => by
    have hmem : (⟨stackArgAddr s 0, nsaa sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, show nsaa sig ≠ 0 by omega]
    refine ⟨⟨stackArgAddr s 0, nsaa sig⟩, List.mem_append_left _ ?_, ?_⟩
    · simp only [allocState_rd, hrd]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
    · rw [sa_alloc]
      show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), nsaa sig⟩ : Region).Contains
        (sa s.sp (4 * i)) 4
      rw [sa_eq (by omega), hN, show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp by simp]
      exact Offset.contains_base _ (by omega) (by omega)
  have hE : (allocState bytes s).sp.toNat = s.sp.toNat - bytes := sub_toNat' (by omega)
  obtain ⟨hrun, hrd', hwr', hsp', hg, hf, hv, hW⟩ := tagSetup_run (bytes := bytes) (m := m) (j := j)
    (off := off) (u := allocState bytes s) (by rw [hE]; omega) hj hb1 hb2 hoff ho hargs
    (List.mem_cons_self ..) (by rw [slotPtr_alloc]; exact ht16)
    (fun k hk => by
      rw [slotPtr_alloc]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ htw),
        Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [slotPtr_alloc]; exact htd)
  rw [slotPtr_alloc] at hrun hW
  refine ⟨hrun, hrd', hwr', hsp', fun r hr => hg r hr, ?_, hf, fun i hi => ?_⟩
  · rw [armArgs, locs, widths_tagWork nm e n hq ⟨_, _, _, _, rfl⟩]
    refine armArgs_tagSet hlay (fun r hr => hg r ?_)
      (fun i hi hij => ?_) ?_
    · intro h; subst h; simp [argRegs] at hr
    · show (tagSetupState bytes m j off (allocState bytes s)).mem.readW
        (State.addr ((tagSetupState bytes m j off (allocState bytes s)).sp + BitVec.ofNat 32 (4 * i))) 32 = _
      rw [hsp']
      exact (hv i hi).trans (by simp only [hij, ↓reduceIte]; rw [sa_alloc]; rfl)
    · show (tagSetupState bytes m j off (allocState bytes s)).mem.readW
        (State.addr ((tagSetupState bytes m j off (allocState bytes s)).sp + BitVec.ofNat 32 (4 * j))) 32 = _
      rw [hsp']
      exact (hv j hj).trans (by simp only [↓reduceIte]; rfl)
  · have := hW i hi
    rw [← sa_eq (sp := (allocState bytes s).sp) (by omega)] at this
    exact this

/-- The relation of `Sig.contract`'s disjointness is symmetric. -/
theorem disj_symm {x y : Region × Bool} (h : (x.2 || y.2) → x.1.Disjoint y.1) :
    (y.2 || x.2) → y.1.Disjoint x.1 :=
  fun hb => (h (by rw [Bool.or_comm]; exact hb)).symm

/-- The function's other buffers, those around the tag. -/
abbrev otherBufs (sig : Sig) (q : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs (sig.params.take q) ((armArgs sig s).take (tagWord sig q)) ++
    Sig.bufs (sig.params.drop (q + 1)) ((armArgs sig s).drop (tagWord sig q + 1))

theorem mem_otherBufs (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s : State}
    {b : Region × Bool} (hb : b ∈ otherBufs sig q s) : b ∈ Sig.bufs sig.params (armArgs sig s) := by
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := "") (e := .u8) (n := 0) hq s 0
  rw [hbO]
  rcases List.mem_append.mp hb with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- The function's buffers lie outside the `stack + bytes` bytes below its
stack pointer. -/
theorem bufs_below {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) (hb0 : 0 < bytes) :
    ∀ a ∈ Sig.bufs sig.params (armArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 x, k⟩ := by
  rw [pre_arm hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  intro a ha x k hx hk
  exact (Region.Disjoint.symm (hres _ (mem_stackBelow _ (by omega)) a (List.mem_append_left _ ha))).sub_right
    (Offset.sub_below _ hx hk)

/-- The tag lies outside the other buffers, and the code's memory agrees
with the function's on them and holds the tag in the buffer (`TagIn`). -/
theorem narrowT_tagIn (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    TagIn (otherBufs sig q s) ((armArgs sig s).getD (tagWord sig q) 0) (tagBuf bytes off s) s.mem
      (narrowT sig q nm e n bytes m j off s).mem ∧
    ∀ b ∈ otherBufs sig q s, b.1.Disjoint ⟨(armArgs sig s).getD (tagWord sig q) 0, 16⟩ := by
  obtain ⟨-, -, -, -, -, -, hf, hW⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb hs hl
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s 0
  have hout := bufs_below hs hl (bytes := bytes) (by omega)
  rw [pre_arm hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hP : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  refine ⟨⟨fun b hb x hx => (hf x fun r hr hc => ?_).symm, by rw [hlay.getD]; exact hW⟩, fun b hb => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hP] at hc
    exact hout b (mem_otherBufs hq hb) (x := bytes) (k := bytes)
      (by omega) (by omega) x hx hc
  · rw [allRegions, hbO, List.pairwise_append, List.pairwise_middle disj_symm] at hpw
    exact (((List.pairwise_cons.mp hpw.1).1 b hb rfl)).symm

theorem allRegions_narrowT (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) (hl : Sig.noLists sig.params = true) :
    allRegions (sig.tagWork q nm e n) (narrowT sig q nm e n bytes m j off s) =
      innerRegions sig q nm e n bytes m off s := by
  obtain ⟨-, -, -, hsp, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb hs hl
  have hm : m ≠ 0 := by have := hlay.j_lt; omega
  rw [allRegions, hargs, innerRegions, argArea, nsaa, widths_tagWork nm e n hq ⟨_, _, _, _, rfl⟩,
    ← nsaa, hlay.1]
  simp only [hm, Nat.mul_eq_zero, false_or, show (4 : Nat) ≠ 0 by decide, ↓reduceIte]
  show _ ++ [((⟨State.addr ((narrowT sig q nm e n bytes m j off s).sp + BitVec.ofNat 32 (4 * 0)), 4 * m⟩ :
    Region), false)] = _
  simp only [hsp, Nat.mul_zero, BitVec.add_zero]

/-- The code's precondition holds in `narrowT`, from the function's. -/
theorem narrowT_pre (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pre
      (narrowT sig q nm e n bytes m j off s) := by
  obtain ⟨-, -, -, hsp, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb hs hl
  have hall := allRegions_narrowT (nm := nm) (e := e) (n := n) hq hlay hb hs hl
  obtain ⟨hin, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hlay hb hs hl
  obtain ⟨hl₁, hl₂, hsplit, hset, hbO, hbI⟩ :=
    tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBuf bytes off s)
  have hout := bufs_below hs hl (bytes := bytes) (by omega)
  have hN := hlay.1
  obtain ⟨hb1, hb2, hb3, -⟩ := hb
  rw [pre_arm hl] at hs
  obtain ⟨⟨hst, hfit⟩, -, -, hpw, -, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hlt := s.sp.isLt
  have hP : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hscr : tagBuf bytes off s = State.addr s.sp - BitVec.ofNat 64 (bytes - off) :=
    sa_sub (by omega) (by omega)
  have hE : (State.addr s.sp).toNat = s.sp.toNat := toNat_addr _
  have hB : ∀ b ∈ otherBufs sig q s, b ∈ Sig.bufs sig.params (armArgs sig s) :=
    fun b hb => mem_otherBufs hq hb
  have hpwB : (otherBufs sig q s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) := by
    rw [allRegions, hbO, List.pairwise_append, List.pairwise_middle disj_symm] at hpw
    exact (List.pairwise_cons.mp hpw.1).2
  have hWB : ∀ b ∈ otherBufs sig q s, (⟨tagBuf bytes off s, n * e.size⟩ : Region).Disjoint b.1 :=
    fun b hb => by rw [hscr]; exact (hout b (hB b hb) (by omega) (by omega)).symm
  refine (pre_arm (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
    (Sig.noLists_tagWork _ _ _ hq hl)).mpr ?_
  rw [hall, hsp, hargs, nsaa, widths_tagWork nm e n hq ⟨_, _, _, _, rfl⟩, ← nsaa, hN]
  refine ⟨⟨.inr ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [sub_toNat' (by omega)]; omega
  · rw [sub_toNat' (by omega)]; omega
  · -- Pairwise disjoint.
    rw [innerRegions, hbI, List.pairwise_append, List.pairwise_middle disj_symm]
    refine ⟨List.pairwise_cons.mpr ⟨fun b hb _ => hWB b hb, hpwB⟩, List.pairwise_singleton _ _,
      fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    rw [hP]
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hout a (hB a (List.mem_append_left _ ha)) (by omega) (by omega)
    · rw [hscr]
      exact below_disjoint _ (stack + bytes) (a := bytes - off) (n := n * e.size) (b := bytes)
        (k := 4 * m) (by omega) (by omega) (.inr (by omega)) (by omega) (by omega)
    · exact hout a (hB a (List.mem_append_right _ ha)) (by omega) (by omega)
  · -- The reserved stack: the stack below the frame.
    intro r hr a ha
    rw [hP, stackBelow_sub] at hr
    by_cases h0 : stack = 0
    · simp [h0] at hr
    simp only [h0, ite_false, List.mem_singleton] at hr; subst hr
    rw [innerRegions, hbI] at ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (ha | rfl | ha) | rfl
    · exact Region.Disjoint.symm (hout a (hB a (List.mem_append_left _ ha)) (by omega) (by omega))
    · rw [hscr]
      exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack)
        (b := bytes - off) (k := n * e.size) (by omega) (by omega) (.inl (by omega))
        (by omega) (by omega)
    · exact Region.Disjoint.symm (hout a (hB a (List.mem_append_right _ ha)) (by omega) (by omega))
    · rw [hP]
      exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack) (b := bytes)
        (k := 4 * m) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
  · -- No buffer wraps around.
    intro a ha
    rw [hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a (hB a (List.mem_append_left _ ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · show (tagBuf bytes off s).toNat + n * e.size ≤ 2 ^ 32
        rw [hscr, toNat_sub64 (by omega), hE]
        omega
      · exact hnw a (hB a (List.mem_append_right _ ha))
  · -- The precondition.
    rw [hset]
    exact ho.pre _ _ _ _ _ _ hl₁ hl₂ hin (by rw [← hsplit]; exact hpr)

/-- What a contract's `leak` says of the values and memory of two runs:
nothing, if it has none. -/
def leakAgree {ws : List ArgWord} : Option (Curry ws (Mem → List Nat)) → List (BitVec 64) → Mem →
    List (BitVec 64) → Mem → Prop
  | none, _, _, _, _ => True
  | some f, vs₁, m₁, vs₂, m₂ => Curry.apply ws f vs₁ m₁ = Curry.apply ws f vs₂ m₂

/-- The public data of a contract, by where AAPCS passes the arguments. -/
theorem pubL_arm {s₁ s₂ : State} (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.sp = s₂.sp ∧ leakAgree leak (armArgs sig s₁) s₁.mem (armArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((armArgs sig s₁).getD i 0).setWidth ((widths sig).getD i 64) =
          ((armArgs sig s₂).getD i 0).setWidth ((widths sig).getD i 64) := by
  simp only [Sig.contract]
  rw [args_arm]
  simp only [Sig.descs_of_noLists _ _ _ hl, List.not_mem_nil, false_implies, implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

theorem getD_set_ne {l : List (BitVec 64)} {k i : Nat} {a : BitVec 64} (h : k ≠ i) :
    (l.set k a).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_self {l : List (BitVec 64)} {k : Nat} {a : BitVec 64} (h : k < l.length) :
    (l.set k a).getD k 0 = a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self h, Option.getD_some]

/-- The function's public data is the code's public data in `narrowT`. -/
theorem narrowT_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pub
      (narrowT sig q nm e n bytes m j off s₁) (narrowT sig q nm e n bytes m j off s₂) := by
  rw [pubL_arm hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  obtain ⟨-, -, -, e₁, -, a₁, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb h₁ hl
  obtain ⟨-, -, -, e₂, -, a₂, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb h₂ hl
  obtain ⟨t₁, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hlay hb h₁ hl
  obtain ⟨t₂, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hlay hb h₂ hl
  obtain ⟨l₁, l₁', s₁', st₁, -, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s₁ (tagBuf bytes off s₁)
  obtain ⟨l₂, l₂', s₂', st₂, -, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s₂ (tagBuf bytes off s₂)
  have p₁ := ((pre_arm hl).mp h₁).2.2.2.2.2.2
  rw [s₁'] at p₁
  have p₂ := ((pre_arm hl).mp h₂).2.2.2.2.2.2
  rw [s₂'] at p₂
  refine (pubL_arm (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
    (Sig.noLists_tagWork _ _ _ hq hl)).mpr ⟨⟨by rw [e₁, e₂, hsp], ?_⟩, fun i hi => ?_⟩
  · rw [a₁, a₂, st₁, st₂]
    have hol := ho.leak
    revert hlk hol
    cases leak <;> cases leakI <;> simp only [leakAgree, imp_self, implies_true, false_implies]
    rename_i f g
    intro hlk hol
    rw [hol _ _ _ _ _ _ l₁ l₁' t₁ p₁, hol _ _ _ _ _ _ l₂ l₂' t₂ p₂, ← s₁', ← s₂']
    exact hlk
  · rw [Sig.pubs_tagWork _ _ _ hq] at hi
    rw [a₁, a₂, widths_tagWork nm e n hq ⟨_, _, _, _, rfl⟩]
    by_cases hik : tagWord sig q = i
    · subst hik
      rw [getD_set_self (tagWord_lt hq s₁), getD_set_self (tagWord_lt hq s₂), tagBuf, tagBuf, hsp]
    · rw [getD_set_ne hik, getD_set_ne hik]
      exact hpa i hi

/-- The tag pointer is public. -/
theorem tag_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    stackArg s₁ j = stackArg s₂ j := by
  obtain ⟨-, hpa⟩ := (pubL_arm hl).mp hp
  have hpub : (sig.params.flatMap (·.2.pubs)).getD (tagWord sig q) false = true := by
    conv => lhs; rw [Sig.params_split hq]
    rw [List.flatMap_append, List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Sig.pubs_length _ abi.ptrBits]),
      Sig.pubs_length _ abi.ptrBits]
    simp only [tagWord, Nat.sub_self]
    rfl
  have hw : (widths sig).getD (tagWord sig q) 64 = 32 := by
    rw [widths, Sig.words_split _ hq, List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_map])]
    simp [ArgWord.bits, abi]
  have h := hpa _ hpub
  rw [hw, hlay.getD, hlay.getD] at h
  simpa [State.addr] using h

/-! ## The run -/

/-- Every region of the code's contract is one of the function's buffers,
the working space, or the copy of the stack arguments. -/
theorem mem_innerRegions (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s : State}
    {a : Region × Bool} (ha : a ∈ innerRegions sig q nm e n bytes m off s) :
    a ∈ Sig.bufs sig.params (armArgs sig s) ∨ a = (⟨tagBuf bytes off s, n * e.size⟩, true) ∨
      a = (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), 4 * m⟩, false) := by
  obtain ⟨-, -, -, -, hbO, hbI⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBuf bytes off s)
  rw [innerRegions, hbI] at ha
  rw [hbO]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (ha | rfl | ha) | rfl
  · exact .inl (List.mem_append_left _ ha)
  · exact .inr (.inl rfl)
  · exact .inl (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  · exact .inr (.inr rfl)

/-- A run of the code from `narrowT s` is a run of `withTagScratch` from
`s`, after `tagSetup`'s accesses and before `tagOut`'s, which keeps what the
calling convention requires, whose memory is the code's with the buffer's
first 16 bytes copied to the tag, and whose `r0` and `r1` are the code's. -/
theorem withTagScratch_run {c : Prog isa} (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n) (hd : armStack c ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowT sig q nm e n bytes m j off s) t s₃)
    (ha : abiPreserved (narrowT sig q nm e n bytes m j off s) s₃) (hl : Sig.noLists sig.params = true) :
    ∃ s', Exec isa (withTagScratch bytes m j off c) s
        (tagSetupTrace bytes m j off (s.sp - BitVec.ofNat 32 bytes) (stackArg s j) ++
          (t ++ tagOutAll bytes j off (s.sp - BitVec.ofNat 32 bytes) (stackArg s j))) s' ∧
      abiPreserved s s' ∧
      TagOut ((armArgs sig s).getD (tagWord sig q) 0) (tagBuf bytes off s) s₃.mem s'.mem ∧
      s'.gpr .r0 = s₃.gpr .r0 ∧ s'.gpr .r1 = s₃.gpr .r1 := by
  obtain ⟨hrun, hrd', hwr', hsp, hg, -, hf, -⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb hs hl
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBuf bytes off s)
  have hout := bufs_below hs hl (bytes := bytes) (by omega)
  have hj := hlay.j_lt
  have hN := hlay.1
  rw [hlay.getD] at hbO ⊢
  obtain ⟨hb1, hb2, hb3, hoff, hb5, hb6, hb7, ho⟩ := hb
  rw [pre_arm hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, hpw, -, hnw, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hlt := s.sp.isLt
  have hP : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hscr : tagBuf bytes off s = State.addr s.sp - BitVec.ofNat 64 (bytes - off) :=
    sa_sub (by omega) (by omega)
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by omega, hb5, hb6, hb7, by omega⟩
  -- The regions of `narrowT`: the buffers, and the frame's buffer and arguments.
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨State.addr s.sp - BitVec.ofNat 64 a, k⟩]
        (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := fun ha hk =>
    Covers.one ⟨_, List.mem_cons_self .., by
      rw [hP]; exact Offset.contains_below _ ha hk (by omega)⟩
  have hbufR : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (((innerRegions sig q nm e n bytes m off s).filter (·.2)).map (·.1))
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega) (by omega)
    · simp at hf'
  have hcovR : Covers (((innerRegions sig q nm e n bytes m off s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (by simpa only [hP] using hF (a := bytes) (k := 4 * m) (by omega) (by omega))
  have hw := Exec.widen he (rd := s.rd)
    (wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowT sig q nm e n bytes m j off s).withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) =
      tagSetupState bytes m j off (allocState bytes s) by
    rw [narrowT, State.withRegions_withRegions, ← allocState_rd bytes s, ← hrd',
      show ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr = (allocState bytes s).wr
        from rfl, ← hwr', State.withRegions_self]] at hw
  -- What the code leaves: the caller's slot, and `sp`.
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans hsp
  have hfs := Exec.frameSp he (by rw [hsp, sub_toNat' (by omega)]; omega)
  rw [hsp] at hfs
  have hslotA : sa (s.sp - BitVec.ofNat 32 bytes) (bytes + 4 * j) = State.addr s.sp + BitVec.ofNat 64 (4 * j) := by
    rw [show sa (s.sp - BitVec.ofNat 32 bytes) (bytes + 4 * j) = stackArgAddr s j from sa_alloc bytes j s,
      stackArgAddr]
    exact addr_add (by omega)
  have hslotR : Region.Sub ⟨State.addr s.sp + BitVec.ofNat 64 (4 * j), 4⟩ ⟨stackArgAddr s 0, nsaa sig⟩ := by
    show Region.Sub _ ⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), nsaa sig⟩
    rw [hN, show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp by simp]
    exact Offset.sub_base _ (by omega)
  have hslot₃ : s₃.mem.readW (State.addr s.sp + BitVec.ofNat 64 (4 * j)) 32 = stackArg s j := by
    rw [hfs.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide),
      hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · show s.mem.readW _ 32 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32
      rw [addr_add (by omega)]
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hP]
      exact Offset.disjoint_below _ (by omega)
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        rcases mem_innerRegions hq ha with ha | rfl | rfl
        · -- A writable buffer, separate from the stack arguments.
          have h3 := (List.pairwise_append.mp hpw).2.2 a ha (⟨stackArgAddr s 0, nsaa sig⟩, false)
            (by simp [argArea, show nsaa sig ≠ 0 by omega]) (by simp [hf'])
          exact h3.symm.sub_left hslotR
        · rw [hscr]
          exact (Offset.disjoint_below _ (n := bytes - off) (d := 4 * j) (k := 4) (by omega)).sub_right
            (Region.sub_prefix (by omega))
        · simp at hf'
      · simp only [List.mem_singleton] at hr; subst hr
        show Region.Disjoint _
          ⟨State.addr (s.sp - BitVec.ofNat 32 bytes - BitVec.ofNat 32 (armStack c)), armStack c⟩
        rw [addr_sub' (by rw [sub_toNat' (by omega)]; omega), hP, BitVec.sub_sub, ← BitVec.ofNat_add]
        exact (Offset.disjoint_below _ (n := bytes + armStack c) (d := 4 * j) (k := 4)
          (by omega)).sub_right (Region.sub_prefix (by omega))
  -- `tagOut`, with the function's regions and the frame.
  have htb : ((⟨State.addr (stackArg s j), 16⟩ : Region), true) ∈ Sig.bufs sig.params (armArgs sig s) := by
    rw [hbO]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have htw := hbufW _ htb rfl
  have ht16 : (stackArg s j).toNat + 16 ≤ 2 ^ 32 := by
    have := hnw _ htb
    simp only [toNat_addr] at this
    exact this
  have hArd : (⟨stackArgAddr s 0, nsaa sig⟩ : Region) ∈ s.rd := by
    have hmem : (⟨stackArgAddr s 0, nsaa sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, show nsaa sig ≠ 0 by omega]
    rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hareaC : (⟨stackArgAddr s 0, nsaa sig⟩ : Region).Contains
      (State.addr s.sp + BitVec.ofNat 64 (4 * j)) 4 := by
    show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), nsaa sig⟩ : Region).Contains _ 4
    rw [hN, show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp by simp]
    exact Offset.contains_base _ (by omega) (by omega)
  have hW64 : tagBuf bytes off s = State.addr (s.sp - BitVec.ofNat 32 bytes) + BitVec.ofNat 64 off :=
    sa_eq (by rw [sub_toNat' (by omega)]; omega)
  have htd : (⟨tagBuf bytes off s, 16⟩ : Region).Disjoint ⟨State.addr (stackArg s j), 16⟩ := by
    rw [hscr]
    exact (hout _ htb (x := bytes - off) (k := 16) (by omega) (by omega)).symm
  have hsl : slotPtr bytes j (s₃.withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)) = stackArg s j := by
    simp only [slotPtr, State.withRegions_sp, State.withRegions_mem, hsp₃, hslotA, hslot₃]
  obtain ⟨w', hto, sp', rd', wr', g', mem'⟩ := tagOut_run (bytes := bytes) (j := j) (off := off)
    (w := s₃.withRegions s.rd (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr))
    (D := tagBuf bytes off s) (T := State.addr (stackArg s j)) (by omega) (by omega)
    (by
      simp only [State.withRegions_sp, State.withRegions_rd, State.withRegions_wr, hsp₃, hslotA]
      exact ⟨_, List.mem_append_left _ hArd, hareaC⟩)
    (fun k hk => by
      simp only [State.withRegions_sp, hsp₃]
      rw [hW64, Offset.add_add]
      exact sa_eq (by rw [sub_toNat' (by omega)]; omega))
    (fun k hk => by rw [hsl]; exact addr_add (by omega)) htd
    (fun k hk => ⟨_, List.mem_append_right _ (List.mem_cons_self ..), by
      rw [hW64, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun k hk => ⟨_, List.mem_cons_of_mem _ htw, Offset.contains_base _ (by omega) (by omega)⟩)
  rw [hsl] at hto
  simp only [State.withRegions_sp, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, State.withRegions_gpr, hsp₃] at hto sp' rd' wr' g' mem'
  -- The pop.
  have hpop : isa.pop (.free bytes) (allocState bytes s) w' =
      some { w' with sp := w'.sp + BitVec.ofNat 32 bytes, wr := w'.wr.tail } := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by omega, hb5, hb6, hb7, by rw [sp']; rfl, by rw [wr']; rfl, rfl⟩
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) (Exec.seq hw (Exec.block hto))) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  obtain ⟨fo, fv⟩ := copyWords_facts (M := s₃.mem) (dst := State.addr (stackArg s j))
    (src := tagBuf bytes off s) 4 (by decide) htd
  rw [← mem'] at fo fv
  refine ⟨_, hex, ⟨fun r hr => ?_, ?_⟩, ⟨fun x hx => fo x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hx, fv⟩, ?_, ?_⟩
  · have hr2 : r ≠ .r2 ∧ r ≠ .r12 := by
      revert hr; simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    show w'.gpr r = s.gpr r
    rw [g' r hr2.1 hr2.2, ha.1 r hr, hg r hr2.2]
  · show w'.sp + BitVec.ofNat 32 bytes = s.sp
    rw [sp', BitVec.sub_add_cancel]
  · exact g' _ (by decide) (by decide)
  · exact g' _ (by decide) (by decide)

/-- Code verified for a function whose parameter `q` is working space that
also carries a 16-byte tag in its first 16 bytes (`Sig.tagWork`), with
`stack` bytes of stack, is verified for the function whose parameter `q` is
the tag, which allocates the working space in a frame of `bytes` more bytes
of stack (`withTagScratch`), if the two contracts are related by
`Sig.TagFrame`. AAPCS passes the tag pointer in stack slot `j` of the `m`
slots of stack arguments (`hlay`, decidable); the buffer is at `sp + off` in
the frame (`hb`); the code's frames use at most `stack` bytes (`hd`). -/
theorem Verified.tagScratch {c : Prog isa}
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI))
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hlay : TagLayout sig q m j) (hb : TagFits m off bytes e n) (hd : armStack c ≤ stack)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withTagScratch bytes m j off c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  -- Every run is `tagSetup`, the code's run from `narrowT`, and `tagOut`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowT sig q nm e n bytes m j off s) t s₃ ∧
      ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).post
        (narrowT sig q nm e n bytes m j off s) s₃ ∧
      ∃ s', Exec isa (withTagScratch bytes m j off c) s
          (tagSetupTrace bytes m j off (s.sp - BitVec.ofNat 32 bytes) (stackArg s j) ++
            (t ++ tagOutAll bytes j off (s.sp - BitVec.ofNat 32 bytes) (stackArg s j))) s' ∧
        abiPreserved s s' ∧
        TagOut ((armArgs sig s).getD (tagWord sig q) 0) (tagBuf bytes off s) s₃.mem s'.mem ∧
        s'.gpr .r0 = s₃.gpr .r0 ∧ s'.gpr .r1 = s₃.gpr .r1 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq'⟩ := hcor _ (narrowT_pre hq hlay hb ho hs hl)
    exact ⟨t, s₃, he, hq', withTagScratch_run hq hlay hb hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hpost, s', hex, ha, hto, h0, h1⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_arm]
    have hq' := (post_arm (sig := sig.tagWork q nm e n) (pre := preI) (post := postI)
      (leak := leakI)).mp hpost
    obtain ⟨-, -, -, -, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hlay hb hs hl
    obtain ⟨hl₁, hl₂, hsplit, hset, -, -⟩ :=
      tag_bufs (nm := nm) (e := e) (n := n) hq s (tagBuf bytes off s)
    obtain ⟨hin, hdis⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hlay hb hs hl
    have hpr := ((pre_arm hl).mp hs).2.2.2.2.2.2
    rw [hsplit] at hpr
    rw [hargs, hset] at hq'
    rw [h0, h1, hsplit]
    exact ho.post _ _ _ _ _ _ _ _ _ hl₁ hl₂ hin hpr hdis hto hq'
  · obtain ⟨u₁, r₁, f₁, -, _, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, _, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_arm hl).mp hp).1.1, tag_pub hq hlay hp hl,
      hct _ _ _ _ _ _ (narrowT_pre hq hlay hb ho h₁ hl) (narrowT_pre hq hlay hb ho h₂ hl)
        (narrowT_pub hq hlay hb ho h₁ h₂ hp hl) f₁ f₂]

end

/-- `withTagScratch` writes `sp` only in its frame: no modelled instruction
writes it. -/
theorem withTagScratch_spSafe (bytes m j off : Nat) (c : Prog isa) :
    (withTagScratch bytes m j off c).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

end VG.Arm
