module

import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `CmacAes.Stream.X86_64.AbsorbBlocks`, which only this module used -/

section

@[expose] public section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb`'s saved registers

`absorb` saves the six callee-saved registers it uses at `scratch + 2176`,
where the functions it calls do not write, and restores them at the end.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat readW_writeW_other)

/-- The memory after saving the registers at `S + 2176`. -/
def absSavedMem (s : State) (S : Addr) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (S + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem absSaved_read (s : State) (S : Addr) :
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .rbx ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .rbp ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .r12 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2200) 64 = s.gpr .r13 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2208) 64 = s.gpr .r14 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2216) 64 = s.gpr .r15 := by
  simp only [absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2224) :
    (⟨b + BitVec.ofNat 64 2176, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2176) + BitVec.ofNat 64 (d - 2176) from
    (Offset.add_add_eq b (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 48⟩] s.mem (absSavedMem s S) := by
  simp only [absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide)))

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .r9 = S)
    (hw : ∀ d, 2176 ≤ d → d + 8 ≤ 2224 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r13 = s.gpr .rcx ∧
      s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = S ∧ s'.gpr .rdx = s.gpr .rdx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rdx == 0) ∧
      s'.mem = absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, saved, sOff, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat, hS, Nat.reduceAdd,
      hw 2176 (by decide) (by decide), hw 2184 (by decide) (by decide), hw 2192 (by decide) (by decide),
      hw 2200 (by decide) (by decide), hw 2208 (by decide) (by decide), hw 2216 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
    BitVec.and_self, hS]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  simp only [absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 2176 ≤ d → d + 8 ≤ 2224 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 2192) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 2200) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 2208) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 2216) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, restore, saved, sOff, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.map_some, hb, Nat.reduceAdd,
      hr 2176 (by decide) (by decide), hr 2184 (by decide) (by decide), hr 2192 (by decide) (by decide),
      hr 2200 (by decide) (by decide), hr 2208 (by decide) (by decide), hr 2216 (by decide) (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, mem_setReg]

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (16 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega_using [this]

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega_using [this]

/-! ## Arithmetic on registers -/

theorem sub16 {h : Nat} (hh : h ≤ 16) :
    BitVec.setWidth 64 (16 : BitVec 32) - BitVec.ofNat 64 h = BitVec.ofNat 64 (16 - h) :=
  Offset.ofNat_sub_ofNat hh

/-- `16 nb` for the data left `x > 0`, as `sub 1; mov; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - 1 - ((BitVec.ofNat 64 x - 1) &&& 15) = BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : (BitVec.ofNat 64 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega_using []

theorem shr4 {n : Nat} (hn : 16 * n < 2 ^ 64) :
    BitVec.ofNat 64 (16 * n) >>> 4 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hn]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .rdx = BitVec.ofNat 64 c)
    (hz : s.zf = some (s.gpr .rdx == 0)) :
    WP isa held s fun s' => s'.gpr .rax = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by show s.zf = _; rw [hz, hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
    exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by show s.zf = _; rw [hz, hd, beq_eq_false_iff_ne.mpr hne]) (fun h => by cases h)
      fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
        Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, hd, sx1, sx15]
    refine ⟨by rw [held_bv _ hne, toNat_ofNat hc], fun r h => by simp [h], trivial, trivial, trivial⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : Addr} {c L : Nat} (hL : L < 2 ^ 64) (hax : s.gpr .rax = BitVec.ofNat 64 (held c))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hbx : s.gpr .rbx = St) :
    WP isa fill s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 (288 + held c) ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hh := held_le c
  obtain ⟨s₁, run₁, rcx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (.imm 16),
      .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - held c) ∧ s₁.cf = some (decide (L < 16 - held c)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, cf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, hax, h14, sub16 hh,
      toNat_ofNat hL, toNat_ofNat (show 16 - held c < 2 ^ 64 by omega_using [])]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hl : L < 16 - held c
    · refine WP.ite true (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
      refine ⟨by rw [g₁ _ (by decide), h14, fOf, Nat.min_eq_left (by omega_using [hl])],
        fun r h => by simp [h, g₁ r h], m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.block_nil ⟨by rw [rcx₁, fOf, Nat.min_eq_right (by omega_using [hl])], g₁, m₁, rd₁, wr₁⟩
  · obtain ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g₂ _ (by decide : Reg.rbx ≠ .rcx),
      g₂ _ (by decide : Reg.rax ≠ .rcx), hbx, hax, sx288, rcx₂]
    refine ⟨trivial, by rw [BitVec.add_assoc, ← BitVec.ofNat_add], fun r h₁ h₂ => by simp [h₂, g₂ r h₁],
      m₂, rd₂, wr₂⟩

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h13 : s.gpr .r13 = D) (hcx : s.gpr .rcx = BitVec.ofNat 64 f) (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (hbx : s.gpr .rbx = St) (h15 : s.gpr .r15 = S) :
    WP isa chain1 s fun s' => s'.gpr .r13 = D + BitVec.ofNat 64 f ∧ s'.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .rdi = St ∧
      s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = St + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s'.gpr .r9 = S ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r13₁, r14₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.alu .add .r13 (.reg .rcx),
      .mov32 .r8 (.imm 0), .alu .sub .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r13 = D + BitVec.ofNat 64 f ∧ s₁.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .r8 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L - f = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_setReg, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h14, hcx,
      Offset.ofNat_sub_ofNat hf, beq_zero_iff, toNat_ofNat (show L - f < 2 ^ 64 by omega_using [hL])]
    exact ⟨trivial, trivial, rfl, trivial, fun r a b c => by simp [a, b, c], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r8 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r8₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, h0, ↓reduceIte]
      exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · obtain ⟨r8₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .r13) (b : r ≠ .r14) (c : r ≠ .r8) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g _ (by decide : Reg.rbx ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.rbp ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.r15 ≠ .r13) (by decide) (by decide), hbx, h15, sx272, sx288,
      g₂ _ (by decide : Reg.r13 ≠ .r8), g₂ _ (by decide : Reg.r14 ≠ .r8), r13₁, r14₁, r8₂]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, fun r hr a b => ?_,
      by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .rdi = s.gpr .rbx ∧
      s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = s.gpr .r13 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r12 (.imm 0),
      .alu .test .r14 (.reg .r14)] s = some s₁ ∧ s₁.gpr .r12 = BitVec.ofNat 64 0 ∧
      s₁.zf = some (decide (x = 0)) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h14, BitVec.and_self,
      beq_zero_iff, toNat_ofNat hx]
    exact ⟨rfl, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .r12 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .r12 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_
    fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r12₁]; simp [h0], fun r h _ => g₁ r h, m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
          Option.bind_some]
        rfl, ?_⟩
      simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, reduceCtorEq, h0, ↓reduceIte, g₁ _ (by decide : Reg.r14 ≠ .r12), h14,
        sx1, sx15]
      exact ⟨nb16_bv (by omega_using [h0]) hx, fun r a b => by simp [a, b, g₁ r a], m₁, rd₁, wr₁⟩
  · obtain ⟨r12₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, BitVec.reduceSignExtend, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, execShift, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
      rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags, ite_true, reduceCtorEq, ite_false,
      g₂ _ (by decide : Reg.rbx ≠ .r12) (by decide), g₂ _ (by decide : Reg.rbp ≠ .r12) (by decide),
      g₂ _ (by decide : Reg.r13 ≠ .r12) (by decide), g₂ _ (by decide : Reg.r15 ≠ .r12) (by decide), r12₂]
    refine ⟨trivial, shr4 (by split <;> omega_arith), trivial, trivial, trivial, trivial, trivial,
      fun r hr a => ?_, m₂, rd₂, wr₂⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h13 : s.gpr .r13 = D + BitVec.ofNat 64 a) (h12 : s.gpr .r12 = BitVec.ofNat 64 (16 * n))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .r13 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 288 ∧
      s'.gpr .rcx = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [rest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
    wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h12, h14, sx288, Offset.ofNat_sub_ofNat hn]
  refine ⟨by rw [BitVec.add_assoc, ← BitVec.ofNat_add], trivial, trivial, trivial, fun r hr a b => ?_,
    trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end VG.Proof.CmacAes.Stream.X86_64

end

end


@[expose] public section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch pointer `S`, the writable working space `Z` (which holds the
registers saved at `S + 2176`) and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (Z : Region) (L R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = D
  r8 : (s₀.gpr .r8).toNat = L
  r9 : s₀.gpr .r9 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, Z]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint Z
  d_s : (⟨D, L⟩ : Region).Disjoint Z
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, L⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint Z
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, L⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint Z
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : Z.base.toNat + Z.len ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  slot : ∃ o, S + BitVec.ofNat 64 2176 = Z.base + BitVec.ofNat 64 o ∧ o + 48 ≤ Z.len

theorem APre.of {s₀ : State} (h : absorbX86_64.pre s₀) :
    APre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) ⟨s₀.gpr .r9, 2304⟩ (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, ⟨2176, rfl, by simp⟩⟩

/-- A slot of the saved registers lies within them. -/
theorem slot_in (S : Addr) {d n : Nat} (h₁ : 2176 ≤ d) (h : d + n ≤ 2224) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S + BitVec.ofNat 64 2176, 48⟩ := by
  obtain e : S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (d - 2176) := by
    rw [Offset.add_add, Nat.add_sub_cancel' h₁]
  rw [e]; exact Offset.sub_base _ (by omega_using [h, h₁])

section
variable {s₀ : State} {St D S : Addr} {Z : Region} {L R : Nat} (hp : APre s₀ St D S Z L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r8]; exact BitVec.isLt _

theorem APre.r8' : s₀.gpr .r8 = BitVec.ofNat 64 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.r8, toNat_ofNat hp.lt])

theorem APre.rsi' : s₀.gpr .rsi = BitVec.ofNat 64 R := rsi_ofNat hp.rsi hp.rounds

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

/-- A slot of the saved registers, at an offset of `Z`. -/
theorem APre.slotAt {d : Nat} (h₁ : 2176 ≤ d) :
    ∃ o, S + BitVec.ofNat 64 d = Z.base + BitVec.ofNat 64 (o + (d - 2176)) ∧ o + 48 ≤ Z.len := by
  obtain ⟨o, e, le⟩ := hp.slot
  refine ⟨o, ?_, le⟩
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (d - 2176) by
    rw [Offset.add_add, Nat.add_sub_cancel' h₁], e, Offset.add_add]

/-- A slot of the saved registers lies within `Z`. -/
theorem APre.slotSub {d n : Nat} (h₁ : 2176 ≤ d) (h : d + n ≤ 2224) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ Z := by
  obtain ⟨o, e, le⟩ := hp.slotAt h₁
  rw [e]; exact Offset.sub_base _ (by omega_using [le, h, h₁])

theorem APre.slot48 : Region.Sub ⟨S + BitVec.ofNat 64 2176, 48⟩ Z := hp.slotSub (by decide) (by decide)

theorem APre.inS {d n : Nat} (h₁ : 2176 ≤ d) (h : d + n ≤ 2224) (hn : 0 < n := by decide) :
    InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]
  obtain ⟨o, e, le⟩ := hp.slotAt h₁
  have := hp.wS
  rw [e]
  exact ⟨Z, by simp, Offset.contains_base _ (by omega_using [le, h, h₁]) (by omega_using [le, h, h₁, hn, this])⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hrdi : s.gpr .rdi = St)
    (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdx : s.gpr .rdx = St + BitVec.ofNat 64 272) (hrcx : s.gpr .rcx = Dd)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (hr9 : s.gpr .r9 = S) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint Z)
    (hstk : (below (s₀.gpr .rsp) 16).Disjoint ⟨Dd, 16 * n⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, Z] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgsZ s St (St + BitVec.ofNat 64 272) Dd S Z R n := by
  have hw := hp.wSt
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { rdi := hrdi, rdx := hrdx, rcx := hrcx, r8 := hr8, r9 := hr9, rounds := hp.rounds, hn := hn
    rsi := by rw [hrsi]; exact hp.rsi'
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    wz := hp.st_s.sub_left (Region.sub_prefix (by decide))
    dc := hdc, dz := hds
    cz := hp.st_s.sub_left c272
    stkW := by rw [hsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkD := by rw [hsp]; exact hstk
    stkC := by rw [hsp]; exact hp.stk_st.sub_right c272
    stkZ := by rw [hsp]; exact hp.stk_s
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapZ := hp.wS
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
    zw := by
      rw [hwr, hp.wr]
      exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (Z : Region) (L R : Nat) (s : State) : Prop where
  args : UArgsZ s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S Z R (b1Of (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .rdx).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {Z : Region} {L R : Nat} (hp : APre s₀ St D S Z L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S Z L R) := by
  generalize hc : (s₀.gpr .rdx).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hdx : s₀.gpr .rdx = BitVec.ofNat 64 c := BitVec.eq_of_toNat_eq (by rw [hc, toNat_ofNat hcl])
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r13₁, r14₁, r15₁, rdx₁, rsp₁, zf₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.r9 fun d h₁ h => hp.inS h₁ h
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [rdx₁, hdx]) (by rw [zf₁, rdx₁])) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) hL ax₂ (by rw [g₂ _ (by decide), r14₁, hp.r8'])
    (by rw [g₂ _ (by decide), rbx₁, hp.rdi])) fun s₃ ⟨cx₃, dx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c, g₂ r a]
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (L := fOf c L) (by omega_using [hfh])
    (by rw [g _ (by decide) (by decide) (by decide), r13₁, hp.rcx]) dx₃ cx₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by
      rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  have g' (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) (d : r ≠ .r10) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a d, g r a b c]
  refine WP.mono (chain1_wp hfL hL (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r13₁, hp.rcx])
    (by rw [h₄.other _ (by decide) (by decide), cx₃])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r14₁, hp.r8'])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), rbx₁, hp.rdi])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r15₁])) fun s₅ h₅ => ?_
  obtain ⟨r13₅, r14₅, r8₅, rdi₅, rsi₅, rdx₅, rcx₅, r9₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r13) (b : r ≠ .r14) : s₅.gpr r = s₁.gpr r := by
    rw [sv₅ r hr a b, g' r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  obtain hsp : s₅.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rsp₁]
  obtain hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_using []
  obtain c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hb1])
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs rdi₅ (by rw [rsi₅, g' _ (by decide) (by decide) (by decide) (by decide), rbp₁]) rdx₅ rcx₅
      (by rw [r8₅, b1Of, leftOf]) r9₅ hsp hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      (hp.st_s.sub_left c288)
      (hp.stk_st.sub_right c288) (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_using [hb1]⟩,
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbx₁, hp.rdi],
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbp₁],
    r13₅, by rw [r14₅]; rfl, by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), r15₁], hsp, m₀, hrd,
    hwr⟩

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.X86_64 (UpdateImpl bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

/-- A region disjoint from every region of a frame is unchanged. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := bytesAt_frame hf hd hn

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- `absorb` over the calls `hcall`, for any working space they need. -/
theorem absorb_wpG {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S (Zf S) L R) :
    WP isa (absorb u) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64.post s₀ s' := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, rbx₅, rbp₅, r13₅, r14₅, r15₅, rsp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ r13₅ r14₅ m₅
  refine WP.seq (WP.mono (hcall.call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ _ (by simp [calleeSaved]), r14₅])) fun s₇ h₇ => ?_)
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s₅.gpr r := by rw [sv₇ r hr a, k₆ r hr]
  obtain hsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₅]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_using [hsum])
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [rdi₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rsi₇, k₆ _ (by simp [calleeSaved]), rbp₅])
    (by rw [rdx₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rcx₇, k₆ _ (by simp [calleeSaved]), r13₅]) r8₇
    (by rw [r9₇, k₆ _ (by simp [calleeSaved]), r15₅]) hsp₇ (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c272).symm.sub_left dD)
    (hp.d_s.sub_left dD) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.seq (WP.mono (hcall.call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ calleeSaved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  obtain ⟨s₉, run₉, r13₉, r14₉, rdx₉, rcx₉, sv₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D) (a := fOf c L)
    (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r13₅])
    (by rw [k₈ _ (by simp [calleeSaved]), r12₇])
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r14₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by unfold restOf nbOf leftOf; split <;> omega_arith)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_using [hL, hsum]) r13₉
    (by rw [rdx₉, k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), rbx₅]) rcx₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by unfold restOf nbOf leftOf at hi; split at hi <;> omega_arith))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  obtain r15₁₀ : s₁₀.gpr .r15 = S := by
    rw [h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
      k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r15₅]
  obtain ⟨s₁₁, run₁₁, rbx₁₁, rbp₁₁, r12₁₁, r13₁₁, r14₁₁, r15₁₁, rsp₁₁, m₁₁⟩ := restore_ok s₁₀ r15₁₀
    (fun d h₁ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) h₁ h
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨S + BitVec.ofNat 64 2176, 48⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  obtain f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, Xf S, below (s₀.gpr .rsp) 16] s₅.mem s₆.mem := by
    rw [← rsp₅]; exact h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, Xf S, below (s₀.gpr .rsp) 16] s₆.mem s₈.mem := by
    rw [← hsp₇, ← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 48⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, Xf S, below (s₀.gpr .rsp) 16, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  obtain hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  -- The key, the data and the return address are in none of these.
  obtain dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right hp.slot48
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (hcall.sub S)
    · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
  obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right hp.slot48
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (hcall.sub S)
    · exact hp.stk_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
  obtain dRet : ∀ r ∈ K, (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right hp.slot48
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
    · exact hp.ret_s.sub_right (hcall.sub S)
    · exact Offset.base_disjoint_below _ (by decide)
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega_using [hrr]))
  obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, F11.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  · -- The registers, restored from their slots.
    obtain Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2224) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ (Zf S) := hp.slotSub h₁ h₂
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact (hcall.slotX S).sub_left (slot_in S h₁ h₂)
      · exact hp.stk_s.symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := absSaved_read s₀ S
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₁₁, slot 2176 (by decide) (by decide), a₁]
    · rw [rbp₁₁, slot 2184 (by decide) (by decide), a₂]
    · rw [rsp₁₁, h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
        k₈ _ (by simp [calleeSaved]), hsp₇]
    · rw [r12₁₁, slot 2192 (by decide) (by decide), a₃]
    · rw [r13₁₁, slot 2200 (by decide) (by decide), a₄]
    · rw [r14₁₁, slot 2208 (by decide) (by decide), a₅]
    · rw [r15₁₁, slot 2216 (by decide) (by decide), a₆]
  · intro key msg hr hR hcnt hlen
    rw [hp.rdi] at hr ⊢
    rw [hp.rcx, hp.r8]
    rw [hp.r8] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    obtain hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    obtain hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_using [h]
    obtain hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [frame_bytes hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb]), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, frame_bytes hf dDat (by omega_using [hlen])]
    obtain fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [frame_bytes fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right hp.slot48)
          (by decide)]
    obtain cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      frame_bytes fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega_using [hw]) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hh]))).sub_right hp.slot48)
          (by omega_using [hh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hsum])
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hsum, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfL', this]) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, Xf S, below (s₀.gpr .rsp) 16],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (hcall.sub S)
          · exact (hp.stk_st.sub_right sub).symm
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, frame_bytes f8 dj (by omega_using [hfh, hfL']), frame_bytes f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

theorem absorb_wp (v : UpdateImpl) {s₀ : State} (h0 : absorbX86_64.pre s₀) :
    WP isa (absorb v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64.post s₀ s' :=
  absorb_wpG (ACall.base v) (APre.of h0)

end VG.Proof.CmacAes.Stream.X86_64
