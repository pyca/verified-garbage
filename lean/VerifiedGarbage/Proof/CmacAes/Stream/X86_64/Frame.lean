module

public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Init
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.AbsorbF
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Init
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.AbsorbF
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
meta import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `CmacAes.Stream.X86_64.Verified`, which only this module used -/

section

/-! ### `CmacAes.Stream.X86_64.AbsorbCorrect`, which only this module used -/

section

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

end

end

@[expose] public section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_finish`

The code copies the chaining value to `out`, computes the number of bytes held
back, and calls `vg_cmac_aes_finalize` with the state as its key and `out` as
its state: its result is the MAC of the message the state represents
(`repr_finish`). The code before the call is constant time by the taint
analysis, and the call by its own proof (`fin_rel`), its arguments pinned by
`HMid`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (ScrSub scrSub_ok scrSub_rel)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
pointer `S`, the rounds `R` and the writable working space `Z`: all of it
(`finishX86_64`), or all but its first 512 bytes (`finishS_wp`). -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) (Z : Region) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = O
  r8 : s₀.gpr .r8 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, Z]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint Z
  o_s : (⟨O, 16⟩ : Region).Disjoint Z
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint Z
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_o : (below (s₀.gpr .rsp) 16).Disjoint ⟨O, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint Z
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wZ : Z.base.toNat + Z.len ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishX86_64.pre s₀) :
    HPre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat ⟨s₀.gpr .r8, 2304⟩ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-! ## Before the call -/

theorem finishPre_ok {s₀ : State} {St O S : Addr} {R : Nat} {Z : Region} (hp : HPre s₀ St O S R Z) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = s₀.gpr .rsi ∧
      s₁.gpr .rdx = O ∧ s₁.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s₁.gpr .r8 = s₀.gpr .rdx ∧
      s₁.gpr .r9 = S ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (s₀.gpr .rdx == 0) ∧
      s₁.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega_arith)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, finishPre, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, 
      hp.rdi, hp.rcx, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide), inO 8 (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
    BitVec.and_self, hp.rdi, hp.r8]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [copyMem, k0, Offset.add_add]

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (Z : Region) (s : State) : Prop where
  args : FArgsZ s St O (St + BitVec.ofNat 64 288) S Z (held (s₀.gpr .rdx).toNat) R
  mem : s.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272)
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} {Z : Region} (hp : HPre s₀ St O S R Z)
    (hL : L ≤ 16) (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = O)
    (rcx : s.gpr .rcx = St + BitVec.ofNat 64 288) (r8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r9 : s.gpr .r9 = S) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgsZ s St O (St + BitVec.ofNat 64 288) S Z L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  exact
  { rdi := rdi, rdx := rdx, rcx := rcx, r8 := r8, r9 := r9
    rsi := by rw [rsi]; exact rsi_ofNat hp.rsi hp.rounds
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    kz := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    pz := hp.st_s.sub_left pSt
    stz := hp.o_s
    stkK := by rw [rsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkP := by rw [rsp]; exact hp.stk_st.sub_right pSt
    stkSt := by rw [rsp]; exact hp.stk_o
    stkZ := by rw [rsp]; exact hp.stk_s
    wrapK := by omega_arith
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapZ := hp.wZ
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
    zw := by
      rw [wr, hp.wr]; exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr] }

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} {Z : Region} (hp : HPre s₀ St O S R Z) :
    WP isa finPre s₀ (HMid s₀ St O S R Z) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rdx).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ ?_ r9₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, r8₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, r8₁, sx1, sx15]
    have hne : s₀.gpr .rdx ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .r8 := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ (held_bv _ hne) r9₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

/-! ## The whole function -/

/-- `finish` over the calls `T` of `vg_cmac_aes_finalize`, with the working
space `Z S`. -/
theorem finish_wpG {c : Impl.Aes.X86_64.Ctr32} {sfx : String} {Z X : Addr → Region} (T : HCall c sfx Z X)
    {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R (Z S)) :
    WP isa (finish c sfx) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' := by
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (T.call h₁.args) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The state is unchanged before the call.
  have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
      Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
    rw [h₁.mem]
    exact bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St hd)) (by omega_arith)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 16⟩, X S, below (s₀.gpr .rsp) 16] s₀.mem s₂.mem := by
      refine ((h₁.mem ▸ copyMem_frame _ _ _ : Frame [⟨O, 16⟩] s₀.mem s₁.mem).mono (by simp)).trans ?_
      rw [← rsp₁]; exact h₂.frame
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s.sub_right (T.sub S)
    · exact Offset.base_disjoint_below _ (by decide)
  · intro key msg hr hR hc hlen
    rw [hp.rdi] at hr
    -- `St + 240` and the others, as offsets.
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .rdx).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    rw [hp.rcx]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_arith)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem]; exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .rdx).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

theorem finish_wp (v : Ctr32Impl) {s₀ : State} (h0 : finishX86_64.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' :=
  finish_wpG (HCall.base v) (HPre.of h0)

/-! ## Constant time -/

theorem finish_relG {c : Impl.Aes.X86_64.Ctr32} {sfx : String} {Z X : Addr → Region} (T : HCall c sfx Z X)
    {s₀ s₀' : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R (Z S)) (hp' : HPre s₀' St O S R (Z S))
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (q4 : s₀.gpr .rdx = s₀'.gpr .rdx) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish c sfx) fun _ _ => True := by
  have q2 : s₀.gpr .rdi = s₀'.gpr .rdi := by rw [hp.rdi, hp'.rdi]
  have q3 : s₀.gpr .rsi = s₀'.gpr .rsi := BitVec.eq_of_toNat_eq (by rw [hp.rsi, hp'.rsi])
  have q5 : s₀.gpr .rcx = s₀'.gpr .rcx := by rw [hp.rcx, hp'.rcx]
  have q6 : s₀.gpr .r8 = s₀'.gpr .r8 := by rw [hp.r8, hp'.r8]
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := HMid s₀ St O S R (Z S)) (F₂ := HMid s₀' St O S R (Z S)) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := T.rel (P := fun s₁ s₂ => HMid s₀ St O S R (Z S) s₁ ∧ HMid s₀' St O S R (Z S) s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finish_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finishX86_64.pre s₀)
    (h0' : finishX86_64.pre s₀') (hq : finishX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp' : HPre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat ⟨s₀.gpr .r8, 2304⟩ := by
    rw [q2, q3, q5, q6]; exact HPre.of h0'
  exact finish_relG (HCall.base v) (HPre.of h0) hp' q1 q4

theorem finish_ct (v : Ctr32Impl) :
    ConstantTime isa finishX86_64.pre finishX86_64.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Without the first 512 bytes of the working space (`finishS`) -/

/-- `finishX86_64` with a scratch buffer of 1792 bytes, for `finishS`. -/
def finishX86_64S : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let out : Region := ⟨s.gpr .rcx, 16⟩
    let scr : Region := ⟨s.gpr .r8, 1792⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 1792 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := finishX86_64.post
  pub := finishX86_64.pub

/-- `HPre` after the `sub`, with the 1792 bytes of the scratch buffer as all
of the working space but its first 512 bytes. -/
theorem HPre.ofS {s₀ s₁ : State} (h : finishX86_64S.pre s₀) (a : ScrSub .r8 s₀ s₁) :
    HPre s₁ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8 - BitVec.ofNat 64 512) (s₀.gpr .rsi).toNat
      ⟨s₀.gpr .r8 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512, 1792⟩ := by
  obtain ⟨r8₁, g₁, -, rd₁, wr₁⟩ := a
  obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p⟩ := h
  have eS : s₀.gpr .r8 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512 = s₀.gpr .r8 := BitVec.sub_add_cancel _ _
  have sp := g₁ .rsp (by decide)
  rw [eS]
  exact ⟨g₁ _ (by decide), g₁ _ (by decide), r8₁, by rw [g₁ _ (by decide)], by rw [sp]; exact a,
    by rw [rd₁]; exact b, by rw [wr₁]; exact c, d, e, f, by rw [sp]; exact g, by rw [sp]; exact h',
    by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l, m, n, o, p⟩

theorem finishS_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) {s₀ : State}
    (h0 : finishX86_64S.pre s₀) :
    WP isa (finishS v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64S.post s₀ s' := by
  obtain ⟨s₁, run₁, a⟩ := scrSub_ok .r8 s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := HPre.ofS h0 a
  obtain ⟨-, g₁, m₁, -, -⟩ := a
  refine WP.mono (finish_wpG (HCall.small v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · simp only [finishX86_64S, finishX86_64] at hpost ⊢
    rw [m₁, g₁ .rdi (by decide), g₁ .rsi (by decide), g₁ .rdx (by decide), g₁ .rcx (by decide)] at hpost
    exact hpost

theorem finishS_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    ConstantTime isa finishX86_64S.pre finishX86_64S.pub (finishS v.callee v.suffix) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have r : RelCT isa (fun t₁ t₂ => ∃ a b, (a = s₀ ∧ b = s₀') ∧ ScrSub .r8 a t₁ ∧ ScrSub .r8 b t₂)
      (finish v.callee v.suffix) fun _ _ => True := by
    rintro x y t t' x' y' ⟨_, _, ⟨rfl, rfl⟩, a₁, a₂⟩ ex ey
    have hp := HPre.ofS h₁ a₁
    have hp' := HPre.ofS h₂ a₂
    rw [← q2, ← q3, ← q5, ← q6] at hp'
    exact finish_relG (HCall.small v f) hp hp' (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q1])
      (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q4]) _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact (((scrSub_rel .r8).seq r) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Without working space for `vg_aes_ctr32` (`finishF`) -/

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPreF (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = O
  r8 : s₀.gpr .r8 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 16⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 16⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 16⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 16⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_o : (below (s₀.gpr .rsp) 16).Disjoint ⟨O, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 16⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 16 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPreF.of {s₀ : State} (h : finishX86_64F.pre s₀) :
    HPreF s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-! ## Before the call -/

theorem finishPreF_ok {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPreF s₀ St O S R) :
    ∃ s₁, runBlock isa finishPreF s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = s₀.gpr .rsi ∧
      s₁.gpr .rdx = O ∧ s₁.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s₁.gpr .r8 = s₀.gpr .rdx ∧
      s₁.gpr .r9 = S - BitVec.ofNat 64 2048 ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (s₀.gpr .rdx == 0) ∧
      s₁.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega_arith)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, finishPreF, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, 
      hp.rdi, hp.rcx, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide), inO 8 (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
    BitVec.and_self, hp.rdi, hp.r8]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [copyMem, k0, Offset.add_add]

/-- What the code before the call leaves. -/
structure HMidF (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgsF s St O (St + BitVec.ofNat 64 288) (S - BitVec.ofNat 64 2048) (held (s₀.gpr .rdx).toNat) R
  mem : s.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272)
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPreF.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : HPreF s₀ St O S R) (hL : L ≤ 16)
    (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = O)
    (rcx : s.gpr .rcx = St + BitVec.ofNat 64 288) (r8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r9 : s.gpr .r9 = S - BitVec.ofNat 64 2048) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd)
    (wr : s.wr = s₀.wr) :
    FArgsF s St O (St + BitVec.ofNat 64 288) (S - BitVec.ofNat 64 2048) L R := by
  have hw := hp.wSt
  have e : S - BitVec.ofNat 64 2048 + BitVec.ofNat 64 2048 = S := BitVec.sub_add_cancel _ _
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  exact
  { rdi := rdi, rdx := rdx, rcx := rcx, r8 := r8, r9 := r9
    rsi := by rw [rsi]; exact rsi_ofNat hp.rsi hp.rounds
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := by rw [e]; exact hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := by rw [e]; exact hp.st_s.sub_left pSt
    sts := by rw [e]; exact hp.o_s
    stkK := by rw [rsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkP := by rw [rsp]; exact hp.stk_st.sub_right pSt
    stkSt := by rw [rsp]; exact hp.stk_o
    stkS := by rw [rsp, e]; exact hp.stk_s
    wrapK := by omega_arith
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapS := by rw [e]; exact hp.wS
    reads := by
      rw [rd, wr, hp.rd, hp.wr, e]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 16⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr, e]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 16⟩, by simp, 0, by simp, by simp⟩ }

theorem finPreF_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPreF s₀ St O S R) :
    WP isa finPreF s₀ (HMidF s₀ St O S R) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPreF_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rdx).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ ?_ r9₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, r8₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, r8₁, sx1, sx15]
    have hne : s₀.gpr .rdx ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .r8 := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ (held_bv _ hne) r9₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

/-! ## The whole function -/

/-- `finish_wp`, over an implementation of `vg_aes_ctr32` that needs no
working space. -/
theorem finishF_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ : State}
    (h0 : finishX86_64F.pre s₀) :
    WP isa (finishF v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64F.post s₀ s' := by
  have hp := HPreF.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rcx = O at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPreF_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_callF v f _ h₁.args) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The state is unchanged before the call.
  have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
      Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
    rw [h₁.mem]
    exact bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St hd)) (by omega_arith)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 16⟩, ⟨S, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s₂.mem := by
      refine ((h₁.mem ▸ copyMem_frame _ _ _ : Frame [⟨O, 16⟩] s₀.mem s₁.mem).mono (by simp)).trans ?_
      have := h₂.frame
      rw [BitVec.sub_add_cancel] at this
      rw [← rsp₁]; exact this
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
    · exact Offset.base_disjoint_below _ (by decide)
  · intro key msg hr hR hc hlen
    rw [hp.rdi] at hr
    -- `St + 240` and the others, as offsets.
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .rdx).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    rw [hp.rcx]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_arith)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem]; exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .rdx).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finishF_rel (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ s₀' : State}
    (h0 : finishX86_64F.pre s₀) (h0' : finishX86_64F.pre s₀') (hq : finishX86_64F.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finishF v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := HPreF.of h0
  have hp' : HPreF s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6]; exact HPreF.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) finPreF h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := HMidF s₀ _ _ _ _) (F₂ := HMidF s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPreF_wp hp, finPreF_wp hp'⟩
  have c := fin_relF v f ("vg_cmac_aes_finalize" ++ v.suffix) (P := fun s₁ s₂ =>
      HMidF s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₁ ∧
      HMidF s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finishF_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ConstantTime isa finishX86_64F.pre finishX86_64F.pub (finishF v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finishF_rel v f h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to values of the public arguments
(`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S (Zf S) L R s) :
    WP isa (.call u.name u.code) s
      (AAfter₁ s₀ St D S L) :=
  WP.mono (hcall.call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₆.saved _ (by simp [calleeSaved]), h.rbp],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r13], by rw [h₆.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r15], by rw [h₆.saved _ (by simp [calleeSaved]), h.rsp],
      by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (Z : Region) (L R : Nat) (s : State) : Prop where
  args : UArgsZ s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)) S Z R
    (nbOf (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {Z : Region} {L R : Nat} (hp : APre s₀ St D S Z L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S Z L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨rbx₆, rbp₆, r13₆, r14₆, r15₆, rsp₆, rd₆, wr₆⟩ := h
  rw [hc] at r13₆ r14₆
  refine WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith) r14₆) fun s₇ h₇ => ?_
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s.gpr r := sv₇ r hr a
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L), 16 * nbOf (s₀.gpr .rdx).toNat L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_arith)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)) (n := nbOf (s₀.gpr .rdx).toNat L)
    (by rw [rdi₇, rbx₆]) (by rw [rsi₇, rbp₆]) (by rw [rdx₇, rbx₆]) (by rw [rcx₇, r13₆]) r8₇
    (by rw [r9₇, r15₆]) (by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]) (by rw [rd₇, rd₆])
    (by rw [wr₇, wr₆]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    (hp.d_s.sub_left dD) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : nbOf (s₀.gpr .rdx).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .rdx).toNat L, rfl, by simp; omega_arith⟩,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rbx₆], r12₇,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r13₆], by rw [k₇ _ (by simp [calleeSaved]) (by decide), r14₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r15₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S

theorem call2_after {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S (Zf S) L R s) :
    WP isa (.call u.name u.code) s
      (AAfter₂ s₀ St D S L) :=
  WP.mono (hcall.call h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₈.saved _ (by simp [calleeSaved]), h.r12],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r13], by rw [h₈.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r15]⟩

/-- `absorb` over the calls `hcall` is constant time, for runs from two
states with the same public arguments. -/
theorem absorb_relG {u : Impl.CmacAes.X86_64.Update} {Zf Xf : Addr → Region} (hcall : ACall u Zf Xf)
    {s₀ s₀' : State} {St D S : Addr} {L R : Nat}
    (hp : APre s₀ St D S (Zf S) L R) (hp' : APre s₀' St D S (Zf S) L R)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (q3 : s₀.gpr .rsi = s₀'.gpr .rsi) (q4 : s₀.gpr .rdx = s₀'.gpr .rdx) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb u) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r13, .r14, .r15, .rsp]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .r12, .r13, .r14, .r15]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hp.rdi, hp'.rdi]
      · exact q3
      · exact q4
      · rw [hp.rcx, hp'.rcx]
      · rw [hp.r8', hp'.r8']
      · rw [hp.r9, hp'.r9]
      · exact q1) hA).wp
    (F₁ := AMid₁ s₀ St D S (Zf S) L R) (F₂ := AMid₁ s₀' St D S (Zf S) L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩
  have c₁ := (hcall.rel (P := fun a b => AMid₁ s₀ St D S (Zf S) L R a ∧ AMid₁ s₀' St D S (Zf S) L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h =>
      ⟨call1_after hcall h.1, call1_after hcall h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp, q3]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := AMid₂ s₀ St D S (Zf S) L R) (F₂ := AMid₂ s₀' St D S (Zf S) L R) fun a b h =>
      ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (hcall.rel (P := fun a b => AMid₂ s₀ St D S (Zf S) L R a ∧ AMid₂ s₀' St D S (Zf S) L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after hcall h.1, call2_after hcall h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.r12, h.2.r12, q4]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_rel (v : UpdateImpl) {s₀ s₀' : State} (h0 : absorbX86_64.pre s₀) (h0' : absorbX86_64.pre s₀')
    (hq : absorbX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp' : APre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) ⟨s₀.gpr .r9, 2304⟩ (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6, q7]; exact APre.of h0'
  exact absorb_relG (ACall.base v) (APre.of h0) hp' q1 q3 q4

theorem absorb_ct (v : UpdateImpl) :
    ConstantTime isa absorbX86_64.pre absorbX86_64.pub (absorb v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with 16 bytes of stack: the return addresses of the
call of a CMAC function and of its call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl subkeys_mx finalize_mx subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs,
    ekCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.expandMxcsr, subkeys_mx v]
  decide +kernel

theorem absorb_mx (v : UpdateImpl) : (absorb v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.allInstrs, v.mxcsr]
  decide +kernel

theorem finish_mx (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_mx v]; decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all,
    ekCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.expandSpSafe, subkeys_spSafe v]
  decide +kernel

theorem absorb_spSafe (v : UpdateImpl) :
    (absorb v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.all, v.spSafe]
  decide +kernel

theorem finish_spSafe (v : Ctr32Impl) :
    (finish v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finish, finPre, lastLen, Code.all, finalize_spSafe v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

theorem absorb_correct (v : UpdateImpl) (s : State) (hs : absorbX86_64.pre s) :
    ∃ t s', Exec isa (absorb v.callee) s t s' ∧ abiPreserved s s' ∧ absorbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorb_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorb_mx v) he hg, hp⟩

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishX86_64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finish_mx v) he hg, hp⟩

theorem initF_mx (v : Ctr32Impl) :
    (initF ekF v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h : ekF.code.allInstrs (fun i => !loadsMxcsr i) = true := Ctr32Impl.aesni.expandMxcsr
  simp only [initF, init, Code.allInstrs,
    ekCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) h, subkeys_mx v]
  decide +kernel

theorem initF_spSafe (v : Ctr32Impl) :
    (initF ekF v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h : ekF.code.all (fun i => !X86_64.isa.writesSp i) = true := Ctr32Impl.aesni.expandSpSafe
  simp only [initF, init, Code.all,
    ekCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) h, subkeys_spSafe v]
  decide +kernel

theorem initF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : initX86_64F.pre s) :
    ∃ t s', Exec isa (initF ekF v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (initF_mx v) he hg, hp⟩

theorem finishF_mx (v : Ctr32Impl) : (finishF v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finishF, finPreF, lastLen, Code.allInstrs, finalize_mx v]; decide +kernel

theorem finishF_spSafe (v : Ctr32Impl) :
    (finishF v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finishF, finPreF, lastLen, Code.all, finalize_spSafe v]; decide +kernel

theorem finishF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : finishX86_64F.pre s) :
    ∃ t s', Exec isa (finishF v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finishF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finishF_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 16 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (initScratchContract X86_64.abi 16) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, initX86_64, X86_64.abi,
      X86_64.argRegs] [initSat] using initSat)

/-- `vg_cmac_aes_init` with `scratch: *mut [u64; 19]`, for `initF`. -/
def initScratchSigF : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 19)]

/-- `aesInitContract`, whatever `scratch` is (of 19 words). -/
def initScratchContractF {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigF.contract A
    (pre := fun state key keyLen _scratch => Spec.Cmac.aesInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => Spec.Cmac.aesInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, with 152 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 152⟩] }

theorem initF_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target (initF ekF v.callee v.suffix) (initScratchContractF X86_64.abi 16) :=
  Verified.of_correct (initF_correct v f) (initF_ct v f) (by
    sig_implies [initScratchContractF, initScratchSigF, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initX86_64F, initX86_64, X86_64.abi, X86_64.argRegs] [initSatF, initSat] using initSatF)

theorem initS_mx (v : Ctr32Impl) :
    (initS v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [initS, Code.allInstrs, init_mx v]; decide +kernel

theorem initS_spSafe (v : Ctr32Impl) :
    (initS v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [initS, Code.all, init_spSafe v]; decide +kernel

theorem initS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : initX86_64S.pre s) :
    ∃ t s', Exec isa (initS v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧
      initX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (initS_mx v) he hg, hp⟩

/-- `vg_cmac_aes_init` with `scratch: *mut [u64; 224]`, for `initS`. -/
def initScratchSigS : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 224)]

/-- `aesInitContract`, whatever `scratch` is (of 224 words). -/
def initScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigS.contract A
    (pre := fun state key keyLen _scratch => Spec.Cmac.aesInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => Spec.Cmac.aesInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, with 1792 bytes of
working space. -/
def initSatS : State := { initSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 1792⟩] }

theorem initS_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target (initS v.expand v.callee v.suffix) (initScratchContractS X86_64.abi 16) :=
  Verified.of_correct (initS_correct v f) (initS_ct v f) (by
    sig_implies [initScratchContractS, initScratchSigS, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initX86_64S, initX86_64, X86_64.abi, X86_64.argRegs] [initSatS, initSat] using initSatS)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : UpdateImpl) :
    Verified X86_64.target (absorb v.callee) (absorbScratchContract X86_64.abi 16) :=
  Verified.of_correct (absorb_correct v) (absorb_ct v) (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, absorbX86_64, X86_64.abi,
      X86_64.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x2000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified X86_64.target (finish v.callee v.suffix) (finishScratchContract X86_64.abi 16) :=
  Verified.of_correct (finish_correct v) (finish_ct v) (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, finishX86_64, X86_64.abi,
      X86_64.argRegs] [finishSat] using finishSat)

theorem finishS_mx (v : Ctr32Impl) :
    (finishS v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finishS, Code.allInstrs, finish_mx v]; decide +kernel

theorem finishS_spSafe (v : Ctr32Impl) :
    (finishS v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finishS, Code.all, finish_spSafe v]; decide +kernel

theorem finishS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : finishX86_64S.pre s) :
    ∃ t s', Exec isa (finishS v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finishS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finishS_mx v) he hg, hp⟩

/-- `vg_cmac_aes_finish` with `scratch: *mut [u64; 224]`, for `finishS`. -/
def finishScratchSigS : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("out", .array true .u8 16),
    ("scratch", .array true .u64 224)]

/-- `aesFinishContract`, whatever `scratch` is (of 224 words). -/
def finishScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSigS.contract A
    (pre := fun state rounds count out _scratch => Spec.Cmac.aesFinishPre A.ptrBits state rounds count out)
    (post := fun state rounds count out _scratch => Spec.Cmac.aesFinishPost A.ptrBits state rounds count out)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, with 1792 bytes
of working space. -/
def finishSatS : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 1792⟩] }

theorem finishS_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target (finishS v.callee v.suffix) (finishScratchContractS X86_64.abi 16) :=
  Verified.of_correct (finishS_correct v f) (finishS_ct v f) (by
    sig_implies [finishScratchContractS, finishScratchSigS, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishX86_64S, finishX86_64, X86_64.abi, X86_64.argRegs] [finishSatS, finishSat] using finishSatS)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, with 16 bytes of
working space. -/
def finishSatF : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 16⟩] }

theorem finishF_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target (finishF v.callee v.suffix) (finishScratchContractF X86_64.abi 16) :=
  Verified.of_correct (finishF_correct v f) (finishF_ct v f) (by
    sig_implies [finishScratchContractF, finishScratchSigF, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishX86_64F, finishX86_64, X86_64.abi, X86_64.argRegs] [finishSatF, finishSat] using finishSatF)

end VG.Proof.CmacAes.Stream.X86_64

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` without working space

Over an implementation of `vg_cmac_aes_update` that never touches its
scratch buffer (`UpdateFree`), `absorbF` is given `scratch - 2176`, so its
own scratch buffer is only the 48 bytes of the registers it saves
(`absorbX86_64F`): the proof is `absorb`'s over those calls
(`ACall.free`), after the `sub`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl UpdateFree)

/-- `absorbX86_64` with a scratch buffer of 48 bytes, for `absorbF`. -/
def absorbX86_64F : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 48 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := absorbX86_64.post
  pub := absorbX86_64.pub

/-- The `sub` before `absorb`. -/
theorem subA_ok (s₀ : State) :
    ∃ s₁, runBlock isa [.alu .sub .r9 (.imm (BitVec.ofNat 32 2176))] s₀ = some s₁ ∧
      s₁.gpr .r9 = s₀.gpr .r9 - BitVec.ofNat 64 2176 ∧ (∀ r, r ≠ .r9 → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  refine ⟨_, by simp only [runBlock_cons, exec, readSrc, execAlu]; rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ↓reduceIte]
  exact ⟨by rw [show BitVec.signExtend 64 (BitVec.ofNat 32 2176) = BitVec.ofNat 64 2176 by decide],
    fun r h => by simp [h], trivial, trivial, trivial⟩

/-- `APre` after the `sub`, with the 48 bytes of the scratch buffer as the
working space. -/
theorem APre.ofF {s₀ s₁ : State} (h : absorbX86_64F.pre s₀)
    (r9₁ : s₁.gpr .r9 = s₀.gpr .r9 - BitVec.ofNat 64 2176) (g₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s₀.gpr r)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    APre s₁ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9 - BitVec.ofNat 64 2176)
      ⟨s₀.gpr .r9 - BitVec.ofNat 64 2176 + BitVec.ofNat 64 2176, 48⟩ (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
  obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p⟩ := h
  have eS : s₀.gpr .r9 - BitVec.ofNat 64 2176 + BitVec.ofNat 64 2176 = s₀.gpr .r9 := BitVec.sub_add_cancel _ _
  have sp := g₁ .rsp (by decide)
  rw [eS]
  exact ⟨g₁ _ (by decide), g₁ _ (by decide), by rw [g₁ _ (by decide)], r9₁, by rw [g₁ _ (by decide)],
    by rw [sp]; exact a, by rw [rd₁]; exact b, by rw [wr₁]; exact c, d, e, f, by rw [sp]; exact g,
    by rw [sp]; exact h', by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l,
    m, n, o, p, ⟨0, by rw [eS, BitVec.add_zero], by simp⟩⟩

theorem absorbF_wp (v : UpdateImpl) (f : UpdateFree v.callee) {s₀ : State} (h0 : absorbX86_64F.pre s₀) :
    WP isa (absorbF v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64F.post s₀ s' := by
  obtain ⟨s₁, run₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := subA_ok s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := APre.ofF h0 r9₁ g₁ rd₁ wr₁
  refine WP.mono (absorb_wpG (ACall.free v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · simp only [absorbX86_64F, absorbX86_64] at hpost ⊢
    rw [m₁, g₁ .rdi (by decide), g₁ .rsi (by decide), g₁ .rdx (by decide), g₁ .rcx (by decide),
      g₁ .r8 (by decide)] at hpost
    exact hpost

/-- What the `sub` before `absorb` leaves. -/
def SubA (s₀ s : State) : Prop :=
  s.gpr .r9 = s₀.gpr .r9 - BitVec.ofNat 64 2176 ∧ (∀ r, r ≠ .r9 → s.gpr r = s₀.gpr r) ∧
    s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

theorem absorbF_ct (v : UpdateImpl) (f : UpdateFree v.callee) :
    ConstantTime isa absorbX86_64F.pre absorbX86_64F.pub (absorbF v.callee) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block [.alu .sub .r9 (.imm (BitVec.ofNat 32 2176))]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SubA s₀) (F₂ := SubA s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, r, h⟩ := subA_ok a
      obtain ⟨_, r', h'⟩ := subA_ok b
      exact ⟨WP.of_runBlock ⟨_, r, h⟩, WP.of_runBlock ⟨_, r', h'⟩⟩
  have r : RelCT isa (fun a b => SubA s₀ a ∧ SubA s₀' b) (absorb v.callee) fun _ _ => True := by
    intro x y t t' x' y' ⟨⟨r9₁, g₁, _, rd₁, wr₁⟩, ⟨r9₂, g₂, _, rd₂, wr₂⟩⟩ ex ey
    have hp := APre.ofF h₁ r9₁ g₁ rd₁ wr₁
    have hp' := APre.ofF h₂ r9₂ g₂ rd₂ wr₂
    rw [← q2, ← q5, ← q6, ← q7, ← q3] at hp'
    exact absorb_relG (ACall.free v f) hp hp' (by rw [g₁ _ (by decide), g₂ _ (by decide), q1])
      (by rw [g₁ _ (by decide), g₂ _ (by decide), q3]) (by rw [g₁ _ (by decide), g₂ _ (by decide), q4])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact ((a.mono (fun _ _ h => h) fun _ _ h => h.2).seq r _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem absorbF_mx (v : UpdateImpl) : (absorbF v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorbF, Code.allInstrs, absorb_mx v]; decide +kernel

theorem absorbF_spSafe (v : UpdateImpl) :
    (absorbF v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorbF, Code.all, absorb_spSafe v]; decide +kernel

theorem absorbF_correct (v : UpdateImpl) (f : UpdateFree v.callee) (s : State) (hs : absorbX86_64F.pre s) :
    ∃ t s', Exec isa (absorbF v.callee) s t s' ∧ abiPreserved s s' ∧ absorbX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorbF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorbF_mx v) he hg, hp⟩

/-- `vg_cmac_aes_absorb` with `scratch: *mut [u64; 6]`, for `absorbF`. -/
def absorbScratchSigF : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 6)]

/-- `aesAbsorbContract`, whatever `scratch` is (of 6 words). -/
def absorbScratchContractF {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSigF.contract A
    (pre := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPre A.ptrBits state rounds count data len)
    (post := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPost A.ptrBits state rounds count data len)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, with 48 bytes of
working space. -/
def absorbSatF : State := { absorbSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 48⟩] }

theorem absorbF_verified (v : UpdateImpl) (f : UpdateFree v.callee) :
    Verified X86_64.target (absorbF v.callee) (absorbScratchContractF X86_64.abi 16) :=
  Verified.of_correct (absorbF_correct v f) (absorbF_ct v f) (by
    sig_implies [absorbScratchContractF, absorbScratchSigF, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbX86_64F, absorbX86_64, X86_64.abi, X86_64.argRegs] [absorbSatF, absorbSat] using absorbSatF)

/-! ## `vg_cmac_aes_absorb` without the first 512 bytes of the working space

Over an implementation of `vg_cmac_aes_update` that never touches the first
512 bytes of its scratch buffer (`UpdateSmall`), `absorbS` is given
`scratch - 512`, so its own scratch buffer is 512 bytes smaller
(`absorbX86_64S`): the proof is `absorb`'s over those calls
(`ACall.small`), after the `sub`. -/

open VG.Proof.CmacAes.X86_64 (UpdateSmall ScrSub scrSub_ok scrSub_rel)

/-- `absorbX86_64` with a scratch buffer of 1792 bytes, for `absorbS`. -/
def absorbX86_64S : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 1792⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 1792 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := absorbX86_64.post
  pub := absorbX86_64.pub

/-- `APre` after the `sub`, with the 1792 bytes of the scratch buffer as all
of the working space but its first 512 bytes. -/
theorem APre.ofS {s₀ s₁ : State} (h : absorbX86_64S.pre s₀) (a : ScrSub .r9 s₀ s₁) :
    APre s₁ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9 - BitVec.ofNat 64 512)
      ⟨s₀.gpr .r9 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512, 1792⟩ (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
  obtain ⟨r9₁, g₁, -, rd₁, wr₁⟩ := a
  obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p⟩ := h
  have eS : s₀.gpr .r9 - BitVec.ofNat 64 512 + BitVec.ofNat 64 512 = s₀.gpr .r9 := BitVec.sub_add_cancel _ _
  have sp := g₁ .rsp (by decide)
  rw [eS]
  exact ⟨g₁ _ (by decide), g₁ _ (by decide), by rw [g₁ _ (by decide)], r9₁, by rw [g₁ _ (by decide)],
    by rw [sp]; exact a, by rw [rd₁]; exact b, by rw [wr₁]; exact c, d, e, f, by rw [sp]; exact g,
    by rw [sp]; exact h', by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l,
    m, n, o, p, ⟨1664, sub_add_ofNat _ (by decide), by simp⟩⟩

theorem absorbS_wp (v : UpdateImpl) (f : UpdateSmall v.callee) {s₀ : State} (h0 : absorbX86_64S.pre s₀) :
    WP isa (absorbS v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64S.post s₀ s' := by
  obtain ⟨s₁, run₁, a⟩ := scrSub_ok .r9 s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := APre.ofS h0 a
  obtain ⟨-, g₁, m₁, -, -⟩ := a
  refine WP.mono (absorb_wpG (ACall.small v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · simp only [absorbX86_64S, absorbX86_64] at hpost ⊢
    rw [m₁, g₁ .rdi (by decide), g₁ .rsi (by decide), g₁ .rdx (by decide), g₁ .rcx (by decide),
      g₁ .r8 (by decide)] at hpost
    exact hpost

theorem absorbS_ct (v : UpdateImpl) (f : UpdateSmall v.callee) :
    ConstantTime isa absorbX86_64S.pre absorbX86_64S.pub (absorbS v.callee) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have r : RelCT isa (fun t₁ t₂ => ∃ a b, (a = s₀ ∧ b = s₀') ∧ ScrSub .r9 a t₁ ∧ ScrSub .r9 b t₂)
      (absorb v.callee) fun _ _ => True := by
    rintro x y t t' x' y' ⟨_, _, ⟨rfl, rfl⟩, a₁, a₂⟩ ex ey
    have hp := APre.ofS h₁ a₁
    have hp' := APre.ofS h₂ a₂
    rw [← q2, ← q5, ← q6, ← q7, ← q3] at hp'
    exact absorb_relG (ACall.small v f) hp hp' (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q1])
      (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q3])
      (by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), q4]) _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact (((scrSub_rel .r9).seq r) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem absorbS_mx (v : UpdateImpl) : (absorbS v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorbS, Code.allInstrs, absorb_mx v]; decide +kernel

theorem absorbS_spSafe (v : UpdateImpl) :
    (absorbS v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorbS, Code.all, absorb_spSafe v]; decide +kernel

theorem absorbS_correct (v : UpdateImpl) (f : UpdateSmall v.callee) (s : State) (hs : absorbX86_64S.pre s) :
    ∃ t s', Exec isa (absorbS v.callee) s t s' ∧ abiPreserved s s' ∧ absorbX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorbS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorbS_mx v) he hg, hp⟩

/-- `vg_cmac_aes_absorb` with `scratch: *mut [u64; 224]`, for `absorbS`. -/
def absorbScratchSigS : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 224)]

/-- `aesAbsorbContract`, whatever `scratch` is (of 224 words). -/
def absorbScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSigS.contract A
    (pre := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPre A.ptrBits state rounds count data len)
    (post := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPost A.ptrBits state rounds count data len)
    (stack := stack)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, with 1792 bytes
of working space. -/
def absorbSatS : State := { absorbSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, 1792⟩] }

theorem absorbS_verified (v : UpdateImpl) (f : UpdateSmall v.callee) :
    Verified X86_64.target (absorbS v.callee) (absorbScratchContractS X86_64.abi 16) :=
  Verified.of_correct (absorbS_correct v f) (absorbS_ct v f) (by
    sig_implies [absorbScratchContractS, absorbScratchSigS, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbX86_64S, absorbX86_64, X86_64.abi, X86_64.argRegs] [absorbSatS, absorbSat] using absorbSatS)

end VG.Proof.CmacAes.Stream.X86_64

end

end

/-!
# Streaming AES-CMAC on x86-64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2312 bytes that allocates it
(`Verified.stackScratch`): the 2304 bytes of working space, and 8 more to
keep `rsp` aligned. Their own calls use at most 16 bytes below it: two
return addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no
stack (and `vg_cmac_aes_update_aesni` none at all). Over implementations of
AES that need no working space, `init` (`initF`) needs only 152 bytes of it,
in a frame of 168 (`initF_framed`). Over implementations that never touch
the first 512 bytes of the working space (the bitsliced AES, which uses 1480
bytes of its own, 512 bytes into it), the functions (`initS`, `absorbS`,
`finishS`) need 1792 bytes, in a frame of 1800 (`initS_framed`,
`absorbS_framed`, `finishS_framed`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl UpdateFree)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, ekCall_xdepth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack, v.expandNoStack]
  decide +kernel

theorem initS_xdepth (v : Ctr32Impl) : (initS v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  have := init_xdepth v
  simp only [initS, Code.x86_64Depth, Nat.max_le]
  omega

theorem initF_xdepth (v : Ctr32Impl) : (initF ekF v.callee v.suffix).x86_64Depth ≤ 16 := by
  have h : ekF.code.x86_64Depth = 0 := Ctr32Impl.aesni.expandNoStack
  simp only [initF, init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, ekCall_xdepth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack, h]
  decide +kernel

theorem absorb_xdepth (v : UpdateImpl) : (absorb v.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.x86_64Depth, Nat.max_le]
  omega_using [this]

theorem absorbF_xdepth (v : UpdateImpl) : (absorbF v.callee).x86_64Depth ≤ 16 := by
  have := absorb_xdepth v
  simp only [absorbF, Code.x86_64Depth, Nat.max_le]
  omega

theorem absorbS_xdepth (v : UpdateImpl) : (absorbS v.callee).x86_64Depth ≤ 16 := by
  have := absorb_xdepth v
  simp only [absorbS, Code.x86_64Depth, Nat.max_le]
  omega

theorem finish_xdepth (v : Ctr32Impl) : (finish v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [finish, finPre, lastLen, Impl.CmacAes.X86_64.finalize, Code.x86_64Depth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack]
  decide +kernel

theorem finishS_xdepth (v : Ctr32Impl) : (finishS v.callee v.suffix).x86_64Depth ≤ 16 := by
  have := finish_xdepth v
  simp only [finishS, Code.x86_64Depth, Nat.max_le]
  omega

theorem finishF_xdepth (v : Ctr32Impl) : (finishF v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [finishF, finPreF, lastLen, Impl.CmacAes.X86_64.finalize, Code.x86_64Depth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem initFrameSatF_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 184).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem initFrameSatS_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 1816).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

theorem absorbFrameSatF_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 72).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

theorem absorbFrameSatS_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 1816).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem finishFrameSatF_pre : ∃ s, (Spec.Cmac.aesFinishContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem finishFrameSatS_pre : ∃ s, (Spec.Cmac.aesFinishContract X86_64.abi 1816).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .rcx (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.initPostOut_local _) (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 2312)
    (init_verified v) (by decide) (by decide) (by decide) (init_spSafe v) (init_xdepth v)
    initFrameSat_pre

/-- `init_framed`, over implementations of AES that need no working space
(`initF`): a frame of the 152 bytes from `vg_cmac_aes_subkeys`'s counter
block to the end of our saved registers, and 16 more to keep `rsp` aligned. -/
theorem initF_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 168 .rcx (initF ekF v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 184) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.initPostOut_local _) (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 19) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 168)
    (initF_verified v f) (by decide) (by decide) (by decide) (initF_spSafe v) (initF_xdepth v)
    initFrameSatF_pre

/-- `init_framed`, over an implementation of AES that never touches the
first 512 bytes of the working space (`initS`): a frame 512 bytes smaller. -/
theorem initS_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1800 .rcx (initS v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 1816) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.initPostOut_local _) (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 224) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 1800)
    (initS_verified v f) (by decide) (by decide) (by decide) (initS_spSafe v) (initS_xdepth v)
    initFrameSatS_pre

theorem absorb_framed (v : UpdateImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (absorb v.callee))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2312) (absorb_verified v) (by decide) (by decide) (by decide) (absorb_spSafe v)
    (absorb_xdepth v) absorbFrameSat_pre

/-- `absorb_framed`, over an implementation of `vg_cmac_aes_update` that
needs no working space (`absorbF`): a frame of the 48 bytes of the registers
saved, after the 8 that stand for the return address. -/
theorem absorbF_framed (v : UpdateImpl) (f : UpdateFree v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 56 .r9 (absorbF v.callee))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 72) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 6) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 56) (absorbF_verified v f) (by decide) (by decide) (by decide) (absorbF_spSafe v)
    (absorbF_xdepth v) absorbFrameSatF_pre

/-- `absorb_framed`, over an implementation of `vg_cmac_aes_update` that
never touches the first 512 bytes of its scratch buffer (`absorbS`): a frame
512 bytes smaller. -/
theorem absorbS_framed (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateSmall v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1800 .r9 (absorbS v.callee))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 1816) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 224) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 1800) (absorbS_verified v f) (by decide) (by decide) (by decide) (absorbS_spSafe v)
    (absorbS_xdepth v) absorbFrameSatS_pre

theorem finish_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.finishPostOut_local _) (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2312) (finish_verified v) (by decide) (by decide) (by decide) (finish_spSafe v)
    (finish_xdepth v) finishFrameSat_pre

/-- `finish_framed`, over an implementation of `vg_aes_ctr32` that needs no
working space: a frame of the 16 bytes of `vg_cmac_aes_finalize`'s counter
block, after the 8 that stand for the return address. -/
theorem finishF_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (finishF v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 40) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.finishPostOut_local _) (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 2) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 24) (finishF_verified v f) (by decide) (by decide) (by decide) (finishF_spSafe v)
    (finishF_xdepth v) finishFrameSatF_pre

/-- `finish_framed`, over an implementation of `vg_aes_ctr32` that never
touches the first 512 bytes of the working space (`finishS`): a frame 512
bytes smaller. -/
theorem finishS_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1800 .r8 (finishS v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 1816) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.finishPostOut_local _) (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 224) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 1800) (finishS_verified v f) (by decide) (by decide) (by decide) (finishS_spSafe v)
    (finishS_xdepth v) finishFrameSatS_pre

end VG.Proof.CmacAes.Stream.X86_64
