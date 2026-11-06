module

public import VerifiedGarbage.Impl.Modes.X86_64.CfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinalSteps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# CFB of a message's last piece on x86-64: the states at the calls

What `cfbFinal`'s proof (`Proof/Modes/X86_64/CfbFinal.lean`) asks of its
arguments (`FinalArgs.Ok`), and the states its inlined functions run from:

* `Call₁ a s₀ len u`: the first, `whole` on the `len / 2^lg` whole blocks,
  from the state `u` after the frame's push and `entry`: the arguments of
  `s₀` but the number of blocks, saved in their callee-saved registers too,
  `rsp` 80 bytes lower, and memory changed only in the frame;
* `Call₂ a s₀ u₁ u`: the second, `enc` on the working block, from `u`, made
  from the state `u₁` after the first by `rest`, `zeroBlock` and
  `oneBlock`: the same arguments but the data's address, the block's, and
  the number of blocks, 1, with the block zero.

`entry_ok` and `oneBlock_ok` run the blocks that make them.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64

/-- What `cfbFinal` asks of where the whole-block functions take their
arguments: at most six argument registers, distinct, the data's and the
number of blocks' among them, and blocks of 8 or 16 bytes. -/
structure FinalOk (a : FinalArgs) : Prop where
  length : a.regs.length ≤ 6
  args : ∀ i < a.regs.length, a.arg i ∈ argRegs
  distinct : ∀ i < a.regs.length, ∀ j < a.regs.length, a.arg i = a.arg j → i = j
  data : a.dataIx < a.regs.length
  len : a.lenIx < a.regs.length
  dl : a.dataIx ≠ a.lenIx
  lg : a.lg = 3 ∨ a.lg = 4

theorem saved_mem : ∀ i < 6, FinalArgs.saved i ∈ calleeSaved := by decide

theorem saved_inj : ∀ i < 6, ∀ j < 6, FinalArgs.saved i = FinalArgs.saved j → i = j := by decide

theorem saved_ne_rsp : ∀ i < 6, FinalArgs.saved i ≠ .rsp := by decide

theorem saved_not_arg : ∀ i < 6, FinalArgs.saved i ∉ argRegs := by decide

theorem saved_scratch : ∀ i < 6, FinalArgs.saved i ≠ .rax ∧ FinalArgs.saved i ≠ .r10 ∧ FinalArgs.saved i ≠ .r11 := by
  decide

theorem argRegs_scratch' : ∀ r ∈ argRegs, r ≠ Reg.rsp ∧ r ≠ Reg.rax ∧ r ≠ Reg.r10 ∧ r ≠ Reg.r11 ∧ r ∉ calleeSaved := by
  decide

theorem FinalOk.blk_eq {a : FinalArgs} (ha : FinalOk a) : a.blk = 8 ∨ a.blk = 16 := by
  rcases ha.lg with h | h <;> simp [FinalArgs.blk, h]

/-- The frame: the 80 bytes below `rsp` on entry. -/
def frameRegion (s₀ : State) : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 80, 80⟩

/-- The working block, at `rsp + 8` within the frame. -/
def blockAddr (s₀ : State) : Addr := s₀.gpr .rsp - BitVec.ofNat 64 72

/-- Where the caller's callee-saved registers are: the 48 bytes below `rsp`
on entry. -/
def slotsRegion (s₀ : State) : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 48, 48⟩

/-- The state the first function runs from (see above). -/
structure Call₁ (a : FinalArgs) (s₀ : State) (len : Nat) (u : State) : Prop where
  args : ∀ i < a.regs.length, i ≠ a.lenIx → u.gpr (a.arg i) = s₀.gpr (a.arg i)
  blocks : u.gpr (a.arg a.lenIx) = BitVec.ofNat 64 (len / a.blk)
  saved : ∀ i < a.regs.length, u.gpr (FinalArgs.saved i) = s₀.gpr (a.arg i)
  rsp : u.gpr .rsp = s₀.gpr .rsp - BitVec.ofNat 64 80
  slots : ∀ j < 6, u.mem.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s₀.gpr (FinalArgs.saved j)
  frame : Frame [frameRegion s₀] s₀.mem u.mem
  rd : u.rd = s₀.rd
  wr : u.wr = frameRegion s₀ :: s₀.wr

/-- The state the second function runs from, after the first left `u₁` (see
above). -/
structure Call₂ (a : FinalArgs) (s₀ u₁ : State) (u : State) : Prop where
  args : ∀ i < a.regs.length, i ≠ a.lenIx → i ≠ a.dataIx → u.gpr (a.arg i) = s₀.gpr (a.arg i)
  data : u.gpr (a.arg a.dataIx) = blockAddr s₀
  blocks : u.gpr (a.arg a.lenIx) = 1
  rsp : u.gpr .rsp = s₀.gpr .rsp - BitVec.ofNat 64 80
  zero : ∀ k < a.blk / 8, u.mem.readW (blockAddr s₀ + BitVec.ofNat 64 (8 * k)) 64 = 0
  frame : Frame [⟨blockAddr s₀, a.blk⟩] u₁.mem u.mem
  rd : u.rd = u₁.rd
  wr : u.wr = u₁.wr

theorem nodup_map_range {α : Type} (f : Nat → α) :
    ∀ n, (∀ i < n, ∀ j < n, f i = f j → i = j) → ((List.range n).map f).Nodup
  | 0, _ => List.nodup_nil
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨nodup_map_range f n fun i hi j hj e => h i (by omega) j (by omega) e, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy e
    simp only [List.mem_map, List.mem_range] at hx
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    obtain ⟨i, hi, rfl⟩ := hx
    subst hy
    have := h i (by omega) n (by omega) e
    omega

/-- `entry` is the moves of the arguments to their callee-saved registers. -/
theorem entry_eq (a : FinalArgs) :
    a.entry = movs ((List.range a.regs.length).map fun i => (FinalArgs.saved i, a.arg i)) := by
  simp only [FinalArgs.entry, movs, List.map_map]; rfl

theorem pushRegs_length : FinalArgs.pushRegs.length = 10 := rfl

theorem pushRegs_get (j : Nat) (hj : j < 6) :
    FinalArgs.pushRegs[j]'(by rw [pushRegs_length]; omega) = FinalArgs.saved j := by
  revert j; decide

/-- The frame's push and `entry ++ toBlocks`: the state the first function
runs from. -/
theorem entry_ok {a : FinalArgs} (ha : FinalOk a) {s₀ : State} {len : Nat}
    (hL : s₀.gpr (a.arg a.lenIx) = BitVec.ofNat 64 len) (hlen : len < 2 ^ 64)
    (hsp : 80 ≤ (s₀.gpr .rsp).toNat) :
    ∃ u, runBlock isa (a.entry ++ a.toBlocks) (pushed FinalArgs.pushRegs s₀) = some u ∧ Call₁ a s₀ len u := by
  let p := pushed FinalArgs.pushRegs s₀
  let l := (List.range a.regs.length).map fun i => (FinalArgs.saved i, a.arg i)
  have hlen6 := ha.length
  have hdst : (l.map Prod.fst).Nodup := by
    simp only [l, List.map_map, Function.comp_def]
    exact nodup_map_range _ _ fun i hi j hj h => saved_inj i (by omega) j (by omega) h
  have hsrc : ∀ q ∈ l, q.1 ∉ l.map Prod.snd := by
    intro q hq h
    simp only [l, List.mem_map, List.mem_range] at hq h
    obtain ⟨i, hi, rfl⟩ := hq
    obtain ⟨⟨_, r⟩, ⟨j, hj, e⟩, e'⟩ := h
    simp only [Prod.mk.injEq] at e
    simp only at e'
    exact saved_not_arg i (by omega) (e' ▸ e.2 ▸ ha.args j hj)
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -⟩ := movs_ok l p hdst hsrc
  have hlg1 : 1 ≤ a.lg := by rcases ha.lg with h | h <;> omega
  have hlg2 : a.lg ≤ 63 := by rcases ha.lg with h | h <;> omega
  obtain ⟨u, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := shrImm_ok s₁ (a.arg a.lenIx) hlg1 hlg2
  have argNotDst : ∀ i < a.regs.length, a.arg i ∉ l.map Prod.fst := by
    intro i hi h
    simp only [l, List.map_map, Function.comp_def, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, e⟩ := h
    exact saved_not_arg j (by omega) (e ▸ ha.args i hi)
  have hp : ∀ r, r ≠ .rsp → p.gpr r = s₀.gpr r := fun r h => pushed_gpr _ _ h
  have argNe : ∀ i < a.regs.length, a.arg i ≠ .rsp := fun i hi => (argRegs_scratch' _ (ha.args i hi)).1
  have hpm := pushRegs_mem s₀ FinalArgs.pushRegs (by decide) (by rw [pushRegs_length]; omega)
  refine ⟨u, by rw [runBlock_app, entry_eq, e₁, Option.bind_some]; exact e₂, ⟨fun i hi hne => ?_, ?_, fun i hi => ?_,
    ?_, fun j hj => ?_, ?_, ?_, ?_⟩⟩
  · have : a.arg i ≠ a.arg a.lenIx := fun h => hne (ha.distinct i hi _ ha.len h)
    rw [o₂ _ this, o₁ _ (argNotDst i hi), hp _ (argNe i hi)]
  · rw [v₂, o₁ _ (argNotDst _ ha.len), hp _ (argNe _ ha.len), hL, shr_ofNat hlen]; rfl
  · have hne : FinalArgs.saved i ≠ a.arg a.lenIx := fun h => saved_not_arg i (by omega) (h ▸ ha.args _ ha.len)
    rw [o₂ _ hne, v₁ (FinalArgs.saved i, a.arg i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      hp _ (argNe i hi)]
  · have h1 : Reg.rsp ≠ a.arg a.lenIx := Ne.symm (argNe _ ha.len)
    have h2 : Reg.rsp ∉ l.map Prod.fst := by
      intro h
      simp only [l, List.map_map, Function.comp_def, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, e⟩ := h
      exact saved_ne_rsp j (by omega) e
    rw [o₂ _ h1, o₁ _ h2, pushed_rsp, pushRegs_length]
  · have := hpm.2 j (by rw [pushRegs_length]; omega)
    rw [pushRegs_get j hj] at this
    rw [m₂, m₁]
    exact this
  · rw [m₂, m₁]
    have := hpm.1
    rw [pushRegs_length] at this
    exact this
  · rw [rd₂, rd₁]; exact (pushRegs_eq s₀ _).1
  · rw [wr₂, wr₁, pushed_wr, pushRegs_length]; rfl

end VG.Proof.Modes.X86_64
