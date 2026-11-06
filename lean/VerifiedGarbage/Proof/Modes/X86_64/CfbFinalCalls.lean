module

public import VerifiedGarbage.Impl.Modes.X86_64.CfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
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
open VG.Impl.Aes.X86_64 (movR)

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

/-- `mov r, imm32`. -/
theorem movImm32_ok (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.mov r (.imm v)] s = some s' ∧ s'.gpr r = v.signExtend 64 ∧
      (∀ x, x ≠ r → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg r (v.signExtend 64), ?_, RegUpd.gpr_setReg_self _ _ _, fun _ h => RegUpd.gpr_setReg_of_ne _ _ h,
    rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]

theorem eight_signExtend : (8 : BitVec 32).signExtend 64 = 8 := by decide

/-- `reload` is the moves of the callee-saved registers back to the
arguments. -/
theorem reload_eq (a : FinalArgs) :
    a.reload = movs ((List.range a.regs.length).map fun i => (a.arg i, FinalArgs.saved i)) := by
  simp only [FinalArgs.reload, movs, List.map_map]; rfl

/-- `zeroBlock ++ oneBlock`, from a state `v` whose callee-saved registers
hold the arguments of `s₀` (but the data's address and the length) and whose
`rsp` is the frame's: the state the second function runs from, with the
callee-saved registers as in `v`. -/
theorem tailSetup_ok {a : FinalArgs} (ha : FinalOk a) {s₀ v : State}
    (hsv : ∀ i < a.regs.length, i ≠ a.lenIx → i ≠ a.dataIx → v.gpr (FinalArgs.saved i) = s₀.gpr (a.arg i))
    (hsp : v.gpr .rsp = s₀.gpr .rsp - BitVec.ofNat 64 80) (hfr : frameRegion s₀ ∈ v.wr) :
    ∃ u, runBlock isa (a.zeroBlock ++ a.oneBlock) v = some u ∧ Call₂ a s₀ v u ∧
      (∀ i < 6, u.gpr (FinalArgs.saved i) = v.gpr (FinalArgs.saved i)) := by
  have hlen6 := ha.length
  have hb := ha.blk_eq
  have hw8 : 8 + 8 * (a.blk / 8) ≤ 2 ^ 64 := by omega
  have hK : v.gpr .rsp + BitVec.ofNat 64 8 = blockAddr s₀ := by
    rw [hsp, blockAddr, sub_add_ofNat _ (by decide)]
  have hKk : ∀ k, v.gpr .rsp + BitVec.ofNat 64 (8 + 8 * k) = blockAddr s₀ + BitVec.ofNat 64 (8 * k) := fun k => by
    rw [← VG.Offset.add_add, hK]
  have hfr' : frameRegion s₀ = ⟨v.gpr .rsp, 80⟩ := by rw [frameRegion, hsp]
  obtain ⟨s₁, e₁, f₁, z₁, g₁, r₁, rd₁, wr₁⟩ := wipe_zero ⟨blockAddr s₀, a.blk⟩ (frameRegion s₀) v hfr (a.blk / 8) hw8
    (fun k hk => by rw [hKk]; exact Offset.contains_base _ (by omega) (by omega))
    (fun k hk => by rw [hfr']; exact Offset.contains_base _ (by omega) (by omega))
  -- `reload`.
  let l := (List.range a.regs.length).map fun i => (a.arg i, FinalArgs.saved i)
  have hdst : (l.map Prod.fst).Nodup := by
    simp only [l, List.map_map, Function.comp_def]
    exact nodup_map_range _ _ fun i hi j hj h => ha.distinct i hi j hj h
  have hsrc : ∀ q ∈ l, q.1 ∉ l.map Prod.snd := by
    intro q hq h
    simp only [l, List.mem_map, List.mem_range] at hq h
    obtain ⟨i, hi, rfl⟩ := hq
    obtain ⟨⟨_, r⟩, ⟨j, hj, e⟩, e'⟩ := h
    simp only [Prod.mk.injEq] at e
    simp only at e'
    exact saved_not_arg j (by omega) (e.2 ▸ e' ▸ ha.args i hi)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -⟩ := movs_ok l s₁ hdst hsrc
  have notDst : ∀ x, (x = .rsp ∨ ∃ i < 6, x = FinalArgs.saved i) → x ∉ l.map Prod.fst := by
    intro x hx h
    simp only [l, List.map_map, Function.comp_def, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, rfl⟩ := h
    rcases hx with h | ⟨i, hi, h⟩
    · exact (argRegs_scratch' _ (ha.args j hj)).1 h
    · exact saved_not_arg i hi (h ▸ ha.args j hj)
  have hD := ha.data
  have hL := ha.len
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ (a.arg a.dataIx) .rsp
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ (a.arg a.dataIx) 8
  obtain ⟨u, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := movImm32_ok s₄ (a.arg a.lenIx) 1
  have dl : a.arg a.lenIx ≠ a.arg a.dataIx := fun h => ha.dl (ha.distinct _ hD _ hL h.symm)
  have hrsp₂ : s₂.gpr .rsp = v.gpr .rsp := by rw [o₂ _ (notDst _ (.inl rfl)), g₁ _ (by decide)]
  have hsav : ∀ i < 6, u.gpr (FinalArgs.saved i) = v.gpr (FinalArgs.saved i) := fun i hi => by
    have h1 : FinalArgs.saved i ≠ a.arg a.lenIx := fun h => saved_not_arg i hi (h ▸ ha.args _ hL)
    have h2 : FinalArgs.saved i ≠ a.arg a.dataIx := fun h => saved_not_arg i hi (h ▸ ha.args _ hD)
    rw [o₅ _ h1, o₄ _ h2, o₃ _ h2, o₂ _ (notDst _ (.inr ⟨i, hi, rfl⟩)), g₁ _ (saved_scratch i hi).2.2]
  refine ⟨u, ?_, ⟨fun i hi h1 h2 => ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_⟩, hsav⟩
  · have h : a.oneBlock = movs l ++ [movR (a.arg a.dataIx) .rsp] ++ [.alu .add (a.arg a.dataIx) (.imm 8)] ++
        [.mov (a.arg a.lenIx) (.imm 1)] := by
      simp only [FinalArgs.oneBlock, reload_eq, List.append_assoc]; rfl
    rw [runBlock_app, FinalArgs.zeroBlock, e₁, Option.bind_some, h, runBlock_app, runBlock_app, runBlock_app, e₂, Option.bind_some, e₃,
      Option.bind_some, e₄, Option.bind_some, e₅]
  · have n1 : a.arg i ≠ a.arg a.lenIx := fun h => h1 (ha.distinct i hi _ hL h)
    have n2 : a.arg i ≠ a.arg a.dataIx := fun h => h2 (ha.distinct i hi _ hD h)
    rw [o₅ _ n1, o₄ _ n2, o₃ _ n2, v₂ (a.arg i, FinalArgs.saved i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      g₁ _ (saved_scratch i (by omega)).2.2]
    exact hsv i hi h1 h2
  · rw [o₅ _ (Ne.symm dl), v₄, v₃, hrsp₂, eight_signExtend]; exact hK
  · rw [v₅]; rfl
  · rw [o₅ _ (Ne.symm (argRegs_scratch' _ (ha.args _ hL)).1), o₄ _ (Ne.symm (argRegs_scratch' _ (ha.args _ hD)).1),
      o₃ _ (Ne.symm (argRegs_scratch' _ (ha.args _ hD)).1), hrsp₂, hsp]
  · rw [m₅, m₄, m₃, m₂, ← hKk]
    exact z₁ k hk
  · rw [m₅, m₄, m₃, m₂]; exact f₁
  · rw [rd₅, rd₄, rd₃, rd₂, rd₁]
  · rw [wr₅, wr₄, wr₃, wr₂, wr₁]

end VG.Proof.Modes.X86_64
