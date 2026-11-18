module

public import VerifiedGarbage.Proof.Framework.AArch64.Straight
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Proof.Modes.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.AArch64.Xor
public import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Modes.AArch64.Group`, which the modules that import this one used -/

section

/-!
# One group of blocks of CTR on AArch64, for any core

`ctrGroup_wp`: one iteration of the data loop writes the group's `G`
counter blocks to the core's buffer (`ctrBlocks_ok`), encrypts them there
(`CoreSpec.crypt_wp`), XORs the first `min(G, left)` into the group's blocks
(`xorBlocks_wp`) and steps to the next group. Block `j` of the data becomes
CTR's output block `j` (`ctrOut`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem lsr_beq {v k : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> k == 0) = decide (v < 2 ^ k) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  have := Nat.two_pow_pos k
  obtain e : (BitVec.ofNat 64 v >>> k).toNat = v / 2 ^ k := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    obtain h' := congrArg BitVec.toNat h
    rw [e, show (0 : BitVec 64).toNat = 0 from rfl, Nat.div_eq_zero_iff] at h'
    omega_using [this, h']
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e, show (0 : BitVec 64).toNat = 0 from rfl, Nat.div_eq_zero_iff]
    omega_using [h]

/-- `x16 := min(left, G)`. -/
theorem groupCount_wp (hlg : c.lgG < 16) (hl13 : c.leftReg ≠ .x13) {s : State} {v : Nat}
    (hv : s.gpr c.leftReg = BitVec.ofNat 64 v) (hv64 : v < 2 ^ 64) :
    WP isa c.groupCount s fun s' => s'.gpr .x16 = BitVec.ofNat 64 (min v c.G) ∧
      (∀ r, r ≠ .x13 → r ≠ .x16 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hG : c.G < 2 ^ 16 := Nat.pow_lt_pow_right (by decide) hlg
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := lsr_ok s .x13 c.leftReg (sh := c.lgG) (by omega_using [hlg])
  unfold Core.groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain hz : isa.eval (.nonzero .x .x13) s₁ = some !(decide (v < c.G)) := by
    rw [eval_nonzero, r₁, hv, lsr_beq hv64]; rfl
  refine WP.ite (!(decide (v < c.G))) hz (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movz_ok s₁ .x16 (v := c.G) hG
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [r₂, Nat.min_eq_right (by simp at h; omega_using [h])]
    · rw [o₂ r h2, o₁ r h1]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .x16 c.leftReg
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [r₂, o₁ _ hl13, hv, Nat.min_eq_left (by simp at h; omega_using [h])]
    · rw [o₂ r h2, o₁ r h1]

/-- The buffer's address to `x14`, the data's to `x15`, the count to `x17`. -/
theorem xorArgs_ok (hbI : 8 * c.buf < 4096) (hd14 : c.dataReg ≠ .x14) (s : State) {B : Addr} (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.xorArgs s = some s' ∧ s'.gpr .x14 = B + BitVec.ofNat 64 (8 * c.buf) ∧
      s'.gpr .x15 = s.gpr c.dataReg ∧ s'.gpr .x17 = s.gpr .x16 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x14 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x14 .x14 hbI
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x15 c.dataReg
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .x17 .x16
  refine ⟨s₄, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.xorArgs, show ([movR .x14 sb, .addImm .x .x14 .x14 (8 * c.buf), movR .x15 c.dataReg,
        movR .x17 .x16] : List Instr) = [movR .x14 sb] ++ (([.addImm .x .x14 .x14 (8 * c.buf)] :
        List Instr) ++ (([movR .x15 c.dataReg] : List Instr) ++ [movR .x17 .x16])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB]
  · rw [o₄ _ (by decide), r₃, o₂ _ hd14, o₁ _ hd14]
  · rw [r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  · rw [o₄ r h3, o₃ r h2, o₂ r h1, o₁ r h1]

/-- On past the group's blocks: the data's address from `x15`, the count
from `x16` off the blocks left. -/
theorem advance_ok (hdl : c.dataReg ≠ c.leftReg) (hd16 : c.dataReg ≠ .x16)
    (s : State) :
    ∃ s', runBlock isa c.advance s = some s' ∧ s'.gpr c.dataReg = s.gpr .x15 ∧
      s'.gpr c.leftReg = s.gpr c.leftReg - s.gpr .x16 ∧
      (∀ r, r ≠ c.dataReg → r ≠ c.leftReg → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s c.dataReg .x15
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := subReg_ok s₁ c.leftReg c.leftReg .x16
  obtain l₁ : s₁.gpr c.leftReg = s.gpr c.leftReg := o₁ _ (Ne.symm hdl)
  obtain t₁ : s₁.gpr .x16 = s.gpr .x16 := o₁ _ (Ne.symm hd16)
  refine ⟨s₂, ?_, by rw [o₂ _ hdl, r₁], by rw [r₂, l₁, t₁],
    fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [Core.advance, show ([movR c.dataReg .x15, .sub .x c.leftReg c.leftReg .x16] : List Instr) =
    [movR c.dataReg .x15] ++ [.sub .x c.leftReg c.leftReg .x16] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- What the data loop works on: the scratch buffer at `B`, the `n` blocks at
`D`. -/
structure GPre (c : Core) (s₀ : State) (B D : Addr) (n : Nat) (L : Nat := 16) : Prop where
  scr : ScrIn s₀ B c.total
  dat : (⟨D, L * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, L * n⟩ ⟨B, 8 * c.total⟩
  fitD : D.toNat + L * n ≤ 2 ^ 64

/-- The data loop, before group `g`, from the counter block `V` with the key
`k`. -/
structure GInv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  hi : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (V + c.G * g)
  lo : s.mem.readW (wordAddr B c.loSlot) 64 = loOf (V + c.G * g)
  data : DInv 16 s₀.mem s.mem D n (c.G * g) (ctrOut (cs.cipher k) s₀.mem D V)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv 16 s₀.mem s.mem D n n (ctrOut (cs.cipher k) s₀.mem D V)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Byte `u` of the 16 at `p`. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {L u : Nat} (hu : u < L) :
    (bytesAt m p L).getD u 0 = m (p + BitVec.ofNat 64 u) := by
  simp [bytesAt, hu]

theorem ctrGroup_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : GInv cs s₀ B D n k V g s) :
    WP isa c.ctrGroup s fun s' => (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ GDone cs s₀ B D n k V s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ GInv cs s₀ B D n k V (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain nown : ∀ {r : Reg}, r ∉ ownRegs → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x13 ∧
      r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := fun h => by
    simp only [ownRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h; exact h
  obtain ⟨-, -, -, -, -, d13, d14, -, d16, -⟩ := nown down
  obtain ⟨-, -, -, -, -, l13, l14, l15, l16, l17⟩ := nown lown
  obtain hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  obtain hv : v < 2 ^ 64 := by omega_using [hfitD]
  obtain hc0 : 0 < cc := by omega_using [hG0, hk]
  obtain hcG : cc ≤ c.G := by omega_using []
  obtain hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega_using [hc0]
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * c.total → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.total⟩ :=
    fun h => VG.Offset.sub_base B h
  obtain subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega_using [hroom])
  obtain mSlot : ∀ j, c.slots ≤ j → j < c.total → ∀ r ∈ [coreRegion c B],
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base B (by omega_using [h1]) (by omega_using [hN, h2])
  obtain inT : ∀ t, t < 2 * c.G → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base B (by omega_using [hroom, hbuf, ht]) (by omega_using [hroom, hbuf, hN, ht])
  obtain inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_using [ht]) (by omega_using [hfitD, ht])
  obtain sepAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right (subS (by omega_using [hroom, hbuf]))
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctrBlocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctrGroup
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide), hi.base]
  obtain subBC : ∀ r ∈ [bufRegion c B, ctrRegion c B], Region.Sub r ⟨B, 8 * c.total⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> (try simp only [Core.hiSlot]) <;> omega_using [hroom, hbuf]
  obtain ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr fun _ h => h
    · exact .inl (VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega_using [])
        (by simp only [Core.hiSlot]; omega_using [hroom, hN])).symm) ⟨fun r hr => ⟨_, hwS, subBC r hr⟩, rd₁, wr₁,
      runBlock_syms e₁⟩
    fun r hr => o₁ r (of_not_modeRegs hr).1
  -- The keystream.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  obtain keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (mSlot j h1 h2) (by decide)
  obtain keep₁ : ∀ j, c.slots ≤ j → j < c.slots + 10 →
      s₁.mem.readW (wordAddr B j) 64 = s.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint B (Or.inr (by omega_using [hbuf, h1])) (by omega_using [hroom, hN, h2]) (by omega_using [hroom, hbuf, hN])
      · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_using [h2]) (by omega_using [hroom, hN, h2])
          (by simp only [Core.hiSlot]; omega_using [hroom, hN])) (by decide)
  -- The count.
  obtain left₂ : s₂.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₂, o₁ _ lown, hi.leftR]
  obtain data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, o₁ _ down, hi.dataR]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  refine WP.seq (WP.mono_syms (groupCount_wp hL.lgG_lt l13 left₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ sy₃ => ?_)
  obtain base₃ : s₃.gpr sb = B := by rw [o₃ _ (by decide) (by decide), base₂]
  obtain ⟨s₄, e₄, a₄, b₄, t₄, o₄, m₄, rd₄, wr₄⟩ := xorArgs_ok hL.bufImm d14 s₃ base₃
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  obtain mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  -- The keystream XORed into the group's blocks.
  refine WP.seq (WP.mono_syms (xorBlocks_wp (A := T) (B := A) hc0 (by omega_using [hsm, hroom, hbuf])
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega_using [ht])))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [a₄]; simp [T], by rw [b₄, o₃ _ d13 d16, data₂]; simp [A],
      by rw [t₄, c₃, Nat.sub_zero], fun t ht => by omega_using [ht], fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ sy₅ => ?_)
  obtain f₅ : Frame [⟨A, 16 * cc⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact h₅.frame
  obtain keep₄ : ∀ r, r ∉ ownRegs → s₅.gpr r = s₂.gpr r := fun r hr => by
    obtain ⟨-, -, h8, h9, -, h13, h14, h15, h16, h17⟩ := nown hr
    rw [h₅.regs r h8 h9 h14 h15 h17, o₄ r h14 h15 h17, o₃ r h13 h16]
  obtain base₅ : s₅.gpr sb = B := by rw [keep₄ _ (by decide), base₂]
  obtain left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 v := by rw [keep₄ _ lown, left₂]
  obtain x16₅ : s₅.gpr .x16 = BitVec.ofNat 64 cc := by
    rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), o₄ _ (by decide) (by decide) (by decide),
      c₃]
  have x15₅ : s₅.gpr .x15 = A + BitVec.ofNat 64 (16 * cc) := h₅.x15
  obtain wr₅' : s₅.wr = s.wr := by rw [h₅.wr, wr₄']
  obtain rd₅' : s₅.rd = s.rd := by rw [h₅.rd, rd₄']
  obtain keep₅ : ∀ j, j < c.total → s₅.mem.readW (wordAddr B j) 64 = s₂.mem.readW (wordAddr B j) 64 :=
    fun j hj => f₅.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right
        (subS (by omega_using [hj]))).symm) (by decide)
  -- On to the next group.
  obtain ⟨s₆, e₆, d₆, l₆, o₆, m₆, rd₆, wr₆⟩ := advance_ok hdl d16 s₅
  obtain left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (v - cc) := by
    rw [l₆, left₅, x16₅, VG.Offset.ofNat_sub_ofNat (by omega_using [])]
  obtain hz : isa.eval (.nonzero .x c.leftReg) s₆ = some !(decide (v = cc)) := by
    rw [eval_nonzero, left₆, ofNat_beq_zero (by omega_using [hv]), decide_eq_decide.mpr (show v - cc = 0 ↔ v = cc by omega_using [])]
  obtain ready₆ : cs.Ready s₆ B k := by
    refine cs.ready_frame ready₂ (by rw [m₆]; exact f₅) (fun r hr => ?_) ⟨fun r hr => ?_, ?_, ?_, ?_⟩ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right subCore).symm)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [wr₂, wr₁]; exact hwD, VG.Offset.sub_base D (by omega_using [hkc])⟩
    · rw [rd₆, rd₅', rd₂, rd₁]
    · rw [wr₆, wr₅', wr₂, wr₁]
    · rw [runBlock_syms e₆, sy₅, runBlock_syms e₄, sy₃]
    · obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
      rw [o₆ r h2 h3, keep₄ r h1]
  -- The data.
  obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨B, 8 * c.total⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain dCore : ∀ r ∈ [coreRegion c B], Region.Disjoint ⟨D, 16 * n⟩ r := hdS fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact subCore
  obtain hn64 : 16 * n ≤ 2 ^ 64 := by omega_using [hfitD]
  obtain via₁₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [f₂.bytes (R := ⟨D, 16 * n⟩) dCore hn64 hin, f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subBC) hn64 hin]
  obtain hdata : DInv 16 s₀.mem s₆.mem D n (c.G * g + cc) (ctrOut (cs.cipher k) s₀.mem D V) := by
    intro i hin
    rw [m₆]
    by_cases hin1 : 16 * (c.G * g) ≤ i ∧ i < 16 * (c.G * g) + 16 * cc
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 16 * (c.G * g)) := by
        rw [addr_add, show 16 * (c.G * g) + (i - 16 * (c.G * g)) = i by omega_using [hin1]]
      let t := i - 16 * (c.G * g)
      obtain hj : t / 16 < c.G := by omega_using [hin1]
      obtain hu : t % 16 < 16 := Nat.mod_lt _ (by decide)
      obtain eT : T + BitVec.ofNat 64 t = bufAddr c B (t / 16) + BitVec.ofNat 64 (t % 16) := by
        simp only [T, bufAddr]
        rw [addr_add, addr_add, show 8 * c.buf + 16 * (t / 16) + t % 16 = 8 * c.buf + t by omega_using []]
      obtain hks : s₂.mem (T + BitVec.ofNat 64 t) =
          (cs.cipher k (Spec.Ctr.ofNat (V + c.G * g + t / 16) 16)).getD (t % 16) 0 := by
        rw [eT, ← bytesAt_getD s₂.mem _ hu, ks₂ _ hj, tb₁ _ hj]
      obtain hd₂ : s₂.mem (A + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 i) := by
        rw [← e1, via₁₂ i hin, hi.data i hin, ite_eq_right (by omega_using [hin1])]
      rw [e1, h₅.xored _ (by omega_using [hin1]), mem₄, hks, hd₂, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [hin1]),
        ctrOut_getD (cs.cipher_len k) _ _ _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega_using [],
        show V + c.G * g + t / 16 = V + i / 16 by omega_using [hin1], show t % 16 = i % 16 by omega_using [hin1], BitVec.xor_comm]
    · have hout : ∀ r ∈ [(⟨A, 16 * cc⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_using [hin1]) (by omega_using [hn64, hin]) (by omega_using [hc0]) (by omega_using [hkc, hn64])
      rw [f₅ _ hout, via₁₂ i hin, hi.data i hin]
      by_cases h2 : i < 16 * (c.G * g)
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [h2])]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * (c.G * g + cc) by omega_using [hin1, h2])]
  -- The slots.
  obtain saved₆ : ∀ i < 10, s₆.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [m₆, keep₅ _ (by omega_using [hroom, hi10]), keep₂ _ (by omega_using []) (by omega_using [hroom, hi10]), keep₁ _ (by omega_using []) (by omega_using [hi10]), hi.saved i hi10]
  obtain hiSlot₆ : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
      s₆.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
    obtain h1 : c.slots ≤ j := by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using []
    obtain h2 : j < c.total := by
      rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using [hroom]
    rw [m₆, keep₅ j h2, keep₂ j h1 h2]
  obtain fr₆ : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s.mem s₆.mem := by
    rw [m₆]
    refine ((f₁.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, subBC r hr⟩).trans
      (f₂.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₅.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base D (by omega_using [hkc])⟩
  obtain fr : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s₆.mem := hi.frame.trans fr₆
  obtain base₆ : s₆.gpr sb = B := by rw [o₆ _ (Ne.symm dsb) (Ne.symm lsb), base₅]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅', hi.rd]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅', hi.wr]
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₆, saved₆, ?_, fr, rd₆', wr₆'⟩
    rw [show n = c.G * g + cc by omega_using [hkc, hdone]] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega_using [hdone]
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₆, ready₆, saved₆, ?_, ?_,
      by rw [Nat.mul_succ]; omega_using [hdone], ?_, ?_,
      by rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact hdata, fr, rd₆', wr₆'⟩
    · rw [d₆, x15₅, addr_add, hcc,
        show 16 * (c.G * g) + 16 * c.G = 16 * (c.G * (g + 1)) by rw [Nat.mul_succ]; omega_using []]
    · rw [left₆, hcc, show v - c.G = n - c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]
    · rw [hiSlot₆ _ (.inl rfl), h₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]
    · rw [hiSlot₆ _ (.inr rfl), l₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]

end VG.Proof.Modes.AArch64

end

end

/-!
# CTR on AArch64: entry and exit

`setup_ok`: the entry block of `ctr` moves the scratch buffer to `sb`,
stores the callee-saved registers in the mode's slots, reads the counter
block `T₁` at `r.ctr` (a number `V`, big-endian) into the running counter's
slots, as `hiOf V` and `loOf V`, and writes `T₁ + n` back. `ctrArgs_ok`:
the data's address and `n` to the registers the core keeps.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

/-! ## Words to and from consecutive slots -/

/-- `k` stores of registers to consecutive slots from `base`. -/
theorem stores_ok {B : Addr} (base : Nat) (g : Nat → Reg) : ∀ (k : Nat) (s : State), s.gpr sb = B →
    (∀ i < k, InRegions s.wr (wordAddr B (base + i)) 8) → 8 * (base + k) < 32768 →
    ∃ s', runBlock isa ((List.range k).map fun i => stS (base + i) (g i)) s = some s' ∧
      (∀ i < k, s'.mem.readW (wordAddr B (base + i)) 64 = s.gpr (g i)) ∧
      Frame [⟨wordAddr B base, 8 * k⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, s, _, _, _ => ⟨s, rfl, fun i hi => by omega_arith, Frame.refl _ _, rfl, rfl, rfl⟩
  | k + 1, s, hB, hw, hk => by
    obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := stores_ok base g k s hB (fun i hi => hw i (by omega_arith)) (by omega_arith)
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_ok (s := s₁) (b := B) (k := base + k) (g k) (by rw [g₁, hB])
      (by omega_arith) (by rw [wr₁]; exact hw k (by omega_arith))
    refine ⟨s₂, ?_, fun i hi => ?_, ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.map_append, runBlock_app, e₁, Option.bind_some, List.map_singleton, e₂]
    · rw [m₂, readW_slot_write _ (by omega_arith) (by omega_arith), g₁]
      split
      · rename_i h; rw [show i = k by omega_arith]
      · exact v₁ i (by omega_arith)
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega_arith) (by omega_arith)
      · exact VG.Offset.contains B (by omega_arith) (by omega_arith) (by omega_arith)

/-- `k` loads of consecutive slots from `base` to distinct registers other
than `sb`. -/
theorem loads_ok {B : Addr} (base : Nat) (g : Nat → Reg) : ∀ (k : Nat) (s : State), s.gpr sb = B →
    (∀ i < k, g i ≠ sb) → (∀ i < k, ∀ j < k, g i = g j → i = j) → 8 * (base + k) < 32768 →
    (∀ i < k, InRegions (s.rd ++ s.wr) (wordAddr B (base + i)) 8) →
    ∃ s', runBlock isa ((List.range k).map fun i => ldS (g i) (base + i)) s = some s' ∧
      (∀ i < k, s'.gpr (g i) = s.mem.readW (wordAddr B (base + i)) 64) ∧
      (∀ r, (∀ i < k, r ≠ g i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, s, _, _, _, _, _ => ⟨s, rfl, fun i hi => by omega_arith, fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, s, hB, hsb, hinj, hk, hr => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := loads_ok base g k s hB (fun i hi => hsb i (by omega_arith))
      (fun i hi j hj => hinj i (by omega_arith) j (by omega_arith)) (by omega_arith) (fun i hi => hr i (by omega_arith))
    obtain hB₁ : s₁.gpr sb = B := by
      rw [o₁ _ (fun i hi h => hsb i (by omega_arith) h.symm), hB]
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (s := s₁) (b := B) (k := base + k) (g k) hB₁ (by omega_arith)
      (by rw [rd₁, wr₁]; exact hr k (by omega_arith))
    refine ⟨s₂, ?_, fun i hi => ?_, fun r hr' => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.map_append, runBlock_app, e₁, Option.bind_some, List.map_singleton, e₂]
    · by_cases h : i = k
      · subst h; rw [v₂, m₁]
      · rw [o₂ _ (fun he => h (hinj i hi k (by omega_arith) he)), v₁ i (by omega_arith)]
    · rw [o₂ r (hr' k (by omega_arith)), o₁ r (fun i hi => hr' i (by omega_arith))]

/-! ## Entry -/

/-- The mode's slots. -/
abbrev modeRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.slots), 96⟩

theorem ctrSetup_eq (c : Core) (r : CtrRegs) : c.ctrSetup r =
    ([.ldr .x .x6 r.ctr 0] : List Instr) ++ (([.rev .x6 .x6] : List Instr) ++
      (([.ldr .x .x7 r.ctr 8] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([stS c.hiSlot .x6] : List Instr) ++ (([stS c.loSlot .x7] : List Instr) ++
      (([.movz .x .x10 (BitVec.ofNat 16 0) 0] : List Instr) ++
      (([.adds .x .x7 .x7 r.n, .adc .x .x6 .x6 .x10] : List Instr) ++
      (([.rev .x6 .x6] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([.str .x .x7 r.ctr 8] : List Instr) ++ ([.str .x .x6 r.ctr 0] : List Instr))))))))))) := rfl

theorem ctrEntry_eq (c : Core) (r : CtrRegs) : c.ctrEntry r =
    ([movR sb r.scr] : List Instr) ++ ((List.range 10).map fun i => stS (c.slots + i) (Core.savedRegs.getD i .x19)) :=
  rfl

/-- The registers of a mode's arguments: none of them `sb`, nor a register
the entry writes (`x6`, `x7`, `x10`). -/
def SetupRegs : List Reg := [sb, .x6, .x7, .x10]

structure RegsOk (r : CtrRegs) : Prop where
  ctr : r.ctr ∉ SetupRegs
  data : r.data ∉ SetupRegs
  n : r.n ∉ SetupRegs

theorem not_setupRegs {r : Reg} (h : r ∉ SetupRegs) : r ≠ sb ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x10 := by
  simp only [SetupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

variable {c : Core}

/-- The entry block. -/
theorem setup_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.total) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctrSetup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 10, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .x19)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctrVal s.mem P + (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ∉ SetupRegs → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  obtain hN : 8 * c.total < 2 ^ 64 := by omega_arith
  obtain sl : ∀ k, c.slots ≤ k → k < c.total → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  obtain p0 : P + BitVec.ofNat 64 0 = P := by simp
  obtain ⟨cs, c6, c7, c10⟩ := not_setupRegs hr.ctr
  obtain ⟨ns, n6, n7, n10⟩ := not_setupRegs hr.n
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  obtain b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₁
    b₁' (fun i hi => by rw [wr₁]; exact sl _ (by omega_arith) (by omega_arith)) (by omega_arith)
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  obtain keep₂ : ∀ x, x ≠ sb → s₂.gpr x = s.gpr x := fun x hx => by rw [g₂, o₁ x hx]
  obtain P₂ : s₂.gpr r.ctr = P := by rw [keep₂ _ cs, hP]
  obtain fe : Frame [modeRegion c B] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega_arith) (by omega_arith)⟩
  obtain dP : ∀ k, c.slots ≤ k → k < c.total → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega_arith))).symm
  -- The counter.
  obtain inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega_arith)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  obtain mP : ∀ d, d + 8 ≤ 16 →
      s₂.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega_arith) (by omega_arith)) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by omega_arith))) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := ldr_ok s₂ .x6 r.ctr (off := 0) (by decide)
    (by rw [rd₂', wr₂', P₂]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rev_ok s₃ .x6 .x6
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ldr_ok s₄ .x7 r.ctr (off := 8) (by decide)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂', wr₂', o₄ _ (Ne.symm c6).symm, o₃ _ c6, P₂]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := rev_ok s₅ .x7 .x7
  obtain g₆ : ∀ x, x ≠ .x6 → x ≠ .x7 → s₆.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₆ x h2, o₅ x h2, o₄ x h1, o₃ x h1]
  obtain mP0 := mP 0 (by decide)
  rw [p0] at mP0
  obtain x6₆ : s₆.gpr .x6 = hiOf V := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₄, r₃, P₂, p0, mP0, hv]; rfl
  obtain x7₆ : s₆.gpr .x7 = loOf V := by
    rw [r₆, r₅, m₄, m₃, o₄ _ c6, o₃ _ c6, P₂, mP 8 (by decide), lv]; rfl
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂']
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂']
  obtain b₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide), g₂, b₁']
  obtain hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega_arith
  obtain hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega_arith
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := stS_ok (s := s₆) (b := B) (k := c.hiSlot) .x6 b₆ (by omega_arith)
    (by rw [wr₆']; exact sl _ (by simp only [Core.hiSlot]; omega_arith) hH)
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_ok (s := s₇) (b := B) (k := c.loSlot) .x7 (by rw [g₇, b₆]) (by omega_arith)
    (by rw [wr₇, wr₆']; exact sl _ (by simp only [Core.loSlot]; omega_arith) hLo)
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movz_ok s₈ .x10 (v := 0) (by decide)
  let N := (s.gpr r.n).toNat
  obtain n₉ : s₉.gpr r.n = BitVec.ofNat 64 N := by
    rw [o₉ _ n10, g₈, g₇, g₆ _ n6 n7, keep₂ _ ns]; simp [N]
  obtain ⟨s₁₀, e₁₀, h₁₀, l₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := addc_ok s₉ r.n (V := V) (N := N) (s.gpr r.n).isLt
    (by rw [o₉ _ (by decide), g₈, g₇, x6₆]) (by rw [o₉ _ (by decide), g₈, g₇, x7₆]) n₉ (by rw [r₉]; rfl)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := rev_ok s₁₀ .x6 .x6
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := rev_ok s₁₁ .x7 .x7
  obtain keep₁₂ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x10 → s₁₂.gpr x = s₆.gpr x := fun x h1 h2 h3 => by
    rw [o₁₂ x h2, o₁₁ x h1, o₁₀ x h1 h2, o₉ x h3, g₈, g₇]
  obtain P₁₂ : s₁₂.gpr r.ctr = P := by rw [keep₁₂ _ c6 c7 c10, g₆ _ c6 c7, P₂]
  obtain wr₁₂' : s₁₂.wr = s.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, wr₈, wr₇, wr₆']
  obtain ⟨s₁₃, e₁₃, m₁₃, g₁₃, rd₁₃, wr₁₃⟩ := str_ok s₁₂ .x7 r.ctr (off := 8) (by decide)
    (by rw [P₁₂, wr₁₂']; exact inP 8 (by decide))
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := str_ok s₁₃ .x6 r.ctr (off := 0) (by decide)
    (by rw [g₁₃, P₁₂, wr₁₃, wr₁₂']; exact inP 0 (by decide))
  obtain mem₈ : s₈.mem = (s₂.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₈, m₇, g₇, x6₆, x7₆, m₆, m₅, m₄, m₃]
  obtain mem₁₄ : s₁₄.mem = (s₈.mem.writeW (P + BitVec.ofNat 64 8) (rev64 (loOf (V + N)))).writeW P
      (rev64 (hiOf (V + N))) := by
    rw [m₁₄, g₁₃, P₁₂, p0, m₁₃, P₁₂, m₁₂, m₁₁, m₁₀, m₉, o₁₂ .x6 (by decide), r₁₁, h₁₀, r₁₂, o₁₁ .x7 (by decide),
      l₁₀]
  -- The frames.
  obtain fS : Frame [modeRegion c B] s₂.mem s₈.mem := by
    rw [mem₈]
    obtain hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega_arith)
      (by simp only [Core.hiSlot]; omega_arith) (by omega_arith))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith) (by omega_arith))
  obtain fP : Frame [⟨P, 16⟩] s₈.mem s₁₄.mem := by
    rw [mem₁₄]
    obtain hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  obtain thruP : ∀ k, c.slots ≤ k → k < c.total →
      s₁₄.mem.readW (wordAddr B k) 64 = s₈.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  obtain b8 : ∀ k, k < c.total → 8 * k < 2 ^ 64 := fun k hk => by omega_arith
  obtain mem8 : ∀ k, c.slots ≤ k → k < c.total → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₈.mem.readW (wordAddr B k) 64 = s₂.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₈, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH),
      ite_eq_right hh]
  obtain hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  refine ⟨s₁₄, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆'], by rw [wr₁₄, wr₁₃, wr₁₂']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctrSetup_eq,
      runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some,
      runBlock_app, e₉, Option.bind_some, runBlock_app, e₁₀, Option.bind_some, runBlock_app, e₁₁,
      Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃, Option.bind_some, e₁₄]
  · rw [g₁₄, g₁₃, keep₁₂ _ (by decide) (by decide) (by decide), b₆]
  · have k1 : c.slots ≤ c.slots + i := by omega_arith
    obtain k2 : c.slots + i < c.total := by omega_arith
    rw [thruP _ k1 k2, mem8 _ k1 k2 (by simp only [Core.hiSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith),
      v₂ i hi, o₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega_arith) hH, mem₈,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega_arith) hLo, mem₈, Mem.readW_writeW_self64]
  · rw [mem₁₄]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · obtain ⟨h1, h2, h3, h4⟩ := not_setupRegs hx
    rw [g₁₄, g₁₃, keep₁₂ x h2 h3 h4, g₆ x h2 h3, keep₂ x h1]

/-- The data's address and `n` to `dataReg` and `leftReg`. -/
theorem ctrArgs_ok (s : State) (r : CtrRegs) (hd : c.dataReg ≠ r.n) (hdl : c.dataReg ≠ c.leftReg) :
    ∃ s', runBlock isa (c.ctrArgs r) s = some s' ∧ s'.gpr c.dataReg = s.gpr r.data ∧
      s'.gpr c.leftReg = s.gpr r.n ∧ (∀ x, x ≠ c.dataReg → x ≠ c.leftReg → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s c.dataReg r.data
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ c.leftReg r.n
  refine ⟨s₂, ?_, ?_, by rw [r₂, o₁ _ (Ne.symm hd)], fun x h1 h2 => by rw [o₂ x h2, o₁ x h1], by rw [m₂, m₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [Core.ctrArgs, show ([movR c.dataReg r.data, movR c.leftReg r.n] : List Instr) =
      [movR c.dataReg r.data] ++ [movR c.leftReg r.n] from rfl, runBlock_app, e₁, Option.bind_some, e₂]
  · rw [o₂ _ hdl, r₁]

end VG.Proof.Modes.AArch64
