import VerifiedGarbage.Proof.Modes.AArch64.Setup
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Ctr

/-!
# One group of blocks of CTR on AArch64, for any core

`ctrGroup_wp`: one iteration of the data loop writes the group's `G`
counter blocks to the core's buffer (`ctrBlocks_ok`), encrypts them there
(`CoreSpec.crypt_wp`), XORs the first `min(G, left)` into the group's blocks
(`xorBlocks_wp`) and steps to the next group. Block `j` of the data becomes
CTR's output block `j` (`ctrOut`).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem lsr_beq {v k : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> k == 0) = decide (v < 2 ^ k) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  have := Nat.two_pow_pos k
  have e : (BitVec.ofNat 64 v >>> k).toNat = v / 2 ^ k := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [e, show (0 : BitVec 64).toNat = 0 from rfl, Nat.div_eq_zero_iff] at h'
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e, show (0 : BitVec 64).toNat = 0 from rfl, Nat.div_eq_zero_iff]
    omega

/-- `x16 := min(left, G)`. -/
theorem groupCount_wp (hL : Layout c) (hl13 : c.leftReg ≠ .x13) {s : State} {v : Nat}
    (hv : s.gpr c.leftReg = BitVec.ofNat 64 v) (hv64 : v < 2 ^ 64) :
    WP isa c.groupCount s fun s' => s'.gpr .x16 = BitVec.ofNat 64 (min v c.G) ∧
      (∀ r, r ≠ .x13 → r ≠ .x16 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hG := hL.G_lt
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := lsr_ok s .x13 c.leftReg (sh := c.lgG) (by have := hL.lgG_lt; omega)
  unfold Core.groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hz : isa.eval (.nonzero .x .x13) s₁ = some !(decide (v < c.G)) := by
    rw [eval_nonzero, r₁, hv, lsr_beq hv64]; rfl
  refine WP.ite (!(decide (v < c.G))) hz (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movz_ok s₁ .x16 (v := c.G) hG
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [r₂, Nat.min_eq_right (by simp at h; omega)]
    · rw [o₂ r h2, o₁ r h1]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .x16 c.leftReg
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [r₂, o₁ _ hl13, hv, Nat.min_eq_left (by simp at h; omega)]
    · rw [o₂ r h2, o₁ r h1]

/-- The buffer's address to `x14`, the data's to `x15`, the count to `x17`. -/
theorem xorArgs_ok (hL : Layout c) (hd14 : c.dataReg ≠ .x14) (s : State) {B : Addr} (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.xorArgs s = some s' ∧ s'.gpr .x14 = B + BitVec.ofNat 64 (8 * c.buf) ∧
      s'.gpr .x15 = s.gpr c.dataReg ∧ s'.gpr .x17 = s.gpr .x16 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x14 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x14 .x14 hL.bufImm
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
  have l₁ : s₁.gpr c.leftReg = s.gpr c.leftReg := o₁ _ (Ne.symm hdl)
  have t₁ : s₁.gpr .x16 = s.gpr .x16 := o₁ _ (Ne.symm hd16)
  refine ⟨s₂, ?_, by rw [o₂ _ hdl, r₁], by rw [r₂, l₁, t₁],
    fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [Core.advance, show ([movR c.dataReg .x15, .sub .x c.leftReg c.leftReg .x16] : List Instr) =
    [movR c.dataReg .x15] ++ [.sub .x c.leftReg c.leftReg .x16] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- What the data loop works on: the scratch buffer at `B`, the `n` blocks at
`D`. -/
structure GPre (c : Core) (s₀ : State) (B D : Addr) (n : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.total⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 64

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
theorem bytesAt_getD (m : Mem) (p : Addr) {u : Nat} (hu : u < 16) :
    (bytesAt m p 16).getD u 0 = m (p + BitVec.ofNat 64 u) := by
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
  have nown : ∀ {r : Reg}, r ∉ ownRegs → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x13 ∧
      r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := fun h => by
    simp only [ownRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h; exact h
  obtain ⟨-, -, -, -, -, d13, d14, -, d16, -⟩ := nown down
  obtain ⟨-, -, -, -, -, l13, l14, l15, l16, l17⟩ := nown lown
  have hN : 8 * c.total < 2 ^ 64 := by omega
  let v := n - c.G * g
  let cc := min v c.G
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < cc := by omega
  have hcG : cc ≤ c.G := by omega
  have hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.total → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.total⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega)
  have mSlot : ∀ j, c.slots ≤ j → j < c.total → ∀ r ∈ [coreRegion c B],
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base B (by omega) (by omega)
  have inT : ∀ t, t < 2 * c.G → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base B (by omega) (by omega)
  have inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega) (by omega)
  have sepAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right (subS (by omega))
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctrBlocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctrGroup
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide), hi.base]
  have subBC : ∀ r ∈ [bufRegion c B, ctrRegion c B], Region.Sub r ⟨B, 8 * c.total⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> (try simp only [Core.hiSlot]) <;> omega
  have ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr fun _ h => h
    · exact .inl (VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega)
        (by simp only [Core.hiSlot]; omega)).symm) fun r hr => o₁ r (of_not_modeRegs hr).1
  -- The keystream.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (mSlot j h1 h2) (by decide)
  have keep₁ : ∀ j, c.slots ≤ j → j < c.slots + 10 →
      s₁.mem.readW (wordAddr B j) 64 = s.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint B (Or.inr (by omega)) (by omega) (by omega)
      · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega) (by omega)
          (by simp only [Core.hiSlot]; omega)) (by decide)
  -- The count.
  have left₂ : s₂.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₂, o₁ _ lown, hi.leftR]
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, o₁ _ down, hi.dataR]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  refine WP.seq (WP.mono (groupCount_wp hL l13 left₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_)
  have base₃ : s₃.gpr sb = B := by rw [o₃ _ (by decide) (by decide), base₂]
  obtain ⟨s₄, e₄, a₄, b₄, t₄, o₄, m₄, rd₄, wr₄⟩ := xorArgs_ok hL d14 s₃ base₃
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  -- The keystream XORed into the group's blocks.
  refine WP.seq (WP.mono (xorBlocks_wp (A := T) (B := A) hc0 (by omega)
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega)))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [a₄]; simp [T], by rw [b₄, o₃ _ d13 d16, data₂]; simp [A],
      by rw [t₄, c₃, Nat.sub_zero], fun t ht => by omega, fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨A, 16 * cc⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact h₅.frame
  have keep₄ : ∀ r, r ∉ ownRegs → s₅.gpr r = s₂.gpr r := fun r hr => by
    obtain ⟨-, -, h8, h9, -, h13, h14, h15, h16, h17⟩ := nown hr
    rw [h₅.regs r h8 h9 h14 h15 h17, o₄ r h14 h15 h17, o₃ r h13 h16]
  have base₅ : s₅.gpr sb = B := by rw [keep₄ _ (by decide), base₂]
  have left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 v := by rw [keep₄ _ lown, left₂]
  have x16₅ : s₅.gpr .x16 = BitVec.ofNat 64 cc := by
    rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), o₄ _ (by decide) (by decide) (by decide),
      c₃]
  have x15₅ : s₅.gpr .x15 = A + BitVec.ofNat 64 (16 * cc) := h₅.x15
  have wr₅' : s₅.wr = s.wr := by rw [h₅.wr, wr₄']
  have rd₅' : s₅.rd = s.rd := by rw [h₅.rd, rd₄']
  have keep₅ : ∀ j, j < c.total → s₅.mem.readW (wordAddr B j) 64 = s₂.mem.readW (wordAddr B j) 64 :=
    fun j hj => f₅.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right
        (subS (by omega))).symm) (by decide)
  -- On to the next group.
  obtain ⟨s₆, e₆, d₆, l₆, o₆, m₆, rd₆, wr₆⟩ := advance_ok hdl d16 s₅
  have left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (v - cc) := by
    rw [l₆, left₅, x16₅, VG.Offset.ofNat_sub_ofNat (by omega)]
  have hz : isa.eval (.nonzero .x c.leftReg) s₆ = some !(decide (v = cc)) := by
    rw [eval_nonzero, left₆, ofNat_beq_zero (by omega)]
    congr 2
    exact decide_eq_decide.mpr (by omega)
  have ready₆ : cs.Ready s₆ B k := by
    refine cs.ready_frame ready₂ (by rw [m₆]; exact f₅) (fun r hr => ?_) fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right subCore).symm)
    · obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
      rw [o₆ r h2 h3, keep₄ r h1]
  -- The data.
  have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨B, 8 * c.total⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have dCore : ∀ r ∈ [coreRegion c B], Region.Disjoint ⟨D, 16 * n⟩ r := hdS fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact subCore
  have hn64 : 16 * n ≤ 2 ^ 64 := by omega
  have via₁₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [f₂.bytes (R := ⟨D, 16 * n⟩) dCore hn64 hin, f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subBC) hn64 hin]
  have hdata : DInv 16 s₀.mem s₆.mem D n (c.G * g + cc) (ctrOut (cs.cipher k) s₀.mem D V) := by
    intro i hin
    rw [m₆]
    by_cases hin1 : 16 * (c.G * g) ≤ i ∧ i < 16 * (c.G * g) + 16 * cc
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 16 * (c.G * g)) := by
        rw [addr_add, show 16 * (c.G * g) + (i - 16 * (c.G * g)) = i by omega]
      let t := i - 16 * (c.G * g)
      have hj : t / 16 < c.G := by omega
      have hu : t % 16 < 16 := Nat.mod_lt _ (by decide)
      have eT : T + BitVec.ofNat 64 t = bufAddr c B (t / 16) + BitVec.ofNat 64 (t % 16) := by
        simp only [T, bufAddr]
        rw [addr_add, addr_add, show 8 * c.buf + 16 * (t / 16) + t % 16 = 8 * c.buf + t by omega]
      have hks : s₂.mem (T + BitVec.ofNat 64 t) =
          (cs.cipher k (Spec.Ctr.ofNat (V + c.G * g + t / 16) 16)).getD (t % 16) 0 := by
        rw [eT, ← bytesAt_getD s₂.mem _ hu, ks₂ _ hj, tb₁ _ hj]
      have hd₂ : s₂.mem (A + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 i) := by
        rw [← e1, via₁₂ i hin, hi.data i hin, ite_eq_right (by omega)]
      rw [e1, h₅.xored _ (by omega), mem₄, hks, hd₂, ite_eq_left (show i < 16 * (c.G * g + cc) by omega),
        ctrOut_getD (cs.cipher_len k) _ _ _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega,
        show V + c.G * g + t / 16 = V + i / 16 by omega, show t % 16 = i % 16 by omega, BitVec.xor_comm]
    · have hout : ∀ r ∈ [(⟨A, 16 * cc⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega) (by omega) (by omega) (by omega)
      rw [f₅ _ hout, via₁₂ i hin, hi.data i hin]
      by_cases h2 : i < 16 * (c.G * g)
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (c.G * g + cc) by omega)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * (c.G * g + cc) by omega)]
  -- The slots.
  have saved₆ : ∀ i < 10, s₆.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [m₆, keep₅ _ (by omega), keep₂ _ (by omega) (by omega), keep₁ _ (by omega) (by omega), hi.saved i hi10]
  have hiSlot₆ : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
      s₆.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
    have h1 : c.slots ≤ j := by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega
    have h2 : j < c.total := by
      rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega
    rw [m₆, keep₅ j h2, keep₂ j h1 h2]
  have fr₆ : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s.mem s₆.mem := by
    rw [m₆]
    refine ((f₁.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, subBC r hr⟩).trans
      (f₂.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₅.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base D (by omega)⟩
  have fr : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s₆.mem := hi.frame.trans fr₆
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (Ne.symm dsb) (Ne.symm lsb), base₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅', hi.rd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅', hi.wr]
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₆, saved₆, ?_, fr, rd₆', wr₆'⟩
    rw [show n = c.G * g + cc by omega] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₆, ready₆, saved₆, ?_, ?_,
      by rw [Nat.mul_succ]; omega, ?_, ?_,
      by rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact hdata, fr, rd₆', wr₆'⟩
    · rw [d₆, x15₅, addr_add, hcc,
        show 16 * (c.G * g) + 16 * c.G = 16 * (c.G * (g + 1)) by rw [Nat.mul_succ]; omega]
    · rw [left₆, hcc, show v - c.G = n - c.G * (g + 1) by rw [Nat.mul_succ]; omega]
    · rw [hiSlot₆ _ (.inl rfl), h₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega]
    · rw [hiSlot₆ _ (.inr rfl), l₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega]

end VG.Proof.Modes.AArch64
