import VerifiedGarbage.Proof.Modes.X86_64.Setup
import VerifiedGarbage.Proof.Modes.X86_64.Xor
import VerifiedGarbage.Proof.Modes.Ctr

/-!
# One group of blocks of CTR on x86-64, for any core

`ctrGroup_wp`: one iteration of the data loop writes the group's `G`
counter blocks to the core's buffer (`ctrBlocks_ok`), encrypts them there
(`CoreSpec.crypt_wp`), XORs the first `min(G, left)` into the group's blocks
(`xorBlocks_wp`) and steps to the next group. Block `j` of the data becomes
CTR's output block `j` (`ctrOut`).
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- `rcx := min(left, G)`. -/
theorem groupCount_wp (hL : Layout c) (hlc : c.leftReg ≠ .rcx) {s : State} {v : Nat}
    (hv : s.gpr c.leftReg = BitVec.ofNat 64 v) (hv64 : v < 2 ^ 64) :
    WP isa c.groupCount s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min v c.G) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hG : c.G < 2 ^ 31 := by have := hL.buf_le; have := hL.room; omega
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s .rcx (BitVec.ofNat 64 c.G)
  obtain ⟨s₃, e₃, f₃, g₃, m₃, rd₃, wr₃⟩ := cmpImm_ok s₂ c.leftReg (BitVec.ofNat 32 c.G) (v := v) (K := c.G)
    (by rw [o₂ _ hlc, hv]) hv64 (by rw [signExtend_small hG, BitVec.toNat_ofNat]; omega)
  unfold Core.groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [show ([.movImm64 .rcx (BitVec.ofNat 64 c.G), .alu .cmp c.leftReg (.imm (BitVec.ofNat 32 c.G))] : List Instr) =
        [.movImm64 .rcx (BitVec.ofNat 64 c.G)] ++ [.alu .cmp c.leftReg (.imm (BitVec.ofNat 32 c.G))] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  refine WP.ite (decide (v < c.G)) (by simp [X86_64.eval, f₃]) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rcx c.leftReg
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 => ?_, by rw [m₄, m₃, m₂], by rw [rd₄, rd₃, rd₂],
      by rw [wr₄, wr₃, wr₂]⟩
    · rw [r₄, g₃, o₂ _ hlc, hv, Nat.min_eq_left (by simp at h; omega)]
    · rw [o₄ r h1, g₃, o₂ r h1]
  · refine WP.of_runBlock ⟨s₃, rfl, ?_, fun r h1 => ?_, by rw [m₃, m₂], by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    · rw [g₃, r₂, Nat.min_eq_right (by simp at h; omega)]
    · rw [g₃, o₂ r h1]

/-- The buffer's address to `rax`, the data's to `rbx`, the count to `r10`. -/
theorem xorArgs_ok (hL : Layout c) (hda : c.dataReg ≠ .rax) (s : State) {B : Addr} (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.xorArgs s = some s' ∧ s'.gpr .rax = B + BitVec.ofNat 64 (8 * c.buf) ∧
      s'.gpr .rbx = s.gpr c.dataReg ∧ s'.gpr .r10 = s.gpr .rcx ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hs := hL.small
  have hb := hL.buf_le
  have hroom := hL.room
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rax sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rax (BitVec.ofNat 32 (8 * c.buf))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rbx c.dataReg
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .r10 .rcx
  refine ⟨s₄, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.xorArgs, show ([movR .rax sb, .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf))), movR .rbx c.dataReg,
        movR .r10 .rcx] : List Instr) = [movR .rax sb] ++ (([.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))] :
        List Instr) ++ (([movR .rbx c.dataReg] : List Instr) ++ [movR .r10 .rcx])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB, signExtend_small (by omega)]
  · rw [o₄ _ (by decide), r₃, o₂ _ hda, o₁ _ hda]
  · rw [r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  · rw [o₄ r h3, o₃ r h2, o₂ r h1, o₁ r h1]

/-- On past the group's blocks: the data's address from `rbx`, the count
from `r10` off the blocks left; ZF is set when none are left. -/
theorem advance_ok (hdl : c.dataReg ≠ c.leftReg) (hd10 : c.dataReg ≠ .r10) (s : State) :
    ∃ s', runBlock isa c.advance s = some s' ∧ s'.gpr c.dataReg = s.gpr .rbx ∧
      s'.gpr c.leftReg = s.gpr c.leftReg - s.gpr .r10 ∧
      s'.zf = some (s.gpr c.leftReg - s.gpr .r10 == 0) ∧
      (∀ r, r ≠ c.dataReg → r ≠ c.leftReg → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s c.dataReg .rbx
  obtain ⟨s₂, e₂, r₂, z₂, o₂, m₂, rd₂, wr₂⟩ := subReg_ok s₁ c.leftReg .r10
  have l₁ : s₁.gpr c.leftReg = s.gpr c.leftReg := o₁ _ (Ne.symm hdl)
  have t₁ : s₁.gpr .r10 = s.gpr .r10 := o₁ _ (Ne.symm hd10)
  refine ⟨s₂, ?_, by rw [o₂ _ hdl, r₁], by rw [r₂, l₁, t₁], by rw [z₂, l₁, t₁],
    fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [Core.advance, show ([movR c.dataReg .rbx, .alu .sub c.leftReg (.reg .r10)] : List Instr) =
    [movR c.dataReg .rbx] ++ [.alu .sub c.leftReg (.reg .r10)] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- What the data loop works on: the scratch buffer at `B`, the `n` blocks at
`D`. -/
structure GPre (c : Core) (s₀ : State) (B D : Addr) (n : Nat) : Prop where
  scr : ScrIn s₀ B c.ctrSlots
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.ctrSlots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 64

/-- The data loop, before group `g`, from the counter block `V` with the key
`k`. -/
structure GInv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s.mem B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  hi : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (V + c.G * g)
  lo : s.mem.readW (wordAddr B c.loSlot) 64 = loOf (V + c.G * g)
  data : DInv s₀.mem s.mem D n (c.G * g) (ctrOut (cs.cipher k) s₀.mem D V)
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv s₀.mem s.mem D n n (ctrOut (cs.cipher k) s₀.mem D V)
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Byte `u` of the 16 at `p`. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {u : Nat} (hu : u < 16) :
    (bytesAt m p 16).getD u 0 = m (p + BitVec.ofNat 64 u) := by
  simp [bytesAt, hu]

theorem ctrGroup_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : GInv cs s₀ B D n k V g s) :
    WP isa c.ctrGroup s fun s' => (s'.zf = some true ∧ GDone cs s₀ B D n k V s') ∨
      (s'.zf = some false ∧ GInv cs s₀ B D n k V (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, dc, dbp, d10, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, lc, lbp, l10, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  let v := n - c.G * g
  let cc := min v c.G
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < cc := by omega
  have hcG : cc ≤ c.G := by omega
  have hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.ctrSlots → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ := Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have mSlot : ∀ j, c.slots ≤ j → j < c.ctrSlots → ∀ r ∈ [coreRegion c B],
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base B (by omega) (by omega)
  have inT : ∀ t, t < 2 * c.G → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega) (by omega)
  have inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega) (by omega)
  have sepAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right (subS (by simp only [Core.ctrSlots]; omega))
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctrBlocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctrGroup
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide) (by decide) (by decide), hi.base]
  have subBC : ∀ r ∈ [bufRegion c B, ctrRegion c B], Region.Sub r ⟨B, 8 * c.ctrSlots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> simp only [Core.hiSlot, Core.ctrSlots] <;> omega
  have ready₁ : cs.Ready s₁.mem B k := cs.ready_frame hi.ready f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr fun _ h => h
    · exact .inl (VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega)
        (by simp only [Core.hiSlot]; omega)).symm
  -- The keystream.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (mSlot j h1 h2) (by decide)
  have keep₁ : ∀ j, c.slots ≤ j → j < c.slots + 6 →
      s₁.mem.readW (wordAddr B j) 64 = s.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint B (Or.inr (by omega)) (by omega) (by omega)
      · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega) (by omega)
          (by simp only [Core.hiSlot]; omega)) (by decide)
  -- The count.
  have left₂ : s₂.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₂, o₁ _ la lb lc, hi.leftR]
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, o₁ _ da db dc, hi.dataR]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  refine WP.seq (WP.mono (groupCount_wp hL lc left₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_)
  have base₃ : s₃.gpr sb = B := by rw [o₃ _ (by decide), base₂]
  obtain ⟨s₄, e₄, a₄, b₄, t₄, o₄, m₄, rd₄, wr₄⟩ := xorArgs_ok hL da s₃ base₃
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  -- The keystream XORed into the group's blocks.
  refine WP.seq (WP.mono (xorBlocks_wp (A := T) (B := A) hc0 (by omega)
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega)))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [a₄]; simp [T], by rw [b₄, o₃ _ dc, data₂]; simp [A],
      by rw [o₄ _ (by decide) (by decide) (by decide), c₃, Nat.sub_zero], fun t ht => by omega, fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨A, 16 * cc⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact h₅.frame
  have g₅ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₅.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 => h₅.regs r h1 h2 h3 h4
  have keep₄ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → s₅.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₅ r h1 h2 h3 h4, o₄ r h1 h2 h5, o₃ r h3]
  have base₅ : s₅.gpr sb = B := by
    rw [keep₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), base₂]
  have left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 v := by rw [keep₄ _ la lb lc lbp l10, left₂]
  have r10₅ : s₅.gpr .r10 = BitVec.ofNat 64 cc := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), t₄, c₃]
  have rbx₅ : s₅.gpr .rbx = A + BitVec.ofNat 64 (16 * cc) := h₅.rbx
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [keep₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsp₂,
      o₁ _ (by decide) (by decide) (by decide), hi.rsp]
  have wr₅' : s₅.wr = s.wr := by rw [h₅.wr, wr₄']
  have rd₅' : s₅.rd = s.rd := by rw [h₅.rd, rd₄']
  have keep₅ : ∀ j, j < c.ctrSlots → s₅.mem.readW (wordAddr B j) 64 = s₂.mem.readW (wordAddr B j) 64 :=
    fun j hj => f₅.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right
        (subS (by omega))).symm) (by decide)
  -- On to the next group.
  obtain ⟨s₆, e₆, d₆, l₆, z₆, o₆, m₆, rd₆, wr₆⟩ := advance_ok hdl d10 s₅
  have hz : s₆.zf = some (decide (v = cc)) := by
    rw [z₆, left₅, r10₅, VG.Offset.ofNat_sub_ofNat_beq hv (by omega)]
  have ready₆ : cs.Ready s₆.mem B k := by
    rw [m₆]
    refine cs.ready_frame ready₂ f₅ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right subCore).symm)
  -- The data.
  have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨B, 8 * c.ctrSlots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have dCore : ∀ r ∈ [coreRegion c B], Region.Disjoint ⟨D, 16 * n⟩ r := hdS fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact subCore
  have hn64 : 16 * n ≤ 2 ^ 64 := by omega
  have via₁₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [f₂.bytes (R := ⟨D, 16 * n⟩) dCore hn64 hin, f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subBC) hn64 hin]
  have hdata : DInv s₀.mem s₆.mem D n (c.G * g + cc) (ctrOut (cs.cipher k) s₀.mem D V) := by
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
  have saved₆ : ∀ i < 6, s₆.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [m₆, keep₅ _ (by simp only [Core.ctrSlots]; omega), keep₂ _ (by omega) (by simp only [Core.ctrSlots]; omega),
      keep₁ _ (by omega) (by omega), hi.saved i hi6]
  have hiSlot₆ : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
      s₆.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
    have h1 : c.slots ≤ j := by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega
    have h2 : j < c.ctrSlots := by
      rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot, Core.ctrSlots] <;> omega
    rw [m₆, keep₅ j h2, keep₂ j h1 h2]
  have fr₆ : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] s.mem s₆.mem := by
    rw [m₆]
    refine ((f₁.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, subBC r hr⟩).trans
      (f₂.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₅.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base D (by omega)⟩
  have fr : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] s₀.mem s₆.mem := hi.frame.trans fr₆
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (Ne.symm dsb) (Ne.symm lsb), base₅]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by rw [o₆ _ (Ne.symm dsp) (Ne.symm lsp), rsp₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅', hi.rd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅', hi.wr]
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], base₆, rsp₆, saved₆, ?_, fr, rd₆', wr₆'⟩
    rw [show n = c.G * g + cc by omega] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₆, rsp₆, ready₆, saved₆, ?_, ?_,
      by rw [Nat.mul_succ]; omega, ?_, ?_,
      by rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact hdata, fr, rd₆', wr₆'⟩
    · rw [d₆, rbx₅, addr_add, hcc,
        show 16 * (c.G * g) + 16 * c.G = 16 * (c.G * (g + 1)) by rw [Nat.mul_succ]; omega]
    · rw [l₆, left₅, r10₅, VG.Offset.ofNat_sub_ofNat (by omega), hcc,
        show v - c.G = n - c.G * (g + 1) by rw [Nat.mul_succ]; omega]
    · rw [hiSlot₆ _ (.inl rfl), h₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega]
    · rw [hiSlot₆ _ (.inr rfl), l₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega]

end VG.Proof.Modes.X86_64
