module

public import VerifiedGarbage.Proof.Modes.AArch64.Group
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr32
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Counter32
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Modes.AArch64.Setup
import VerifiedGarbage.Proof.Modes.AArch64.Ctr

/-! ### `Modes.AArch64.Group32`, which only this module used -/

section

/-!
# One group of blocks of counter mode with `inc₃₂` on AArch64, for any core

`ctr32Group_wp`: `ctrGroup_wp` (`Group.lean`) for `ctr32`'s groups, whose
counter blocks are `inc₃₂`'s (`ctr32Blocks_ok`): block `j` of the data
becomes the XOR with the encryption of `ctr32Val V j` (`ctr32Out`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The data loop of `ctr32`, before group `g`, from the counter block `V` with the key
`k`. -/
structure GInv32 (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  hi : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctr32Val V (c.G * g))
  lo : s.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctr32Val V (c.G * g))
  data : DInv 16 s₀.mem s.mem D n (c.G * g) (ctr32Out (cs.cipher k) s₀.mem D V)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop of `ctr32`, done. -/
structure GDone32 (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv 16 s₀.mem s.mem D n n (ctr32Out (cs.cipher k) s₀.mem D V)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ctr32Group_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : GInv32 cs s₀ B D n k V g s) :
    WP isa c.ctr32Group s fun s' => (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ GDone32 cs s₀ B D n k V s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ GInv32 cs s₀ B D n k V (g + 1) s') := by
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
  have hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  have hv : v < 2 ^ 64 := by omega_using [hfitD]
  have hc0 : 0 < cc := by omega_using [hG0, hk]
  have hcG : cc ≤ c.G := by omega_using []
  have hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega_using [hc0]
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.total → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.total⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega_using [hroom])
  have mSlot : ∀ j, c.slots ≤ j → j < c.total → ∀ r ∈ [coreRegion c B],
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base B (by omega_using [h1]) (by omega_using [hN, h2])
  have inT : ∀ t, t < 2 * c.G → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base B (by omega_using [hroom, hbuf, ht]) (by omega_using [hroom, hbuf, hN, ht])
  have inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_using [ht]) (by omega_using [hfitD, ht])
  have sepAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right (subS (by omega_using [hroom, hbuf]))
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctr32Blocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctr32Group
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide), hi.base]
  have subBC : ∀ r ∈ [bufRegion c B, ctrRegion c B], Region.Sub r ⟨B, 8 * c.total⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> (try simp only [Core.hiSlot]) <;> omega_using [hroom, hbuf]
  have ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
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
  have keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (mSlot j h1 h2) (by decide)
  have keep₁ : ∀ j, c.slots ≤ j → j < c.slots + 10 →
      s₁.mem.readW (wordAddr B j) 64 = s.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint B (Or.inr (by omega_using [hbuf, h1])) (by omega_using [hroom, hN, h2]) (by omega_using [hroom, hbuf, hN])
      · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_using [h2]) (by omega_using [hroom, hN, h2])
          (by simp only [Core.hiSlot]; omega_using [hroom, hN])) (by decide)
  -- The count.
  have left₂ : s₂.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₂, o₁ _ lown, hi.leftR]
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, o₁ _ down, hi.dataR]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  refine WP.seq (WP.mono_syms (groupCount_wp hL.lgG_lt l13 left₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ sy₃ => ?_)
  have base₃ : s₃.gpr sb = B := by rw [o₃ _ (by decide) (by decide), base₂]
  obtain ⟨s₄, e₄, a₄, b₄, t₄, o₄, m₄, rd₄, wr₄⟩ := xorArgs_ok hL.bufImm d14 s₃ base₃
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  -- The keystream XORed into the group's blocks.
  refine WP.seq (WP.mono_syms (xorBlocks_wp (A := T) (B := A) hc0 (by omega_using [hsm, hroom, hbuf])
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega_using [ht])))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [a₄]; simp [T], by rw [b₄, o₃ _ d13 d16, data₂]; simp [A],
      by rw [t₄, c₃, Nat.sub_zero], fun t ht => by omega_using [ht], fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ sy₅ => ?_)
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
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right
        (subS (by omega_using [hj]))).symm) (by decide)
  -- On to the next group.
  obtain ⟨s₆, e₆, d₆, l₆, o₆, m₆, rd₆, wr₆⟩ := advance_ok hdl d16 s₅
  have left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (v - cc) := by
    rw [l₆, left₅, x16₅, VG.Offset.ofNat_sub_ofNat (by omega_using [])]
  have hz : isa.eval (.nonzero .x c.leftReg) s₆ = some !(decide (v = cc)) := by
    rw [eval_nonzero, left₆, ofNat_beq_zero (by omega_using [hv]), decide_eq_decide.mpr (show v - cc = 0 ↔ v = cc by omega_using [])]
  have ready₆ : cs.Ready s₆ B k := by
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
  have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨B, 8 * c.total⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have dCore : ∀ r ∈ [coreRegion c B], Region.Disjoint ⟨D, 16 * n⟩ r := hdS fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact subCore
  have hn64 : 16 * n ≤ 2 ^ 64 := by omega_using [hfitD]
  have via₁₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [f₂.bytes (R := ⟨D, 16 * n⟩) dCore hn64 hin, f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subBC) hn64 hin]
  have hdata : DInv 16 s₀.mem s₆.mem D n (c.G * g + cc) (ctr32Out (cs.cipher k) s₀.mem D V) := by
    intro i hin
    rw [m₆]
    by_cases hin1 : 16 * (c.G * g) ≤ i ∧ i < 16 * (c.G * g) + 16 * cc
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 16 * (c.G * g)) := by
        rw [addr_add, show 16 * (c.G * g) + (i - 16 * (c.G * g)) = i by omega_using [hin1]]
      let t := i - 16 * (c.G * g)
      have hj : t / 16 < c.G := by omega_using [hin1]
      have hu : t % 16 < 16 := Nat.mod_lt _ (by decide)
      have eT : T + BitVec.ofNat 64 t = bufAddr c B (t / 16) + BitVec.ofNat 64 (t % 16) := by
        simp only [T, bufAddr]
        rw [addr_add, addr_add, show 8 * c.buf + 16 * (t / 16) + t % 16 = 8 * c.buf + t by omega_using []]
      have hks : s₂.mem (T + BitVec.ofNat 64 t) =
          (cs.cipher k (Spec.Ctr.ofNat (ctr32Val (ctr32Val V (c.G * g)) (t / 16)) 16)).getD (t % 16) 0 := by
        rw [eT, ← bytesAt_getD s₂.mem _ hu, ks₂ _ hj, tb₁ _ hj]
      have hd₂ : s₂.mem (A + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 i) := by
        rw [← e1, via₁₂ i hin, hi.data i hin, ite_eq_right (by omega_using [hin1])]
      rw [e1, h₅.xored _ (by omega_using [hin1]), mem₄, hks, hd₂, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [hin1]),
        ctr32Out_getD (cs.cipher_len k) _ _ _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega_using [],
        ctr32Val_add, show c.G * g + t / 16 = i / 16 by omega_using [hin1], show t % 16 = i % 16 by omega_using [hin1], BitVec.xor_comm]
    · have hout : ∀ r ∈ [(⟨A, 16 * cc⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_using [hin1]) (by omega_using [hn64, hin]) (by omega_using [hc0]) (by omega_using [hkc, hn64])
      rw [f₅ _ hout, via₁₂ i hin, hi.data i hin]
      by_cases h2 : i < 16 * (c.G * g)
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [h2])]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * (c.G * g + cc) by omega_using [hin1, h2])]
  -- The slots.
  have saved₆ : ∀ i < 10, s₆.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [m₆, keep₅ _ (by omega_using [hroom, hi10]), keep₂ _ (by omega_using []) (by omega_using [hroom, hi10]), keep₁ _ (by omega_using []) (by omega_using [hi10]), hi.saved i hi10]
  have hiSlot₆ : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
      s₆.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
    have h1 : c.slots ≤ j := by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using []
    have h2 : j < c.total := by
      rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using [hroom]
    rw [m₆, keep₅ j h2, keep₂ j h1 h2]
  have fr₆ : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s.mem s₆.mem := by
    rw [m₆]
    refine ((f₁.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, subBC r hr⟩).trans
      (f₂.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₅.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base D (by omega_using [hkc])⟩
  have fr : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s₆.mem := hi.frame.trans fr₆
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (Ne.symm dsb) (Ne.symm lsb), base₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅', hi.rd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅', hi.wr]
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
    · rw [hiSlot₆ _ (.inl rfl), h₁, ctr32Val_add, show c.G * g + c.G = c.G * (g + 1) by rw [Nat.mul_succ]]
    · rw [hiSlot₆ _ (.inr rfl), l₁, ctr32Val_add, show c.G * g + c.G = c.G * (g + 1) by rw [Nat.mul_succ]]

end VG.Proof.Modes.AArch64

end

end

/-! ### `Modes.AArch64.Setup32`, which only this module used -/

section

/-!
# Counter mode with `inc₃₂` on AArch64: the entry

`setup32_ok`: the entry block of `ctr32` does what `ctr`'s does
(`setup_ok`, `Setup.lean`), but writes `inc₃₂ⁿ(T₁)` back
(`ctr32Val V n`) rather than `T₁ + n`.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

theorem ctr32Setup_eq (c : Core) (r : CtrRegs) : c.ctr32Setup r =
    ([.ldr .x .x6 r.ctr 0] : List Instr) ++ (([.rev .x6 .x6] : List Instr) ++
      (([.ldr .x .x7 r.ctr 8] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([stS c.hiSlot .x6] : List Instr) ++ (([stS c.loSlot .x7] : List Instr) ++
      (Core.inc32By .x10 r.n ++
      (([.rev .x6 .x6] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([.str .x .x7 r.ctr 8] : List Instr) ++ ([.str .x .x6 r.ctr 0] : List Instr)))))))))) := rfl

variable {c : Core}

/-- The entry block. -/
theorem setup32_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.total) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctr32Setup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 10, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .x19)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctr32Val (ctrVal s.mem P) (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ∉ SetupRegs → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  have sl : ∀ k, c.slots ≤ k → k < c.total → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  obtain ⟨cs, c6, c7, c10⟩ := not_setupRegs hr.ctr
  obtain ⟨ns, n6, n7, n10⟩ := not_setupRegs hr.n
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₁
    b₁' (fun i hi => by rw [wr₁]; exact sl _ (by omega_using []) (by omega_using [hroom, hi])) (by omega_using [hsm, hroom])
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have keep₂ : ∀ x, x ≠ sb → s₂.gpr x = s.gpr x := fun x hx => by rw [g₂, o₁ x hx]
  have P₂ : s₂.gpr r.ctr = P := by rw [keep₂ _ cs, hP]
  have fe : Frame [modeRegion c B] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega_using []) (by omega_using [])⟩
  have dP : ∀ k, c.slots ≤ k → k < c.total → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega_using [h2]))).symm
  -- The counter.
  have inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega_using [hd])⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  have mP : ∀ d, d + 8 ≤ 16 →
      s₂.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega_using [hd]) (by omega_using [hd])) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by omega_using [hroom]))) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := ldr_ok s₂ .x6 r.ctr (off := 0) (by decide)
    (by rw [rd₂', wr₂', P₂]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rev_ok s₃ .x6 .x6
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ldr_ok s₄ .x7 r.ctr (off := 8) (by decide)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂', wr₂', o₄ _ (Ne.symm c6).symm, o₃ _ c6, P₂]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := rev_ok s₅ .x7 .x7
  have g₆ : ∀ x, x ≠ .x6 → x ≠ .x7 → s₆.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₆ x h2, o₅ x h2, o₄ x h1, o₃ x h1]
  have mP0 := mP 0 (by decide)
  rw [p0] at mP0
  have x6₆ : s₆.gpr .x6 = hiOf V := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₄, r₃, P₂, p0, mP0, hv]; rfl
  have x7₆ : s₆.gpr .x7 = loOf V := by
    rw [r₆, r₅, m₄, m₃, o₄ _ c6, o₃ _ c6, P₂, mP 8 (by decide), lv]; rfl
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂']
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂']
  have b₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide), g₂, b₁']
  have hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega_using [hroom]
  have hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega_using [hroom]
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := stS_ok (s := s₆) (b := B) (k := c.hiSlot) .x6 b₆ (by omega_using [hsm, hH])
    (by rw [wr₆']; exact sl _ (by simp only [Core.hiSlot]; omega_using []) hH)
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_ok (s := s₇) (b := B) (k := c.loSlot) .x7 (by rw [g₇, b₆]) (by omega_using [hsm, hLo])
    (by rw [wr₇, wr₆']; exact sl _ (by simp only [Core.loSlot]; omega_using []) hLo)
  let N := (s.gpr r.n).toNat
  obtain ⟨s₁₀, e₁₀, l₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := inc32By_ok s₈ (T := .x10) (by decide) r.n (V := V) (j := N)
    (by rw [g₈, g₇, g₆ _ n6 n7, keep₂ _ ns]; simp [N]) (by rw [g₈, g₇, x7₆])
  have h₁₀ : s₁₀.gpr .x6 = hiOf (ctr32Val V N) := by
    rw [o₁₀ _ (by decide) (by decide), g₈, g₇, x6₆, hiOf_ctr32Val]
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := rev_ok s₁₀ .x6 .x6
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := rev_ok s₁₁ .x7 .x7
  have keep₁₂ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x10 → s₁₂.gpr x = s₆.gpr x := fun x h1 h2 h3 => by
    rw [o₁₂ x h2, o₁₁ x h1, o₁₀ x h2 h3, g₈, g₇]
  have P₁₂ : s₁₂.gpr r.ctr = P := by rw [keep₁₂ _ c6 c7 c10, g₆ _ c6 c7, P₂]
  have wr₁₂' : s₁₂.wr = s.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₈, wr₇, wr₆']
  obtain ⟨s₁₃, e₁₃, m₁₃, g₁₃, rd₁₃, wr₁₃⟩ := str_ok s₁₂ .x7 r.ctr (off := 8) (by decide)
    (by rw [P₁₂, wr₁₂']; exact inP 8 (by decide))
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := str_ok s₁₃ .x6 r.ctr (off := 0) (by decide)
    (by rw [g₁₃, P₁₂, wr₁₃, wr₁₂']; exact inP 0 (by decide))
  have mem₈ : s₈.mem = (s₂.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₈, m₇, g₇, x6₆, x7₆, m₆, m₅, m₄, m₃]
  have mem₁₄ : s₁₄.mem = (s₈.mem.writeW (P + BitVec.ofNat 64 8) (rev64 (loOf (ctr32Val V N)))).writeW P
      (rev64 (hiOf (ctr32Val V N))) := by
    rw [m₁₄, g₁₃, P₁₂, p0, m₁₃, P₁₂, m₁₂, m₁₁, m₁₀, o₁₂ .x6 (by decide), r₁₁, h₁₀, r₁₂, o₁₁ .x7 (by decide),
      l₁₀]
  -- The frames.
  have fS : Frame [modeRegion c B] s₂.mem s₈.mem := by
    rw [mem₈]
    have hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega_using [])
      (by simp only [Core.hiSlot]; omega_using []) (by omega_using [hsm, hroom]))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega_using []) (by simp only [Core.loSlot]; omega_using []) (by omega_using [hsm, hroom]))
  have fP : Frame [⟨P, 16⟩] s₈.mem s₁₄.mem := by
    rw [mem₁₄]
    have hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have thruP : ∀ k, c.slots ≤ k → k < c.total →
      s₁₄.mem.readW (wordAddr B k) 64 = s₈.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  have b8 : ∀ k, k < c.total → 8 * k < 2 ^ 64 := fun k hk => by omega_using [hsm, hk]
  have mem8 : ∀ k, c.slots ≤ k → k < c.total → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₈.mem.readW (wordAddr B k) 64 = s₂.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₈, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH),
      ite_eq_right hh]
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  refine ⟨s₁₄, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₈, rd₇, rd₆'], by rw [wr₁₄, wr₁₃, wr₁₂']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctr32Setup_eq,
      runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some,
      runBlock_app, e₁₀, Option.bind_some, runBlock_app, e₁₁,
      Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃, Option.bind_some, e₁₄]
  · rw [g₁₄, g₁₃, keep₁₂ _ (by decide) (by decide) (by decide), b₆]
  · have k1 : c.slots ≤ c.slots + i := by omega_using []
    have k2 : c.slots + i < c.total := by omega_using [hroom, hi]
    rw [thruP _ k1 k2, mem8 _ k1 k2 (by simp only [Core.hiSlot]; omega_using [hi]) (by simp only [Core.loSlot]; omega_using [hi]),
      v₂ i hi, o₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega_using []) hH, mem₈,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_using []),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega_using []) hLo, mem₈, Mem.readW_writeW_self64]
  · rw [mem₁₄]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · obtain ⟨h1, h2, h3, h4⟩ := not_setupRegs hx
    rw [g₁₄, g₁₃, keep₁₂ x h2 h3 h4, g₆ x h2 h3, keep₂ x h1]

end VG.Proof.Modes.AArch64

end

end


/-!
# Counter mode with `inc₃₂` on AArch64, for any core: the whole function

`ctr32_wp`: `c.ctr32 r`, for a core `c` with `CoreSpec c` and its
arguments in the registers `r`, transforms the `n` blocks at `D` by
`Spec.Gcm.ctr32` with the core's cipher under the key `k` that its key
arguments give (on GCM's blocks, `onBlocks`), from the counter block at
`P`, which it replaces with `inc₃₂ⁿ` of it; it keeps the callee-saved
registers `x19`–`x28`, and writes nothing but the scratch buffer, the
counter block and the data. As `ctr_wp` (`Ctr.lean`), whose proof it
follows.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem ctr32Loop_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {s : State} (hi : GInv32 cs s₀ B D n k V 0 s) :
    WP isa (.loop c.ctr32Group (.nonzero .x c.leftReg)) s (GDone32 cs s₀ B D n k V) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ GInv32 cs s₀ B D n k V g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (ctr32Group_wp cs hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨z, n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega_arith, g + 1, rfl, d⟩

/-- `CoreSpec.Ready`, `prepare`'s and the test's states, and the loop. -/
theorem ctr32_wp (cs : CoreSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State} {B P D : Addr}
    {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total) (hwP : (⟨P, 16⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩)
    (sDS : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.total⟩) (sPD : Region.Disjoint ⟨P, 16⟩ ⟨D, 16 * n⟩)
    (fitD : D.toNat + 16 * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨P, 16⟩] k) :
    WP isa (c.ctr32 r) s₀ fun s' => (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      Spec.Gcm.blocksAt s'.mem D n =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.blockAt s₀.mem P) (Spec.Gcm.blocksAt s₀.mem D n) ∧
      Spec.Gcm.blockAt s'.mem P = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt s₀.mem P) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨P, 16⟩, ⟨D, 16 * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  -- The entry.
  obtain ⟨s₁a, e₁a, b₁a, sv₁, hi₁, lo₁, bP₁, f₁, g₁a, rd₁a, wr₁a⟩ := setup32_ok hL hr s₀ hB hs hP hwP sPS
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok s₁a r hdn hdl
  have g₁ : ∀ x, x ∉ SetupRegs → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1]
  have b₁ : s₁.gpr sb = B := by rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), b₁a]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rd₁a]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wr₁a]
  have mem₁ : s₁.mem = s₁a.mem := m₁b
  unfold Core.ctr32
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, e₁a, Option.bind_some, e₁b], ?_⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_using [hroom])
  have f₁' : Frame [⟨B, 8 * c.total⟩, ⟨P, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁]
    exact f₁.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, List.mem_cons_self, subMode⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.total⟩, ⟨P, 16⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx) (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rd₁ wr₁
      (by rw [runBlock_syms e₁b, runBlock_syms e₁a]) f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega_using [h1]) (by omega_using [hsm, h2])) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  have left₂ : s₂.gpr c.leftReg = s₀.gpr r.n := by
    rw [lr₂, lr₁, g₁a _ hr.n]
  have hz₂ : isa.eval (.zero .x c.leftReg) s₂ = some (decide (n = 0)) := by
    rw [eval_zero, left₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let V := ctrVal s₀.mem P
  have hp : GPre c s₂ B D n := ⟨⟨by rw [wr₂']; exact hs.wr, hs.fit⟩, by rw [wr₂']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone32 cs s₂ B D n k V)
    (WP.ite (decide (n = 0)) hz₂ (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₂, fun _ _ => rfl, fun i hi' => by omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    have hsl : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
        s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj =>
      keep₂ j (by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using [])
        (by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using [hroom])
    refine ctr32Loop_wp cs hp ⟨b₂, ready₂, fun _ _ => rfl, ?_, ?_, by omega_using [hn0], ?_, ?_,
      fun i _ => by rw [ite_eq_right (by omega_using [])], Frame.refl _ _, rfl, rfl⟩
    · rw [dr₂, dr₁, g₁a _ hr.data, hD]; simp
    · rw [left₂, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · rw [hsl _ (.inl rfl), mem₁, hi₁, Nat.mul_zero, ctr32Val_zero]
    · rw [hsl _ (.inr rfl), mem₁, lo₁, Nat.mul_zero, ctr32Val_zero]
  -- The exit.
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₅, e₅, v₅, -, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₄
    d₄.base hsv hinj (by omega_using [hsm, hroom]) (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₂', wr₂']
      exact inRd (slot_wr hs.wr hN (by omega_using [hroom, hi'])))
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₅, d₄.rd, rd₂'], by rw [wr₅, d₄.wr, wr₂']⟩
  · rw [v₅ i hi', d₄.saved i hi', keep₂ _ (by omega_using []) (by omega_using [hroom, hi']), mem₁, sv₁ i hi']
  · have subCore : ∀ x ∈ [coreRegion c B], Region.Sub x ⟨B, 8 * c.total⟩ := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega_using [hroom])
    have ht : (bytesAt s₀.mem P 16).length = 16 := by simp [bytesAt]
    rw [m₅, ctr32_of_dinv (cs.cipher_len k) ht d₄.data, gcmBlocks_eq s₂.mem, gcmBlocks_eq s₀.mem,
      cbcBlocks_frame f₂ (fun x hx => sDS.sub_right (subCore x hx)),
      cbcBlocks_frame f₁' (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sDS
        · exact sPD.symm)]
    rfl
  · refine ctr32_next ?_
    rw [m₅, bytesAt_frame d₄.frame (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sPS
        · exact sPD) (by decide),
      bytesAt_frame f₂ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right (Region.sub_prefix (by omega_using [hroom])))
        (by decide), mem₁, bP₁, hn]
  · rw [m₅]
    refine ((f₁'.sub fun x hx => ⟨x, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₂.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega_using [hroom])⟩)).trans ?_
    exact d₄.frame.sub fun x hx => ⟨x, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp, fun _ h => h⟩

end VG.Proof.Modes.AArch64
