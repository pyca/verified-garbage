module

import VerifiedGarbage.Proof.Modes.X86_64.Xor
public import VerifiedGarbage.Proof.Modes.X86_64.Group
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr32
import VerifiedGarbage.Proof.Modes.X86_64.Counter32
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# One group of blocks of counter mode with `inc₃₂` on x86-64, for any core

`ctr32Group_wp`: `ctrGroup_wp` (`Group.lean`) for `ctr32`'s groups, whose
counter blocks are `inc₃₂`'s (`ctr32Blocks_ok`): block `j` of the data
becomes the XOR with the encryption of `ctr32Val V j` (`ctr32Out`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The data loop of `ctr32`, before group `g`, from the counter block `V`
with the key `k`. -/
structure GInv32 (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  hi : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctr32Val V (c.G * g))
  lo : s.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctr32Val V (c.G * g))
  data : DInv 16 s₀.mem s.mem D n (c.G * g) (ctr32Out (cs.cipher k) s₀.mem D V)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop of `ctr32`, done. -/
structure GDone32 (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv 16 s₀.mem s.mem D n n (ctr32Out (cs.cipher k) s₀.mem D V)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ctr32Group_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : GInv32 cs s₀ B D n k V g s) :
    WP isa c.ctr32Group s fun s' => (s'.zf = some true ∧ GDone32 cs s₀ B D n k V s') ∨
      (s'.zf = some false ∧ GInv32 cs s₀ B D n k V (g + 1) s') := by
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
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  have hv : v < 2 ^ 64 := by omega_using [hfitD]
  have hc0 : 0 < cc := by omega_using [hG0, hk]
  have hcG : cc ≤ c.G := by omega_using []
  have hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega_using [hc0]
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.ctrSlots → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ := Region.sub_prefix (by simp only [Core.ctrSlots]; omega_using [hroom])
  have stkS : ∀ {R : Region}, Region.Sub R ⟨B, 8 * c.ctrSlots⟩ → ∀ r ∈ stkList c (s₀.gpr .rsp),
      Region.Disjoint R r := fun h => hp.stk.disj ⟨_, hp.scr.wr, h⟩
  have mSlot : ∀ j, c.slots ≤ j → j < c.ctrSlots → ∀ r ∈ coreFrame c B (s₀.gpr .rsp),
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 =>
    coreFrame_disj (VG.Offset.disjoint_base B (by omega_using [h1]) (by omega_using [hN, h2]))
      (stkS (VG.Offset.sub_base B (by omega_using [h2])))
  have inT : ∀ t, t < 2 * c.G → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_using [hroom, hbuf, ht]) (by omega_using [hsm, hroom, hbuf, ht])
  have inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_using [ht]) (by omega_using [hfitD, ht])
  have sepAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right (subS (by simp only [Core.ctrSlots]; omega_using [hroom, hbuf]))
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctr32Blocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctr32Group
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide) (by decide) (by decide), hi.base]
  have subBC : ∀ r ∈ [bufRegion c B, ctrRegion c B], Region.Sub r ⟨B, 8 * c.ctrSlots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> simp only [Core.hiSlot, Core.ctrSlots] <;> omega_using [hroom, hbuf]
  have ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr fun _ h => h
    · exact .inl (VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega_using [])
        (by simp only [Core.hiSlot]; omega_using [hsm, hroom])).symm) ⟨fun r hr => ⟨_, hwS, subBC r hr⟩, rd₁, wr₁, runBlock_syms e₁⟩ fun r hr => by
    obtain ⟨h1, h2, h3, -⟩ := of_not_modeRegs hr
    exact o₁ r h1 h2 h3
  -- The keystream.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [o₁ _ (by decide) (by decide) (by decide), hi.rsp]
  rw [rsp₁] at f₂
  have keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (mSlot j h1 h2) (by decide)
  have keep₁ : ∀ j, c.slots ≤ j → j < c.slots + 6 →
      s₁.mem.readW (wordAddr B j) 64 = s.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint B (Or.inr (by omega_using [hbuf, h1])) (by omega_using [hsm, hroom, h2]) (by omega_using [hsm, hroom, hbuf])
      · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_using [h2]) (by omega_using [hsm, hroom, h2])
          (by simp only [Core.hiSlot]; omega_using [hsm, hroom])) (by decide)
  -- The count.
  have left₂ : s₂.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₂, o₁ _ la lb lc, hi.leftR]
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, o₁ _ da db dc, hi.dataR]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  refine WP.seq (WP.mono_syms (groupCount_wp (by omega_using [hsm, hroom, hbuf]) lc left₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ sy₃ => ?_)
  have base₃ : s₃.gpr sb = B := by rw [o₃ _ (by decide), base₂]
  obtain ⟨s₄, e₄, a₄, b₄, t₄, o₄, m₄, rd₄, wr₄⟩ := xorArgs_ok (by omega_using [hsm, hroom, hbuf]) da s₃ base₃
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  -- The keystream XORed into the group's blocks.
  refine WP.seq (WP.mono_syms (xorBlocks_wp (A := T) (B := A) hc0 (by omega_using [hsm, hroom, hbuf])
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega_using [ht])))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [a₄]; simp [T], by rw [b₄, o₃ _ dc, data₂]; simp [A],
      by rw [o₄ _ (by decide) (by decide) (by decide), c₃, Nat.sub_zero], fun t ht => by omega_using [ht], fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ sy₅ => ?_)
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
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right
        (subS (by omega_using [hj]))).symm) (by decide)
  -- On to the next group.
  obtain ⟨s₆, e₆, d₆, l₆, z₆, o₆, m₆, rd₆, wr₆⟩ := advance_ok hdl d10 s₅
  have hz : s₆.zf = some (decide (v = cc)) := by
    rw [z₆, left₅, r10₅, VG.Offset.ofNat_sub_ofNat_beq hv (by omega_using [hfitD])]
  have ready₆ : cs.Ready s₆ B k := by
    refine cs.ready_frame ready₂ (by rw [m₆]; exact f₅) (fun r hr => ?_) ⟨fun r hr => ?_, ?_, ?_, ?_⟩ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right subCore).symm)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [wr₂, wr₁]; exact hwD, VG.Offset.sub_base D (by omega_using [hkc])⟩
    · rw [rd₆, rd₅', rd₂, rd₁]
    · rw [wr₆, wr₅', wr₂, wr₁]
    · rw [runBlock_syms e₆, sy₅, runBlock_syms e₄, sy₃]
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := of_not_modeRegs hr
      rw [o₆ r h6 h7, keep₄ r h1 h2 h3 h4 h5]
  -- The data.
  have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨B, 8 * c.ctrSlots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have dCore : ∀ r ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨D, 16 * n⟩ r :=
    coreFrame_disj (hp.sep.sub_right subCore) (hp.stk.disj ⟨_, hp.dat, fun _ h => h⟩)
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
  have saved₆ : ∀ i < 6, s₆.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [m₆, keep₅ _ (by simp only [Core.ctrSlots]; omega_using [hroom, hi6]), keep₂ _ (by omega_using []) (by simp only [Core.ctrSlots]; omega_using [hroom, hi6]),
      keep₁ _ (by omega_using []) (by omega_using [hi6]), hi.saved i hi6]
  have hiSlot₆ : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
      s₆.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
    have h1 : c.slots ≤ j := by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using []
    have h2 : j < c.ctrSlots := by
      rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot, Core.ctrSlots] <;> omega_using [hroom]
    rw [m₆, keep₅ j h2, keep₂ j h1 h2]
  have fr₆ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s.mem s₆.mem := by
    rw [m₆]
    refine ((f₁.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, subBC r hr⟩).trans
      (f₂.sub (coreFrame_sub ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, subCore⟩))).trans (f₅.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base D (by omega_using [hkc])⟩
  have fr : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₆.mem := hi.frame.trans fr₆
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (Ne.symm dsb) (Ne.symm lsb), base₅]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by rw [o₆ _ (Ne.symm dsp) (Ne.symm lsp), rsp₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅', hi.rd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅', hi.wr]
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], base₆, rsp₆, saved₆, ?_, fr, rd₆', wr₆'⟩
    rw [show n = c.G * g + cc by omega_using [hkc, hdone]] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega_using [hdone]
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₆, rsp₆, ready₆, saved₆, ?_, ?_,
      by rw [Nat.mul_succ]; omega_using [hdone], ?_, ?_,
      by rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact hdata, fr, rd₆', wr₆'⟩
    · rw [d₆, rbx₅, addr_add, hcc,
        show 16 * (c.G * g) + 16 * c.G = 16 * (c.G * (g + 1)) by rw [Nat.mul_succ]; omega_using []]
    · rw [l₆, left₅, r10₅, VG.Offset.ofNat_sub_ofNat (by omega_using []), hcc,
        show v - c.G = n - c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]
    · rw [hiSlot₆ _ (.inl rfl), h₁, ctr32Val_add, show c.G * g + c.G = c.G * (g + 1) by rw [Nat.mul_succ]]
    · rw [hiSlot₆ _ (.inr rfl), l₁, ctr32Val_add, show c.G * g + c.G = c.G * (g + 1) by rw [Nat.mul_succ]]

end VG.Proof.Modes.X86_64
