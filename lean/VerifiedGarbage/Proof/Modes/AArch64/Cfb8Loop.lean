module

import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
public import VerifiedGarbage.Proof.Modes.Cfb8
public import VerifiedGarbage.Impl.Modes.AArch64.Cfb8
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CFB8 on AArch64, for any core: the data loop

As on x86-64 (`Proof/Modes/X86_64/Cfb8Loop.lean`). `cfb8Block_wp`: one
iteration copies the input block `Iⱼ` from the IV to the buffer
(`copyN_wp`), enciphers it there (`BlockSpec.crypt_wp`), XORs the output's
first byte into byte `j` of the data (`cfb8Xor_wp`), making it `cfb8Out`,
and shifts the input block at the IV to `Iⱼ₊₁` (`cfb8Shift_wp`, `cfb8In`).
Blocks are `8 bw` bytes. The IV's address is kept in the register `ivR`,
which the core keeps (`KeepsReg`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeW8_apply)

variable {c : Core}

/-- What CFB8's data loop works on: the scratch buffer at `B`, the `n`
bytes at `D`, the input block at `P`. -/
structure C8Pre (c : Core) (s₀ : State) (B D P : Addr) (n : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dat : (⟨D, n⟩ : Region) ∈ s₀.wr
  ivw : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr
  sepD : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.total⟩
  sepP : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩
  sepPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩
  fitD : D.toNat + n ≤ 2 ^ 64
  small : n < 2 ^ 64

/-- The data loop, before byte `j`; `m₀` is the memory on entry, `iv` the
IV. -/
structure C8Inv (cs : BlockSpec c) (enc : Bool) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D P : Addr) (n : Nat)
    (k : cs.Key) (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 j
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  ivB : ∀ u < 8 * c.bw, s.mem (P + BitVec.ofNat 64 u) = (cfb8In enc (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ q < n, s.mem (D + BitVec.ofNat 64 q) =
    if q < j then cfb8Out enc (cs.cipher k) m₀ D iv q else m₀ (D + BitVec.ofNat 64 q)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = P

/-- The data loop, done. -/
structure C8Done (cs : BlockSpec c) (enc : Bool) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D P : Addr) (n : Nat)
    (k : cs.Key) (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  ivB : ∀ u < 8 * c.bw, s.mem (P + BitVec.ofNat 64 u) = (cfb8In enc (cs.cipher k) m₀ D iv n).getD u 0
  data : ∀ q < n, s.mem (D + BitVec.ofNat 64 q) = cfb8Out enc (cs.cipher k) m₀ D iv q
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = P

theorem headD_eq_getD (l : List Byte) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem writeW8_frame (m : Mem) (A : Addr) (b : Byte) : Frame [⟨A, 1⟩] m (m.writeW A b) := fun x hx => by
  rw [writeW8_apply, ite_eq_right (fun h => hx _ List.mem_cons_self (by
    subst h; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))]

theorem cfb8Block_wp (cs : BlockSpec c) (enc : Bool) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D P : Addr} {n : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : C8Pre c s₀ B D P n)
    (hsc : KeepsReg ivR c.crypt) {j : Nat} {s : State} (hi : C8Inv cs enc ivR s₀ m₀ B D P n k iv j s) :
    WP isa (c.cfb8Block enc ivR) s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ C8Done cs enc ivR s₀ m₀ B D P n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ C8Inv cs enc ivR s₀ m₀ B D P n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hn64 := hp.small
  have hj := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hivR
  obtain ⟨i6, i7, -⟩ := not_own iown
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 j
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let S : Region := ⟨B, 8 * c.total⟩
  have hwS : S ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.ivw
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ S := VG.Offset.sub_base B (by omega)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by omega)
  have subA : Region.Sub ⟨A, 1⟩ ⟨D, n⟩ := VG.Offset.sub_base D (by omega)
  have dTP : Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨P, 8 * c.bw⟩ := (hp.sepP.sub_right subT).symm
  have dAP : Region.Disjoint ⟨A, 1⟩ ⟨P, 8 * c.bw⟩ := (hp.sepPD.sub_right subA).symm
  have dAS : Region.Disjoint ⟨A, 1⟩ S := hp.sepD.sub_left subA
  have dPcore : Region.Disjoint ⟨P, 8 * c.bw⟩ (coreRegion c B) := hp.sepP.sub_right subCore
  have dDcore : Region.Disjoint ⟨D, n⟩ (coreRegion c B) := hp.sepD.sub_right subCore
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.total → InRegions s.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hwS, VG.Offset.contains_base B h (by omega)⟩
  have inA : InRegions s.wr A 1 := ⟨_, hwD, VG.Offset.contains_base D (by omega) (by omega)⟩
  have slotIn : ∀ i < 10, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by omega)
  have slotOut : ∀ i < 10, ∀ {R : Region}, (R = ⟨T, 8 * c.bw⟩ ∨ R = coreRegion c B ∨ R = ⟨A, 1⟩ ∨
      R = ⟨P, 8 * c.bw⟩) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi10 R hR => by
    rcases hR with rfl | rfl | rfl | rfl
    · exact VG.Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
    · exact VG.Offset.disjoint_base B (by omega) (by omega)
    · exact (dAS.sub_right (slotIn i hi10)).symm
    · exact (hp.sepP.sub_right (slotIn i hi10)).symm
  -- The input block to the buffer.
  unfold Core.cfb8Block
  refine WP.seq (WP.mono_syms (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := sb) (rs := ivR) (od := 8 * c.buf)
    (os := 0) (P := T) (Q := P)
    ⟨hi.base ▸ rfl, by rw [hi.ivK]; simp, by decide, Ne.symm i6, by decide, Ne.symm i6, by omega, by decide,
      by omega, by omega, fun w hw => by rw [addr_add]; exact inS (by omega),
      fun w hw => inRd ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩, dTP, by omega⟩) fun s₁ h₁ sy₁ => ?_)
  have mem₁ : s₁.mem = over s.mem T (8 * c.bw) fun i => s.mem (P + BitVec.ofNat 64 i) := h₁.mem
  have f₁ : Frame [⟨T, 8 * c.bw⟩] s.mem s₁.mem := by rw [mem₁]; exact over_frame _ _ _ _
  have g₁ : ∀ x, x ≠ .x6 → s₁.gpr x = s.gpr x := fun x h => h₁.regs x h h
  have base₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hi.base]
  have ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf)
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hwS, subT⟩, h₁.rd, h₁.wr, sy₁⟩
    fun r hr => by
    obtain ⟨h1, -, -⟩ := of_not_modeRegs hr; exact g₁ r (not_own h1).1
  have rd₁ : s₁.rd = s₀.rd := by rw [h₁.rd, hi.rd]
  have wr₁ : s₁.wr = s₀.wr := by rw [h₁.wr, hi.wr]
  -- Enciphered.
  refine WP.seq (WP.mono (WP.keepReg hsc (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hp.scr.wr, hfit⟩ ready₁))
    fun s₂ ⟨⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, i₂⟩ => ?_)
  have eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  have hX : bytesAt s₁.mem T (8 * c.bw) = cfb8In enc ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [cfb8In_length enc ciph m₀ D hiv hL0])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mem₁, over_at hu (by omega), hi.ivB u hu, List.getElem_eq_getD 0]
  have T₂ : s₂.mem T = (ciph (cfb8In enc ciph m₀ D iv j)).headD 0 := by
    have h0 := bytesAt_getD s₂.mem T hL0
    rw [p0] at h0
    rw [← h0, ← eT, ks₂ 0 hG0, eT, hX, headD_eq_getD]
  -- The memory outside the buffer and the core, as before.
  have out₂ : ∀ x, (∀ R ∈ [(⟨T, 8 * c.bw⟩ : Region), coreRegion c B], ¬ R.Contains x 1) → s₂.mem x = s.mem x :=
    fun x hx => by
      rw [f₂ x (fun R hR => hx R (by simp only [List.mem_singleton] at hR; subst hR; simp)),
        f₁ x (fun R hR => hx R (by simp only [List.mem_singleton] at hR; subst hR; simp))]
  have A₂ : s₂.mem A = m₀ A := by
    rw [out₂ A (fun R hR hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact (dAS.sub_right subT) A (Region.contains_self A 1) hc
      · exact (dAS.sub_right subCore) A (Region.contains_self A 1) hc)]
    have := hi.data j hj
    rw [ite_eq_right (Nat.lt_irrefl _)] at this
    exact this
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, g₁ _ d6, hi.dataR]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have iv₂ : s₂.gpr ivR = P := by rw [i₂, g₁ _ i6, hi.ivK]
  -- The byte.
  refine WP.block_append (WP.block_append (WP.mono_syms (cfb8Xor_wp enc (T := T) hbI data₂ (by rw [base₂]) d6 d7
    (by rw [wr₂', ← hi.wr]; exact inA)
    (by rw [rd₂', wr₂', ← hi.rd, ← hi.wr]; exact inRd (inS (by omega))))
    fun s₃ ⟨g₃, rd₃, wr₃, m₃, x₃⟩ sy₃ => ?_))
  have cj : (s₃.gpr .x6).setWidth 8 = cfb8C enc ciph m₀ D iv j := by
    rw [x₃, A₂, T₂]; rfl
  -- The shift.
  refine WP.mono_syms (cfb8Shift_wp (c := c) (P := P) i7 (by rw [g₃ _ i6 i7, iv₂]) (by rw [wr₃, wr₂']; exact hp.ivw) hbw0 hbw2)
    fun s₄ ⟨g₄, rd₄, wr₄, P₄, f₄⟩ sy₄ => ?_
  -- On to the next byte.
  obtain ⟨s₅a, e₅a, a₅a, o₅a, m₅a, rd₅a, wr₅a⟩ := addImm_ok s₄ c.dataReg c.dataReg (v := 1) (by decide)
  obtain ⟨s₅, e₅, l₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₅a c.leftReg c.leftReg (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [Core.cfb8Next, show ([.addImm .x c.dataReg c.dataReg 1, .subImm .x c.leftReg c.leftReg 1] : List Instr) =
      [.addImm .x c.dataReg c.dataReg 1] ++ [.subImm .x c.leftReg c.leftReg 1] from rfl, runBlock_app, e₅a,
      Option.bind_some, e₅], ?_⟩
  have keep₅ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ c.dataReg → x ≠ c.leftReg → s₅.gpr x = s₂.gpr x :=
    fun x h1 h2 h3 h4 => by rw [o₅ x h4, o₅a x h3, g₄ x h2, g₃ x h1 h2]
  have left₄ : s₅a.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [o₅a _ (Ne.symm hdl), g₄ _ l7, g₃ _ l6 l7, lr₂, g₁ _ l6, hi.leftR]
  have left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₅, left₄, VG.Offset.ofNat_sub_ofNat (by omega), show n - j - 1 = n - (j + 1) by omega]
  have hz₅ : isa.eval (.nonzero .x c.leftReg) s₅ = some !(decide (j + 1 = n)) := by
    rw [eval_nonzero, left₅, ofNat_beq_zero (by omega), decide_eq_decide.mpr (show n - (j + 1) = 0 ↔ j + 1 = n by omega)]
  have data₅ : s₅.gpr c.dataReg = D + BitVec.ofNat 64 (j + 1) := by
    rw [o₅ _ hdl, a₅a, g₄ _ d7, g₃ _ d6 d7, data₂, addr_add]
  have mem₅ : s₅.mem = s₄.mem := by rw [m₅, m₅a]
  have base₅ : s₅.gpr sb = B := by
    rw [keep₅ _ (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
  have ivK₅ : s₅.gpr ivR = P := by rw [keep₅ _ i6 i7 idr ilr, iv₂]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₅a, rd₄, rd₃, rd₂']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₅a, wr₄, wr₃, wr₂']
  -- What changed after `crypt`: the data's byte and the input block.
  have f₅ : Frame [⟨A, 1⟩, ⟨P, 8 * c.bw⟩] s₂.mem s₅.mem := by
    rw [mem₅]
    refine (?_ : Frame [⟨A, 1⟩, ⟨P, 8 * c.bw⟩] s₂.mem s₃.mem).trans
      (f₄.mono fun R hR => by simp only [List.mem_singleton] at hR; subst hR; simp)
    rw [m₃]; exact (writeW8_frame _ _ _).mono fun R hR => by simp only [List.mem_singleton] at hR; subst hR; simp
  have ready₅ : cs.Ready s₅ B k := cs.ready_frame ready₂ f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (dDcore.sub_left subA).symm
    · exact .inl dPcore.symm)
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by rw [wr₂, wr₁, ← hi.wr]; exact hwD, subA⟩
      · exact ⟨_, by rw [wr₂, wr₁, ← hi.wr]; exact hwP, fun _ h => h⟩,
      by rw [rd₅, rd₅a, rd₄, rd₃], by rw [wr₅, wr₅a, wr₄, wr₃],
      by rw [runBlock_syms e₅, runBlock_syms e₅a, sy₄, sy₃]⟩ fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    exact keep₅ r (not_own h1).1 (not_own h1).2.1 h2 h3
  have saved₅ : ∀ i < 10, s₅.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [← hi.saved i hi10]
    refine (f₅.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact slotOut i hi10 (.inr (.inr (.inl rfl)))
      · exact slotOut i hi10 (.inr (.inr (.inr rfl)))) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact slotOut i hi10 (.inr (.inl rfl))) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact slotOut i hi10 (.inl rfl)) (by decide)
  have fr₅ : Frame [S, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s₅.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨S, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub fun r hr => ⟨S, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans
      (f₅.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩))
  -- The input block and the data.
  have hPout : ∀ u < 8 * c.bw, s₃.mem (P + BitVec.ofNat 64 u) = s.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    have hc : (⟨P, 8 * c.bw⟩ : Region).Contains (P + BitVec.ofNat 64 u) 1 :=
      VG.Offset.contains_base P (by omega) (by omega)
    rw [m₃, writeW8_apply, ite_eq_right (fun h => dAP _ (by rw [h]; exact Region.contains_self A 1) hc),
      out₂ _ (fun R hR hR' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact dTP _ hR' hc
        · exact dPcore _ hc hR')]
  have ivB₅ : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = (cfb8In enc ciph m₀ D iv (j + 1)).getD u 0 :=
    fun u hu => by
      rw [mem₅, P₄ u hu, cfb8In_succ_getD enc ciph m₀ D hiv hL0 j hu]
      split
      · rename_i h; rw [hPout _ h, hi.ivB _ h]
      · rw [cj]
  have data₅' : ∀ q < n, s₅.mem (D + BitVec.ofNat 64 q) =
      if q < j + 1 then cfb8Out enc ciph m₀ D iv q else m₀ (D + BitVec.ofNat 64 q) := fun q hq => by
    have hcD : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 q) 1 := VG.Offset.contains_base D (by omega) (by omega)
    have hnP : ¬ (⟨P, 8 * c.bw⟩ : Region).Contains (D + BitVec.ofNat 64 q) 1 := fun h => hp.sepPD _ h hcD
    rw [mem₅, f₄ _ (fun R hR => by simp only [List.mem_singleton] at hR; subst hR; exact hnP), m₃, writeW8_apply]
    by_cases hqj : q = j
    · rw [ite_eq_left (by rw [hqj]), ite_eq_left (by omega), A₂, T₂, hqj]; rfl
    · have hne : D + BitVec.ofNat 64 q ≠ A := fun h => hqj (by
        have := (sub_eq_iff (x := D + BitVec.ofNat 64 q) (P := D) (i := j) (by omega)).mp h
        rwa [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
      rw [ite_eq_right hne, out₂ _ (fun R hR hR' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact (hp.sepD.sub_right subT) _ hcD hR'
        · exact dDcore _ hcD hR'), hi.data q hq]
      by_cases h3 : q < j
      · rw [ite_eq_left h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h3, ite_eq_right (by omega)]
  by_cases hdone : j + 1 = n
  · exact .inl ⟨by rw [hz₅, decide_eq_true hdone]; rfl, base₅, saved₅, by rw [← hdone]; exact ivB₅,
      fun q hq => by rw [data₅' q hq, ite_eq_left (by omega)], fr₅, rd₅', wr₅', ivK₅⟩
  · exact .inr ⟨by rw [hz₅, decide_eq_false hdone]; rfl, base₅, ready₅, saved₅, data₅, left₅, by omega, ivB₅,
      data₅', fr₅, rd₅', wr₅', ivK₅⟩

/-- The data loop. -/
theorem cfb8Loop_wp (cs : BlockSpec c) (enc : Bool) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D P : Addr} {n : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : C8Pre c s₀ B D P n)
    (hsc : KeepsReg ivR c.crypt) {s : State} (hi : C8Inv cs enc ivR s₀ m₀ B D P n k iv 0 s) :
    WP isa (.loop (c.cfb8Block enc ivR) (.nonzero .x c.leftReg)) s (C8Done cs enc ivR s₀ m₀ B D P n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ C8Inv cs enc ivR s₀ m₀ B D P n k iv j s)
    (fun m s hs => ?_) n s ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (cfb8Block_wp cs enc hivR hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.AArch64
