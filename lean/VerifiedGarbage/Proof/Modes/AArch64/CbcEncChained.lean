module

import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
public import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
public import VerifiedGarbage.Proof.Modes.CbcEnc
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CBC encryption on AArch64 that updates the chaining value, for any core

`cbcEncryptChained_wp`: `c.cbcEncryptChained r ivR` is `c.cbcEncrypt r`
(`cbcEncrypt_wp`), which also replaces the IV at `P` with the last
ciphertext block (`Spec.Cbc.next`): the IV's address stays in `ivR`, which
the core's `prepare` and `crypt` keep (`KeepsReg`, as for OFB and CFB), and
after the last block the buffer, which still holds it (`EDone.last`), is
copied back to the IV. As on x86-64 (`Proof/Modes/X86_64/CbcEncChained.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

theorem copyW_keepsReg {r t rd rs : Reg} {od os w : Nat} (h : r ≠ t) :
    (copyW t rd rs od os w).all (keepsReg r) = true := by
  simp [copyW, keepsReg, clobbers, dstOf, Ne.symm h]

theorem xorW_keepsReg {r t u rd rs : Reg} {od os w : Nat} (ht : r ≠ t) (hu : r ≠ u) :
    (xorW t u rd rs od os w).all (keepsReg r) = true := by
  simp [xorW, eorR, keepsReg, clobbers, dstOf, Ne.symm ht, Ne.symm hu]

theorem flatMap_keepsReg {r : Reg} {f : Nat → List Instr} (h : ∀ w, (f w).all (keepsReg r) = true) (k : Nat) :
    ((List.range k).flatMap f).all (keepsReg r) = true := by
  simp only [List.all_flatMap, List.all_eq_true]
  intro w _ i hi
  exact List.all_eq_true.mp (h w) i hi

variable {c : Core}

/-- The data loop of CBC encryption keeps a register that the core keeps and
the mode does not write. -/
theorem keepsReg_cbcEncBlock {r : Reg} (hm : r ∉ modeRegs c) (h : KeepsReg r c.crypt) :
    KeepsReg r c.cbcEncBlock := by
  obtain ⟨own, hd, hl⟩ := of_not_modeRegs hm
  obtain ⟨h6, h7, -⟩ := not_own own
  have hc : ∀ {rd rs : Reg} {od os : Nat}, ((List.range c.bw).flatMap (copyW .x6 rd rs od os)).all (keepsReg r) = true :=
    flatMap_keepsReg (fun _ => copyW_keepsReg h6) _
  refine KeepsReg.seq (keepsReg_of_regSafe hc) (KeepsReg.seq h (KeepsReg.seq (keepsReg_of_regSafe ?_)
    (KeepsReg.seq (KeepsReg.ite (keepsReg_of_regSafe rfl)
      (keepsReg_of_regSafe (flatMap_keepsReg (fun _ => xorW_keepsReg h6 h7) _)))
      (keepsReg_of_regSafe ?_))))
  · simp only [regSafe, Core.encOut, List.all_append, hc, Bool.true_and]
    simp [keepsReg, clobbers, dstOf, Ne.symm hl]
  · simp [regSafe, Core.encNext, keepsReg, clobbers, dstOf, Ne.symm hd]

/-- After the blocks: `EDone`, the IV written as well. -/
structure EDoneC (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B P D : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s.mem
  ivOut : bytesAt s.mem P (8 * c.bw) = Spec.Cbc.next iv (Spec.Cbc.encrypt (cs.cipher k) iv (blocksOf (8 * c.bw) m₀ D n))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cbcEncryptChained_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {ivR : Reg}
    (hiv : IvRegOk c r ivR) {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B)
    (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩) (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] k)
    (hsc : KeepsReg ivR c.prepare ∧ KeepsReg ivR c.crypt) :
    WP isa (c.cbcEncryptChained r ivR) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw))
        (Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n)) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_arith)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_arith
  have hN : 8 * c.total < 2 ^ 64 := by omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨cs', c6, c7, -⟩ := not_setupRegs hr.ctr
  obtain ⟨ds', dd6, dd7, -⟩ := not_setupRegs hr.data
  obtain ⟨ns', n6, n7, -⟩ := not_setupRegs hr.n
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hiv.mode
  obtain ⟨i6, i7, -⟩ := not_own iown
  obtain ⟨isb, -, -, -⟩ := not_setupRegs hiv.setup
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  have subT : Region.Sub ⟨T, (8 * c.bw)⟩ ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  have dTP : Region.Disjoint ⟨T, (8 * c.bw)⟩ ⟨P, (8 * c.bw)⟩ := (sPS.sub_right subT).symm
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.total → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The entry, and the IV's address to `ivR`.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨s₁, eS, xS, gS, mS, rdS, wrS⟩ := movR_ok sE ivR r.ctr
  unfold Core.cbcEncryptChained
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, eE, Option.bind_some, eS], ?_⟩)
  have g₁ : ∀ x, x ≠ sb → x ≠ ivR → s₁.gpr x = s₀.gpr x := fun x h1 h2 => by rw [gS x h2, gE x h1]
  have b₁ : s₁.gpr sb = B := by rw [gS _ (Ne.symm isb), bE]
  have iv₁ : s₁.gpr ivR = P := by rw [xS, gE _ cs', hP]
  have ctr₁ : s₁.gpr r.ctr = P := by
    by_cases h : r.ctr = ivR
    · rw [h, iv₁]
    · rw [g₁ _ cs' h, hP]
  have sv₁ : ∀ i < 10, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by rw [mS, svE i hi]
  have f₁ : Frame [modeRegion c B] s₀.mem s₁.mem := by rw [mS]; exact fE
  have rd₁ : s₁.rd = s₀.rd := by rw [rdS, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wrS, wrE]
  have sy₁ : s₁.syms = s₀.syms := by rw [runBlock_syms eS, runBlock_syms eE]
  have mP : ∀ u < 8 * c.bw, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode)
      (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  have mD : ∀ i < 8 * c.bw * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  -- The IV into the first block.
  have hz₁ : isa.eval (.zero .x r.n) s₁ = some (decide (n = 0)) := by
    rw [eval_zero, g₁ _ ns' (Ne.symm hiv.n)]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .x6 → x ≠ .x7 → s₂.gpr x = s₁.gpr x) ∧
    s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ Frame [⟨D, 8 * c.bw * n⟩] s₁.mem s₂.mem ∧
    ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = 0 then s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) ^^^ s₀.mem (P + BitVec.ofNat 64 r)
      else s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  have hw : WP isa (c.cbcWhiten r) s₁ Qw := by
    unfold Core.cbcWhiten
    refine WP.ite (decide (n = 0)) hz₁ (fun h0 => ?_) (fun h0 => ?_)
    · exact WP.block_nil ⟨b₁, fun x _ _ => rfl, rfl, rfl, Frame.refl _ _, fun q hq => by simp at h0; omega_arith⟩
    · have hn0 : 0 < n := by simp at h0; omega_arith
      have sub0 : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * 0), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
        VG.Offset.sub_base D (idx_lt hn0)
      refine WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * 0)) (Q := P) (t := .x6) (u := .x7)
        ⟨by rw [g₁ _ ds' (Ne.symm hiv.data), hD]; simp, by rw [ctr₁]; simp, Ne.symm dd6,
          Ne.symm c6, Ne.symm dd7, Ne.symm c7,
          by decide, by decide, by omega_arith, by omega_arith, fun w hw' => ⟨_, by rw [wr₁]; exact hwD, by
            rw [addr_add]
            exact VG.Offset.contains_base D (by
              have := idx_lt (L := c.bw) hn0; rw [Nat.mul_zero] at this ⊢; have := Nat.mul_assoc 8 c.bw n; omega_arith)
              (by rw [Nat.mul_zero]; omega_arith)⟩,
          fun w hw' => by
            rw [rd₁, wr₁]
            exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
          sPD.symm.sub_left sub0, by omega_arith⟩ (by decide)) fun s₂ h₂ => ?_
      refine ⟨by rw [h₂.regs _ (by decide) (by decide), b₁], fun x h1 h2 => h₂.regs x h1 h2, h₂.rd, h₂.wr, ?_,
        fun q hq r hr => ?_⟩
      · rw [h₂.mem]
        exact (over_frame _ _ _ _).sub fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, sub0⟩
      rw [h₂.mem, over_blk _ _ _ hn0 hq hr hn64]
      split
      · rename_i h; subst h; rw [addr_add, mD _ (hqr hq hr), mP r hr]
      · exact mD _ (hqr hq hr)
  have hwK : KeepsReg ivR (c.cbcWhiten r) := by
    unfold Core.cbcWhiten
    exact KeepsReg.ite (keepsReg_of_regSafe rfl) (keepsReg_of_regSafe (flatMap_keepsReg (fun _ => xorW_keepsReg i6 i7) _))
  refine WP.seq (WP.mono_syms (WP.keepReg hwK hw) fun s₂ ⟨⟨b₂, g₂, rd₂, wr₂, f₂, d₂⟩, iv₂⟩ sy₂ => ?_)
  -- The data's address and `n`.
  obtain ⟨s₃, e₃, dr₃, lr₃, g₃, m₃, rd₃, wr₃⟩ := ctrArgs_ok s₂ r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have iv₃ : s₃.gpr ivR = P := by rw [g₃ _ idr ilr, iv₂, iv₁]
  have g₃' : ∀ x, x ∉ SetupRegs → x ≠ ivR → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by
      obtain ⟨h5, h6, h7, -⟩ := not_setupRegs h1
      rw [g₃ x h3 h4, g₂ x h6 h7, g₁ x h5 h2]
  have b₃ : s₃.gpr sb = B := by rw [g₃ _ (Ne.symm dsb) (Ne.symm lsb), b₂]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  have f₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₃' x (kr x hx) (fun e => hiv.key (e ▸ hx)) (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₃' wr₃' (by rw [runBlock_syms e₃, sy₂, sy₁]) f₃
  -- The key.
  refine WP.seq (WP.mono (WP.keepReg hsc.1 (cs.prepare_wp b₃ ⟨by rw [wr₃']; exact hs.wr, hs.fit⟩
    List.mem_cons_self hk₃)) fun s₄ ⟨⟨ready₄, b₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, iv₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
  have ivR₄ : s₄.gpr ivR = P := by rw [iv₄, iv₃]
  have left₄ : s₄.gpr c.leftReg = s₀.gpr r.n := by rw [lr₄, lr₃, g₂ _ n6 n7, g₁ _ ns' (Ne.symm hiv.n)]
  have hz₄ : isa.eval (.zero .x c.leftReg) s₄ = some (decide (n = 0)) := by
    rw [eval_zero, left₄]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hivl : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₄ B D n (8 * c.bw) := ⟨⟨by rw [wr₄']; exact hs.wr, hs.fit⟩, by rw [wr₄']; exact hwD, sDS, fitD⟩
  have dCore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 8 * c.bw * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right (Region.sub_prefix (by omega_arith))
  have m₄P : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact sPS.sub_right (Region.sub_prefix (by omega_arith))) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu]
    exact f₃.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sPS
        · exact sPD) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  -- The blocks, and the last back to the IV.
  refine WP.seq (WP.mono (M := isa) (Q := EDoneC cs s₄ s₀.mem B P D n k iv)
    (WP.ite (decide (n = 0)) hz₄ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    subst hn0
    refine WP.block_nil ⟨b₄, fun _ _ => rfl, fun i hi' => by rw [Nat.mul_zero] at hi'; omega_arith,
      Frame.refl _ _, ?_, rfl, rfl⟩
    rw [show blocksOf (8 * c.bw) s₀.mem D 0 = [] from rfl, show Spec.Cbc.encrypt (cs.cipher k) iv [] = [] from rfl,
      next_nil]
    exact bytesAt_of_getD hivl fun u hu => by rw [m₄P u hu]; exact (bytesAt_getD _ _ hu).symm
  · have hn0 : n ≠ 0 := by simpa using h0
    refine WP.seq (WP.mono (WP.keepReg (KeepsReg.loop (keepsReg_cbcEncBlock hiv.mode hsc.2))
      (cbcEncLoop_wp cs (m₀ := s₀.mem) hivl hp ⟨b₄, ready₄, fun _ _ => rfl, ?_, ?_, by omega_arith, fun q hq r hr => ?_,
        Frame.refl _ _, rfl, rfl⟩)) fun s₆ ⟨d₆, iv₆⟩ => ?_)
    · rw [dr₄, dr₃, g₂ _ dd6 dd7, g₁ _ ds' (Ne.symm hiv.data), hD]; simp
    · rw [left₄, Nat.sub_zero, ← hn]; simp
    · rw [f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dCore hn64 (hqr hq hr), m₃, d₂ q hq r hr, encByte,
        ite_eq_right (Nat.not_lt_zero _)]
      split
      · rw [cbcEncPrev, ite_eq_left rfl, bytesAt_getD _ _ hr]
      · rfl
    -- The buffer, the last ciphertext block, back to the IV.
    have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₄']
    have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₄']
    have ivR₆ : s₆.gpr ivR = P := by rw [iv₆, ivR₄]
    refine WP.mono (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := ivR) (rs := sb) (od := 0)
      (os := 8 * c.buf) (P := P) (Q := T)
      ⟨by rw [ivR₆]; simp, by rw [d₆.base], Ne.symm i6, by decide, Ne.symm i6, by decide, by decide, by omega_arith,
        by omega_arith, by omega_arith, fun w hw => by rw [wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
        fun w hw => by
          rw [rd₆, wr₆, addr_add]
          exact inRd (inS (by omega_arith)),
        dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_
    have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := h₇.mem
    have f₇ : Frame [⟨P, 8 * c.bw⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
    refine ⟨by rw [h₇.regs _ (by decide) (by decide), d₆.base], fun i hi => ?_, fun i hi => ?_, ?_, ?_,
      by rw [h₇.rd, d₆.rd], by rw [h₇.wr, d₆.wr]⟩
    · rw [← d₆.saved i hi]
      exact f₇.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
          omega_arith))).symm) (by decide)
    · rw [f₇.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
      exact d₆.data i hi
    · exact (d₆.frame.mono fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self).trans
        (f₇.mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · rw [next_encrypt _ _ _ _ hn0]
      refine bytesAt_of_getD (by generalize n - 1 = t; cases t <;> exact cs.cipher_len k _) fun u hu => ?_
      rw [mem₇, over_at hu (by omega_arith)]
      exact d₆.last hn0 u hu
  -- The exit.
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₇, e₇, v₇, -, m₇, rd₇, wr₇⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₆
    d₆.base hsv hinj (by omega_arith) (fun i hi' => by
      rw [d₆.rd, d₆.wr, rd₄', wr₄']
      exact inRd (slot_wr hs.wr hN (by omega_arith)))
  refine WP.of_runBlock ⟨s₇, e₇, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₇, d₆.rd, rd₄'], by rw [wr₇, d₆.wr, wr₄']⟩
  · rw [v₇ i hi', d₆.saved i hi', ← sv₁ i hi']
    refine (f₄.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)) (by decide)).trans ?_
    rw [m₃]
    exact f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact (sDS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega_arith))).symm) (by decide)
  · rw [m₇]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₇]; exact d₆.ivOut
  · rw [m₇]
    exact (((f₃.trans (f₄.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega_arith)⟩)).mono fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self)).trans d₆.frame

end VG.Proof.Modes.AArch64
