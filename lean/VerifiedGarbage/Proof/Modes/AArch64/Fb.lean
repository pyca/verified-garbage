module

public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Proof.Modes.AArch64.Setup
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# OFB and CFB on AArch64, for any core: the whole function

`fb_wp`: `c.fb mo r ivR`, for a core `c` with `BlockSpec c` whose cipher is
the forward cipher `CIPH_K`, its arguments in the registers `r`, and the IV's
address kept in `ivR` (which the core keeps: `KeepsReg`), replaces the `n`
blocks at `D` with the mode's output (`fbOut`) under the key `k` that its
key arguments give, from the IV at `P`, and the IV with the input block
after the last (`fbIn`); it keeps the callee-saved registers `x19`–`x28`,
and writes nothing but the scratch buffer, the data and the IV. As on
x86-64 (`Proof/Modes/X86_64/Fb.lean`); `ofb_of`, `cfbEnc_of` and
`cfbDec_of` (`Proof/Modes/Fb.lean`) state these as the specification's.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- Where the IV's address may be kept: none of the modes' registers, nor
`sb`, a key argument, or an argument the entry reads after it. -/
structure IvRegOk (c : Core) (r : CtrRegs) (ivR : Reg) : Prop where
  mode : ivR ∉ modeRegs c
  setup : ivR ∉ SetupRegs
  key : ivR ∉ c.keyRegs
  data : ivR ≠ r.data
  n : ivR ≠ r.n

theorem fb_wp (cs : BlockSpec c) (mo : FbMode) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {ivR : Reg}
    (hiv : IvRegOk c r ivR) {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B)
    (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩) (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩] k) (hsc : KeepsReg ivR c.prepare ∧ KeepsReg ivR c.crypt) :
    WP isa (c.fb mo r ivR) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        (List.range n).map (fbOut mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw))) ∧
      bytesAt s'.mem P (8 * c.bw) = fbIn mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) n ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
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
  let S : Region := ⟨B, 8 * c.total⟩
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by omega_arith)
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by omega_arith)
  have subT : Region.Sub ⟨T, (8 * c.bw)⟩ S := VG.Offset.sub_base B (by omega_arith)
  have subTbuf : Region.Sub ⟨T, (8 * c.bw)⟩ (blkRegion c B) := Region.sub_prefix hLG
  have dTP : Region.Disjoint ⟨T, (8 * c.bw)⟩ ⟨P, (8 * c.bw)⟩ := (sPS.sub_right subT).symm
  have dDcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 8 * c.bw * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subCore
  have dPcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨P, (8 * c.bw)⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subCore
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.total → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The mode's slots: none of the core's, nor in the data or at the IV.
  have slotIn : ∀ i < 10, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by omega_arith)
  have slotCore : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have slotT : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ ⟨T, (8 * c.bw)⟩ := fun i hi =>
    VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movR_ok sE ivR r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.fb
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  have gA' : ∀ x, x ≠ sb → x ≠ ivR → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by rw [gA x h3 h4, gS x h2, gE x h1]
  have bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS _ (Ne.symm isb), bE]
  have ivA : sA.gpr ivR = P := by rw [gA _ idr ilr, xS, gE _ cs', hP]
  have rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  have wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  have fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩
  have svA : ∀ i < 10, sA.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by rw [mA, mS, svE i hi]
  have kr := keyRegs_ne cs.keyRegs_ok
  have hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (not_setupRegs (kr x hx)).1 (fun e => hiv.key (e ▸ hx))
      (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA'
      (by rw [runBlock_syms eA, runBlock_syms eS, runBlock_syms eE]) fA
  -- The key.
  refine WP.seq (WP.mono (WP.keepReg hsc.1 (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩
    List.mem_cons_self hkA)) fun s₄ ⟨⟨ready₄, b₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, iv₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  have ivR₄ : s₄.gpr ivR = P := by rw [iv₄, ivA]
  have sv₄ : ∀ i < 10, s₄.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← svA i hi]
      exact f₄.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotCore i hi) (by decide)
  -- The IV to the buffer.
  refine WP.seq (WP.mono_syms (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := sb) (rs := ivR) (od := 8 * c.buf)
    (os := 0) (P := T) (Q := P)
    ⟨by rw [b₄], by rw [ivR₄]; simp, by decide, Ne.symm i6, by decide, Ne.symm i6, by omega_arith, by decide, by omega_arith,
      by omega_arith, fun w hw => by rw [wr₄', addr_add]; exact inS (by omega_arith),
      fun w hw => by
        rw [rd₄', wr₄']
        exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      dTP, by omega_arith⟩) fun s₅ h₅ sy₅ => ?_)
  have g₅ : ∀ x, x ≠ .x6 → s₅.gpr x = s₄.gpr x := fun x h => h₅.regs x h h
  have mem₅ : s₅.mem = over s₄.mem T (8 * c.bw) fun i => s₄.mem (P + BitVec.ofNat 64 i) := h₅.mem
  have f₅ : Frame [⟨T, (8 * c.bw)⟩] s₄.mem s₅.mem := by rw [mem₅]; exact over_frame _ _ _ _
  have b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide), b₄]
  have ivR₅ : s₅.gpr ivR = P := by rw [g₅ _ i6, ivR₄]
  have rd₅' : s₅.rd = s₀.rd := by rw [h₅.rd, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [h₅.wr, wr₄']
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅ _ l6, lr₄, lrA, gS _ (Ne.symm hiv.n), gE _ ns']
  have hz₅ : isa.eval (.zero .x c.leftReg) s₅ = some (decide (n = 0)) := by
    rw [eval_zero, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have sv₅ : ∀ i < 10, s₅.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← sv₄ i hi]
      exact f₅.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotT i hi) (by decide)
  -- The memory before the loop: the IV and the data as on entry.
  have m₄P : ∀ u < (8 * c.bw), s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, (8 * c.bw)⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu]
    exact fA.bytes (R := ⟨P, (8 * c.bw)⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  have m₅D : ∀ i < 8 * c.bw * n, s₅.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi => by
    rw [f₅.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subT) hn64 hi,
      f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dDcore hn64 hi]
    exact fA.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      hn64 hi
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hivl : iv.length = (8 * c.bw) := by simp [iv, bytesAt]
  have buf₅ : ∀ u < (8 * c.bw), s₅.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
      (fbIn mo (8 * c.bw) (cs.cipher k) s₀.mem D iv 0).getD u 0 := fun u hu => by
    rw [mem₅, over_at hu (by omega_arith), m₄P u hu, fbIn, bytesAt_getD _ _ hu]
  have hp : GPre c s₅ B D n (8 * c.bw) := ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD⟩
  have fr₅ : Frame [S] s₀.mem s₅.mem :=
    fA.trans ((f₄.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩).trans
      (f₅.sub fun x hx => ⟨S, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hx; subst hx; exact subT⟩))
  -- The blocks.
  refine WP.seq (WP.mono (M := isa) (Q := FDone cs mo ivR s₅ s₀.mem B D n k iv)
    (WP.ite (decide (n = 0)) hz₅ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₅, fun _ _ => rfl, by rw [hn0]; exact buf₅,
      fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega_arith, Frame.refl _ _, rfl, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine fbLoop_wp cs mo hiv.mode hivl hp hsc.2 ⟨b₅, cs.ready_frame ready₄ f₅ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact .inr subTbuf)
        ⟨fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨S, by rw [wr₄']; exact hs.wr, subT⟩,
          h₅.rd, h₅.wr, sy₅⟩
        (fun x hx => by obtain ⟨h1, -, -⟩ := of_not_modeRegs hx; exact g₅ x (not_own h1).1),
      fun _ _ => rfl, ?_, ?_, by omega_arith, buf₅, fun q hq r hr => ?_, Frame.refl _ _, rfl, rfl, rfl⟩
    · rw [g₅ _ d6, dr₄, drA, gS _ (Ne.symm hiv.data), gE _ ds', hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (Nat.not_lt_zero _)]; exact m₅D _ (hqr hq hr)
  -- The block to continue from back to the IV.
  have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
  have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
  have ivR₆ : s₆.gpr ivR = P := by rw [d₆.ivK, ivR₅]
  refine WP.block_append (WP.mono (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := ivR) (rs := sb) (od := 0)
    (os := 8 * c.buf) (P := P) (Q := T)
    ⟨by rw [ivR₆]; simp, by rw [d₆.base], Ne.symm i6, by decide, Ne.symm i6, by decide, by decide, by omega_arith, by omega_arith,
      by omega_arith, fun w hw => by rw [wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      fun w hw => by
        rw [rd₆, wr₆, addr_add]
        exact inRd (inS (by omega_arith)),
      dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_)
  have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := h₇.mem
  have f₇ : Frame [⟨P, (8 * c.bw)⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
  have b₇ : s₇.gpr sb = B := by rw [h₇.regs _ (by decide) (by decide), d₆.base]
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₈, e₈, v₈, -, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₇
    b₇ hsv hinj (by omega_arith) (fun i hi' => by
      rw [h₇.rd, h₇.wr, rd₆, wr₆]
      exact inRd (slot_wr hs.wr hN (by omega_arith)))
  refine WP.of_runBlock ⟨s₈, e₈, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₈, h₇.rd, rd₆],
    by rw [wr₈, h₇.wr, wr₆]⟩
  · rw [v₈ i hi', f₇.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact ((sPS.sub_right (slotIn i hi')).symm)) (by decide), d₆.saved i hi', sv₅ i hi']
  · rw [m₈]
    refine blocksOf_of_dinv (m₀ := s₀.mem) (fbOut_length (cs.cipher_len k) _ _ _) fun i hi => ?_
    rw [f₇.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
    exact d₆.data i hi
  · rw [m₈]
    apply List.ext_getElem (by
      rw [fbIn_length (iv := bytesAt s₀.mem P (8 * c.bw)) (cs.cipher_len k) _ _ (by simp [bytesAt])]; simp [bytesAt])
    intro u h1 _
    have hu : u < (8 * c.bw) := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mem₇, over_at hu (by omega_arith), d₆.buf u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    refine ((fr₅.mono fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans
      (d₆.frame.mono fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self)).trans
      (f₇.mono fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

end VG.Proof.Modes.AArch64
