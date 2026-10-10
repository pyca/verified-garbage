import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
import VerifiedGarbage.Proof.Modes.X86_64.Ctr

/-!
# OFB and CFB on x86-64, for any core: the whole function

`fb_wp`: `c.fb mo r`, for a core `c` with `BlockSpec c` whose cipher is the
forward cipher `CIPH_K`, and its arguments in the registers `r`, replaces
the `n` blocks at `D` with the mode's output (`fbOut`) under the key `k`
that its key arguments give, from the IV at `P`, and the IV with the input
block after the last (`fbIn`); it keeps the callee-saved registers, and
writes nothing but the scratch buffer, the data and the IV. `ofb_of`,
`cfbEnc_of` and `cfbDec_of` (`Proof/Modes/Fb.lean`) state these as the
specification's.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem fb_wp (cs : BlockSpec c) (mo : FbMode) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩] k) :
    WP isa (c.fb mo r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        (List.range n).map (fbOut mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw))) ∧
      bytesAt s'.mem P (8 * c.bw) = fbIn mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) n ∧
      Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, dbp, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, lbp, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have subT : Region.Sub ⟨T, (8 * c.bw)⟩ S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subTbuf : Region.Sub ⟨T, (8 * c.bw)⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subTcore : Region.Sub ⟨T, (8 * c.bw)⟩ (coreRegion c B) := VG.Offset.sub_base B (by omega)
  have dTP : Region.Disjoint ⟨T, (8 * c.bw)⟩ ⟨P, (8 * c.bw)⟩ := (sPS.sub_right subT).symm
  have dDcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 8 * c.bw * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subCore
  have dPcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨P, (8 * c.bw)⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subCore
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega)⟩
  -- The mode's 7 slots: none of the core's, nor in the data or at the IV.
  have slotIn : ∀ i < 7, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have slotCore : ∀ i < 7, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega) (by omega)
  have slotT : ∀ i < 7, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ ⟨T, (8 * c.bw)⟩ := fun i hi =>
    VG.Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, mS, gS, rdS, wrS⟩ := stReg_ok (s := sE) (k := c.hiSlot) r.ctr bE
    (by rw [wrE]; exact inS (by simp only [Core.hiSlot, Core.ctrSlots]; omega))
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.fb
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  have gA' : ∀ x, x ≠ sb → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gA x h2 h3, gS, gE x h1]
  have bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS, bE]
  have rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  have wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  have fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact (fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains_base B (by simp only [Core.hiSlot, Core.ctrSlots]; omega)
        (by simp only [Core.hiSlot]; omega))
  -- The slots after the entry: the callee-saved registers and the IV's address.
  let sv : Nat → BitVec 64 := fun i => if i < 6 then s₀.gpr (Core.savedRegs.getD i .rbx) else P
  have svA : ∀ i < 7, sA.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [mA, mS, readW_slot_write _ (by omega) (by simp only [Core.hiSlot]; omega)]
    by_cases h : i < 6
    · rw [ite_eq_right (show c.slots + i ≠ c.hiSlot by simp only [Core.hiSlot]; omega), svE i h]
      show _ = if i < 6 then _ else _
      rw [ite_eq_left h]
    · rw [ite_eq_left (show c.slots + i = c.hiSlot by simp only [Core.hiSlot]; omega), gE _ hr.ctr.1, hP]
      show _ = if i < 6 then _ else _
      rw [ite_eq_right h]
  have kr := keyRegs_ne cs.keyRegs_ok
  have hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (kr x hx).1 (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA' fA
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩ List.mem_cons_self hkA)
    fun s₄ ⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  have sv₄ : ∀ i < 7, s₄.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [← svA i hi]
    exact f₄.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact slotCore i hi) (by decide)
  -- The IV to the buffer.
  obtain ⟨s₅a, e₅a, ax₅a, o₅a, m₅a, rd₅a, wr₅a⟩ := movS_ok (s := s₄) (k := c.hiSlot) .rax b₄
    (by rw [rd₄', wr₄']; exact inRd (inS (by simp only [Core.hiSlot, Core.ctrSlots]; omega)))
  have ax₅ : s₅a.gpr .rax = P := by
    rw [ax₅a, show c.hiSlot = c.slots + 6 from rfl, sv₄ 6 (by decide)]; rfl
  refine WP.seq (WP.block_append (WP.block_append (WP.of_runBlock ⟨s₅a, e₅a, WP.mono (copyN_wp (k := c.bw)
    (t := .rbp) (rd := sb) (rs := .rax) (od := 8 * c.buf) (os := 0) (P := T) (Q := P)
    ⟨by rw [o₅a _ (by decide), b₄], by rw [ax₅]; simp, by decide, by decide,
      fun w hw => by rw [wr₅a, wr₄', addr_add]; exact inS (by simp only [Core.ctrSlots]; omega),
      fun w hw => by
        rw [rd₅a, wr₅a, rd₄', wr₄']
        exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩,
      dTP, by omega⟩) fun s₅b h₅b => ?_⟩)))
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₅b c.leftReg
  refine WP.of_runBlock ⟨s₅, e₅, ?_⟩
  have g₅' : ∀ x, x ≠ .rax → x ≠ .rbp → s₅.gpr x = s₄.gpr x := fun x h1 h2 => by
    rw [g₅, h₅b.regs x h2, o₅a x h1]
  have mem₅ : s₅.mem = over s₄.mem T (8 * c.bw) fun i => s₄.mem (P + BitVec.ofNat 64 i) := by
    rw [m₅, h₅b.mem, m₅a]
  have f₅ : Frame [⟨T, (8 * c.bw)⟩] s₄.mem s₅.mem := by rw [mem₅]; exact over_frame _ _ _ _
  have b₅ : s₅.gpr sb = B := by rw [g₅' _ (by decide) (by decide), b₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅' _ (by decide) (by decide), rsp₄, gA' _ (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, h₅b.rd, rd₅a, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, h₅b.wr, wr₅a, wr₄']
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅' _ la lbp, lr₄, lrA, gS, gE _ hr.n.1]
  have hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have sv₅ : ∀ i < 7, s₅.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [← sv₄ i hi]
    exact f₅.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact slotT i hi) (by decide)
  -- The memory before the loop: the IV and the data as on entry.
  have m₄P : ∀ u < (8 * c.bw), s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, (8 * c.bw)⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega) hu]
    exact fA.bytes (R := ⟨P, (8 * c.bw)⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have m₅D : ∀ i < 8 * c.bw * n, s₅.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi => by
    rw [f₅.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subT) hn64 hi,
      f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dDcore hn64 hi]
    exact fA.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      hn64 hi
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = (8 * c.bw) := by simp [iv, bytesAt]
  have buf₅ : ∀ u < (8 * c.bw), s₅.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
      (fbIn mo (8 * c.bw) (cs.cipher k) s₀.mem D iv 0).getD u 0 := fun u hu => by
    rw [mem₅, over_at hu (by omega), m₄P u hu, fbIn, bytesAt_getD _ _ hu]
  have hp : GPre c s₅ B D n (8 * c.bw) := ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD⟩
  have fr₅ : Frame [S] s₀.mem s₅.mem :=
    fA.trans ((f₄.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩).trans
      (f₅.sub fun x hx => ⟨S, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hx; subst hx; exact subT⟩))
  -- The blocks.
  refine WP.seq (WP.mono (M := isa) (Q := FDone cs mo s₅ s₀.mem B D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, by rw [hn0]; exact buf₅,
      fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine fbLoop_wp cs mo hiv hp ⟨b₅, rfl, cs.ready_frame ready₄ f₅ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact .inr subTbuf)
        (fun x hx => by obtain ⟨h1, -, -, h4, -, -, -⟩ := of_not_modeRegs hx; exact g₅' x h1 h4),
      fun _ _ => rfl, ?_, ?_, by omega, buf₅, fun q hq r hr => ?_, Frame.refl _ _, rfl, rfl⟩
    · rw [g₅' _ da dbp, dr₄, drA, gS, gE _ hr.data.1, hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (Nat.not_lt_zero _)]; exact m₅D _ (hqr hq hr)
  -- The block to continue from back to the IV.
  have hsv7 : ∀ i < 7, s₆.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [d₆.saved i hi, sv₅ i hi]
  have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
  have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
  obtain ⟨s₇a, e₇a, ax₇a, o₇a, m₇a, rd₇a, wr₇a⟩ := movS_ok (s := s₆) (k := c.hiSlot) .rax d₆.base
    (by rw [rd₆, wr₆]; exact inRd (inS (by simp only [Core.hiSlot, Core.ctrSlots]; omega)))
  have ax₇ : s₇a.gpr .rax = P := by
    rw [ax₇a, show c.hiSlot = c.slots + 6 from rfl, hsv7 6 (by decide)]; rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₇a, e₇a, WP.mono (copyN_wp (k := c.bw)
    (t := .rbp) (rd := .rax) (rs := sb) (od := 0) (os := 8 * c.buf) (P := P) (Q := T)
    ⟨by rw [ax₇]; simp, by rw [o₇a _ (by decide), d₆.base], by decide, by decide,
      fun w hw => by rw [wr₇a, wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩,
      fun w hw => by
        rw [rd₇a, wr₇a, rd₆, wr₆, addr_add]
        exact inRd (inS (by simp only [Core.ctrSlots]; omega)),
      dTP.symm, by omega⟩) fun s₇ h₇ => ?_⟩))
  have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := by rw [h₇.mem, m₇a]
  have f₇ : Frame [⟨P, (8 * c.bw)⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
  have b₇ : s₇.gpr sb = B := by rw [h₇.regs _ (by decide), o₇a _ (by decide), d₆.base]
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₈, e₈, v₈, o₈, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₇
    b₇ hsv hinj (fun i hi' => by
      rw [h₇.rd, h₇.wr, rd₇a, wr₇a, rd₆, wr₆]
      exact inRd (inS (by simp only [Core.ctrSlots]; omega)))
  refine WP.of_runBlock ⟨s₈, e₈, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₈, h₇.rd, rd₇a, rd₆],
    by rw [wr₈, h₇.wr, wr₇a, wr₆]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₈.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₈ i hi', f₇.readW (Region.contains_self _ _) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact ((sPS.sub_right (slotIn i (by omega))).symm)) (by decide), hsv7 i (by omega)]
        simp only [sv, ite_eq_left hi']
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₈ _ (fun i hi' => by revert i; decide), h₇.regs _ (by decide), o₇a _ (by decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
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
    rw [mem₇, over_at hu (by omega), d₆.buf u hu, List.getElem_eq_getD 0]
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

end VG.Proof.Modes.X86_64
