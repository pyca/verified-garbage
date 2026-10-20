module

import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Loop
public import VerifiedGarbage.Proof.Modes.AArch64.Fb
public import VerifiedGarbage.Impl.Modes.AArch64.Cfb8
public import VerifiedGarbage.Proof.Modes.Cfb8
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CFB8 on AArch64, for any core: the whole function

`cfb8_wp`: `c.cfb8 enc r ivR`, for a core `c` with `BlockSpec c` whose
cipher is the forward cipher `CIPH_K`, its arguments in the registers `r`,
and the input block's address kept in `ivR` (which the core keeps:
`KeepsReg`), replaces the `n` bytes at `D` with CFB8's output (`cfb8Out`)
under the key `k` that its key arguments give, from the input block at `P`,
and that block with the input block after the last byte (`cfb8In`); it
keeps the callee-saved registers `x19`–`x28`, and writes nothing but the
scratch buffer, the data and the input block. As on x86-64
(`Proof/Modes/X86_64/Cfb8.lean`); `cfb8Enc_of` and `cfb8Dec_of`
(`Proof/Modes/Cfb8.lean`) state these as the specification's.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cfb8_wp (cs : BlockSpec c) (enc : Bool) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {ivR : Reg}
    (hiv : IvRegOk c r ivR) {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B)
    (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩) (sDS : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.total⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩) (fitD : D.toNat + n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩] k) (hsc : KeepsReg ivR c.prepare ∧ KeepsReg ivR c.crypt) :
    WP isa (c.cfb8 enc r ivR) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      bytesAt s'.mem D n = (List.range n).map (cfb8Out enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw))) ∧
      bytesAt s'.mem P (8 * c.bw) = cfb8In enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) n ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega
  have hn64 : n < 2 ^ 64 := by rw [← hn]; exact BitVec.isLt _
  have hN : 8 * c.total < 2 ^ 64 := by omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨cs', -⟩ := not_setupRegs hr.ctr
  obtain ⟨ds', -⟩ := not_setupRegs hr.data
  obtain ⟨ns', -⟩ := not_setupRegs hr.n
  obtain ⟨-, idr, ilr⟩ := of_not_modeRegs hiv.mode
  obtain ⟨isb, -⟩ := not_setupRegs hiv.setup
  let S : Region := ⟨B, 8 * c.total⟩
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by omega)
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by omega)
  have slotIn : ∀ i < 10, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by omega)
  have slotCore : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega) (by omega)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movR_ok sE ivR r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.cfb8
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
  have left₄ : s₄.gpr c.leftReg = s₀.gpr r.n := by rw [lr₄, lrA, gS _ (Ne.symm hiv.n), gE _ ns']
  have hz₄ : isa.eval (.zero .x c.leftReg) s₄ = some (decide (n = 0)) := by
    rw [eval_zero, left₄]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have dDcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subCore
  have dPcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨P, 8 * c.bw⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subCore
  have m₄P : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, 8 * c.bw⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega) hu]
    exact fA.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have m₄D : ∀ q < n, s₄.mem (D + BitVec.ofNat 64 q) = s₀.mem (D + BitVec.ofNat 64 q) := fun q hq => by
    rw [f₄.bytes (R := ⟨D, n⟩) dDcore (show n ≤ 2 ^ 64 by omega) hq]
    exact fA.bytes (R := ⟨D, n⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      (show n ≤ 2 ^ 64 by omega) hq
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hivl : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : C8Pre c s₄ B D P n := ⟨⟨by rw [wr₄']; exact hs.wr, hs.fit⟩, by rw [wr₄']; exact hwD,
    by rw [wr₄']; exact hwP, sDS, sPS, sPD, fitD, hn64⟩
  have fr₄ : Frame [S] s₀.mem s₄.mem :=
    fA.trans (f₄.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩)
  -- The bytes.
  refine WP.seq (WP.mono (M := isa) (Q := C8Done cs enc ivR s₄ s₀.mem B D P n k iv)
    (WP.ite (decide (n = 0)) hz₄ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₄, fun _ _ => rfl, fun u hu => by rw [hn0, m₄P u hu]; simp [cfb8In, iv, bytesAt, hu],
      fun q hq => by omega, Frame.refl _ _, rfl, rfl, ivR₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cfb8Loop_wp cs enc hiv.mode hivl hp hsc.2 ⟨b₄, ready₄, fun _ _ => rfl, ?_, ?_, by omega,
      fun u hu => by rw [m₄P u hu]; simp [cfb8In, iv, bytesAt, hu], fun q hq => ?_, Frame.refl _ _, rfl, rfl, ivR₄⟩
    · rw [dr₄, drA, gS _ (Ne.symm hiv.data), gE _ ds', hD]; simp
    · rw [left₄, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (Nat.not_lt_zero _)]; exact m₄D q hq
  -- The exit.
  have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₄']
  have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₄']
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₈, e₈, v₈, -, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₆
    d₆.base hsv hinj (by omega) (fun i hi' => by
      rw [rd₆, wr₆]
      exact inRd (slot_wr hs.wr hN (by omega)))
  refine WP.of_runBlock ⟨s₈, e₈, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₈, rd₆], by rw [wr₈, wr₆]⟩
  · rw [v₈ i hi', d₆.saved i hi', sv₄ i hi']
  · rw [m₈]
    apply List.ext_getElem (by simp [bytesAt])
    intro q h1 _
    have hq : q < n := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact d₆.data q hq
  · rw [m₈]
    apply List.ext_getElem (by
      rw [cfb8In_length (iv := bytesAt s₀.mem P (8 * c.bw)) enc _ _ _ (by simp [bytesAt]) hL0]; simp [bytesAt])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [d₆.ivB u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    exact (fr₄.mono fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans
      d₆.frame

end VG.Proof.Modes.AArch64
