module

import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
public import VerifiedGarbage.Proof.Modes.AArch64.Setup
public import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CBC decryption on AArch64 that updates the chaining value, for any core

`cbcDecryptChained_wp`: `c.cbcDecryptChained r` is `c.cbcDecrypt r`
(`cbcDecrypt_wp`), which also replaces the IV at `P` with the last block of
the data on entry (`Spec.Cbc.next`): once the IV is in the chaining value's
slots, `cbcLastToIv` copies the last block, at `D + 8 bw (n - 1)`
(`lastAddr_ok`), to the IV (`cbcLastToIv_wp`); the rest is
`cbcDecrypt`'s, which no longer reads the IV. As on x86-64
(`Proof/Modes/X86_64/CbcDecChained.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

/-- `lsl d, n, #sh`. -/
theorem lsl_ok (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    ∃ s', runBlock isa [.lsl .x d n sh] s = some s' ∧ s'.gpr d = s.gpr n <<< sh ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n <<< sh), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, h, ite_true, read_x]

/-- `add d, n, m`. -/
theorem addReg_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.add .x d n m] s = some s' ∧ s'.gpr d = s.gpr n + s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n + s.gpr m), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x]

variable {c : Core}

theorem blkShift_pow (hbw0 : 0 < c.bw) (hbw2 : c.bw ≤ 2) : 2 ^ c.blkShift = 8 * c.bw ∧ c.blkShift < 64 := by
  unfold Core.blkShift
  split
  · rename_i h; rw [h]; decide
  · have : c.bw = 2 := by omega
    rw [this]; decide

/-- The last block's address, `D + 8 bw (n - 1)`, to `x7`. -/
theorem lastAddr_ok (hbw0 : 0 < c.bw) (hbw2 : c.bw ≤ 2) {r : CtrRegs} (hdr : r.data ≠ .x7) (s : State)
    {D : Addr} {n : Nat} (hD : s.gpr r.data = D) (hn : (s.gpr r.n).toNat = n) (hn0 : n ≠ 0) :
    ∃ s', runBlock isa (c.lastAddr r) s = some s' ∧ s'.gpr .x7 = D + BitVec.ofNat 64 (8 * c.bw * (n - 1)) ∧
      (∀ x, x ≠ .x7 → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hp, hk⟩ := blkShift_pow hbw0 hbw2
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := subImm_ok s .x7 r.n (v := 1) (by decide)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := lsl_ok s₁ .x7 .x7 hk
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addReg_ok s₂ .x7 .x7 r.data
  refine ⟨s₃, ?_, ?_, fun x hx => by rw [o₃ x hx, o₂ x hx, o₁ x hx], by rw [m₃, m₂, m₁],
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [Core.lastAddr, show ([.subImm .x .x7 r.n 1, .lsl .x .x7 .x7 c.blkShift, .add .x .x7 .x7 r.data] :
      List Instr) = [.subImm .x .x7 r.n 1] ++ ([.lsl .x .x7 .x7 c.blkShift] ++ [.add .x .x7 .x7 r.data]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [a₃, a₂, a₁, o₂ _ hdr, o₁ _ hdr, hD, BitVec.add_comm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hlt := (s.gpr r.n).isLt
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub, hn, Nat.shiftLeft_eq, hp, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [show (2 ^ 64 - 1 % 2 ^ 64 + n) % 2 ^ 64 = n - 1 by omega, Nat.mul_comm]

/-- `cbcLastToIv`: unless `n` is zero, the last of the `n` blocks at `D` to
the IV at `P`, through `x6` and `x7`. -/
theorem cbcLastToIv_wp (hbw0 : 0 < c.bw) (hbw2 : c.bw ≤ 2) {r : CtrRegs} (hr : RegsOk r) {s : State}
    {m₀ : Mem} {P D : Addr} {n : Nat} (hP : s.gpr r.ctr = P) (hD : s.gpr r.data = D)
    (hn : (s.gpr r.n).toNat = n) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr) (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hm : ∀ i < 8 * c.bw * n, s.mem (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i)) :
    WP isa (c.cbcLastToIv r) s fun s' => (∀ x, x ≠ .x6 → x ≠ .x7 → s'.gpr x = s.gpr x) ∧
      Frame [⟨P, 8 * c.bw⟩] s.mem s'.mem ∧ bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next
        (bytesAt s.mem P (8 * c.bw)) (blocksOf (8 * c.bw) m₀ D n) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL0 : 0 < 8 * c.bw := by omega
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  obtain ⟨-, c6, c7, -⟩ := not_setupRegs hr.ctr
  obtain ⟨-, -, d7, -⟩ := not_setupRegs hr.data
  have hz : isa.eval (.zero .x r.n) s = some (decide (n = 0)) := by
    rw [eval_zero]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  unfold Core.cbcLastToIv
  refine WP.ite (decide (n = 0)) hz (fun h0 => ?_) (fun h0 => ?_)
  · have hn0 : n = 0 := by simpa using h0
    subst hn0
    exact WP.block_nil ⟨fun x _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl⟩
  have hn0 : n ≠ 0 := by simpa using h0
  have hn1 : n - 1 < n := by omega
  have subA : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (n - 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
    VG.Offset.sub_base D (idx_lt hn1)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := lastAddr_ok hbw0 hbw2 d7 s hD hn hn0
  refine WP.block_append (WP.of_runBlock ⟨s₂, e₂, WP.mono (copyN_wp (k := c.bw) (t := .x6) (u := .x6)
    (rd := r.ctr) (rs := .x7) (od := 0) (os := 0) (P := P) (Q := D + BitVec.ofNat 64 (8 * c.bw * (n - 1)))
    ⟨by rw [o₂ _ c7, hP]; simp, by rw [a₂]; simp, Ne.symm c6, by decide, Ne.symm c6, by decide, by decide,
      by decide, by omega, by omega,
      fun w hw => by rw [wr₂]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩,
      fun w hw => by
        rw [rd₂, wr₂]
        exact inRd ⟨_, hwD, by
          rw [addr_add]
          have := idx_lt (L := 8 * c.bw) hn1
          exact VG.Offset.contains_base D (by omega) (by omega)⟩,
      sPD.sub_right subA, by omega⟩) fun s' h' => ?_⟩)
  have mem' : s'.mem = over s.mem P (8 * c.bw) fun i =>
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * (n - 1)) + BitVec.ofNat 64 i) := by
    rw [h'.mem, m₂]
  refine ⟨fun x h1 h2 => by rw [h'.regs x h1 h1, o₂ x h2], by rw [mem']; exact over_frame _ _ _ _, ?_,
    by rw [h'.rd, rd₂], by rw [h'.wr, wr₂]⟩
  rw [next_blocksOf _ _ _ _ hn0]
  refine bytesAt_of_getD (by simp [bytesAt]) fun u hu => ?_
  rw [mem', over_at hu (by omega), bytesAt_getD _ _ hu, addr_add]
  exact hm _ (by have := idx_lt (L := 8 * c.bw) hn1; omega)

theorem cbcDecryptChained_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩) (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨P, 8 * c.bw⟩] k) :
    WP isa (c.cbcDecryptChained r) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.decrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨cs', c6, -, -⟩ := not_setupRegs hr.ctr
  let H := chainAddr c B
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega)
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ (modeRegion c B) := VG.Offset.sub B (by simp only [Core.hiSlot]; omega)
    (by simp only [Core.hiSlot]; omega)
  have dPm : Region.Disjoint ⟨P, 8 * c.bw⟩ (modeRegion c B) := sPS.sub_right subMode
  -- The entry, and the IV to the chaining value.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cbcDecryptChained
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨sE, eE, WP.mono_syms (copyN_wp (k := c.bw) (P := H)
    (Q := P) (u := .x6) ⟨by rw [bE], by rw [gE _ cs', hP]; simp, by decide, Ne.symm c6, by decide, Ne.symm c6,
      by omega, by decide, by simp only [Core.hiSlot]; omega, by omega,
      fun w hw => ⟨_, by rw [wrE]; exact hs.wr, by
        rw [addr_add]
        exact VG.Offset.contains_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)⟩,
      fun w hw => inRd ⟨_, by rw [wrE]; exact hwP, VG.Offset.contains_base P (by omega) (by omega)⟩,
      (dPm.sub_left (fun _ h => h)).symm.sub_left subH |>.symm.symm, by omega⟩) fun sC hC syC => ?_⟩))
  have gC : ∀ x, x ∉ SetupRegs → sC.gpr x = s₀.gpr x := fun x hx => by
    obtain ⟨h1, h2, -, -⟩ := not_setupRegs hx
    rw [hC.regs x h2 h2, gE x h1]
  have memC : sC.mem = over sE.mem H (8 * c.bw) fun i => sE.mem (P + BitVec.ofNat 64 i) := hC.mem
  have fCH : Frame [⟨H, 8 * c.bw⟩] sE.mem sC.mem := by rw [memC]; exact over_frame _ _ _ _
  have fC : Frame [modeRegion c B] s₀.mem sC.mem :=
    fE.trans (fCH.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, subH⟩)
  have mCD : ∀ i < 8 * c.bw * n, sC.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    fC.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  have mCP : ∀ u < 8 * c.bw, sC.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    fC.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dPm) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  -- The last block to the IV.
  refine WP.seq (WP.mono_syms (cbcLastToIv_wp (m₀ := s₀.mem) hbw0 hbw2 hr (by rw [gC _ hr.ctr, hP])
    (by rw [gC _ hr.data, hD]) (by rw [gC _ hr.n, hn])
    (by rw [hC.wr, wrE]; exact hwP) (by rw [hC.wr, wrE]; exact hwD) sPD fitD mCD)
    fun sL ⟨gL, fL, ivL, rdL, wrL⟩ syL => ?_)
  have bytesP : bytesAt sC.mem P (8 * c.bw) = bytesAt s₀.mem P (8 * c.bw) :=
    bytesAt_of_getD (by simp [bytesAt]) fun u hu => by rw [mCP u hu]; exact (bytesAt_getD _ _ hu).symm
  rw [bytesP] at ivL
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok sL r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁b, ?_⟩)
  have g₁a : ∀ x, x ∉ SetupRegs → sL.gpr x = s₀.gpr x := fun x hx => by
    obtain ⟨-, h2, h3, -⟩ := not_setupRegs hx
    rw [gL x h2 h3, gC x hx]
  have g₁ : ∀ x, x ∉ SetupRegs → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1]
  have b₁ : s₁.gpr sb = B := by
    rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), gL _ (by decide) (by decide), hC.regs _ (by decide) (by decide), bE]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rdL, hC.rd, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wrL, hC.wr, wrE]
  have mem₁ : s₁.mem = sL.mem := m₁b
  have dPH : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨H, 8 * c.bw⟩ := dPm.sub_right subH
  have sv₁ : ∀ i < 10, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← svE i hi, mem₁]
      refine (fL.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by omega))).symm)
        (by decide)).trans ?_
      exact fCH.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega)) (by omega)
          (by simp only [Core.hiSlot]; omega)) (by decide)
  have ch₁ : ∀ u < 8 * c.bw, s₁.mem (H + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₁, fL.bytes (R := ⟨H, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact dPH.symm) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu,
      memC, over_at hu (by omega)]
    exact fE.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dPm) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
  have kr := keyRegs_ne cs.keyRegs_ok
  have f₁' : Frame [⟨B, 8 * c.total⟩, ⟨P, 8 * c.bw⟩] s₀.mem s₁.mem := by
    rw [mem₁]
    exact (fC.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (fL.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.total⟩, ⟨P, 8 * c.bw⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx) (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rd₁ wr₁
      (by rw [runBlock_syms e₁b, syL, syC, runBlock_syms eE]) f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  have keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  have left₂ : s₂.gpr c.leftReg = s₀.gpr r.n := by rw [lr₂, lr₁, g₁a _ hr.n]
  have hz₂ : isa.eval (.zero .x c.leftReg) s₂ = some (decide (n = 0)) := by
    rw [eval_zero, left₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₂ B D n (8 * c.bw) := ⟨⟨by rw [wr₂']; exact hs.wr, hs.fit⟩, by rw [wr₂']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := CDone cs s₂ B D n k iv)
    (WP.ite (decide (n = 0)) hz₂ (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₂, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega, Frame.refl _ _,
      rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcDecLoop_wp cs hiv hp ⟨b₂, ready₂, fun _ _ => rfl, ?_, ?_, by omega, fun u hu => ?_,
      fun i _ => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl⟩
    · rw [dr₂, dr₁, g₁a _ hr.data, hD]; simp
    · rw [left₂, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · have dH : Region.Disjoint ⟨chainAddr c B, 8 * c.bw⟩ (coreRegion c B) :=
        VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)
      rw [Nat.mul_zero, cbcPrev, ite_eq_left rfl,
        f₂.bytes (R := ⟨chainAddr c B, 8 * c.bw⟩) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact dH) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu,
        ch₁ u hu, bytesAt_getD _ _ hu]
  -- The exit.
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₅, e₅, v₅, -, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₄
    d₄.base hsv hinj (by omega) (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₂', wr₂']
      exact inRd (slot_wr hs.wr hN (by omega)))
  have subCore : ∀ x ∈ [coreRegion c B], Region.Sub x ⟨B, 8 * c.total⟩ := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega)
  have f₄ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s₄.mem := by
    refine ((f₁'.trans (f₂.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, subCore x hx⟩)).mono
      fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)).trans ?_
    exact d₄.frame.mono fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi' => ?_, ?_, ?_, by rw [m₅]; exact f₄, by rw [rd₅, d₄.rd, rd₂'],
    by rw [wr₅, d₄.wr, wr₂']⟩
  · rw [v₅ i hi', d₄.saved i hi', keep₂ _ (by omega) (by omega), sv₁ i hi']
  · rw [m₅, cbc_of_dinv (cs.cipher_len k) hiv d₄.data,
      blocksOf_frame f₂ (by omega) (fun x hx => sDS.sub_right (subCore x hx)),
      blocksOf_frame f₁' (by omega) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sDS
        · exact sPD.symm)]
  · -- The IV: written before the blocks, and not since.
    rw [m₅]
    have fIv : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₁.mem (P + BitVec.ofNat 64 u) := fun u hu => by
      rw [d₄.frame.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact sPS
          · exact sPD) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu]
      exact f₂.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact sPS.sub_right (Region.sub_prefix (by omega))) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
    have e : bytesAt s₄.mem P (8 * c.bw) = bytesAt sL.mem P (8 * c.bw) :=
      bytesAt_of_getD (by simp [bytesAt]) fun u hu => by rw [fIv u hu, mem₁]; exact (bytesAt_getD _ _ hu).symm
    rw [e]
    exact ivL

end VG.Proof.Modes.AArch64
