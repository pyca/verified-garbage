module

import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# CBC decryption on x86-64 that updates the chaining value, for any core

`cbcDecryptChained_wp`: `c.cbcDecryptChained r` is `c.cbcDecrypt r`
(`cbcDecrypt_wp`), which also replaces the IV at `P` with the last block of
the data on entry (`Spec.Cbc.next`): once the IV is in the chaining value's
slots, `cbcLastToIv` copies the last block, at `D + 8 bw (n - 1)`
(`lastAddr_ok`), to the IV (`cbcLastToIv_wp`); the rest is
`cbcDecrypt`'s, which no longer reads the IV.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

/-- `shl r, k`. -/
theorem shlImm_ok (s : State) (r : Reg) {k : Nat} (hk : 1 ≤ k ∧ k ≤ 63) :
    ∃ s', runBlock isa [.shift .shl r k] s = some s' ∧ s'.gpr r = s.gpr r <<< k ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, hk, and_self, ↓reduceIte]; rfl, ?_,
    fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `add d, r`. -/
theorem addReg_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [.alu .add d (.reg r)] s = some s' ∧ s'.gpr d = s.gpr d + s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

variable {c : Core}

theorem blkShift_pow (hbw0 : 0 < c.bw) (hbw2 : c.bw ≤ 2) : 2 ^ c.blkShift = 8 * c.bw ∧ 1 ≤ c.blkShift ∧
    c.blkShift ≤ 63 := by
  unfold Core.blkShift
  split
  · rename_i h; rw [h]; decide
  · have : c.bw = 2 := by omega
    rw [this]; decide

/-- The last block's address, `D + 8 bw (n - 1)`, to `rax`. -/
theorem lastAddr_ok (hbw0 : 0 < c.bw) (hbw2 : c.bw ≤ 2) {r : CtrRegs} (hdr : r.data ≠ .rax) (s : State)
    {D : Addr} {n : Nat} (hD : s.gpr r.data = D) (hn : (s.gpr r.n).toNat = n) (hn0 : n ≠ 0) :
    ∃ s', runBlock isa (c.lastAddr r) s = some s' ∧ s'.gpr .rax = D + BitVec.ofNat 64 (8 * c.bw * (n - 1)) ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hp, hk⟩ := blkShift_pow hbw0 hbw2
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rax r.n
  obtain ⟨s₂, e₂, a₂, -, o₂, m₂, rd₂, wr₂⟩ := subImm_ok s₁ .rax 1
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := shlImm_ok s₂ .rax hk
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addReg_ok s₃ .rax r.data
  refine ⟨s₄, ?_, ?_, fun x hx => by rw [o₄ x hx, o₃ x hx, o₂ x hx, o₁ x hx], by rw [m₄, m₃, m₂, m₁],
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.lastAddr, show ([movR .rax r.n, .alu .sub .rax (.imm 1), .shift .shl .rax c.blkShift,
      .alu .add .rax (.reg r.data)] : List Instr) = [movR .rax r.n] ++ ([.alu .sub .rax (.imm 1)] ++
      ([.shift .shl .rax c.blkShift] ++ [.alu .add .rax (.reg r.data)])) from rfl, runBlock_app, e₁,
      Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [a₄, a₃, a₂, a₁, o₃ _ hdr, o₂ _ hdr, o₁ _ hdr, hD, BitVec.add_comm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hlt := (s.gpr r.n).isLt
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub, show (1 : BitVec 32).signExtend 64 = 1 from rfl, hn,
      Nat.shiftLeft_eq, hp, BitVec.toNat_ofNat]
    rw [show (2 ^ 64 - (1 : BitVec 64).toNat + n) % 2 ^ 64 = n - 1 by
      rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega, Nat.mul_comm]

/-- `cbcLastToIv`: unless `n` is zero, the last of the `n` blocks at `D` to
the IV at `P`, through `rax` and `rbx`. -/
theorem cbcLastToIv_wp (hbw0 : 0 < c.bw) (hbw2 : c.bw ≤ 2) {r : CtrRegs} (hr : RegsOk r) {s : State}
    {m₀ : Mem} {P D : Addr} {n : Nat} (hP : s.gpr r.ctr = P) (hD : s.gpr r.data = D)
    (hn : (s.gpr r.n).toNat = n) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr) (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hm : ∀ i < 8 * c.bw * n, s.mem (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i)) :
    WP isa (c.cbcLastToIv r) s fun s' => (∀ x, x ≠ .rax → x ≠ .rbx → s'.gpr x = s.gpr x) ∧
      Frame [⟨P, 8 * c.bw⟩] s.mem s'.mem ∧ bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next
        (bytesAt s.mem P (8 * c.bw)) (blocksOf (8 * c.bw) m₀ D n) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL0 : 0 < 8 * c.bw := by omega
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  obtain ⟨s₁, e₁, z₁, g₁, m₁, rd₁, wr₁⟩ := testSelf_ok s r.n
  have hz₁ : s₁.zf = some (decide (n = 0)) := by
    rw [z₁]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  unfold Core.cbcLastToIv
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₁])
    (fun h0 => ?_) (fun h0 => ?_)⟩)
  · have hn0 : n = 0 := by simpa using h0
    subst hn0
    exact WP.block_nil ⟨fun x _ _ => by rw [g₁], by rw [m₁]; exact Frame.refl _ _, by rw [m₁]; rfl, rd₁, wr₁⟩
  have hn0 : n ≠ 0 := by simpa using h0
  have hn1 : n - 1 < n := by omega
  let A := D + BitVec.ofNat 64 (8 * c.bw * (n - 1))
  have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D (idx_lt hn1)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := lastAddr_ok hbw0 hbw2 hr.data.2.1 s₁ (by rw [g₁, hD])
    (by rw [g₁, hn]) hn0
  refine WP.block_append (WP.of_runBlock ⟨s₂, e₂, WP.mono (copyN_wp (k := c.bw) (t := .rbx) (rd := r.ctr)
    (rs := .rax) (od := 0) (os := 0) (P := P) (Q := D + BitVec.ofNat 64 (8 * c.bw * (n - 1)))
    ⟨by rw [o₂ _ hr.ctr.2.1, g₁, hP]; simp, by rw [a₂]; simp, Ne.symm hr.ctr.2.2, by decide,
      fun w hw => by rw [wr₂, wr₁]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩,
      fun w hw => by
        rw [rd₂, wr₂, rd₁, wr₁]
        exact inRd ⟨_, hwD, by
          rw [addr_add]
          have := idx_lt (L := 8 * c.bw) hn1
          exact VG.Offset.contains_base D (by omega) (by omega)⟩,
      sPD.sub_right subA, by omega⟩) fun s' h' => ?_⟩)
  have mem' : s'.mem = over s.mem P (8 * c.bw) fun i =>
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * (n - 1)) + BitVec.ofNat 64 i) := by
    rw [h'.mem, m₂, m₁]
  refine ⟨fun x h1 h2 => by rw [h'.regs x h2, o₂ x h1, g₁], by rw [mem']; exact over_frame _ _ _ _, ?_,
    by rw [h'.rd, rd₂, rd₁], by rw [h'.wr, wr₂, wr₁]⟩
  rw [next_blocksOf _ _ _ _ hn0]
  refine bytesAt_of_getD (by simp [bytesAt]) fun u hu => ?_
  rw [mem', over_at hu (by omega), bytesAt_getD _ _ hu, addr_add]
  exact hm _ (by have := idx_lt (L := 8 * c.bw) hn1; omega)

theorem cbcDecryptChained_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P)
    (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩)
    (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩] k)
    (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.cbcDecryptChained r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.decrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let H := chainAddr c B
  have subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ (modeRegion c B) := VG.Offset.sub B (by simp only [Core.hiSlot]; omega)
    (by simp only [Core.hiSlot]; omega)
  have dPm : Region.Disjoint ⟨P, 8 * c.bw⟩ (modeRegion c B) := sPS.sub_right subMode
  -- The entry, and the IV to the chaining value.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  unfold Core.cbcDecryptChained
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨sE, eE, WP.mono_syms (copyN_wp (k := c.bw) (P := H)
    (Q := P) ⟨by rw [bE], by rw [gE _ hr.ctr.1, hP]; simp, by decide, Ne.symm hr.ctr.2.1,
      fun w hw => ⟨_, by rw [wrE]; exact hs.wr, by
        rw [addr_add]
        exact VG.Offset.contains_base B (by simp only [Core.hiSlot, Core.ctrSlots]; omega)
          (by simp only [Core.hiSlot]; omega)⟩,
      fun w hw => inRd ⟨_, by rw [wrE]; exact hwP, VG.Offset.contains_base P (by omega) (by omega)⟩,
      (dPm.sub_left (fun _ h => h)).symm.sub_left subH |>.symm.symm, by omega⟩) fun sC hC syC => ?_⟩))
  have gC : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → sC.gpr x = s₀.gpr x := fun x h1 h2 _ => by
    rw [hC.regs x h2, gE x h1]
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
  refine WP.seq (WP.mono_syms (cbcLastToIv_wp (m₀ := s₀.mem) hbw0 hbw2 hr (by rw [gC _ hr.ctr.1 hr.ctr.2.1 hr.ctr.2.2, hP])
    (by rw [gC _ hr.data.1 hr.data.2.1 hr.data.2.2, hD]) (by rw [gC _ hr.n.1 hr.n.2.1 hr.n.2.2, hn])
    (by rw [hC.wr, wrE]; exact hwP) (by rw [hC.wr, wrE]; exact hwD) sPD fitD mCD)
    fun sL ⟨gL, fL, ivL, rdL, wrL⟩ syL => ?_)
  have bytesP : bytesAt sC.mem P (8 * c.bw) = bytesAt s₀.mem P (8 * c.bw) :=
    bytesAt_of_getD (by simp [bytesAt]) fun u hu => by rw [mCP u hu]; exact (bytesAt_getD _ _ hu).symm
  rw [bytesP] at ivL
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok sL r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁b, ?_⟩)
  have g₁a : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → sL.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gL x h2 h3, gC x h1 h2 h3]
  have g₁ : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1 h2 h3]
  have b₁ : s₁.gpr sb = B := by
    rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), gL _ (by decide) (by decide), hC.regs _ (by decide), bE]
  have rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rdL, hC.rd, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wrL, hC.wr, wrE]
  have mem₁ : s₁.mem = sL.mem := m₁b
  -- What the memory holds before the key.
  have dPH : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨H, 8 * c.bw⟩ := dPm.sub_right subH
  have sv₁ : ∀ i < 6, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .rbx) :=
    fun i hi => by
      rw [← svE i hi, mem₁]
      refine (fL.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
          simp only [Core.ctrSlots]; omega))).symm)
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
  have f₁' : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩] s₀.mem s₁.mem := by
    rw [mem₁]
    exact (fC.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (fL.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx).1 (kr x hx).2.1 (kr x hx).2.2 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₁ wr₁
      (by rw [runBlock_syms e₁b, syL, syC, runBlock_syms eE]) f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, rsp₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  rw [show s₁.gpr .rsp = s₀.gpr .rsp from g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₂
  have keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (hstk.coreFrame_disj (VG.Offset.disjoint_base B (by omega) (by omega))
      ⟨_, hs.wr, VG.Offset.sub_base B (by omega)⟩) (by decide)
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have left₃ : s₃.gpr c.leftReg = s₀.gpr r.n := by rw [g₃, lr₂, lr₁, g₁a _ hr.n.1 hr.n.2.1 hr.n.2.2]
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, ← g₃, left₃]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₃ : s₃.mem = s₂.mem := m₃
  have b₃ : s₃.gpr sb = B := by rw [g₃, b₂]
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃, rsp₂, g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂']
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂']
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₃ B D n (8 * c.bw) :=
    ⟨⟨by rw [wr₃']; exact hs.wr, hs.fit⟩, by rw [wr₃']; exact hwD, sDS, fitD, hstk.congr rsp₃ wr₃'⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := CDone cs s₃ B D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₃, rfl, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cbcDecLoop_wp cs hiv hp ⟨b₃, rfl, cs.ready_frame ready₂ (by rw [mem₃]; exact Frame.refl [] _)
        (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rd₃, wr₃, runBlock_syms e₃⟩ (fun r _ => by rw [g₃]), fun _ _ => rfl, ?_, ?_, by omega, fun u hu => ?_,
      fun i _ => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl⟩
    · rw [g₃, dr₂, dr₁, g₁a _ hr.data.1 hr.data.2.1 hr.data.2.2, hD]; simp
    · rw [left₃, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · have dH : Region.Disjoint ⟨chainAddr c B, 8 * c.bw⟩ (coreRegion c B) :=
        VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)
      rw [Nat.mul_zero, cbcPrev, ite_eq_left rfl, mem₃,
        f₂.bytes (R := ⟨chainAddr c B, 8 * c.bw⟩) (hstk.coreFrame_disj dH ⟨_, hs.wr, VG.Offset.sub_base B
          (by simp only [Core.hiSlot, Core.ctrSlots]; omega)⟩) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu,
        ch₁ u hu, bytesAt_getD _ _ hu]
  -- The exit.
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₄
    d₄.base hsv hinj (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₃', wr₃']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega)))
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have f₄ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp))
      s₀.mem s₄.mem := by
    refine (((f₁'.mono fun x hx => List.mem_append_left _ hx).trans
      (f₂.sub (coreFrame_sub (rs := [⟨B, 8 * c.ctrSlots⟩, ⟨P, 8 * c.bw⟩]) ⟨_, List.mem_cons_self, subCore⟩))).mono
      fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact List.mem_append_right _ hx).trans ?_
    rw [← mem₃]
    exact d₄.frame.mono fun x hx => by
      rw [rsp₃] at hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_append_right _ hx
  refine WP.of_runBlock ⟨s₅, e₅, fun x hx => ?_, ?_, ?_, by rw [m₅]; exact f₄, by rw [rd₅, d₄.rd, rd₃'],
    by rw [wr₅, d₄.wr, wr₃']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₅.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₅ i hi', d₄.saved i hi', mem₃, keep₂ _ (by omega) (by simp only [Core.ctrSlots]; omega), sv₁ i hi']
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₅ _ (fun i hi' => by revert i; decide), d₄.rsp, rsp₃]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₅, cbc_of_dinv (cs.cipher_len k) hiv d₄.data, mem₃,
      blocksOf_frame f₂ (by omega) (hstk.coreFrame_disj (sDS.sub_right subCore) ⟨_, hwD, fun _ h => h⟩),
      blocksOf_frame f₁' (by omega) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sDS
        · exact sPD.symm)]
  · -- The IV: written before the blocks, and not since.
    rw [m₅]
    have fIv : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₁.mem (P + BitVec.ofNat 64 u) := fun u hu => by
      have pStk := hstk.disj (R := ⟨P, 8 * c.bw⟩) ⟨_, hwP, fun _ h => h⟩
      rw [d₄.frame.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
          rw [rsp₃] at hx
          rcases List.mem_append.mp hx with hx | hx
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact sPS
            · exact sPD
          · exact pStk x hx) (show 8 * c.bw ≤ 2 ^ 64 by omega) hu, mem₃]
      exact f₂.bytes (R := ⟨P, 8 * c.bw⟩) (coreFrame_disj (sPS.sub_right subCore) pStk)
        (show 8 * c.bw ≤ 2 ^ 64 by omega) hu
    have e : bytesAt s₄.mem P (8 * c.bw) = bytesAt sL.mem P (8 * c.bw) :=
      bytesAt_of_getD (by simp [bytesAt]) fun u hu => by rw [fIv u hu, mem₁]; exact (bytesAt_getD _ _ hu).symm
    rw [e]
    exact ivL

end VG.Proof.Modes.X86_64
