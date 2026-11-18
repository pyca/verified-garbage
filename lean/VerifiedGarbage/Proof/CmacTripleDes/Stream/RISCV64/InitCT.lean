module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.TripleDes.Schedule

/-! ### `CmacTripleDes.Stream.RISCV64.Init`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on RISC-V: `stream_init`

The code saves `ra`, `s1` and `s2` in the scratch buffer at `sv S`
(`Spill.save_ok`), expands the key into the state (`key_call`), zeroes the
block of `K1` (`Bytes.storeBytes_ok`) and enciphers it in place
(`ecb_call`: `L`), doubles it there (`K1`) and into the next block (`K2`,
`dbl_wp`), zeroes the chaining value and restores the registers
(`Spill.restore_wp`): the state then represents the empty message
(`init_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.Cmac.RISCV64 (dbl_wp dbl_spec8)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a1 : s₀.gpr .a1 = Kp
  a2 : (s₀.gpr .a2).toNat = KL
  a3 : s₀.gpr .a3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 640⟩]
  st_k : (⟨St, 416⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 640⟩
  stk_st : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩
  stk_k : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨Kp, KL⟩
  stk_s : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨S, 640⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 640 ≤ 2 ^ 64
  al : s₀.sp.toNat % 16 = 0
  sp : 944 ≤ s₀.sp.toNat
  valid : Spec.TripleDes.validKey KL

theorem IPre.of {s₀ : State} (h : initRISCV64.pre s₀) :
    IPre s₀ (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a3) (s₀.gpr .a2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- What the code saves: the registers, with `t0` the slots' base. -/
abbrev initG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv S)).gpr

theorem init_bound : ∀ p ∈ initSaved, p.2 + 8 ≤ 24 := by decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : KArgs s Kp St KL
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem (sv S) (initG s₀ S) initSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem initSave_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initSave) s₀ (IMid₁ s₀ St Kp S KL) := by
  obtain hKL : s₀.gpr .a2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.a2
  rw [initSave, saveRegs, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show initSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 initSaved from rfl]
  obtain t₀ : (s₀.write .t0 (sv S)).gpr .t0 = sv S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := initSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := init_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 640⟩, by simp, sv_contains S (by omega_using [this]) (by decide)⟩
  generalize ht : ({ (s₀.write .t0 (sv S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv S)).mem ((s₀.write .t0 (sv S)).gpr .t0)
      (s₀.write .t0 (sv S)).gpr initSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain memt : t.mem = Spill.saveMem s₀.mem (sv S) (initG s₀ S) initSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  obtain spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  obtain s1 : s₅.gpr .s1 = St := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, gt, hp.a0]
  refine ⟨?_, s1, ?_, fun r hr h1 h2 => ?_, ?_, rd₅, wr₅,
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, spt]⟩
  · exact
    { a0 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, gt, hp.a1]
      a1 := by simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, gt, hKL]
      a2 := by rw [u₅.gpr, s1.symm.trans (by rw [u₅.other _ (by decide)])]
      valid := hp.valid
      ks := hp.st_k.symm
      reads := by rw [rd₅, hp.rd]; simp
      writes := by rw [wr₅, hp.wr]; simp }
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, gt, hp.a3]
  · obtain ⟨h0, -, -, -, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    rw [u₅.other _ ha2, u₄.other _ ha1, u₃.other _ ha0, u₂.other _ h2, u₁.other _ h1, gt _ h0]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]


/-! ## Zeroing a block -/

/-- `initZero` from a state with the state in `s1`: the block of `K1`
zeroed, and ECB's arguments on it. -/
theorem initZero_wp {s : State} {St : Addr} (h1 : s.gpr .s1 = St) (hw : (⟨St, 416⟩ : Region) ∈ s.wr) :
    WP isa (.block initZero) s fun s' => s'.gpr .a0 = St ∧ s'.gpr .a1 = St + BitVec.ofNat 64 384 ∧
      s'.gpr .a2 = BitVec.ofInt 64 1 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      Spec.Aes.bytesAt s'.mem (St + BitVec.ofNat 64 384) 8 = Spec.Cmac.zeros 8 ∧
      Frame [⟨St + BitVec.ofNat 64 384, 8⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [initZero, WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t0) (dst := .s1) (doff := 384) (bs := List.replicate 8 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₁ h₁ => ?_
  · simp only [List.length_replicate] at hi
    rw [h1]; exact ⟨_, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain ⟨z, fz⟩ := zeros_stored (by rw [h1]) h₁
  obtain s1₁ : s₁.gpr .s1 = St := by rw [h₁.gpr _ (by decide), h1]
  unfold ecbArgs mov
  refine wp_mv fun s₂ u₂ => wp_addi (imm := 384) (by decide) fun s₃ u₃ => ?_
  refine WP.cons (exec_li (show imm12 1 by decide)) (WP.block_nil ?_)
  refine ⟨?_, ?_, by simp [RegUpd.gpr_write], fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a0 ≠ .a2 by decide)]
    rw [u₃.other _ (by decide), u₂.gpr, s1₁]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .a2 by decide)]
    rw [u₃.gpr, u₂.other _ (by decide), s1₁]
  · obtain ⟨-, -, -, -, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    obtain ⟨h0, -⟩ := preserved_ne r hr
    simp only [RegUpd.gpr_write_of_ne _ _ ha2]
    rw [u₃.other _ ha1, u₂.other _ ha0, h₁.gpr _ h0]
  · simp only [RegUpd.mem_write]; rw [u₃.mem, u₂.mem]; exact z
  · simp only [RegUpd.mem_write]; rw [u₃.mem, u₂.mem]; exact fz
  · simp only [RegUpd.rd_write]; rw [u₃.rd, u₂.rd, h₁.rd]
  · simp only [RegUpd.wr_write]; rw [u₃.wr, u₂.wr, h₁.wr]
  · simp only [RegUpd.sp_write]; rw [u₃.sp, u₂.sp, h₁.sp]


/-! ## The whole function -/

/-- The subkeys from `L`, as the code derives them. -/
theorem subkeys_eq (key : List Byte) :
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8
    ks.1 ++ ks.2 = Spec.Cmac.dbl 8 (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey key) (Spec.Cmac.zeros 8)) ++
      Spec.Cmac.dbl 8 (Spec.Cmac.dbl 8 (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey key) (Spec.Cmac.zeros 8))) :=
  rfl

theorem init_wp {s₀ : State} (h0 : initRISCV64.pre s₀) :
    WP isa streamInit s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ initRISCV64.post s₀ s' := by
  obtain hp := IPre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a1 = Kp at hp
  generalize s₀.gpr .a3 = S at hp
  generalize (s₀.gpr .a2).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  obtain stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (initSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (key_call h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  obtain s1₂ : s₂.gpr .s1 = St := by rw [g₂ _ (by decide), h₁.s1]
  refine WP.seq (WP.mono (initZero_wp s1₂ (by rw [h₂.wr, h₁.wr]; exact stW)) fun s₃ h₃ => ?_)
  obtain ⟨a0₃, a1₃, a2₃, g₃, z₃, fz₃, rd₃, wr₃, sp₃⟩ := h₃
  obtain sp₃' : s₃.sp = s₀.sp := by rw [sp₃, h₂.sp, h₁.sp]
  refine WP.seq (WP.mono (ecb_call (S := St) (off := 384)
    ⟨a0₃, a1₃, a2₃, by decide, by decide, hw, by rw [sp₃']; exact hp.al, by rw [sp₃']; exact hp.sp,
      by rw [sp₃']; exact hp.stk_st, by rw [wr₃, h₂.wr, h₁.wr]; exact stW⟩) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.saved r hr, g₃ r hr, g₂ r hr]
  obtain s1₄ : s₄.gpr .s1 = St := by rw [g₄ _ (by decide), h₁.s1]
  obtain s2₄ : s₄.gpr .s2 = S := by rw [g₄ _ (by decide), h₁.s2]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, wr₃, h₂.wr, h₁.wr]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, rd₃, h₂.rd, h₁.rd]
  obtain inSt : ∀ d, d < 416 → InRegions s₀.wr (St + BitVec.ofNat 64 d) 1 := fun d hd =>
    ⟨_, stW, Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
  rw [initTail, List.append_assoc, List.append_assoc]
  refine dbl_wp (K := St) (src := 384) (dst := 384) (by decide) (by decide) dbl_spec8 s1₄ (.inl rfl)
    (by decide) (by decide) (by omega_using [hw]) (fun j hj => by rw [rd₄, wr₄]; exact in_wr (inSt _ (by omega_using [hj])))
    (fun j hj => by rw [wr₄]; exact inSt _ (by omega_using [hj])) fun s₅ g₅ rd₅ wr₅ sp₅ f₅ b₅ => ?_
  obtain s1₅ : s₅.gpr .s1 = St := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), s1₄]
  refine dbl_wp (K := St) (src := 384) (dst := 392) (by decide) (by decide) dbl_spec8 s1₅ (.inr (by decide))
    (by decide) (by decide) (by omega_using [hw]) (fun j hj => by rw [rd₅, wr₅, rd₄, wr₄]; exact in_wr (inSt _ (by omega_using [hj])))
    (fun j hj => by rw [wr₅, wr₄]; exact inSt _ (by omega_using [hj])) fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ => ?_
  obtain s1₆ : s₆.gpr .s1 = St := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), s1₅]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t0) (dst := .s1) (doff := 400) (bs := List.replicate 8 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₇ h₇ => ?_
  · simp only [List.length_replicate] at hi
    rw [s1₆, wr₆, wr₅, wr₄]; exact inSt _ (by omega_using [hi])
  obtain ⟨z₇, fz₇⟩ := zeros_stored (C := St + BitVec.ofNat 64 400) (by rw [s1₆]) h₇
  obtain s2₇ : s₇.gpr .s2 = S := by
    rw [h₇.gpr _ (by decide), g₆ _ (by decide) (by decide) (by decide) (by decide),
      g₅ _ (by decide) (by decide) (by decide) (by decide), s2₄]
  rw [restoreRegs, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₈ e => ?_
  subst e
  rw [s2₇]
  -- The saved registers, through the calls and the writes.
  have dSv (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨St, 384⟩,
      ⟨St + BitVec.ofNat 64 384, 8⟩, ⟨s₀.sp - 944, 944⟩, ⟨St + BitVec.ofNat 64 392, 8⟩,
      ⟨St + BitVec.ofNat 64 400, 8⟩]) :
      (⟨sv S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    obtain hb := init_bound p hp'
    obtain sub : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 640⟩ := fun a ha =>
      Region.sub_prefix (by decide) a (sv_sub S (d := p.2) (n := 8) (by omega_using [hb]) a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact hp.stk_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  obtain sv₁ : Spill.Saved (sv S) (initG s₀ S) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv S) _
  obtain f₄ : Frame [⟨St + BitVec.ofNat 64 384, 8⟩, ⟨s₀.sp - 944, 944⟩] s₃.mem s₄.mem := by
    have := h₄.frame; rwa [sp₃'] at this
  obtain sv₂ := sv₁.frame h₂.frame fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain sv₃ := sv₂.frame fz₃ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain sv₄ := sv₃.frame f₄ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
  obtain sv₅ := sv₄.frame f₅ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain sv₆ := sv₅.frame f₆ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain sv₇ := sv₆.frame fz₇ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  rw [show initSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 initSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := initSaved) (B := sv S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₇) fun s₉ r₉ => ?_
  · have := init_bound p hp'
    show InRegions (s₇.rd ++ s₇.wr) _ 8
    rw [h₇.rd, h₇.wr, rd₆, wr₆, rd₅, wr₅, rd₄, wr₄, hp.rd, hp.wr]
    exact ⟨⟨S, 640⟩, by simp, sv_contains S (by omega_using [this]) (by decide)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : initG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₉.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2
    · left; rcases hv with rfl | rfl <;> decide
    · right
      obtain ⟨-, h1, -, -, -, -, -, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₇.gpr _ h0, g₆ r h1 (preserved_ne r hr).2.2.1 (preserved_ne r hr).2.2.2.1
        (preserved_ne r hr).2.2.2.2.1, g₅ r h1 (preserved_ne r hr).2.2.1 (preserved_ne r hr).2.2.2.1
        (preserved_ne r hr).2.2.2.2.1, g₄ r hr, h₁.other r hr (fun e => hv (.inl e)) (fun e => hv (.inr e)),
        g₀ r h0]
  · rw [r₉.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₉.sp, RegUpd.sp_write, h₇.sp, sp₆, sp₅, h₄.sp, sp₃']
  · show Spec.Cmac.tdesRepr s₉.mem (s₀.gpr .a0)
      (Spec.TripleDes.bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) []
    rw [hp.a0, hp.a1, hp.a2, Proof.CmacTripleDes.Stream.repr_iff, r₉.mem, RegUpd.mem_write]
    obtain f₁ : Frame [⟨sv S, 24⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      exact Spill.saveMem_frame_base (l := initSaved) (n := 24) init_bound (by decide) s₀.mem (sv S) (initG s₀ S)
    obtain hkey : Spec.TripleDes.bytesAt s₁.mem Kp KL = Spec.TripleDes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := sv_sub S (d := 0) (n := 24) (by decide)
        rw [BitVec.add_zero] at this
        exact hp.k_s.sub_right fun a ha => Region.sub_prefix (by decide) a (this a ha)) (by have := hp.wK; omega_using [this])
    obtain hlen : (Spec.TripleDes.bytesAt s₀.mem Kp KL).length = KL := by simp [Spec.TripleDes.bytesAt]
    -- The schedule, from the key expansion on.
    have dS (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 384, 8⟩, ⟨s₀.sp - 944, 944⟩,
        ⟨St + BitVec.ofNat 64 392, 8⟩, ⟨St + BitVec.ofNat 64 400, 8⟩]) : (⟨St, 384⟩ : Region).Disjoint r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
      · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
    obtain sch₃ : Spec.TripleDes.scheduleAt s₃.mem St = Spec.TripleDes.scheduleAt s₂.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St fz₃ fun r hr => dS r (by
        simp only [List.mem_singleton] at hr; subst hr; simp)
    obtain sch₇ : Spec.TripleDes.scheduleAt s₇.mem St = Spec.TripleDes.scheduleAt s₃.mem St := by
      rw [Proof.TripleDes.scheduleAt_eq_of_frame St fz₇ fun r hr => dS r (by
          simp only [List.mem_singleton] at hr; subst hr; simp),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₆ fun r hr => dS r (by
          simp only [List.mem_singleton] at hr; subst hr; simp),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₅ fun r hr => dS r (by
          simp only [List.mem_singleton] at hr; subst hr; simp),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₄ fun r hr => dS r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)]
    obtain hsch : Spec.TripleDes.scheduleAt s₂.mem St =
        Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    -- The subkeys.
    have dj (d e : Nat) (hd : d + 8 ≤ e ∨ e + 8 ≤ d) (he : e + 8 ≤ 416) (hd' : d + 8 ≤ 416) :
        ∀ r ∈ [(⟨St + BitVec.ofNat 64 e, 8⟩ : Region)], (⟨St + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint St hd (by omega_using [hd']) (by omega_using [he])
    obtain k1 : Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 384) 8 =
        Spec.Cmac.dbl 8 (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s₀.mem Kp KL))
          (Spec.Cmac.zeros 8)) := by
      rw [Proof.Cmac.bytesAt_frame fz₇ (dj 384 400 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
        Proof.Cmac.bytesAt_frame f₆ (dj 384 392 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), b₅, h₄.out, z₃,
        sch₃, hsch]
    obtain k2 : Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 392) 8 =
        Spec.Cmac.dbl 8 (Spec.Cmac.dbl 8 (Spec.Cmac.tdesWith
          (Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s₀.mem Kp KL)) (Spec.Cmac.zeros 8))) := by
      rw [Proof.Cmac.bytesAt_frame fz₇ (dj 392 400 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), b₆, b₅,
        h₄.out, z₃, sch₃, hsch]
    refine ⟨⟨by rw [hlen]; exact hp.valid, by rw [sch₇, sch₃, hsch], ?_⟩, ?_, ?_⟩
    · rw [subkeys_eq, show St + 384 = St + BitVec.ofNat 64 384 from rfl,
        show (16 : Nat) = 8 + 8 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add, k1, k2]
    · rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl, z₇]; rfl
    · simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end

/-!
# Streaming TDEA-CMAC on RISC-V: `stream_init` in constant time

The code between the calls is constant time by the taint analysis
(`taintRegs`), from the registers that hold public values there, and the
calls by their own proofs (`key_rel`, `ecb_rel`), their arguments pinned by
what the code before them leaves (`IMid₁`, `IAfter`, `IZero`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacTripleDes.Stream.RISCV64

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- What the key expansion's call leaves, for `initZero`. -/
structure IAfter (s₀ : State) (St S : Addr) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem key_after {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa keyCall s (IAfter s₀ St S) :=
  WP.mono (key_call h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by decide), h.s1], by rw [h₂.saved _ (by decide), h.s2], by rw [h₂.wr, h.wr],
      by rw [h₂.sp, h.sp]⟩

/-- What `initZero` leaves, for ECB's call. -/
structure IZero (s₀ : State) (St S : Addr) (s : State) : Prop where
  args : EArgs s St 384
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  sp : s.sp = s₀.sp

theorem zero_after {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (h : IAfter s₀ St S s) : WP isa (.block initZero) s (IZero s₀ St S) := by
  have stW : (⟨St, 416⟩ : Region) ∈ s.wr := by rw [h.wr, hp.wr]; simp
  refine WP.mono (initZero_wp h.s1 stW) fun s' h' => ?_
  obtain ⟨a0, a1, a2, g, -, -, -, wr, sp⟩ := h'
  have sp' : s'.sp = s₀.sp := by rw [sp, h.sp]
  exact ⟨⟨a0, a1, a2, by decide, by decide, hp.wSt, by rw [sp']; exact hp.al, by rw [sp']; exact hp.sp,
    by rw [sp']; exact hp.stk_st, by rw [wr]; exact stW⟩, by rw [g _ (by decide), h.s1],
    by rw [g _ (by decide), h.s2], sp'⟩

theorem init_rel {s₀ s₀' : State} (h0 : initRISCV64.pre s₀) (h0' : initRISCV64.pre s₀')
    (hq : initRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a3) (s₀.gpr .a2).toNat := by
    rw [q3, q4, q5, q6]; exact IPre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a1 = Kp at hp hp'
  generalize s₀.gpr .a3 = S at hp hp'
  generalize (s₀.gpr .a2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block initSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block initZero) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block initTail) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := IMid₁ s₀ St Kp S KL) (F₂ := IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initSave_wp hp, initSave_wp hp'⟩
  have e := (key_rel (P := fun a b => IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := IAfter s₀ St S) (F₂ := IAfter s₀' St S) fun a b h => ⟨key_after h.1, key_after h.2⟩
  have z := (taintRegs (P := fun a b => IAfter s₀ St S a ∧ IAfter s₀' St S b) [.s1, .s2]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.s1, h.2.s1]
      · rw [h.1.s2, h.2.s2]) hB).wp
    (F₁ := IZero s₀ St S) (F₂ := IZero s₀' St S) fun a b h => ⟨zero_after hp h.1, zero_after hp' h.2⟩
  have c := (ecb_rel (P := fun a b => IZero s₀ St S a ∧ IZero s₀' St S b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.sp = s₀'.sp)
    fun a b h => ⟨WP.mono (ecb_call h.1.args) fun _ e => ⟨by rw [e.saved _ (by decide), h.1.s1],
        by rw [e.saved _ (by decide), h.1.s2], by rw [e.sp, h.1.sp]⟩,
      WP.mono (ecb_call h.2.args) fun _ e => ⟨by rw [e.saved _ (by decide), h.2.s1],
        by rw [e.saved _ (by decide), h.2.s2], by rw [e.sp, h.2.sp]⟩⟩
  have p := taintRegs
    (P := fun a b => (a.gpr .s1 = St ∧ a.gpr .s2 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .s1 = St ∧ b.gpr .s2 = S ∧ b.sp = s₀'.sp) [.s1, .s2]
    (fun a b h => by
      refine ⟨by rw [h.1.2.2, h.2.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((z.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.RISCV64
