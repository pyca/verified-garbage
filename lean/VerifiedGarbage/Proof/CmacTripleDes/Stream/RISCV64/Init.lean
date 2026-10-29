module

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
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls

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
  have hKL : s₀.gpr .a2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.a2
  rw [initSave, saveRegs, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show initSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 initSaved from rfl]
  have t₀ : (s₀.write .t0 (sv S)).gpr .t0 = sv S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := initSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := init_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 640⟩, by simp, sv_contains S (by omega) (by decide)⟩
  generalize ht : ({ (s₀.write .t0 (sv S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv S)).mem ((s₀.write .t0 (sv S)).gpr .t0)
      (s₀.write .t0 (sv S)).gpr initSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = Spill.saveMem s₀.mem (sv S) (initG s₀ S) initSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  have s1 : s₅.gpr .s1 = St := by
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
    rw [h1]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨z, fz⟩ := zeros_stored (by rw [h1]) h₁
  have s1₁ : s₁.gpr .s1 = St := by rw [h₁.gpr _ (by decide), h1]
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
  have hp := IPre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a1 = Kp at hp
  generalize s₀.gpr .a3 = S at hp
  generalize (s₀.gpr .a2).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (initSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (key_call h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  have s1₂ : s₂.gpr .s1 = St := by rw [g₂ _ (by decide), h₁.s1]
  refine WP.seq (WP.mono (initZero_wp s1₂ (by rw [h₂.wr, h₁.wr]; exact stW)) fun s₃ h₃ => ?_)
  obtain ⟨a0₃, a1₃, a2₃, g₃, z₃, fz₃, rd₃, wr₃, sp₃⟩ := h₃
  have sp₃' : s₃.sp = s₀.sp := by rw [sp₃, h₂.sp, h₁.sp]
  refine WP.seq (WP.mono (ecb_call (S := St) (off := 384)
    ⟨a0₃, a1₃, a2₃, by decide, by decide, hw, by rw [sp₃']; exact hp.al, by rw [sp₃']; exact hp.sp,
      by rw [sp₃']; exact hp.stk_st, by rw [wr₃, h₂.wr, h₁.wr]; exact stW⟩) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.saved r hr, g₃ r hr, g₂ r hr]
  have s1₄ : s₄.gpr .s1 = St := by rw [g₄ _ (by decide), h₁.s1]
  have s2₄ : s₄.gpr .s2 = S := by rw [g₄ _ (by decide), h₁.s2]
  have wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, wr₃, h₂.wr, h₁.wr]
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, rd₃, h₂.rd, h₁.rd]
  have inSt : ∀ d, d < 416 → InRegions s₀.wr (St + BitVec.ofNat 64 d) 1 := fun d hd =>
    ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩
  rw [initTail, List.append_assoc, List.append_assoc]
  refine dbl_wp (K := St) (src := 384) (dst := 384) (by decide) (by decide) dbl_spec8 s1₄ (.inl rfl)
    (by decide) (by decide) (by omega) (fun j hj => by rw [rd₄, wr₄]; exact in_wr (inSt _ (by omega)))
    (fun j hj => by rw [wr₄]; exact inSt _ (by omega)) fun s₅ g₅ rd₅ wr₅ sp₅ f₅ b₅ => ?_
  have s1₅ : s₅.gpr .s1 = St := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), s1₄]
  refine dbl_wp (K := St) (src := 384) (dst := 392) (by decide) (by decide) dbl_spec8 s1₅ (.inr (by decide))
    (by decide) (by decide) (by omega) (fun j hj => by rw [rd₅, wr₅, rd₄, wr₄]; exact in_wr (inSt _ (by omega)))
    (fun j hj => by rw [wr₅, wr₄]; exact inSt _ (by omega)) fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ => ?_
  have s1₆ : s₆.gpr .s1 = St := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), s1₅]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t0) (dst := .s1) (doff := 400) (bs := List.replicate 8 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₇ h₇ => ?_
  · simp only [List.length_replicate] at hi
    rw [s1₆, wr₆, wr₅, wr₄]; exact inSt _ (by omega)
  obtain ⟨z₇, fz₇⟩ := zeros_stored (C := St + BitVec.ofNat 64 400) (by rw [s1₆]) h₇
  have s2₇ : s₇.gpr .s2 = S := by
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
    have hb := init_bound p hp'
    have sub : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 640⟩ := fun a ha =>
      Region.sub_prefix (by decide) a (sv_sub S (d := p.2) (n := 8) (by omega) a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact hp.stk_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved (sv S) (initG s₀ S) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv S) _
  have f₄ : Frame [⟨St + BitVec.ofNat 64 384, 8⟩, ⟨s₀.sp - 944, 944⟩] s₃.mem s₄.mem := by
    have := h₄.frame; rwa [sp₃'] at this
  have sv₂ := sv₁.frame h₂.frame fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have sv₃ := sv₂.frame fz₃ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have sv₄ := sv₃.frame f₄ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
  have sv₅ := sv₄.frame f₅ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have sv₆ := sv₅.frame f₆ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have sv₇ := sv₆.frame fz₇ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  rw [show initSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 initSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := initSaved) (B := sv S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₇) fun s₉ r₉ => ?_
  · have := init_bound p hp'
    show InRegions (s₇.rd ++ s₇.wr) _ 8
    rw [h₇.rd, h₇.wr, rd₆, wr₆, rd₅, wr₅, rd₄, wr₄, hp.rd, hp.wr]
    exact ⟨⟨S, 640⟩, by simp, sv_contains S (by omega) (by decide)⟩
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
    have f₁ : Frame [⟨sv S, 24⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      exact Spill.saveMem_frame_base (l := initSaved) (n := 24) init_bound (by decide) s₀.mem (sv S) (initG s₀ S)
    have hkey : Spec.TripleDes.bytesAt s₁.mem Kp KL = Spec.TripleDes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := sv_sub S (d := 0) (n := 24) (by decide)
        rw [BitVec.add_zero] at this
        exact hp.k_s.sub_right fun a ha => Region.sub_prefix (by decide) a (this a ha)) (by have := hp.wK; omega)
    have hlen : (Spec.TripleDes.bytesAt s₀.mem Kp KL).length = KL := by simp [Spec.TripleDes.bytesAt]
    -- The schedule, from the key expansion on.
    have dS (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 384, 8⟩, ⟨s₀.sp - 944, 944⟩,
        ⟨St + BitVec.ofNat 64 392, 8⟩, ⟨St + BitVec.ofNat 64 400, 8⟩]) : (⟨St, 384⟩ : Region).Disjoint r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.base_disjoint St (by decide) (by omega)
      · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
      · exact Offset.base_disjoint St (by decide) (by omega)
      · exact Offset.base_disjoint St (by decide) (by omega)
    have sch₃ : Spec.TripleDes.scheduleAt s₃.mem St = Spec.TripleDes.scheduleAt s₂.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St fz₃ fun r hr => dS r (by
        simp only [List.mem_singleton] at hr; subst hr; simp)
    have sch₇ : Spec.TripleDes.scheduleAt s₇.mem St = Spec.TripleDes.scheduleAt s₃.mem St := by
      rw [Proof.TripleDes.scheduleAt_eq_of_frame St fz₇ fun r hr => dS r (by
          simp only [List.mem_singleton] at hr; subst hr; simp),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₆ fun r hr => dS r (by
          simp only [List.mem_singleton] at hr; subst hr; simp),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₅ fun r hr => dS r (by
          simp only [List.mem_singleton] at hr; subst hr; simp),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₄ fun r hr => dS r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)]
    have hsch : Spec.TripleDes.scheduleAt s₂.mem St =
        Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    -- The subkeys.
    have dj (d e : Nat) (hd : d + 8 ≤ e ∨ e + 8 ≤ d) (he : e + 8 ≤ 416) (hd' : d + 8 ≤ 416) :
        ∀ r ∈ [(⟨St + BitVec.ofNat 64 e, 8⟩ : Region)], (⟨St + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint St hd (by omega) (by omega)
    have k1 : Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 384) 8 =
        Spec.Cmac.dbl 8 (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s₀.mem Kp KL))
          (Spec.Cmac.zeros 8)) := by
      rw [Proof.Cmac.bytesAt_frame fz₇ (dj 384 400 (by omega) (by omega) (by omega)) (by decide),
        Proof.Cmac.bytesAt_frame f₆ (dj 384 392 (by omega) (by omega) (by omega)) (by decide), b₅, h₄.out, z₃,
        sch₃, hsch]
    have k2 : Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 392) 8 =
        Spec.Cmac.dbl 8 (Spec.Cmac.dbl 8 (Spec.Cmac.tdesWith
          (Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s₀.mem Kp KL)) (Spec.Cmac.zeros 8))) := by
      rw [Proof.Cmac.bytesAt_frame fz₇ (dj 392 400 (by omega) (by omega) (by omega)) (by decide), b₆, b₅,
        h₄.out, z₃, sch₃, hsch]
    refine ⟨⟨by rw [hlen]; exact hp.valid, by rw [sch₇, sch₃, hsch], ?_⟩, ?_, ?_⟩
    · rw [subkeys_eq, show St + 384 = St + BitVec.ofNat 64 384 from rfl,
        show (16 : Nat) = 8 + 8 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add, k1, k2]
    · rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl, z₇]; rfl
    · simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]

end VG.Proof.CmacTripleDes.Stream.RISCV64
