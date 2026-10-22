module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Loops
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Tbl
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: POLYVAL of the data

Untrusted: everything here is checked by Lean. `polyData_ok`: `polyData`
(`Impl.AesGcmSiv.AArch64.Stitch`) absorbs the data padded with zeros, as
`absorb` does (`Proof.AesGcmSiv.AArch64.absorb_ok`): its batches by
`ghLoop`, from the table of keys `tblBuild` writes (`polyBatch_ok`), the
rest by `absorb`; and `polyval_ok` is `Proof.AesGcmSiv.AArch64.polyval_ok`
with it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs Absorbed AbsPost absR absorbR absorbR_buf absR_sub
  elemsAt absorb_ok lens_ok tagIn_ok tagInMem tagInMem_frame tagInMem_bytes polyR PolyPost absorbR_H)
open VG.Proof.AesGcm.AArch64 (GcmImpl Others covers_left lsr_ofNat eval_zero add_ofNat_assoc length_bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly PrepPow rev64b_read blockAt_store ext8_ext8)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (Y C)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## Words -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

/-- 16 bytes as two doublewords. -/
theorem readW128_q (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mem.readW, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  rw [getLsbD_read _ 16 a i (by omega)]
  by_cases h : i < 64
  · simp only [h, decide_true, Bool.cond_true, BitVec.getLsbD_setWidth]
    rw [getLsbD_read _ 8 a i (by omega)]
    simp [hi, h]
  · simp only [h, decide_false, Bool.cond_false, BitVec.getLsbD_setWidth]
    rw [getLsbD_read _ 8 _ (i - 64) (by omega), Offset.add_add, show 8 + (i - 64) / 8 = i / 8 by omega,
      show (i - 64) % 8 = i % 8 by omega]
    simp [hi, h, show i - 64 < 64 by omega]

/-- 16 bytes as a number. -/
theorem ofBytes_readW (m : Mem) (a : Addr) : Spec.GcmSiv.ofBytes (bytesAt m a 16) = m.readW a 128 := by
  rw [GcmSiv.ofBytes_bytesAt, readW128_q]

/-! ## The setup and the end of `ghLoop` -/

/-- `batches` and `ghSetup`: the data's pointer and batches, the reduction
constant and `Y` as loaded. -/
theorem ghPre_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa (.block (batches ++ ghSetup)) s fun s' =>
      s'.gpr .x9 = p.D + BitVec.ofNat 64 (128 * 0) ∧ s'.gpr .x11 = BitVec.ofNat 64 (p.n / 128 - 0) ∧
      s'.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly ∧
      s'.v Y = ext8 (blockAt s.mem (p.W + BitVec.ofNat 64 80)) (blockAt s.mem (p.W + BitVec.ofNat 64 80)) ∧
      Others [.x9, .x11, .x12] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 80) 16 := by
    rw [E.x19]; exact E.perm.wR (by decide)
  simp only [batches, ghSetup, List.cons_append, List.nil_append]
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 7) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_movz_x (imm := 0xc200) (hw := 3) (by decide) _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_dup_d2 C .x12 _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq (t := Y) (off := 80) (by decide) (by decide)
    (by simpa only [gpr_setV, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x11 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), rd_write, wr_write] using hy), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y _, WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_setV, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq, E.x25,
      Nat.mul_zero, BitVec.add_zero]
  · simp only [gpr_setV, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq, E.x26,
      Nat.sub_zero]
    rw [lsr_ofNat _ _ L.n_lt]
  · simp only [v_write, v_setV_of_ne _ _ (show C ≠ Y by decide), v_setV_self, gpr_write_self]
    rfl
  · simp only [v_write, v_setV_self, mem_setV, mem_write, gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x11 by decide), gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      E.x19]
    rw [rev64b_read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setV, gpr_write_of_ne _ _ _ hr.1, gpr_write_of_ne _ _ _ hr.2.1, gpr_write_of_ne _ _ _ hr.2.2]

/-- `ghFinish`: `Y` stored back to `W + 80`. -/
theorem ghFinish_ok {p : Prm} {s : State} (hx19 : s.gpr .x19 = p.W)
    (hw : InRegions s.wr (p.W + BitVec.ofNat 64 80) 16) :
    WP isa (.block ghFinish) s fun s' =>
      blockAt s'.mem (p.W + BitVec.ofNat 64 80) = ext8 (s.v Y) (s.v Y) ∧
      Frame [⟨p.W + BitVec.ofNat 64 80, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [ghFinish, WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_rev64b Y Y _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq (t := Y) (off := 80) (by decide) (by decide)
    (by simpa only [wr_setV, gpr_setV, hx19] using hw), WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · show blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x19 + BitVec.ofNat 64 80) 16 ((s.setV Y _).v Y)) _ = _
    rw [gpr_setV, v_setV_self, mem_setV, hx19, blockAt_store]
  · show Frame _ s.mem ((s.setV Y _).mem.write ((s.setV Y _).gpr .x19 + BitVec.ofNat 64 80) 16 _)
    rw [gpr_setV, mem_setV, hx19]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The batches -/

theorem elemsAt_eq {m m' : Mem} {D : Addr} {k : Nat}
    (h : ∀ i < k, m'.readW (D + BitVec.ofNat 64 (16 * i)) 128 = m.readW (D + BitVec.ofNat 64 (16 * i)) 128) :
    (List.range k).map (fun i => m'.readW (D + BitVec.ofNat 64 (16 * i)) 128) = elemsAt m D k := by
  refine List.map_congr_left fun i hi => ?_
  rw [h i (List.mem_range.mp hi), ofBytes_readW]

/-- The batches of the data hashed by `ghLoop`, from the table of keys. -/
theorem polyBatch_ok (hP : PrepPow) (gh : Gh8Ok) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq ghLoop (.block ghFinish))) t
      (Absorbed p (absR p.W) (elemsAt t.mem p.D (8 * (p.n / 128))) t) := by
  have hn := L.n_lt
  have hww := L.ww
  rw [List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (tblBuild_ok hP (by rw [E.x19]; exact E.perm.wR (by decide)) (by rw [E.x19]; exact E.perm.wW (by decide)))
    fun s₁ ⟨tok₁, f₁, g₁, sp₁, rd₁, wr₁⟩ => ?_
  have E₁ : Env p s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)) sp₁ rd₁ wr₁
  refine WP.mono (ghPre_ok L E₁) fun s₂ ⟨x9₂, x11₂, c₂, y₂, o₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [E.x19] at tok₁ f₁
  -- The context of the loop.
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, blockAt t.mem (p.W + BitVec.ofNat 64 64),
    s₂.mem, t.rd, t.wr⟩
  have hd₁ : Frame [tblR p.W] t.mem s₂.mem := by rw [m₂]; exact f₁
  have dT : (⟨p.D, p.n⟩ : Region).Disjoint (tblR p.W) := L.d_w' (by decide)
  have hp : KPre σ := {
    rounds := by rcases L.rounds with h | h <;> simp [σ, h]
    nb1 := hnb
    n16 := by show 128 * (p.n / 128) < 2 ^ 64; omega
    k_in := by
      show InRegions (t.rd ++ t.wr) (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))
      exact E.perm.wR (by rcases L.rounds with h | h <;> rw [h] <;> decide)
    c_in := E.perm.wR (by decide)
    d_in := by
      show InRegions t.wr p.D (128 * (p.n / 128))
      exact E.perm.d _ _ ⟨⟨p.D, p.n⟩, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩
    t_in := E.perm.wR (by decide)
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega))
    d_t := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega))
    wrap_t := by show p.W.toNat + 480 + 192 ≤ 2 ^ 64; omega
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by decide)]; rcases L.rounds with h | h <;> rw [h] <;> omega
    tbl := by show TblOk s₂.mem p.W _; rw [m₂]; exact tok₁ }
  have hI : GInv σ (blockAt t.mem (p.W + BitVec.ofNat 64 80)) s₂ 0 s₂ := {
    le := Nat.zero_le _
    x9 := x9₂
    x11 := x11₂
    gpr := fun _ _ _ => rfl
    y := by
      rw [y₂, yh, Nat.mul_zero, List.range_zero, List.map_nil]
      have e : blockAt s₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
        Proof.AesGcm.AArch64.blockAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact L.w_w (.inl (by decide)) (by decide) (by decide))
      rw [e]; rfl
    cr := c₂
    mem := rfl
    sp := rfl
    rd := rfl
    wr := rfl }
  have x19₂ : s₂.gpr .x19 = p.W := by rw [o₂ _ (by decide), E₁.x19]
  refine WP.seq (WP.mono (ghLoop_ok hp gh x19₂ (by rw [rd₂, wr₂, rd₁, wr₁]) hI) fun s₃ G => ?_)
  refine WP.mono (ghFinish_ok (p := p) (s := s₃) (by rw [G.gpr _ (by decide) (by decide), x19₂])
    (by rw [G.wr, wr₂, wr₁]; exact E.perm.wW (by decide))) fun s₄ ⟨b₄, f₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  refine ⟨E₁.keep (fun r hr => ?_) (by rw [sp₄, G.sp, sp₂]) (by rw [rd₄, G.rd, rd₂])
    (by rw [wr₄, G.wr, wr₂]), by rw [rd₄, G.rd, rd₂, rd₁], by rw [wr₄, G.wr, wr₂, wr₁], ?_, ?_⟩
  · simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g₄, G.gpr r (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
      (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide),
      o₂ r (by rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)]
  · have f₁' : Frame (absR p.W) t.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 480, 1280⟩, by simp [absR], Region.sub_prefix (by decide)⟩
    have f₄' : Frame (absR p.W) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp [absR], fun _ h => h⟩
    have e₃ : s₃.mem = s₁.mem := by rw [G.mem, ← m₂]
    exact f₁'.trans (e₃ ▸ f₄')
  · rw [b₄, G.y, ext8_ext8, yh]
    have e : blockAt s₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
      Proof.AesGcm.AArch64.blockAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide))
    refine congrArg _ (elemsAt_eq fun i hi => ?_)
    have hσ : σ.nb = p.n / 128 := rfl
    show s₂.mem.readW _ 128 = _
    rw [m₂]
    exact f₁.readW (r := ⟨p.D, p.n⟩) (Offset.contains_base p.D (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) (by decide)

end VG.Proof.AesGcmSiv.AArch64.Stitch
