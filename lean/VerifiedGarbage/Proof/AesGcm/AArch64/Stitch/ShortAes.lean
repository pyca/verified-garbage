module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCopy
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.GhBits
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.AArch64.Flush
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Aes.KeyExp
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Copy

/-!
# AES-GCM on AArch64, short records: one pass of the counter mode

Untrusted: everything here is checked by Lean. `byRounds shortAes`
(`Impl.AesGcm.AArch64.Stitch`), from `x9 = B` and the counter in `w10`
(`APre`), leaves at `B` the eight blocks there XORed with the keystream of
the counter blocks `k … k + 7` (`shortAesB_ok`): `aesPart_ok`, then
`storesB_ok`, for the number of rounds (`byRoundsG_ok`).
-/

@[expose] public section

local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (APre APost aesPart_ok sch cbk kp cbA c0)
open VG.Proof.Aes.AArch64 (keyStream)

/-- `APre` from a state that differs in `x13` and `x14` only. -/
theorem APre.of_x1314 {R o k : Nat} {s t : State} (h : APre R o k s)
    (hg : ∀ r, r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r) (hm : t.mem = s.mem) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : APre R o k t where
  rounds := h.rounds
  o_le := h.o_le
  keys := fun r hr => by
    rw [hrd, hwr, kp, hg _ (by decide) (by decide)]; exact h.keys r hr
  ctr := by rw [hrd, hwr, cbA, hg _ (by decide) (by decide)]; exact h.ctr
  data := fun j hj => by rw [hrd, hwr, hg _ (by decide) (by decide)]; exact h.data j hj
  x10 := by
    simp only [State.read, hg _ (by decide : Reg.x10 ≠ .x13) (by decide)]
    have := h.x10
    simp only [State.read, c0, cbk, cbA] at this ⊢
    rw [hm, hg _ (by decide : Reg.x20 ≠ .x13) (by decide)]
    exact this

/-- `byRounds shortAes` from `x9 = B`: the blocks at `B` XORed with the keystream. -/
theorem shortAesB_ok {R k : Nat} {B : Addr} (s : State) (hp : APre R 0 k s)
    (hx22 : s.gpr .x22 = BitVec.ofNat 64 R) (hx9 : s.gpr .x9 = B) (hw : Covers [⟨B, 128⟩] s.wr) :
    WP isa (Impl.Gcm.AArch64.Stitch.byRounds Impl.AesGcm.AArch64.Stitch.shortAes) s fun s' =>
      (∀ j < 8, ∀ t < 16, s'.mem (B + BitVec.ofNat 64 (16 * j + t)) =
        keyStream R (sch R s) (cbk s) (16 * (k + j) + t) ^^^ s.mem (B + BitVec.ofNat 64 (16 * j + t))) ∧
      Frame [⟨B, 128⟩] s.mem s'.mem ∧ (∀ r, r ∉ [Reg.x10, .x12, .x13, .x14] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.v Impl.Gcm.AArch64.Stitch.Y = s.v Impl.Gcm.AArch64.Stitch.Y := by
  refine byRoundsG_ok hp.rounds hx22 fun t gt mt vt spt rdt wrt => ?_
  have hpt := APre.of_x1314 hp gt mt rdt wrt
  unfold Impl.AesGcm.AArch64.Stitch.shortAes
  rw [WP.block_append_iff]
  refine WP.mono (aesPart_ok hpt (by decide)) fun u hu => ?_
  have x9u : u.gpr .x9 = B := by rw [hu.fr.gpr _ (by decide), gt _ (by decide) (by decide), hx9]
  refine WP.mono (storesB_ok u x9u (by rw [hu.fr.wr, wrt]; exact hw)) fun u' ⟨e, f, g, vv, sp, rd, wr⟩ => ?_
  have hsch : sch R t = sch R s := by simp only [sch, kp, mt, gt _ (by decide : Reg.x21 ≠ .x13) (by decide)]
  have hcbk : cbk t = cbk s := by simp only [cbk, cbA, mt, gt _ (by decide : Reg.x20 ≠ .x13) (by decide)]
  refine ⟨fun j hj tt htt => ?_, ?_, fun r hr => ?_, by rw [sp, hu.fr.sp, spt], by rw [rd, hu.fr.rd, rdt],
    by rw [wr, hu.fr.wr, wrt], by rw [vv, hu.fr.v _ (by decide), vt]⟩
  · rw [e j hj tt htt, hu.out j hj tt htt, hsch, hcbk, mt, gt _ (by decide) (by decide), hx9, Nat.zero_add,
      Offset.add_add]
  · rw [← mt, ← hu.fr.mem]; exact f
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g, hu.fr.gpr r (by simp [hr.1, hr.2.1]), gt r hr.2.2.1 hr.2.2.2]

/-! ## One pass of GHASH -/

open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok GhIn ghPart_ok gh8V blkV tblV ghV gh8V_congr kpack) in
open VG.Proof.Gcm.AArch64.Pmull (ext8 rev64b_read) in
/-- `shortGh`: GHASH from zero of the eight blocks of `B₂`, with the table of `H`, in `v16` as loaded. -/
theorem shortGh_ok {W : Addr} {H : Spec.Gcm.Block} (gh : Gh8Ok) (s : State) (h19 : s.gpr .x19 = W)
    (ht : TblOk s.mem W H) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortGh) s fun s' =>
      s'.v Impl.Gcm.AArch64.Stitch.Y =
        ext8 (Spec.Gcm.ghashFrom H 0 ((List.range 8).map fun j =>
          Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j))))
          (Spec.Gcm.ghashFrom H 0 ((List.range 8).map fun j =>
          Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j)))) ∧
      (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.shortGh
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_movz_x (imm := 0xc200) (hw := 3) (by decide) _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_dup_d2 _ .x12 _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_movi0 _ _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := Impl.AesGcm.AArch64.Stitch.b2O) (by decide), WP.block_nil ?_⟩
  have hx9 : ∀ j, ((((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).setV
      Impl.Gcm.AArch64.Stitch.C (ofVDwords ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12)
        ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12))).setV
      Impl.Gcm.AArch64.Stitch.Y 0).write .x .x9
      ((((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).setV
      Impl.Gcm.AArch64.Stitch.C (ofVDwords ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12)
        ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12))).setV
      Impl.Gcm.AArch64.Stitch.Y 0).read .x .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.b2O)).gpr .x9 +
        BitVec.ofNat 64 (16 * j) = W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j) := fun j => by
    simp only [gpr_write_self, State.read, gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      BitVec.setWidth_eq, Size.bits, h19, Offset.add_add]
  refine WP.mono (ghPart_ok _ ⟨fun j hj => ?_, fun k hk1 hk8 => ?_, fun p hp => ?_⟩ ?_) fun s' ⟨e, o⟩ => ?_
  · simp only [rd_write, wr_write, rd_setV, wr_setV] at *
    rw [hx9 j]
    exact Proof.AesGcm.AArch64.in_off hr (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega) (by decide)
  · simp only [rd_write, wr_write, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
    exact Proof.AesGcm.AArch64.in_off hr (by unfold Impl.Gcm.AArch64.Stitch.sOff Impl.Gcm.AArch64.Stitch.tbl; omega)
      (by decide)
  · simp only [rd_write, wr_write, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
    exact Proof.AesGcm.AArch64.in_off hr (by unfold Impl.Gcm.AArch64.Stitch.kOff Impl.Gcm.AArch64.Stitch.tbl; omega)
      (by decide)
  · simp only [v_write, v_setV_of_ne _ _ (show Impl.Gcm.AArch64.Stitch.C ≠ Impl.Gcm.AArch64.Stitch.Y by decide),
      v_setV_self, gpr_write_self]
    rfl
  have hm₁ : ∀ x : Addr, ((((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).setV
      Impl.Gcm.AArch64.Stitch.C (ofVDwords ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12)
        ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12))).setV
      Impl.Gcm.AArch64.Stitch.Y 0).write .x .x9 x).mem = s.mem := fun _ => by
    simp only [mem_write, mem_setV]
  refine ⟨?_, fun r h9 h12 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, gh8V_congr (y' := ext8 0 0)
      (b' := fun j => ext8 (Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j)))
        (Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j))))
      (S' := fun k => ext8 (VG.Proof.Gcm.AArch64.Pmull.pp H k) (VG.Proof.Gcm.AArch64.Pmull.pp H k))
      (KP' := fun p => kpack H (Impl.Gcm.AArch64.Stitch.pk p) (Impl.Gcm.AArch64.Stitch.pl p))
      (by simp only [v_write, v_setV_self]; rfl)
      (fun j _ => by rw [blkV, hx9 j, hm₁, rev64b_read])
      (fun k hk1 hk8 => by
        rw [tblV, hm₁]
        simp only [gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), gpr_setV,
          gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
        rw [VG.Proof.Gcm.AArch64.Stitch.read_eq_readW]
        exact ht.sw k hk1 hk8)
      (fun p hp => by
        rw [tblV, hm₁]
        simp only [gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), gpr_setV,
          gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
        rw [VG.Proof.Gcm.AArch64.Stitch.read_eq_readW]
        exact ht.key p hp), gh]
  · rw [o.gpr]
    simp only [gpr_write_of_ne _ _ _ h9, gpr_setV, gpr_write_of_ne _ _ _ h12]
  · rw [o.mem]; simp only [mem_write, mem_setV]
  · rw [o.sp]; simp only [sp_write, sp_setV]
  · rw [o.rd]; simp only [rd_write, rd_setV]
  · rw [o.wr]; simp only [wr_write, wr_setV]

/-! ## The lengths block -/

/-- `lensB`: the lengths block of `al` and `n` bytes, at block 7 of `B₂`. -/
theorem lensB_ok {W : Addr} {al n : Nat} (s : State) (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 2560⟩] s.wr)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 al) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hal' : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.lensB) s fun s' =>
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 1008) 16 = Proof.Gcm.lensBlock al n ∧
      Frame [⟨W + BitVec.ofNat 64 1008, 16⟩] s.mem s'.mem ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  have w₁ : InRegions s.wr (W + BitVec.ofNat 64 1008) 8 := Proof.AesGcm.AArch64.in_off hr (by decide) (by decide)
  have w₂ : InRegions s.wr (W + BitVec.ofNat 64 1016) 8 := Proof.AesGcm.AArch64.in_off hr (by decide) (by decide)
  obtain ⟨s', run, m', og, sp', rd', wr', v'⟩ : ∃ s', runBlock isa Impl.AesGcm.AArch64.Stitch.lensB s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 1008) (AArch64.rev64 (BitVec.ofNat 64 al <<< 3))).writeW
        (W + BitVec.ofNat 64 1008 + BitVec.ofNat 64 8) (AArch64.rev64 (BitVec.ofNat 64 n <<< 3)) ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
    refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.lensB, Impl.AesGcm.AArch64.Stitch.b2O, h19, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, Proof.AesGcm.AArch64.add_ofNat_assoc, gpr_write,
      ite_true, ite_false, reduceCtorEq, h24, h26]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, og, sp', rd', wr', v'⟩
  · rw [m', Proof.Cmac.bytesAt_store2, Proof.AesGcm.AArch64.le8_lens, Proof.AesGcm.AArch64.le8_lens,
      Proof.AesGcm.AArch64.toNat_ofNat_of_lt hal', Proof.AesGcm.AArch64.toNat_ofNat_of_lt hn]
    rfl
  · rw [m']; exact Proof.Cmac.frame_store2 _ _ _

/-! ## The tag -/

theorem byteRev64_xor (a b : BitVec 64) : byteRev64 (a ^^^ b) = byteRev64 a ^^^ byteRev64 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [byteRev64, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat (split; · simp [*])
  have : i - 8 - 8 - 8 - 8 - 8 - 8 - 8 < 8 := by omega
  simp [this]

open VG.Proof.Gcm.AArch64.Pmull (vdwords vdword_xor vdword_rev64b) in
theorem rev64b_xor (a b : BitVec 128) :
    VRevOp.eval .rev64b (a ^^^ b) = VRevOp.eval .rev64b a ^^^ VRevOp.eval .rev64b b := by
  rw [vdwords (VRevOp.eval .rev64b (a ^^^ b)), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdwords (VRevOp.eval .rev64b a ^^^ VRevOp.eval .rev64b b), vdword_xor, vdword_xor, vdword_xor, vdword_xor,
    vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdword_rev64b _ (by decide)]
  rw [show AArch64.rev64 = byteRev64 from rfl, byteRev64_xor, byteRev64_xor]

open VG.Proof.Gcm.AArch64.Pmull (ext8 ext8_eq vdword_xor) in
theorem ext8_xor (a b : BitVec 128) : ext8 (a ^^^ b) (a ^^^ b) = ext8 a a ^^^ ext8 b b := by
  rw [ext8_eq, ext8_eq, ext8_eq, vdword_xor, vdword_xor, BitVec.xor_append]

open VG.Proof.Gcm.AArch64.Pmull (ext8 ext8_ext8 rev64b_rev64b rev64b_read blockAt_store exec_rev64b exec_ldrq
  exec_eor exec_strq) in
/-- `shortTagAt o`: GHASH (in `v16`, as loaded) XORed with block `p − 1` of `B₁`, at `W + o`. -/
theorem shortTagAt_ok {W : Addr} {c : Nat} {g : Spec.Gcm.Block} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hc6 : c ≤ 6) (s : State) (h19 : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c))
    (hY : s.v Impl.Gcm.AArch64.Stitch.Y = ext8 g g) (hr : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block (Impl.AesGcm.AArch64.Stitch.shortTagAt o)) s fun s' =>
      Spec.Gcm.blockAt s'.mem (W + BitVec.ofNat 64 o) =
        g ^^^ Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (864 - 16 * c)) ∧
      Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.shortTagAt
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_rev64b _ _ _, WP.block_nil ?_⟩
  obtain ⟨t₁, run₁, x9₁, g₁, m₁, v₁, sp₁, rd₁, wr₁⟩ := atP_ok (c := c) .x9 Impl.AesGcm.AArch64.Stitch.b1O 0
    (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega)
    (s.setV Impl.Gcm.AArch64.Stitch.Y (VRevOp.eval .rev64b (s.v Impl.Gcm.AArch64.Stitch.Y)))
    (by rw [gpr_setV, h19]) (by rw [gpr_setV, h25]) (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  have hin : InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [rd₁, wr₁, x9₁, BitVec.add_zero, rd_setV, wr_setV]
    exact Proof.AesGcm.AArch64.in_left (Proof.AesGcm.AArch64.in_off hr
      (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega) (by decide))
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by decide) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _, ?_⟩
  have hx19 : t₁.gpr .x19 = W := by rw [g₁ _ (by decide), gpr_setV, h19]
  have hout : InRegions ((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).setV
      Impl.Gcm.AArch64.Stitch.Y ((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v
        Impl.Gcm.AArch64.Stitch.Y ^^^ (t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v .v0)).wr
      (((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).setV
      Impl.Gcm.AArch64.Stitch.Y ((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v
        Impl.Gcm.AArch64.Stitch.Y ^^^ (t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v .v0)).gpr .x19 +
        BitVec.ofNat 64 o) 16 := by
    rw [wr_setV, wr_setV, gpr_setV, gpr_setV, hx19, wr₁, wr_setV]
    exact Proof.AesGcm.AArch64.in_off hr (by rcases ho with rfl | rfl <;> decide) (by decide)
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by rcases ho with rfl | rfl <;> decide) (by rcases ho with rfl | rfl <;> decide) hout,
    WP.block_nil ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [gpr_setV, gpr_setV, hx19, v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_self, v₁, v_setV_self,
      mem_setV, mem_setV, m₁, mem_setV, x9₁, BitVec.add_zero, hY,
      show Impl.AesGcm.AArch64.Stitch.b1O + 96 + 16 * 0 - 16 * c = 864 - 16 * c by
        unfold Impl.AesGcm.AArch64.Stitch.b1O; omega,
      ← rev64b_rev64b (s.mem.read (W + BitVec.ofNat 64 (864 - 16 * c)) 16), ← rev64b_xor, blockAt_store,
      ext8_xor, ext8_ext8, rev64b_read, ext8_ext8]
  · dsimp only
    rw [gpr_setV, gpr_setV, hx19, mem_setV, mem_setV, m₁, mem_setV]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · dsimp only
    rw [gpr_setV, gpr_setV, g₁ r hr, gpr_setV]
  · dsimp only; rw [sp_setV, sp_setV, sp₁, sp_setV]
  · dsimp only; rw [rd_setV, rd_setV, rd₁, rd_setV]
  · dsimp only; rw [wr_setV, wr_setV, wr₁, wr_setV]

/-! ## The counter -/

/-- `shortCtr`: `w10 = c₀ + c − 7` (the counter block at `St + 48`'s counter), and `x9 = B₁`. -/
theorem shortCtr_ok {W St : Addr} {c : Nat} (hc6 : c ≤ 6) (s : State) (h19 : s.gpr .x19 = W)
    (h20 : s.gpr .x20 = St) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c))
    (hq : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 60) 4) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortCtr) s fun s' =>
      s'.read .w .x10 = (Spec.Gcm.blockAt s.mem (St + BitVec.ofNat 64 48)).extractLsb' 0 32 +
        BitVec.ofNat 32 (2 ^ 32 + c - 7) ∧
      s'.gpr .x9 = W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.b1O ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.v = s.v ∧ s'.sp = s.sp ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hq' : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 60) 4 := by rw [h20]; exact hq
  refine WP.of_runBlock ⟨_, by
    simp only [Impl.AesGcm.AArch64.Stitch.shortCtr, runBlock_cons]
    rw [exec_ldr_w (by decide) hq', runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r h9 h10 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.read, gpr_write, ite_true, reduceCtorEq, ite_false, Size.bits, h25, mem_write,
      Proof.Aes.AArch64.Aese.sw32, BitVec.setWidth_eq]
    rw [h20, show St + BitVec.ofNat 64 60 = St + BitVec.ofNat 64 48 + BitVec.ofNat 64 12 by rw [Offset.add_add],
      Proof.Aes.AArch64.icb_lo, Proof.AesGcm.AArch64.Gather.ofNat_lsr4 (show 16 * c < 2 ^ 64 by omega),
      show 16 * c / 16 = c by omega]
    generalize (Spec.Gcm.blockAt s.mem (St + BitVec.ofNat 64 48)).extractLsb' 0 32 = x
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · simp [gpr_write, State.read, h19]
  · simp [gpr_write, h9, h10]
  all_goals simp [mem_write, v_write, sp_write, rd_write, wr_write]

end VG.Proof.AesGcm.AArch64.Stitch
