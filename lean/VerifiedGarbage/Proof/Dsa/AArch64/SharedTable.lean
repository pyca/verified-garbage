module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigit
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The buckets' start: every entry the number 1 in Montgomery form -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- After `j` entries `:= Y` from `s`. -/
structure TabInv (s : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (N Xc j : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv N Xc
  tab : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))
  cnt : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (16 - j)
  done : ∀ e < j, wv t.mem P (slot wx (8 + e)) wx = wv s.mem P (slot wx aY) wx
  arr : ∀ a < 8, wv t.mem P (slot wx a) wx = wv s.mem P (slot wx a) wx
  hdr : ∀ i < 32, i ≠ Crt.sTab → i ≠ Crt.sEnt → i ≠ Crt.sBit → word t.mem P (8 * i) = word s.mem P (8 * i)
  frm : Frm P (workRanges wx) s.mem t.mem
  keep : Keep mmRegs s t

theorem tableInit_eq : tableInit = [
    .block (([ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
      sth .x3 Crt.sTab, sth .x3 Crt.sEnt] : List Instr) ++ ([movi .x3 16, sth .x3 Crt.sBit] : List Instr)),
    .loop (seqs (Crt.toEnt aY ++ ([Crt.nextEnt,
      .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]] : List (Prog isa))))
      (.nonzero .x .x3)] := rfl

theorem tabStep_ok {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc j : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hj : j < 16) (hI : TabInv s P wx minv N Xc j t) :
    WP isa (seqs (Crt.toEnt aY ++ ([Crt.nextEnt,
      .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]] : List (Prog isa)))) t fun t' =>
      TabInv s P wx minv N Xc (j + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 16) := by
  have hn := hI.ctx.scrT.nowrap
  have hE := ent_le wx hj
  have hE0 := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
  refine wp_seqs_append (by simp [Crt.toEnt]) (by simp) (WP.mono (toEnt_ok hI.ctx hw hw' (a := aY) (by decide)
    hj hI.ent) fun u ⟨hv, ou, ku⟩ => ?_)
  have hcu := hI.ctx.of_frm (Frm.of_outside (ou.mono (o' := slot wx 8) (n' := tabBytes wx) hE0
    (by omega_arith)) (by simp [crtExpRanges])) ku.wr (ku.gpr .x0 (by decide))
  simp only [seqs]
  refine WP.seq (WP.mono (nextEnt_ok hcu hw' (e := slot wx (8 + j)) ((ent_hdr ou (by decide)).trans hI.ent))
    fun v ⟨hmv, kv⟩ => ?_)
  have ov := writeW_outside u.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + j) + 8 * (wx + 2))) (by decide)
  rw [← hmv] at ov
  have fv : Frm P (crtWinRanges wx) u.mem v.mem := Frm.of_outside ov (by simp [crtWinRanges])
  have hcv := hcu.of_win fv kv.wr (kv.gpr .x0 (by decide))
  have hhv : ∀ i < 32, i ≠ Crt.sEnt → word v.mem P (8 * i) = word t.mem P (8 * i) := fun i hi h => by
    rw [hmv, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h), ent_hdr ou hi]
  refine WP.mono (crtBitEnd_ok hcv (b := 16 - j) ((hhv _ (by decide) (by decide)).trans hI.cnt) (by omega_arith))
    fun z ⟨⟨hmz, h3⟩, kz⟩ => ?_
  have oz := writeW_outside v.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (16 - j - 1)) (by decide)
  rw [← hmz] at oz
  have fz : Frm P (crtWinRanges wx) v.mem z.mem := Frm.of_outside oz (by simp [crtWinRanges])
  have fvz : Frm P (crtWinRanges wx) u.mem z.mem := fv.trans fz
  refine ⟨⟨hcv.of_win fz kz.wr (kz.gpr .x0 (by decide)), ?_, ?_, ?_, fun e he => ?_, fun a ha => ?_,
    fun i hi h1 h2 h3 => ?_, (hI.frm.trans (ent_work ou hj)).trans (win_work fvz),
    (((hI.keep.trans ku).trans kv).trans kz).mono (by decide)⟩, ?_⟩
  · rw [hmz, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hhv _ (by decide) (by decide)]
    exact hI.tab
  · rw [hmz, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmv, word_writeW_self, ← Nat.add_assoc,
      slot_succ]
  · rw [hmz, word_writeW_self]
    congr 1
  · rw [win_ent fvz hn (by omega_arith)]
    by_cases hej : e = j
    · subst hej
      rw [hv, hI.arr _ (by decide)]
    · rw [ent_ent ou hn (by omega_arith) hej]
      exact hI.done e (by omega_arith)
  · rw [fn_arr (m := u.mem) (by
        rw [hmz, hmv]
        exact (fn_outside _ P _ (by decide) (by decide)).trans (fn_outside _ P _ (by decide) (by decide)))
      hn ha, ent_arr ou hn ha, hI.arr a ha]
  · rw [hmz, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h3), hhv i hi h2, hI.hdr i hi h1 h2 h3]
  · rw [h3, cnt_ne (by omega_arith)]
    omega_arith

/-- The table's sixteen entries `:= Y`: the buckets before any digit, for
`Y` the number 1 and `[aXc]` the base, in Montgomery form. -/
theorem tableInit_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g ex eq : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hy : wv s.mem P (slot wx aY) wx < N) (hyv : wv s.mem P (slot wx aY) wx % N = 2 ^ (64 * wx) % N)
    (hx : Xc < N) (hxv : Xc % N = g * 2 ^ (64 * wx) % N) :
    WP isa (seqs tableInit) s fun t => DigitInv P wx minv N g ex eq 0 t ∧
      (∀ a < 8, wv t.mem P (slot wx a) wx = wv s.mem P (slot wx a) wx) ∧
      (∀ i < 32, i ≠ Crt.sTab → i ≠ Crt.sEnt → i ≠ Crt.sBit → word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  rw [tableInit_eq]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tabInit_ok hc hw') fun u ⟨hmu, ku⟩ => ?_
  have ou : Outside P 136 120 s.mem u.mem := by
    rw [hmu]
    exact (fn_outside _ P _ (by decide) (by decide)).trans (fn_outside _ P _ (by decide) (by decide))
  have hcu := ctx_of_fn hc ou ku.wr (ku.gpr .x0 (by decide))
  refine WP.mono (WP.keep [.x3] (Q := fun v => v.mem = u.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 16))
    (by
      brun [hcu.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hcu.st (i := Crt.sBit) (by decide)]
      rfl) rfl rfl rfl) fun v ⟨hmv, kv⟩ => ?_
  have ov : Outside P 136 120 u.mem v.mem := by rw [hmv]; exact fn_outside _ P _ (by decide) (by decide)
  have osv := ou.trans ov
  have hcv := ctx_of_fn hcu ov kv.wr (kv.gpr .x0 (by decide))
  have I0 : TabInv v P wx minv N Xc 0 v := ⟨hcv, by
      rw [hmv, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmu,
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [hmv, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmu, word_writeW_self],
    by rw [hmv, word_writeW_self], fun _ h => by omega, fun _ _ => rfl, fun _ _ _ _ _ => rfl, Frm.refl _ _ _,
    Keep.refl _ _⟩
  refine WP.mono (count_loop (cr := .x3) (n := 16) (by decide) (TabInv v P wx minv N Xc)
    (fun j hj t hI => tabStep_ok hw hw' hj hI) I0) fun t hI => ?_
  have hY : wv v.mem P (slot wx aY) wx = wv s.mem P (slot wx aY) wx := fn_arr osv hn (by decide)
  have ax : wv t.mem P (slot wx Crt.aXc) wx = Xc := (hI.arr _ (by decide)).trans hcv.x
  refine ⟨⟨by rw [ax]; exact hI.ctx, hI.tab, fun j hj => ?_, fun d hd => ?_, fun d hd _ => ?_, by rw [ax]; exact hx,
    ?_⟩, fun a ha => (hI.arr a ha).trans (fn_arr osv hn ha), fun i hi h1 h2 h3 => ?_,
    (fn_work osv).trans hI.frm, ((ku.trans kv).trans hI.keep).mono (by decide)⟩
  · rw [hI.done j hj, hY]; exact hy
  · rw [hI.done d (by omega_arith), hY, hyv, bexp_zero, Nat.pow_zero, Nat.one_mul]
  · rw [hI.done (8 + d) (by omega_arith), hY, hyv, bexp_zero, Nat.pow_zero, Nat.one_mul]
  · rw [ax, hxv, Nat.pow_zero, Nat.pow_one]
  · rw [hI.hdr i hi h1 h2 h3, hmv, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h3), hmu,
      hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]

end VG.Proof.Dsa.AArch64.SharedPower
