module

public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Dsa.AArch64.Call
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.Frame
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedStore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedStore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
public import VerifiedGarbage.Proof.Dsa.SharedPower
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.SharedPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigit

/-! ### `Dsa.AArch64.SharedPowerCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SharedPartsCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.SharedBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SharedTable`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.AArch64.SharedCombine`, which this module and modules that import it used -/

section

/-! # The product of the buckets' powers

`combine` multiplies the buckets from the seventh down into `Y`, and each
of those products into `X`: `X` ends as the product of `bucket_d^d`, which
one more multiplication by 1 takes out of Montgomery form, into `[aT]`. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- What the products keep from `s`: the table, the arrays they do not
write, and the header's slots but the digit's and the count's. -/
structure CmbKeep (s : State) (P : Addr) (wx : Nat) (t : State) : Prop where
  ent : ∀ j < 16, wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx
  arr : ∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT → j ≠ aX →
    wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx
  hdr : ∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sBit → word t.mem P (8 * i) = word s.mem P (8 * i)
  frm : Frm P (workRanges wx) s.mem t.mem
  keep : Keep mmRegs s t

theorem CmbKeep.refl (s : State) (P : Addr) (wx : Nat) : CmbKeep s P wx s :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, Frm.refl _ _ _, Keep.refl _ _⟩

theorem CmbKeep.trans {s t u : State} {P : Addr} {wx : Nat} (h : CmbKeep s P wx t) (k : CmbKeep t P wx u) :
    CmbKeep s P wx u :=
  ⟨fun j hj => (k.ent j hj).trans (h.ent j hj),
    fun j hj h1 h2 h3 h4 h5 => (k.arr j hj h1 h2 h3 h4 h5).trans (h.arr j hj h1 h2 h3 h4 h5),
    fun i hi h1 h2 => (k.hdr i hi h1 h2).trans (h.hdr i hi h1 h2), h.frm.trans k.frm,
    (h.keep.trans k.keep).mono (by decide)⟩

/-- Changes to the arrays the products write. -/
theorem CmbKeep.of_arrays {s t : State} {P : Addr} {wx : Nat} {js : List Nat}
    (ha : Arrays P wx js s.mem t.mem) (hjs : ∀ j ∈ js, j = aAcc ∨ j = aTmp ∨ j = aY ∨ j = Crt.aT ∨ j = aX)
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) (hk : Keep mmRegs s t) : CmbKeep s P wx t := by
  obtain h8 : ∀ j ∈ js, j < 8 := fun j hj => by
    rcases hjs j hj with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨fun j hj => arr_ent ha h8 hn hj,
    fun j hj h1 h2 h3 h4 h5 => ha.wv_of_not_mem hj (fun hm => by
      rcases hjs j hm with h | h | h | h | h
      exacts [h1 h, h2 h, h3 h, h4 h, h5 h]) (by omega_arith),
    fun i hi _ _ => ha.hslot hi, arrays_work ha h8, hk⟩

/-- A store to the digit's slot or the count's. -/
theorem CmbKeep.of_slot {s t : State} {P : Addr} {wx i : Nat} {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off P (8 * i)) v) (hi : i = Crt.sNib ∨ i = Crt.sBit)
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) (hk : Keep mmRegs s t) : CmbKeep s P wx t := by
  obtain hi17 : 17 ≤ i ∧ i < 32 := by rcases hi with rfl | rfl <;> decide
  obtain ho : Outside P 136 120 s.mem t.mem := by rw [hm]; exact fn_outside _ P _ hi17.1 hi17.2
  exact ⟨fun j hj => fn_ent ho hn hj, fun j hj _ _ _ _ _ => fn_arr ho hn hj,
    fun k hk h1 h2 => by
      rw [hm, hdrStore_hdr _ _ _ hi17.2 hk (by rcases hi with rfl | rfl <;> [exact Ne.symm h1; exact Ne.symm h2])],
    fn_work ho, hk⟩

/-- The context through changes to arrays that are neither the modulus nor `[aXc]`. -/
theorem ctx_of_arrays {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat} {js : List Nat}
    (hc : CExpCtx s P wx minv N Xc) (ha : Arrays P wx js s.mem t.mem) (hN : aN ∉ js) (hX : Crt.aXc ∉ js)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : CExpCtx t P wx minv N Xc := by
  have hn := hc.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  have hw := hc.good.scr.nowrap
  exact ⟨⟨hc.good.scr.congr hwr, h0.trans hc.good.x0, ha.hdr hc.good.hdr⟩, hc.scrT.congr hwr,
    (ha.wv_of_not_mem (by decide) hN hnZ).trans hc.n,
    by
      rw [ha.word_eq (fun k hk => by
        have := slot_sep (w := wx) (show aN ≠ k from fun e => hN (e ▸ hk)); omega_arith)
        (by have := slot_le (w := wx) (show aN < 8 by decide); omega_arith)]
      exact hc.inv,
    (ha.wv_of_not_mem (by decide) hX hnZ).trans hc.x⟩

/-! ## What the constant-time proofs need between the steps

The steps' lemmas below state, after each step, the fact the next step's
constant-time lemma starts from (`FGood`, `FSel`), then the rest of the run:
the correctness lemmas forget these facts, and the constant-time proofs
(`SharedPowerCT`) read them off. -/

/-- The workspace's context, for a multiplication or a copy. -/
def FGood (P : Addr) (wx : Nat) (t : State) : Prop := ∃ mi, Good t P (slot wx 8) wx mi

/-- The direct selection's hypotheses for the entry `v`. -/
def FSel (P : Addr) (wx v : Nat) (t : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx t P wx mi X Xc ∧ 2 ≤ wx ∧ wx < 2 ^ 30 ∧ v < 16 ∧
    word t.mem P (8 * Crt.sTab) = off P (slot wx 8) ∧ word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v

/-- `[aT] := T_(b0 + 7)`, directly. -/
theorem pick_steps {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc b0 : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    {K : State → Prop} (hK : ∀ t, CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + (b0 + 7))) wx ∧ CmbKeep s P wx t → K t) :
    WP isa (.block [movi .x3 (b0 + 7), sth .x3 Crt.sNib]) s fun u => FSel P wx (b0 + 7) u ∧
      WP isa VG.Impl.Dsa.AArch64.PublicPower.select u K := by
  have hn := hc.scrT.nowrap
  obtain hv : b0 + 7 < 16 := by omega_using [hoff]
  obtain hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  refine (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off P (8 * Crt.sNib))
      (BitVec.ofNat 64 (b0 + 7))) (by
    rcases hoff with rfl | rfl <;>
    · brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.st (i := Crt.sNib) (by decide)]
      rfl) (by rcases hoff with rfl | rfl <;> rfl) rfl (by rcases hoff with rfl | rfl <;> rfl))
    fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain k₁' : Keep mmRegs s s₁ := k₁.mono (by decide)
  obtain c₁ : CmbKeep s P wx s₁ := CmbKeep.of_slot hm₁ (Or.inl rfl) hn k₁'
  obtain hc₁ := ctx_of_fn hc (by rw [hm₁]; exact fn_outside _ P _ (by decide) (by decide)) k₁.wr
    (k₁.gpr .x0 (by decide))
  obtain ht₁ := (c₁.hdr _ (by decide) (by decide) (by decide)).trans ht
  obtain hn₁ : word s₁.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (b0 + 7) := by rw [hm₁, word_writeW_self]
  refine ⟨⟨minv, N, Xc, hc₁, hw, hw', hv, ht₁, hn₁⟩, ?_⟩
  refine WP.mono (PublicPower.select_ok hc₁ hw hw' hv ht₁ hn₁) fun t ⟨hct, hT', o₂, k₂⟩ => hK t ?_
  obtain a₂ : Arrays P wx [Crt.aT] s₁.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₂ (Nat.le_refl _) (by omega_arith)
  exact ⟨hct, by rw [hT', c₁.ent _ hv], c₁.trans (CmbKeep.of_arrays a₂ (by simp) hn k₂)⟩

/-- `[aT] := T_(b0 + 7)`, directly. -/
theorem pick_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc b0 : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8)) :
    WP isa (pick b0 7) s fun t => CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + (b0 + 7))) wx ∧ CmbKeep s P wx t :=
  WP.seq (WP.mono (pick_steps hc hw hw' hoff ht fun _ h => h) fun _ h => h.2)

/-- After `i` buckets below the seventh: `Y` their product with it, and
`X` the product of those products. -/
structure CmbInv (s : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (N Xc g : Nat) (b : Nat → Nat) (i : Nat)
    (t : State) : Prop where
  ctx : CExpCtx t P wx minv N Xc
  ylt : wv t.mem P (slot wx aY) wx < N
  y : wv t.mem P (slot wx aY) wx % N = g ^ cy b i * 2 ^ (64 * wx) % N
  xlt : wv t.mem P (slot wx aX) wx < N
  x : wv t.mem P (slot wx aX) wx % N = g ^ cx b i * 2 ^ (64 * wx) % N
  cnt : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (6 - i)
  kept : CmbKeep s P wx t

def cmbBody (mul : Nat → Nat → Nat → Prog isa) (b0 : Nat) : Prog isa :=
  seqs [.block [ldh .x3 Crt.sBit, .addImm .x .x3 .x3 b0, sth .x3 Crt.sNib], VG.Impl.Dsa.AArch64.PublicPower.select,
    mul aY aY Crt.aT, mul aX aX aY, .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]

theorem cmbStep_steps (M : Mont) {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 i : Nat}
    {b : Nat → Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) N)
    (hoff : b0 = 0 ∨ b0 = 8) (hi : i < 6)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    (hI : CmbInv s P wx minv N Xc g b i t)
    {K : State → Prop} (hK : ∀ t', CmbInv s P wx minv N Xc g b (i + 1) t' ∧
      ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 6) → K t') :
    WP isa (.block [ldh .x3 Crt.sBit, .addImm .x .x3 .x3 b0, sth .x3 Crt.sNib]) t fun s₁ =>
      FSel P wx (b0 + (6 - i)) s₁ ∧ WP isa VG.Impl.Dsa.AArch64.PublicPower.select s₁ fun s₂ =>
      FGood P wx s₂ ∧ WP isa (M.mm aY aY Crt.aT) s₂ fun s₃ =>
      FGood P wx s₃ ∧ WP isa (M.mm aX aX aY) s₃ fun s₄ =>
      FGood P wx s₄ ∧ WP isa (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]) s₄ K := by
  have hn := hI.ctx.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  obtain hv : b0 + (6 - i) < 16 := by omega_using [hoff, hi]
  obtain hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hc := hI.ctx
  -- The bucket's index.
  refine (WP.mono (WP.keep [.x3] (Q := fun u => u.mem = t.mem.writeW (off P (8 * Crt.sNib))
      (BitVec.ofNat 64 (b0 + (6 - i)))) (by
    rcases hoff with rfl | rfl <;>
    · brun [hc.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
        hc.ld (i := Crt.sBit) (by decide), hc.st (i := Crt.sNib) (by decide), hI.cnt, ofNat_add_ofNat]
      refine congrArg (t.mem.writeW _) (congrArg (BitVec.ofNat 64) ?_)
      omega_arith) (by rcases hoff with rfl | rfl <;> rfl) rfl (by rcases hoff with rfl | rfl <;> rfl))
    fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain o₁ : Outside P 136 120 t.mem s₁.mem := by rw [hm₁]; exact fn_outside _ P _ (by decide) (by decide)
  obtain c₁ : CmbKeep t P wx s₁ := CmbKeep.of_slot hm₁ (Or.inl rfl) hn (k₁.mono (by decide))
  obtain hc₁ := ctx_of_fn hc o₁ k₁.wr (k₁.gpr .x0 (by decide))
  -- The bucket.
  obtain ht₁ := (c₁.hdr _ (by decide) (by decide) (by decide)).trans
    ((hI.kept.hdr _ (by decide) (by decide) (by decide)).trans ht)
  obtain hn₁ : word s₁.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (b0 + (6 - i)) := by rw [hm₁, word_writeW_self]
  refine ⟨⟨minv, N, Xc, hc₁, hw, hw', hv, ht₁, hn₁⟩, ?_⟩
  refine (WP.mono (PublicPower.select_ok hc₁ hw hw' hv ht₁ hn₁) fun s₂ ⟨hc₂, hT₂, o₂, k₂⟩ => ⟨⟨minv, hc₂.good⟩, ?_⟩)
  obtain a₂ : Arrays P wx [Crt.aT] s₁.mem s₂.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₂ (Nat.le_refl _) (by omega_arith)
  obtain c₂ : CmbKeep s₁ P wx s₂ := CmbKeep.of_arrays a₂ (by simp) hn k₂
  obtain hTv : wv s₂.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + (b0 + (6 - i)))) wx := by
    rw [hT₂, c₁.ent _ hv, hI.kept.ent _ hv]
  obtain hY₂ : wv s₂.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx := by
    rw [a₂.wv_of_not_mem (by decide) (by decide) hnZ, fn_arr o₁ hn (by decide)]
  obtain hX₂ : wv s₂.mem P (slot wx aX) wx = wv t.mem P (slot wx aX) wx := by
    rw [a₂.wv_of_not_mem (by decide) (by decide) hnZ, fn_arr o₁ hn (by decide)]
  -- `Y := Y T`.
  refine (WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hc₂.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.inv
    (by rw [hc₂.n, hTv]; exact hlt _ (by omega_arith) (by omega_arith)))
    fun s₃ ⟨hg₃, hlt₃, hm₃, a₃, k₃⟩ => ⟨⟨minv, hg₃⟩, ?_⟩)
  rw [hc₂.n] at hlt₃ hm₃
  obtain c₃ : CmbKeep s₂ P wx s₃ := CmbKeep.of_arrays a₃ (by simp) hn k₃
  obtain hc₃ := ctx_of_arrays hc₂ a₃ (by decide) (by decide) k₃.wr (k₃.gpr .x0 (by decide))
  obtain hYv₃ : wv s₃.mem P (slot wx aY) wx % N = g ^ cy b (i + 1) * 2 ^ (64 * wx) % N :=
    mont_mulT hR (hY₂ ▸ hI.y) (hTv ▸ hb _ (by omega_arith) (by omega_arith)) hm₃
  obtain hX₃ : wv s₃.mem P (slot wx aX) wx = wv t.mem P (slot wx aX) wx := by
    rw [a₃.wv_of_not_mem (by decide) (by decide) hnZ, hX₂]
  -- `X := X Y`.
  refine (WP.mono (M.mm_ok (o := aX) (a := aX) (b := aY) hc₃.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.inv
    (by rw [hc₃.n]; exact hlt₃)) fun s₄ ⟨hg₄, hlt₄, hm₄, a₄, k₄⟩ => ⟨⟨minv, hg₄⟩, ?_⟩)
  rw [hc₃.n] at hlt₄ hm₄
  obtain c₄ : CmbKeep s₃ P wx s₄ := CmbKeep.of_arrays a₄ (by simp) hn k₄
  obtain hc₄ := ctx_of_arrays hc₃ a₄ (by decide) (by decide) k₄.wr (k₄.gpr .x0 (by decide))
  obtain hXv₄ : wv s₄.mem P (slot wx aX) wx % N = g ^ cx b (i + 1) * 2 ^ (64 * wx) % N :=
    mont_mulT hR (hX₃ ▸ hI.x) hYv₃ hm₄
  obtain hY₄ : wv s₄.mem P (slot wx aY) wx = wv s₃.mem P (slot wx aY) wx :=
    a₄.wv_of_not_mem (by decide) (by decide) hnZ
  obtain c04 : CmbKeep t P wx s₄ := ((c₁.trans c₂).trans c₃).trans c₄
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₄ (b := 6 - i)
    ((a₄.hslot (by decide)).trans ((a₃.hslot (by decide)).trans ((a₂.hslot (by decide)).trans
      ((by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)] :
        word s₁.mem P (8 * Crt.sBit) = word t.mem P (8 * Crt.sBit)).trans hI.cnt)))) (by omega_arith))
    fun t' ⟨⟨hm', h3⟩, k'⟩ => hK t' ?_
  obtain o' : Outside P 136 120 s₄.mem t'.mem := by rw [hm']; exact fn_outside _ P _ (by decide) (by decide)
  obtain c' : CmbKeep s₄ P wx t' := CmbKeep.of_slot hm' (Or.inr rfl) hn (k'.mono (by decide))
  refine ⟨⟨ctx_of_fn hc₄ o' k'.wr (k'.gpr .x0 (by decide)), ?_, ?_, ?_, ?_, ?_,
    hI.kept.trans (c04.trans c')⟩, ?_⟩
  · rw [fn_arr o' hn (by decide), hY₄]; exact hlt₃
  · rw [fn_arr o' hn (by decide), hY₄]; exact hYv₃
  · rw [fn_arr o' hn (by decide)]; exact hlt₄
  · rw [fn_arr o' hn (by decide)]; exact hXv₄
  · rw [hm', word_writeW_self, Nat.sub_sub]
  · rw [h3, cnt_ne (by omega_arith)]
    omega_arith

theorem cmbStep_ok (M : Mont) {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 i : Nat}
    {b : Nat → Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) N)
    (hoff : b0 = 0 ∨ b0 = 8) (hi : i < 6)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    (hI : CmbInv s P wx minv N Xc g b i t) :
    WP isa (cmbBody M.mm b0) t fun t' => CmbInv s P wx minv N Xc g b (i + 1) t' ∧
      ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 6) := by
  unfold cmbBody
  simp only [seqs]
  exact WP.seq (WP.mono (cmbStep_steps M hw hw' hR hoff hi ht hlt hb hI fun _ h => h) fun _ h =>
    WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h => h.2))))

theorem combine_eq (mul : Nat → Nat → Nat → Prog isa) (b0 : Nat) : combine mul b0 =
    seqs ([pick b0 7] ++ (Crt.copyArr aY Crt.aT ++ (Crt.copyArr aX Crt.aT ++
      ([.block [movi .x3 6, sth .x3 Crt.sBit], .loop (cmbBody mul b0) (.nonzero .x .x3),
        mul Crt.aT aX aOne] : List (Prog isa))))) := rfl

/-- The seventh bucket into `Y` and `X`, and the count: the start of the
loop over the six buckets below, with what the constant-time proof needs
after each step. -/
theorem combineHead_steps {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 : Nat}
    {b : Nat → Nat} (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    {K : State → Prop} (hK : ∀ t, CmbInv s P wx minv N Xc g b 0 t → K t) :
    WP isa (.block [movi .x3 (b0 + 7), sth .x3 Crt.sNib]) s fun u => FSel P wx (b0 + 7) u ∧
      WP isa VG.Impl.Dsa.AArch64.PublicPower.select u fun s₁ => FGood P wx s₁ ∧
      WP isa (seqs (Crt.copyArr aY Crt.aT)) s₁ fun s₂ => FGood P wx s₂ ∧
      WP isa (seqs (Crt.copyArr aX Crt.aT)) s₂ fun s₃ => FGood P wx s₃ ∧
      WP isa (.block [movi .x3 6, sth .x3 Crt.sBit]) s₃ K := by
  have hn := hc.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  refine pick_steps hc hw hw' hoff ht fun s₁ ⟨hc₁, hT₁, c₁⟩ => ⟨⟨minv, hc₁.good⟩, ?_⟩
  refine WP.mono (copyArr_ok hc₁.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (o := aY) (a := Crt.aT) (by decide) (by decide) (by decide))
    fun s₂ ⟨hY₂, o₂, k₂⟩ => ?_
  obtain a₂ : Arrays P wx [aY] s₁.mem s₂.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₂ (Nat.le_refl _) (by omega_arith)
  obtain c₂ : CmbKeep s₁ P wx s₂ := CmbKeep.of_arrays a₂ (by simp) hn k₂
  obtain hc₂ := ctx_of_arrays hc₁ a₂ (by decide) (by decide) k₂.wr (k₂.gpr .x0 (by decide))
  refine ⟨⟨minv, hc₂.good⟩, ?_⟩
  refine WP.mono (copyArr_ok hc₂.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (o := aX) (a := Crt.aT) (by decide) (by decide) (by decide))
    fun s₃ ⟨hX₃, o₃, k₃⟩ => ?_
  obtain a₃ : Arrays P wx [aX] s₂.mem s₃.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₃ (Nat.le_refl _) (by omega_arith)
  obtain c₃ : CmbKeep s₂ P wx s₃ := CmbKeep.of_arrays a₃ (by simp) hn k₃
  obtain hc₃ := ctx_of_arrays hc₂ a₃ (by decide) (by decide) k₃.wr (k₃.gpr .x0 (by decide))
  refine ⟨⟨minv, hc₃.good⟩, ?_⟩
  -- The count.
  refine WP.mono (WP.keep [.x3] (Q := fun v => v.mem = s₃.mem.writeW (off P (8 * Crt.sBit))
      (BitVec.ofNat 64 6)) (by
    brun [hc₃.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hc₃.st (i := Crt.sBit) (by decide)]
    rfl) rfl rfl rfl) fun s₄ ⟨hm₄, k₄⟩ => hK s₄ ?_
  obtain o₄ : Outside P 136 120 s₃.mem s₄.mem := by rw [hm₄]; exact fn_outside _ P _ (by decide) (by decide)
  obtain c₄ : CmbKeep s₃ P wx s₄ := CmbKeep.of_slot hm₄ (Or.inr rfl) hn (k₄.mono (by decide))
  obtain c04 : CmbKeep s P wx s₄ := ((c₁.trans c₂).trans c₃).trans c₄
  obtain hTs : wv s₁.mem P (slot wx Crt.aT) wx % N = g ^ b 7 * 2 ^ (64 * wx) % N := by
    rw [hT₁]; exact hb 7 (by decide) (by decide)
  obtain hTl : wv s₁.mem P (slot wx Crt.aT) wx < N := by rw [hT₁]; exact hlt 7 (by decide) (by decide)
  obtain hT₂ : wv s₂.mem P (slot wx Crt.aT) wx = wv s₁.mem P (slot wx Crt.aT) wx :=
    a₂.wv_of_not_mem (by decide) (by decide) hnZ
  obtain hY₄ : wv s₄.mem P (slot wx aY) wx = wv s₁.mem P (slot wx Crt.aT) wx := by
    rw [fn_arr o₄ hn (by decide), a₃.wv_of_not_mem (by decide) (by decide) hnZ, hY₂]
  obtain hX₄ : wv s₄.mem P (slot wx aX) wx = wv s₁.mem P (slot wx Crt.aT) wx := by
    rw [fn_arr o₄ hn (by decide), hX₃, hT₂]
  exact ⟨ctx_of_fn hc₃ o₄ k₄.wr (k₄.gpr .x0 (by decide)), by rw [hY₄]; exact hTl, by rw [hY₄]; exact hTs,
    by rw [hX₄]; exact hTl, by rw [hX₄]; exact hTs, by rw [hm₄, word_writeW_self], c04⟩

/-- The product of `bucket_d^d` over the seven buckets after entry `b0`,
whose exponents of `g` are `b d`: `[aT] := g^(Σ d · b d)`, out of Montgomery
form. -/
theorem combine_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 : Nat}
    {b : Nat → Nat} (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) N) (hN : 1 < N) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    (hone : wv s.mem P (slot wx aOne) wx = 1) :
    WP isa (combine M.mm b0) s fun t => CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx Crt.aT) wx =
        g ^ (b 1 + 2 * b 2 + 3 * b 3 + 4 * b 4 + 5 * b 5 + 6 * b 6 + 7 * b 7) % N ∧
      CmbKeep s P wx t := by
  have hn := hc.scrT.nowrap
  rw [combine_eq]
  refine wp_seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  unfold pick
  refine WP.seq (WP.mono (combineHead_steps hc hw hw' hoff ht hlt hb (b := b) (g := g) fun s₄ I0 => ?_)
    fun _ h => WP.mono h.2 fun _ h => wp_seqs_append (by simp [Crt.copyArr]) (by simp [Crt.copyArr])
      (WP.mono h.2 fun _ h => wp_seqs_append (by simp [Crt.copyArr]) (by simp) (WP.mono h.2 fun _ h =>
        WP.seq h.2)))
  -- The six buckets below.
  refine WP.seq (WP.mono (count_loop (cr := .x3) (n := 6) (by decide) (CmbInv s P wx minv N Xc g b)
    (fun i hi t hI => cmbStep_ok M hw hw' hR hoff hi ht hlt hb hI) I0) fun s₅ hI => ?_)
  -- Out of Montgomery form.
  obtain hone₅ : wv s₅.mem P (slot wx aOne) wx = 1 :=
    (hI.kept.arr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hone
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := aX) (b := aOne) hI.ctx.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.ctx.inv
    (by rw [hI.ctx.n, hone₅]; exact hN)) fun t ⟨_, hltt, hmt, at', kt⟩ => ?_
  rw [hI.ctx.n] at hltt hmt
  rw [hone₅] at hmt
  obtain hres := VG.Proof.Dsa.mont_decode hR hI.x hmt
  rw [Nat.mod_eq_of_lt hltt, cx_six] at hres
  exact ⟨ctx_of_arrays hI.ctx at' (by decide) (by decide) kt.wr (kt.gpr .x0 (by decide)), hres,
    hI.kept.trans (CmbKeep.of_arrays at' (by simp) hn kt)⟩

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # g^x and the mask of g^q = 1, in the prime's workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The mask of `[aT] = 1` into `sMaskX`: nothing else of the table or the
header changes. -/
theorem orderCheck_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) :
    WP isa orderCheck s fun t => CExpCtx t P wx minv N Xc ∧
      word t.mem P (8 * Crt.sMaskX) = mask (decide (wv s.mem P (slot wx Crt.aT) wx = 1)) ∧
      (∀ j < 16, wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aX → wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ i < 32, i ≠ Crt.sMaskX → word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  have hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  unfold orderCheck
  refine wp_seqs_append (by simp [Crt.copyArr]) (by simp) (WP.mono (copyArr_ok hc.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (o := aX) (a := Crt.aT) (by decide) (by decide) (by decide))
    fun u ⟨hX, ou, ku⟩ => ?_)
  have au : Arrays P wx [aX] s.mem u.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ou (Nat.le_refl _) (by omega_arith)
  have hcu := ctx_of_arrays hc au (by decide) (by decide) ku.wr (ku.gpr .x0 (by decide))
  simp only [seqs]
  refine WP.seq (WP.mono (oneScan_ok hcu.good (Nat.le_refl _) hw (by omega_arith)) fun v ⟨h15, hmv, kv⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .x15 false) fun z ⟨h3, hmz, kz⟩ => ?_
  have h0 : z.gpr .x0 = P := (kz.gpr .x0 (by decide)).trans ((kv.gpr .x0 (by decide)).trans hcu.good.x0)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = z.mem.writeW (off P (8 * Crt.sMaskX)) (z.gpr .x3))
    (by
      brun [h0, hdr_enc (show Crt.sMaskX < 32 by decide), kz.wr, kv.wr, hcu.st (i := Crt.sMaskX) (by decide)])
    rfl rfl rfl) fun t ⟨hmt, kt⟩ => ?_
  have hmt' : t.mem = u.mem.writeW (off P (8 * Crt.sMaskX)) (z.gpr .x3) := by rw [hmt, hmz, hmv]
  have ot : Outside P 136 120 u.mem t.mem := by rw [hmt']; exact fn_outside _ P _ (by decide) (by decide)
  have kall : Keep mmRegs s t := (((ku.trans kv).trans (kz.mono (rs' := mmRegs) (by decide))).trans kt).mono
    (by decide)
  have kut : Keep mmRegs u t := ((kv.trans (kz.mono (rs' := mmRegs) (by decide))).trans kt).mono (by decide)
  refine ⟨ctx_of_fn hcu ot kut.wr (kut.gpr .x0 (by decide)), ?_, fun j hj => ?_, fun j hj hjx => ?_,
    fun i hi h => ?_, (arrays_work au (by decide)).trans (fn_work ot), kall⟩
  · rw [hmt', word_writeW_self, h3]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    rw [← hX]
    exact decide_eq_decide.mpr h15
  · rw [fn_ent ot hn hj, arr_ent au (by decide) hn hj]
  · rw [fn_arr ot hn hj, au.wv_of_not_mem hj (by simpa using hjx) hnZ]
  · rw [hmt', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h), au.hslot hi]

/-- A word of the parent's workspace through a store to a slot of the child's header. -/
theorem child_store_parent {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx t B Z o w wx minv) (m : Mem) {i d : Nat} (v : BitVec 64) (hi : i < 32) (hd : d + 8 ≤ o) :
    word (m.writeW (off B (o + 8 * i)) v) B d = word m B d := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  rw [store_off]
  exact (Frm.of_outside (rs := [(8 * i, 8)]) (writeW_outside m (off B o) (d := 8 * i) v (by omega_arith))
    (by simp)).word_below (L := slot wx 8)
    (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) (by omega_arith) (by omega_arith) hd

/-- The exponents' pointers and their length, from the parent's header. -/
theorem expInit_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {xp qp : Addr} {L : Nat}
    (he : word s.mem B (8 * arg2) = xp) (hel : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 L)
    (hq : word s.mem B Field.q.offset = qp) :
    WP isa (.block expInit) s fun t =>
      t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) xp).writeW (off (off B o) (8 * Crt.sSrc)) qp).writeW
        (off (off B o) (8 * Crt.sI)) (BitVec.ofNat 64 L) ∧ Keep [.x3, .x5] s t := by
  have hlo := hc.lo
  have hhi := hc.hi
  have h384 : 384 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have hqo : Field.q.offset = 264 := rfl
  have hq₁ : (s.mem.writeW (off B (o + 8 * Crt.sExp)) xp).readW (off B Field.q.offset) 64 = qp :=
    (child_store_parent hc s.mem xp (by decide) (by omega_arith)).trans hq
  have hl₂ : ((s.mem.writeW (off B (o + 8 * Crt.sExp)) xp).writeW (off B (o + 8 * Crt.sSrc)) qp).readW
      (off B (8 * arg2Len)) 64 = BitVec.ofNat 64 L :=
    ((child_store_parent hc _ qp (by decide) (by unfold arg2Len; omega_arith)).trans
      (child_store_parent hc s.mem xp (by decide) (by unfold arg2Len; omega_arith))).trans hel
  refine WP.keep _ ?_ rfl rfl rfl
  brun [SharedPower.expInit, Crt.ldw, hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show arg2 < 32 by decide),
    hdr_enc (show arg2Len < 32 by decide), field_enc .q, fieldAddress,
    hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sSrc < 32 by decide),
    hdr_enc (show Crt.sI < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link',
    hc.ldn (show arg2 < 32 by decide), he, hc.st' (show Crt.sExp < 32 by decide),
    hc.scr.ld (d := Field.q.offset) (by omega_arith), hq₁,
    hc.st' (show Crt.sSrc < 32 by decide), hc.ldn (show arg2Len < 32 by decide), hl₂,
    hc.st' (show Crt.sI < 32 by decide), off_off]

theorem power_eq (mul : Nat → Nat → Nat → Prog isa) : power mul =
    seqs (([Arithmetic.constants mul, Arithmetic.load aX arg argLen, Arithmetic.encodePower mul] : List (Prog isa)) ++
      (tableInit ++ (([.block SharedPower.expInit, digits mul, combine mul 8, orderCheck,
        combine mul 0] : List (Prog isa)) ++ Crt.copyArr aY Crt.aT))) := rfl

/-- A source outside the scratch space, as the child's workspace sees it. -/
theorem src_out {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    {p : Addr} {bs : List Byte} (hs : Src s B Z p bs) :
    ∀ i < bs.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (p + BitVec.ofNat 64 i) := fun i hi' => by
  have hi := hc.hi
  have hBn := hc.scr.nowrap
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have := hs.out i hi'
  rcases ofs_rebase B (p + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
  · omega_arith
  · omega_arith

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! ### `Dsa.AArch64.SharedDigitsCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.SharedBucketCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.SharedStoreCT`, which only this module used -/

section

/-! # The masked store's addresses do not depend on the digit -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowVector
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Dsa.AArch64.SharedPower

/-- `store_ok`'s hypotheses: the digit, in `sNib`, is not among the public data. -/
def StorePre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc v : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    p.wx % 8 = 0 ∧ v < 8 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

def StoreLoopPre (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ s₀ mi X Xc v, StoreInv s₀ (off p.B p.o) p.wx mi X Xc v j s ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 8 ∧
    s.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - j)

def StoreStepPre (q : XPub × Nat) (s : State) : Prop :=
  ∃ mi X Xc v, CExpCtx s (off q.1.B q.1.o) q.1.wx mi X Xc ∧ 8 * q.2 + 8 ≤ q.1.wx ∧
    word s.mem (off q.1.B q.1.o) (8 * Crt.sTab) = off (off q.1.B q.1.o) (slot q.1.wx 8) ∧
    s.gpr .x6 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧
    s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT + 64 * q.2) ∧
    s.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ s.v .v24 = dup2 1

theorem storeStep_pins : Pins StoreStepPre [.x0, .x17] := by
  intro q s t hs ht r hr
  obtain ⟨_, _, _, _, cs, _, _, _, ps, _⟩ := hs
  obtain ⟨_, _, _, _, ct, _, _, _, pt, _⟩ := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact cs.good.x0.trans ct.good.x0.symm
  · exact ps.trans pt.symm

theorem storeRaw_ct : RelCT isa (Two StoreStepPre) storeRaw (fun _ _ => True) := by
  unfold storeRaw
  refine RelCT.seq (two_piece (Ψ := ScanPins 8) [.x0, .x17] storeStep_pins (by taint_decide) ?_)
    (two_taint [.x16, .x6, .x14, .x17] (scan_pins 8) (by taint_decide))
  rintro q s ⟨mi, X, Xc, v, hc, hb, ht, h6, h17, h22, h24⟩
  exact WP.mono (storeHead_ok hc hb ht h17) fun a ⟨h16, h14, _, _, _, ka⟩ =>
    ⟨h16, (ka.gpr .x6 (by decide)).trans h6, h14, (ka.gpr .x17 (by decide)).trans h17⟩

theorem storeLoop_ct :
    RelCT isa (Two fun p s => 0 < p.wx / 8 ∧ StoreLoopPre p 0 s) (.loop storeRaw (.nonzero .x .x13))
      (fun _ _ => True) := by
  refine (two_loop (Φ := StoreLoopPre) (Ψ := fun _ _ => True) (fun p : XPub => p.wx / 8)
    (two_map id ?_ storeRaw_ct) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  · rintro ⟨p, j⟩ s ⟨hj, _, mi, X, Xc, v, hI, _⟩
    have hj' : j < p.wx / 8 := hj
    exact ⟨mi, X, Xc, v, hI.ctx, show 8 * j + 8 ≤ p.wx by omega_using [hj'], hI.tab, hI.stride, hI.ptr, hI.digit, hI.one⟩
  rintro p j s hj ⟨s₀, mi, X, Xc, v, hI, hw, hw', hv, h13⟩
  refine WP.mono ((storeRaw_wp _ _).mpr (storeStep_ok hv (by omega_using [hj]) hI)) fun t ⟨ht, hc⟩ => ?_
  have h13' : t.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - (j + 1)) := by
    rw [hc, h13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hj]
  have hz : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ p.wx / 8 := by
    rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.wx / 8 - (j + 1) < 2 ^ 64 by omega_using [hw'])]
    omega_using [hj]
  exact ⟨eval_nz_count hj hz, fun _ => ⟨s₀, mi, X, Xc, v, ht, hw, hw', hv, h13'⟩, fun _ => trivial⟩

theorem storeSetup_ready {p : XPub} {s : State} (h : StorePre p s) :
    WP isa (.block setup) s fun t => 0 < p.wx / 8 ∧ StoreLoopPre p 0 t := by
  obtain ⟨mi, X, Xc, v, hc, hw, hw', _, hv, ht, hN⟩ := h
  refine WP.mono (setup_ok hc hw' hN) fun u ⟨⟨h6, h13, h17, h22, h24, hm⟩, ku⟩ => ?_
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  refine ⟨by omega_using [hw], u, mi, X, Xc, v, ?_, hw, hw', hv, by simpa using h13⟩
  exact ⟨ctx, by rw [hm]; exact ht, h6, by simpa using h17, h22, h24,
    Outside.refl _ _ _ _, fun _ h => by omega, Keep.refl _ _⟩

/-- The masked store leaks the same in runs with the same workspace. -/
theorem store_ct : RelCT isa (Two StorePre) store (fun _ _ => True) := by
  rw [store_eq]
  exact RelCT.seq (two_piece (Ψ := fun p s => 0 < p.wx / 8 ∧ StoreLoopPre p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.x0)) (by taint_decide)
    (fun _ _ h => storeSetup_ready h)) storeLoop_ct

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # The buckets' updates leak neither digit of the secret exponent

The secret digit's bucket is read by the scan of every entry and written by
the masked store of every entry; the public digit's bucket is read and
written at its address, which the public data fix. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower

/-! ## The secret digit's bucket -/

/-- `secretBucket_ok`'s hypotheses. -/
def SBPre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc V : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    p.wx % 8 = 0 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 64 ∧ Xc < X

/-- With the digit in `sNib`: through the scan and the multiplication. -/
def SBMid (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc v : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    p.wx % 8 = 0 ∧ v < 8 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v ∧ Xc < X

theorem SBMid.sel {p : XPub} {s : State} (h : SBMid p s) : WindowVector.SelPn 16 p s :=
  let ⟨mi, X, Xc, v, hc, hw, hw', _, hv, ht, hn, _⟩ := h
  ⟨mi, X, Xc, v, hc, by omega_using [hw], hw', by omega_using [hv], ht, hn⟩

theorem SBMid.goodW {p : XPub} {s : State} (h : SBMid p s) : GoodW p.ws s :=
  let ⟨mi, _, _, _, hc, _⟩ := h; ⟨mi, hc.good, Nat.le_refl _⟩

theorem sbDigit_post {p : XPub} {s : State} (h : SBPre p s) : WP isa (.block secretDigit) s (SBMid p) := by
  obtain ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', hA⟩ := h
  refine WP.mono (secretDigit_ok hc hV hV') fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 (V % 8)) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem s₁.mem := Frm.of_outside o₁ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, V % 8, hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide)), hw, hw', hd, Nat.mod_lt _ (by decide),
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact ht,
    by rw [hm₁, word_writeW_self], hA⟩

theorem sbSelect_post {p : XPub} {s : State} (h : SBMid p s) :
    WP isa VG.Impl.Rsa.AArch64.Crt.select s (SBMid p) := by
  obtain ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn, hA⟩ := h
  have hv16 : v < 16 := by omega_using [hv]
  refine WP.mono (WindowVector.select_ok (Or.inl rfl)
    (fun hu tab nib => tabSel_ok hu (by omega_using [hw]) hw' hv16 tab nib) hc hw' hv16 ht hn)
    fun t ⟨hc₂, _, f₂, _⟩ => ?_
  exact ⟨mi, X, Xc, v, hc₂, hw, hw', hd, hv, (sel_hdr f₂ (by decide) (by decide) (by decide)).trans ht,
    (sel_hdr f₂ (by decide) (by decide) (by decide)).trans hn, hA⟩

theorem sbMul_post (M : Mont) {p : XPub} {s : State} (h : SBMid p s) :
    WP isa (M.mm Crt.aT Crt.aT Crt.aXc) s (SBMid p) := by
  obtain ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn, hA⟩ := h
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _)
    (by omega_using [hw]) (by omega_using [hw']) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.inv (by rw [hc.n, hc.x]; exact hA)) fun t ⟨_, _, _, ha₃, k₃⟩ => ?_
  have f₃ : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem := Frm.of_arrays ha₃ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, v, hc.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide)), hw, hw', hd, hv,
    (ha₃.hslot (by decide)).trans ht, (ha₃.hslot (by decide)).trans hn, hA⟩

/-- The secret digit's bucket is updated with the same addresses and
branches whatever the digit. -/
theorem secretBucket_ct (M : Mont) : RelCT isa (Two SBPre)
    (seqs [.block secretDigit, VG.Impl.Rsa.AArch64.Crt.select, M.mm Crt.aT Crt.aT Crt.aXc, store])
    (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_piece [.x0] (pins_x0B (fun p : XPub => off p.B p.o)
    fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.x0) (by unfold secretDigit; taint_decide) fun _ _ h => sbDigit_post h) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.sel) (WindowVector.select_ct (Or.inl rfl) tabSel_ct))
    fun _ _ h => sbSelect_post h) ?_
  refine RelCT.seq (two_post (two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW)
    (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide))) fun _ _ h => sbMul_post M h) ?_
  exact two_map id (fun _ _ ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn, _⟩ =>
    ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn⟩) store_ct

/-! ## The public digit's bucket -/

/-- After `put`'s exchange: the source and the destination of the copy. -/
def PutRegs (p : XPub × Nat) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 p.1.wx ∧
  s.gpr .x16 = off (off p.1.B p.1.o) (slot p.1.wx Crt.aT) ∧
  s.gpr .x17 = off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2))

/-- The store of `[aT]` to the entry the public data name. -/
theorem put_ct : RelCT isa (Two PublicPower.SelectPre) put (fun _ _ => True) := by
  unfold put
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := PublicPower.SelectRegs) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0))
    (by unfold VG.Impl.Dsa.AArch64.PublicPower.selectHead; taint_decide) (fun p s ⟨_, _, _, hc, _, hw', hv, ht, hn⟩ =>
      WP.mono (PublicPower.selectHead_ok hc hw' hv ht hn) (fun _ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩)))
    (two_piece (Ψ := PutRegs) [] (fun _ _ _ _ _ _ hr => nomatch hr) (by taint_decide) fun p s ⟨h12, h16, h17⟩ => ?_))) ?_
  · refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun a => a.gpr .x16 = s.gpr .x17 ∧
      a.gpr .x17 = s.gpr .x16) (by brun []) rfl rfl rfl) fun a ⟨⟨a16, a17⟩, ka⟩ => ?_
    exact ⟨(ka.gpr .x12 (by decide)).trans h12, a16.trans h17, a17.trans h16⟩
  exact two_taint [.x12, .x16, .x17] (pins_of
    (fun p r => if r = .x12 then BitVec.ofNat 64 p.1.wx else
      if r = .x16 then off (off p.1.B p.1.o) (slot p.1.wx Crt.aT) else
        off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2))) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)) (by taint_decide)

/-- `publicBucket_ok`'s hypotheses, the digit public. -/
def PBPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    p.2 < 8 ∧ word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    s.gpr .x3 = BitVec.ofNat 64 p.2 ∧ Xc < X

/-- With the entry's index in `sNib`. -/
def PBMid (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    p.2 < 16 ∧ word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 p.2 ∧ Xc < X

theorem PBMid.sel {p : XPub × Nat} {s : State} (h : PBMid p s) : PublicPower.SelectPre p s :=
  let ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn, _⟩ := h; ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn⟩

theorem pbIndex_ok {s : State} {P : Addr} {wx : Nat} {mi : BitVec 64} {X Xc d : Nat}
    (hc : CExpCtx s P wx mi X Xc) (h3 : s.gpr .x3 = BitVec.ofNat 64 d) :
    WP isa (.block [.addImm .x .x3 .x3 8, sth .x3 Crt.sNib]) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (8 + d)) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.st (i := Crt.sNib) (by decide), h3,
    ofNat_add_ofNat]
  rw [Nat.add_comm]

theorem pbIndex_post {p : XPub × Nat} {s : State} (h : PBPre p s) :
    WP isa (.block [.addImm .x .x3 .x3 8, sth .x3 Crt.sNib]) s (PBMid (p.1, 8 + p.2)) := by
  obtain ⟨mi, X, Xc, hc, hw, hw', hd, ht, h3, hA⟩ := h
  refine WP.mono (pbIndex_ok hc h3) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off p.1.B p.1.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 (8 + p.2)) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem s₁.mem :=
    Frm.of_outside o₁ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide)), hw, hw', by omega_using [hd],
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact ht,
    by rw [hm₁, word_writeW_self], hA⟩

theorem pbSelect_post {p : XPub × Nat} {s : State} (h : PBMid p s) :
    WP isa VG.Impl.Dsa.AArch64.PublicPower.select s (PBMid p) := by
  obtain ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn, hA⟩ := h
  refine WP.mono (PublicPower.select_ok hc hw hw' hv ht hn) fun t ⟨hc₂, _, o₂, _⟩ => ?_
  have hh₂ : ∀ k < 32, word t.mem (off p.1.B p.1.o) (8 * k) = word s.mem (off p.1.B p.1.o) (8 * k) :=
    fun k hk => o₂.word (Or.inl (hdr_lt_slot p.1.wx Crt.aT hk)) (by omega_arith)
  exact ⟨mi, X, Xc, hc₂, hw, hw', hv, (hh₂ _ (by decide)).trans ht, (hh₂ _ (by decide)).trans hn, hA⟩

theorem pbMul_post (M : Mont) {p : XPub × Nat} {s : State} (h : PBMid p s) :
    WP isa (M.mm Crt.aT Crt.aT Crt.aXc) s (PBMid p) := by
  obtain ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn, hA⟩ := h
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _)
    hw (by omega_using [hw']) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.inv (by rw [hc.n, hc.x]; exact hA)) fun t ⟨_, _, _, ha₃, k₃⟩ => ?_
  have f₃ : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem :=
    Frm.of_arrays ha₃ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, hc.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide)), hw, hw', hv,
    (ha₃.hslot (by decide)).trans ht, (ha₃.hslot (by decide)).trans hn, hA⟩

/-- The public digit's bucket is updated at the address the digit names. -/
theorem publicBucket_ct (M : Mont) : RelCT isa (Two PBPre) (publicBucket M.mm) (fun _ _ => True) := by
  unfold publicBucket
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun (p : XPub × Nat) s => PBMid (p.1, 8 + p.2) s) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0) (by taint_decide)
    fun _ _ h => pbIndex_post h) ?_
  refine two_map (fun p : XPub × Nat => (p.1, 8 + p.2)) (fun _ _ h => h) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.sel) PublicPower.select_ct)
    fun _ _ h => pbSelect_post h) ?_
  refine RelCT.seq (two_post (two_map (fun p : XPub × Nat => p.1.ws)
    (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
    (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide))) fun _ _ h => pbMul_post M h) ?_
  exact two_map id (fun _ _ h => h.sel) put_ct

/-- `publicHalf_ok`'s hypotheses, the value in `sMaskX` public. -/
def PHPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sMaskX) = BitVec.ofNat 64 p.2 ∧ p.2 < 2 ^ 64 ∧ Xc < X

/-- The public digit: whether it is zero, and its bucket's address, are the
public data's. -/
theorem publicHalf_ct (M : Mont) : RelCT isa (Two PHPre)
    (seqs [.block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket M.mm)]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun (p : XPub × Nat) s => PBPre (p.1, p.2 % 8) s) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0)
    (by unfold publicDigit; taint_decide) fun p s ⟨mi, X, Xc, hc, hw, hw', ht, hQ, hQ', hA⟩ => ?_) ?_
  · refine WP.mono (publicDigit_ok hc hQ hQ') fun u ⟨⟨h3, hm⟩, hk⟩ => ?_
    exact ⟨mi, X, Xc, hc.of_win (hm ▸ Frm.refl _ _ _) hk.wr (hk.gpr .x0 (by decide)), hw, hw',
      Nat.mod_lt _ (by decide), hm ▸ ht, h3, hA⟩
  refine two_ite (fun p s t hs ht => ?_) ?_ ?_
  · obtain ⟨_, _, _, _, _, _, _, _, hs3, _⟩ := hs
    obtain ⟨_, _, _, _, _, _, _, _, ht3, _⟩ := ht
    have hlt : p.2 % 8 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [PublicPower.eval_zero_x3 hs3 hlt, PublicPower.eval_zero_x3 ht3 hlt]
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_map (fun p : XPub × Nat => (p.1, p.2 % 8)) (fun _ _ h => h.1) (publicBucket_ct M)

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # The digits leak only the public exponent and the layout

The secret exponent's bytes are read at addresses its pointer and length
fix, and its digits go only into the scan and the masked store; the public
exponent's digits choose its bucket's address and whether to multiply. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- A block's first part before the rest of a sequence: it runs the same
and leaks the same trace. -/
theorem relct_block_seq {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ c₁ =>
    cases e₂ with
    | seq a₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at a₁ a₂
      obtain ⟨⟨x₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp a₁
      obtain ⟨⟨y₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨x₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp a₂
      obtain ⟨⟨y₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) c₁))
        (.seq (.block ha₂) (.seq (.block hc₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-! ## A digit -/

/-- `baseSq_ok`'s hypotheses. -/
def SqPre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Xc < X

theorem sq_ct (M : Mont) {α : Type} (f : α → XPub) :
    RelCT isa (Two fun a s => SqPre (f a) s) (M.mm Crt.aXc Crt.aXc Crt.aXc) (Two fun a s => SqPre (f a) s) :=
  two_post (two_map (fun a : α => (f a).ws) (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
    (M.ct (o := Crt.aXc) (a := Crt.aXc) (b := Crt.aXc) (by unfold MmUse; decide)))
    fun _ _ ⟨mi, X, _, hc, hw, hw', hA⟩ => WP.mono (baseSq_ok M hc hw hw' hA)
      fun _ ⟨hc', hlt, _⟩ => ⟨mi, X, _, hc', hw, hw', hlt⟩

/-- A digit's hypotheses: the public exponent's value in `sMaskX` is public. -/
def DPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc V : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 8 ≤ p.1.wx ∧
    p.1.wx < 2 ^ 30 ∧ p.1.wx % 8 = 0 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 64 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sMaskX) = BitVec.ofNat 64 p.2 ∧ p.2 < 2 ^ 64 ∧ Xc < X

/-- A digit of each exponent leaks the same in runs with the same workspace
and the same public exponent. -/
theorem digit_ct (M : Mont) : RelCT isa (Two DPre) (digit M.mm) (fun _ _ => True) := by
  rw [digit_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := PHPre)
    (two_map (fun p : XPub × Nat => p.1) (fun _ _ ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', _, _, hA⟩ =>
      ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', hA⟩) (secretBucket_ct M))
    fun p s ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', hQ, hQ', hA⟩ => ?_) ?_)
  · refine WP.mono (secretBucket_ok M hc hw hw' hd ht hV hV' hA) fun a ⟨hca, _, _, _, _, hdrA, _, _⟩ => ?_
    exact ⟨mi, X, Xc, hca, by omega_using [hw], hw',
      (hdrA _ (by decide) (by decide) (by decide) (by decide)).trans ht,
      (hdrA _ (by decide) (by decide) (by decide) (by decide)).trans hQ, hQ', hA⟩
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := fun (p : XPub × Nat) s => SqPre p.1 s)
    (publicHalf_ct M) fun p s ⟨mi, X, Xc, hc, hw, hw', ht, hQ, hQ', hA⟩ => ?_) ?_)
  · exact WP.mono (publicHalf_ok M hc hw hw' ht hQ hQ' hA) fun b ⟨hcb, _⟩ => ⟨mi, X, Xc, hcb, hw, hw', hA⟩
  have sq := sq_ct M (fun p : XPub × Nat => p.1)
  simp only [seqs]
  refine RelCT.seq sq (RelCT.seq sq (RelCT.seq sq ?_))
  exact x0_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0)
    (by unfold digitEnd; taint_decide)

/-- After `i` digits of a group: the public value `p.2.1` and the count `p.2.2`. -/
def DLoop (p : XPub × Nat × Nat) (i : Nat) (s : State) : Prop :=
  ∃ (s₀ : State) (mi : BitVec 64) (N g ex eq k V : Nat),
    DigitsInv s₀ (off p.1.B p.1.o) p.1.wx mi N g ex eq k V p.2.1 p.2.2 i s ∧ 8 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    p.1.wx % 8 = 0 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) N ∧ p.2.2 ≤ 8 ∧ V < 2 ^ 64 ∧ p.2.1 < 2 ^ 64 ∧
    (∀ i < p.2.2, V / 8 ^ i % 8 = ex / 8 ^ (k + i) % 8) ∧
    (∀ i < p.2.2, p.2.1 / 8 ^ i % 8 = eq / 8 ^ (k + i) % 8)

/-- The digits of a group. -/
theorem digitLoop_ct (M : Mont) :
    RelCT isa (Two fun (p : XPub × Nat × Nat) s => 0 < p.2.2 ∧ DLoop p 0 s)
      (.loop (digit M.mm) (.nonzero .x .x3)) (Two fun p s => DLoop p p.2.2 s) := by
  refine two_loop (Φ := DLoop) (fun p => p.2.2)
    (two_map (fun q : (XPub × Nat × Nat) × Nat => (q.1.1, q.1.2.1 / 8 ^ q.2)) ?_ (digit_ct M)) ?_
  · rintro ⟨p, i⟩ s ⟨_, s₀, mi, N, g, ex, eq, k, V, hI, hw, hw', hd, _, _, hV', hQ', _⟩
    have hle (a b : Nat) : a / 8 ^ b ≤ a := Nat.div_le_self _ _
    exact ⟨mi, N, _, V / 8 ^ i, hI.dig.ctx, hw, hw', hd, hI.dig.tab, hI.v,
      Nat.lt_of_le_of_lt (hle V i) hV', hI.q, Nat.lt_of_le_of_lt (hle _ i) hQ', hI.dig.alt⟩
  · rintro p i s hi ⟨s₀, mi, N, g, ex, eq, k, V, hI, hw, hw', hd, hR, hc8, hV', hQ', hVd, hQd⟩
    exact WP.mono (digitStep_ok M hw hw' hd hR hc8 hi hV' hQ' hVd hQd hI) fun t ⟨hI', hz⟩ =>
      ⟨eval_nz_count hi hz, fun _ => ⟨s₀, mi, N, g, ex, eq, k, V, hI', hw, hw', hd, hR, hc8, hV', hQ', hVd, hQd⟩,
        fun h => h ▸ ⟨s₀, mi, N, g, ex, eq, k, V, hI', hw, hw', hd, hR, hc8, hV', hQ', hVd, hQd⟩⟩

/-! ## A group of bytes -/

/-- The public data of the digits: the workspace, the exponents' pointers,
and the public exponent's bytes (its length is the secret exponent's). -/
structure GPub where
  x : XPub
  xp : Addr
  qp : Addr
  qb : List Byte

abbrev GPub.P (a : GPub) : Addr := off a.x.B a.x.o

/-- The number of groups of three bytes. -/
abbrev GPub.groups (a : GPub) : Nat := (a.qb.length + 2) / 3

/-- After `j` groups. -/
def GInv (a : GPub) (j : Nat) (s : State) : Prop :=
  ∃ (s₀ : State) (mi : BitVec 64) (N g : Nat) (xb : List Byte) (k : Nat),
    GroupsInv s₀ a.P a.x.wx mi N g a.xp a.qp xb a.qb j k s ∧ Exps s₀ a.P a.x.wx a.xp a.qp xb a.qb ∧
    8 ≤ a.x.wx ∧ a.x.wx < 2 ^ 30 ∧ a.x.wx % 8 = 0 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) N ∧ xb.length < 2 ^ 31

/-- The bytes' addresses and the bytes left, before the bytes are read. -/
def GroupPins (q : GPub × Nat) (s : State) : Prop :=
  s.gpr .x0 = q.1.P ∧ s.gpr .x1 = q.1.xp + BitVec.ofNat 64 (q.1.qb.length - 3 * q.2 - 1) ∧
  s.gpr .x2 = q.1.qp + BitVec.ofNat 64 (q.1.qb.length - 3 * q.2 - 1) ∧
  s.gpr .x4 = BitVec.ofNat 64 (q.1.qb.length - 3 * q.2 - 1)

theorem pins_group : Pins GroupPins [.x0, .x1, .x2, .x4] := by
  rintro q s₁ s₂ ⟨a₁, b₁, c₁, d₁⟩ ⟨a₂, b₂, c₂, d₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

/-- The addresses of the group's last bytes. -/
def groupAddr : List Instr :=
  [ldh .x4 Crt.sI, .subImm .x .x4 .x4 1, ldh .x1 Crt.sExp, .add .x .x1 .x1 .x4, ldh .x2 Crt.sSrc,
    .add .x .x2 .x2 .x4]

theorem groupAddr_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc r : Nat} {xp qp : Addr}
    (hc : CExpCtx s P wx minv N Xc) (hr1 : 1 ≤ r)
    (hI : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 r) (hE : word s.mem P (8 * Crt.sExp) = xp)
    (hS : word s.mem P (8 * Crt.sSrc) = qp) :
    WP isa (.block groupAddr) s fun t => t.gpr .x0 = P ∧ t.gpr .x1 = xp + BitVec.ofNat 64 (r - 1) ∧
      t.gpr .x2 = qp + BitVec.ofNat 64 (r - 1) ∧ t.gpr .x4 = BitVec.ofNat 64 (r - 1) := by
  have e1 : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  brun [groupAddr, hc.good.x0, hdr_enc (show Crt.sI < 32 by decide), hdr_enc (show Crt.sExp < 32 by decide),
    hdr_enc (show Crt.sSrc < 32 by decide), hc.ld (i := Crt.sI) (by decide), hc.ld (i := Crt.sExp) (by decide),
    hc.ld (i := Crt.sSrc) (by decide), hI, hE, hS, e1, VG.Offset.ofNat_sub_ofNat hr1]

theorem GInv.len {a : GPub} {j : Nat} {s : State} (h : GInv a j s) :
    ∃ (s₀ : State) (mi : BitVec 64) (N g : Nat) (xb : List Byte) (k : Nat),
      GroupsInv s₀ a.P a.x.wx mi N g a.xp a.qp xb a.qb j k s ∧ Exps s₀ a.P a.x.wx a.xp a.qp xb a.qb ∧
      8 ≤ a.x.wx ∧ a.x.wx < 2 ^ 30 ∧ a.x.wx % 8 = 0 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) N ∧ xb.length < 2 ^ 31 ∧
      a.qb.length = xb.length :=
  let ⟨s₀, mi, N, g, xb, k, hI, hx, r⟩ := h; ⟨s₀, mi, N, g, xb, k, hI, hx, r.1, r.2.1, r.2.2.1, r.2.2.2.1,
    r.2.2.2.2, hx.len⟩

/-- A group's bytes are read at addresses the pointers and the length fix,
and how many it has is the length's. -/
theorem group_ct : RelCT isa (Two fun (q : GPub × Nat) s => q.2 < q.1.groups ∧ GInv q.1 q.2 s) group
    (fun _ _ => True) := by
  unfold group
  refine relct_block_seq (l₁ := groupAddr) (RelCT.seq (two_piece (Ψ := GroupPins) [.x0]
    (pins_x0B (fun q : GPub × Nat => q.1.P) fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => hI.dig.ctx.good.x0)
    (by taint_decide) fun q s ⟨hj, h⟩ => ?_) (two_taint [.x0, .x1, .x2, .x4] pins_group (by taint_decide)))
  obtain ⟨s₀, mi, N, g, xb, k, hI, hx, hw, hw', hd, hR, hL, hlen⟩ := h.len
  have hj' : q.2 < (q.1.qb.length + 2) / 3 := hj
  exact groupAddr_ok hI.dig.ctx (by omega_using [hj']) (by rw [hlen]; exact hI.rem) hI.xptr hI.qptr

/-- The group's values and its digits' count: where the digits start. -/
theorem groupStart_post {q : GPub × Nat} {s : State} (h : q.2 < q.1.groups ∧ GInv q.1 q.2 s) :
    WP isa group s fun u => 0 < gcount (q.1.qb.length - 3 * q.2) ∧
      DLoop (q.1.x, gval q.1.qb (q.1.qb.length - 3 * q.2), gcount (q.1.qb.length - 3 * q.2)) 0 u := by
  obtain ⟨hj, h⟩ := h
  obtain ⟨s₀, mi, N, g, xb, k, hI, hx, hw, hw', hd, hR, hL, hlen⟩ := h.len
  have hj' : q.2 < (xb.length + 2) / 3 := by rw [← hlen]; exact hj
  rw [hlen]
  generalize q.2 = j at hj' hI
  have hn := hI.dig.ctx.scrT.nowrap
  have hr1 : 1 ≤ xb.length - 3 * j := by omega_arith
  have hmemx : ∀ i (h : i < xb.length), s.mem (q.1.xp + BitVec.ofNat 64 i) = xb[i] := fun i hi => by
    rw [hI.frm _ fun r hr => Or.inr (by
      have := (workRanges_ok q.1.x.wx r hr).2; have := hx.xout i hi; omega_arith)]
    exact hx.xv i hi
  have hmemq : ∀ i (h : i < q.1.qb.length), s.mem (q.1.qp + BitVec.ofNat 64 i) = q.1.qb[i] := fun i hi => by
    rw [hI.frm _ fun r hr => Or.inr (by
      have := (workRanges_ok q.1.x.wx r hr).2; have := hx.qout i hi; omega_arith)]
    exact hx.qv i hi
  refine WP.mono (group_ok hI.dig.ctx hr1 (by omega_arith) (by rw [hx.len]; omega_arith) (by omega_arith)
    hI.rem hI.xptr hI.qptr (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hx.xrd i hi) hmemx
    (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hx.qrd i hi) hmemq) fun u ⟨hm, ku⟩ => ?_
  have oU : Outside q.1.P 136 120 s.mem u.mem := by
    rw [hm]
    exact (((fn_outside _ _ _ (by decide) (by decide)).trans (fn_outside _ _ _ (by decide) (by decide))).trans
      (fn_outside _ _ _ (by decide) (by decide))).trans (fn_outside _ _ _ (by decide) (by decide))
  have hh : ∀ i < 32, i ≠ Crt.sI → i ≠ Crt.sV → i ≠ Crt.sMaskX → i ≠ Crt.sBit →
      word u.mem q.1.P (8 * i) = word s.mem q.1.P (8 * i) := fun i hi h1 h2 h3 h4 => by
    rw [hm, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h4), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h3),
      hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  have hdigU := hI.dig.of_fn oU (hh _ (by decide) (by decide) (by decide) (by decide) (by decide)) ku.wr
    (ku.gpr .x0 (by decide))
  have I0 : DigitsInv u q.1.P q.1.x.wx mi N g (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip q.1.qb) k
      (gval xb (xb.length - 3 * j)) (gval q.1.qb (xb.length - 3 * j)) (gcount (xb.length - 3 * j)) 0 u :=
    ⟨hdigU, by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
          hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.div_one],
      by rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.pow_zero,
          Nat.div_one],
      by rw [hm, word_writeW_self, Nat.sub_zero], DigitsKeep.refl _ _ _⟩
  have hV24 := gval_lt xb (xb.length - 3 * j)
  have hQ24 := gval_lt q.1.qb (xb.length - 3 * j)
  exact ⟨gcount_pos _, u, mi, N, g, _, _, k, _, I0, hw, hw', hd, hR, gcount_le _, Nat.lt_of_lt_of_le hV24 (by decide),
    Nat.lt_of_lt_of_le hQ24 (by decide), fun i hi => by
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.xr]
      exact (group_digit xb hr1 (by omega_arith) hi).symm,
    fun i hi => by
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.qr]
      exact (group_digit q.1.qb hr1 (by rw [hx.len]; omega_arith) hi).symm⟩

/-- A group and its digits. -/
theorem groupsBody_ct (M : Mont) :
    RelCT isa (Two fun (q : GPub × Nat) s => q.2 < q.1.groups ∧ GInv q.1 q.2 s)
      (seqs [group, .loop (digit M.mm) (.nonzero .x .x3), .block [ldh .x3 Crt.sI]]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post group_ct fun _ _ h => groupStart_post h) (RelCT.seq
    (two_map (fun q : GPub × Nat => (q.1.x, gval q.1.qb (q.1.qb.length - 3 * q.2),
      gcount (q.1.qb.length - 3 * q.2))) (fun _ _ h => h) (digitLoop_ct M)) ?_)
  exact x0_ct (fun p : XPub × Nat × Nat => off p.1.B p.1.o)
    (fun _ _ ⟨_, _, _, _, _, _, _, _, hI, _⟩ => hI.dig.ctx.good.x0) (by taint_decide)

/-- Every digit of both exponents leaks the same in runs with the same
workspace, pointers and public exponent. -/
theorem digits_ct (M : Mont) :
    RelCT isa (Two fun (a : GPub) s => 0 < a.groups ∧ GInv a 0 s) (digits M.mm) (fun _ _ => True) := by
  unfold digits
  refine (two_loop (Φ := GInv) (Ψ := fun _ _ => True) (fun a => a.groups) (groupsBody_ct M) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  intro a j s hj h
  obtain ⟨s₀, mi, N, g, xb, k, hI, hx, hw, hw', hd, hR, hL, hlen⟩ := h.len
  have hj' : j < (xb.length + 2) / 3 := by rw [← hlen]; exact hj
  refine WP.mono (groupsStep_ok M hw hw' hd hR hx hL hj' hI) fun t ⟨⟨k', hI'⟩, hz⟩ => ?_
  have hz' : (t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ a.groups := by
    rw [hz]; show _ ↔ j + 1 ≠ (a.qb.length + 2) / 3; rw [hlen]
  exact ⟨eval_nz_count hj hz', fun _ => ⟨s₀, mi, N, g, xb, k', hI', hx, hw, hw', hd, hR, hL⟩, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # The table's start, the exponents' pointers, the products and the order check

None of them reads or branches on a secret: the buckets' products read the
entries in a fixed order, and whether `g^q = 1` goes into a mask. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

theorem FGood.goodW {p : XPub} {s : State} (h : FGood (off p.B p.o) p.wx s) : GoodW p.ws s :=
  let ⟨mi, hg⟩ := h; ⟨mi, hg, Nat.le_refl _⟩

/-! ## The table's start -/

/-- After `j` of the table's entries. -/
def TLoop (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (s₀ : State) (mi : BitVec 64) (N Xc : Nat), TabInv s₀ (off p.B p.o) p.wx mi N Xc j s ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 30 ∧ Xc < N

theorem tabStart_post {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw' : wx < 2 ^ 30) :
    WP isa (.block (([ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3,
      .add .x .x3 .x3 .x4, sth .x3 Crt.sTab, sth .x3 Crt.sEnt] : List Instr) ++
        ([movi .x3 16, sth .x3 Crt.sBit] : List Instr))) s fun v => TabInv v P wx minv N Xc 0 v := by
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
  exact ⟨ctx_of_fn hcu ov kv.wr (kv.gpr .x0 (by decide)), by
      rw [hmv, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmu,
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [hmv, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmu, word_writeW_self],
    by rw [hmv, word_writeW_self], fun _ h => by omega, fun _ _ => rfl, fun _ _ _ _ _ => rfl, Frm.refl _ _ _,
    Keep.refl _ _⟩

/-- The table's sixteen copies of `Y`. -/
theorem tableInit_ct : RelCT isa (Two XCtx) (seqs tableInit) (fun _ _ => True) := by
  rw [tableInit_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < 16 ∧ TLoop p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) fun _ _ h => h.x0) (by taint_decide)
    fun p s ⟨mi, N, Xc, hc, hA, hw, hw'⟩ => WP.mono (tabStart_post hc hw') fun v hI =>
      ⟨by decide, v, mi, N, Xc, hI, hw, hw', hA⟩) ?_
  refine (two_loop (Φ := TLoop) (Ψ := fun _ _ => True) (fun _ => 16) ?_ ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · refine RelCT.seqs_append (by simp [Crt.toEnt]) (by simp) (RelCT.seq (two_post
      (Ψ := fun (q : XPub × Nat) s => s.gpr .x0 = off q.1.B q.1.o)
      (two_map (fun q : XPub × Nat => q) (fun q s ⟨hj, _, mi, N, Xc, hI, hw, hw', hA⟩ =>
        ⟨⟨mi, N, Xc, hI.ctx, hA, hw, hw'⟩, hI.ent, hj, by decide⟩) (toEnt_ct (a := aY) (by taint_decide)))
      fun q s ⟨hj, _, mi, N, Xc, hI, hw, hw', hA⟩ => WP.mono (toEnt_ok hI.ctx hw hw' (a := aY) (by decide) hj hI.ent)
        fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hI.ctx.good.x0) ?_)
    simp only [seqs]
    exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by unfold Crt.nextEnt; taint_decide)
  · rintro p j s hj ⟨s₀, mi, N, Xc, hI, hw, hw', hA⟩
    exact WP.mono (tabStep_ok hw hw' hj hI) fun t ⟨hI', hz⟩ =>
      ⟨eval_nz_count hj hz, fun _ => ⟨s₀, mi, N, Xc, hI', hw, hw', hA⟩, fun _ => trivial⟩

/-! ## The exponents' pointers -/

/-- The exponents' pointers and length are read through the link to the
parent workspace, which the layout fixes. -/
theorem expInit_ct : RelCT isa (Two fun (p : XPub) s => ∃ minv, SubCtx s p.B p.Z p.o p.w p.wx minv)
    (.block SharedPower.expInit) (fun _ _ => True) := by
  unfold SharedPower.expInit
  refine RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
    (l₂ := ([Crt.ldw .x3 .x5 arg2, sth .x3 Crt.sExp, .ldr .x .x3 .x5 Field.q.offset, sth .x3 Crt.sSrc,
      Crt.ldw .x3 .x5 arg2Len, sth .x3 Crt.sI] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun (p : XPub) t => t.gpr .x0 = off p.B p.o ∧ t.gpr .x5 = p.B) [.x0]
      (pins_x0B (fun p : XPub => off p.B p.o)
        fun p s (h : ∃ minv, SubCtx s p.B p.Z p.o p.w p.wx minv) => let ⟨_, hc⟩ := h; hc.x0) (by taint_decide)
      fun p s h => ?_)
    (two_taint [.x0, .x5] (pins_of (fun p r => if r = .x0 then off p.B p.o else p.B) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) (by taint_decide)))
  obtain ⟨_, hc⟩ := h
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B)
    (by brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h1, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hc.x0, h1⟩

/-! ## The products -/

/-- `combine_ok`'s hypotheses. -/
def CombPre (b0 : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (N Xc g : Nat) (b : Nat → Nat), CExpCtx s (off p.B p.o) p.wx mi N Xc ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) N ∧ 1 < N ∧
    word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx < N) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx % N =
      g ^ b d * 2 ^ (64 * p.wx) % N) ∧
    wv s.mem (off p.B p.o) (slot p.wx aOne) p.wx = 1

/-- After `i` buckets below the seventh. -/
def CLoop (b0 : Nat) (p : XPub) (i : Nat) (t : State) : Prop :=
  ∃ (s : State) (mi : BitVec 64) (N Xc g : Nat) (b : Nat → Nat),
    CmbInv s (off p.B p.o) p.wx mi N Xc g b i t ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) N ∧
    word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx < N) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx % N =
      g ^ b d * 2 ^ (64 * p.wx) % N)

theorem cmbBody_ct' (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x3 Crt.sBit, .addImm .x .x3 .x3 b0, sth .x3 Crt.sNib]) hc).isSome = true) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 6 ∧ CLoop b0 q.1 q.2 s) (cmbBody M.mm b0)
      (fun _ _ => True) := by
  unfold cmbBody
  simp only [seqs]
  refine RelCT.seq (two_piece [.x0] (pins_x0B (fun q : XPub × Nat => off q.1.B q.1.o)
      fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0) hT
    fun q s ⟨hi, s₀, mi, N, Xc, g, b, hI, hw, hw', hR, ht, hlt, hb⟩ =>
      cmbStep_steps M hw hw' hR hoff hi ht hlt hb hI (K := fun _ => True) fun _ _ => trivial) ?_
  refine RelCT.seq (two_post (two_map (fun q : XPub × Nat => (q.1, b0 + (6 - q.2))) (fun _ _ h => h.1)
    PublicPower.select_ct) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.1.goodW)
    (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide))) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.1.goodW)
    (M.ct (o := aX) (a := aX) (b := aY) (by unfold MmUse; decide))) fun _ _ h => h.2) ?_
  exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => let ⟨_, hg⟩ := h.1; hg.x0) (by taint_decide)

theorem cmbBody_ct (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 6 ∧ CLoop b0 q.1 q.2 s) (cmbBody M.mm b0)
      (fun _ _ => True) := by
  rcases hoff with rfl | rfl
  · exact cmbBody_ct' M (Or.inl rfl) (by taint_decide)
  · exact cmbBody_ct' M (Or.inr rfl) (by taint_decide)

theorem combine_ct' (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [movi .x3 (b0 + 7), sth .x3 Crt.sNib]) hc).isSome = true) :
    RelCT isa (Two (CombPre b0)) (combine M.mm b0) (fun _ _ => True) := by
  rw [combine_eq]
  refine RelCT.seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  unfold pick
  refine RelCT.seq (RelCT.seq (two_piece [.x0] (pins_x0B (fun p : XPub => off p.B p.o)
      fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.good.x0) hT
    fun p s ⟨mi, N, Xc, g, b, hc, hw, hw', hR, hN, ht, hlt, hb, hone⟩ =>
      combineHead_steps hc hw hw' hoff ht hlt hb (K := fun t => 0 < 6 ∧ CLoop b0 p 0 t) fun t I0 =>
        ⟨by decide, s, mi, N, Xc, g, b, I0, hw, hw', hR, ht, hlt, hb⟩)
    (two_post (two_map (fun p : XPub => (p, b0 + 7)) (fun _ _ h => h.1) PublicPower.select_ct)
      fun _ _ h => h.2)) ?_
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp [Crt.copyArr]) (RelCT.seq (two_post
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h.1.goodW)
      (copyArr_ct (o := aY) (a := Crt.aT) (by decide) (by decide) (by taint_decide))) fun _ _ h => h.2) ?_)
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp) (RelCT.seq (two_post
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h.1.goodW)
      (copyArr_ct (o := aX) (a := Crt.aT) (by decide) (by decide) (by taint_decide))) fun _ _ h => h.2) ?_)
  simp only [seqs]
  refine RelCT.seq (two_post (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => let ⟨_, hg⟩ := h.1; hg.x0)
    (by taint_decide)) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_loop (Φ := CLoop b0) (Ψ := fun p s => GoodW p.ws s) (fun _ => 6) (cmbBody_ct M hoff) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h) (M.ct (o := Crt.aT) (a := aX) (b := aOne) (by unfold MmUse; decide)))
  rintro p i s hi ⟨s₀, mi, N, Xc, g, b, hI, hw, hw', hR, ht, hlt, hb⟩
  exact WP.mono (cmbStep_ok M hw hw' hR hoff hi ht hlt hb hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_nz_count hi hz, fun _ => ⟨s₀, mi, N, Xc, g, b, hI', hw, hw', hR, ht, hlt, hb⟩,
      fun _ => ⟨mi, hI'.ctx.good, Nat.le_refl _⟩⟩

/-- The buckets' product reads them in a fixed order. -/
theorem combine_ct (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) :
    RelCT isa (Two (CombPre b0)) (combine M.mm b0) (fun _ _ => True) := by
  rcases hoff with rfl | rfl
  · exact combine_ct' M (Or.inl rfl) (by taint_decide)
  · exact combine_ct' M (Or.inr rfl) (by taint_decide)

/-! ## The order check -/

/-- `orderCheck_ok`'s hypotheses. -/
def OrdPre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (N Xc : Nat), CExpCtx s (off p.B p.o) p.wx mi N Xc ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- Whether `[aT] = 1` goes into a mask. -/
theorem orderCheck_ct : RelCT isa (Two OrdPre) orderCheck (fun _ _ => True) := by
  unfold orderCheck
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp) (RelCT.seq (two_post (Ψ := OrdPre)
    (two_map (fun p : XPub => p.ws) (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
      (copyArr_ct (o := aX) (a := Crt.aT) (by decide) (by decide) (by taint_decide)))
    fun p s ⟨mi, N, Xc, hc, hw, hw'⟩ => ?_) ?_)
  · have hn := hc.scrT.nowrap
    refine WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aX) (a := Crt.aT)
      (by decide) (by decide) (by decide)) fun u ⟨_, ou, ku⟩ => ?_
    have au : Arrays (off p.B p.o) p.wx [aX] s.mem u.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ou (Nat.le_refl _) (by omega_arith)
    exact ⟨mi, N, Xc, ctx_of_arrays hc au (by decide) (by decide) ku.wr (ku.gpr .x0 (by decide)), hw, hw'⟩
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun (p : XPub) s => s.gpr .x0 = off p.B p.o)
    (two_map (fun p : XPub => p.ws) (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩) oneScan_ct)
    fun p s ⟨mi, N, Xc, hc, hw, hw'⟩ => ?_) ?_
  · exact WP.mono (oneScan_ok hc.good (Nat.le_refl _) hw (by omega_arith)) fun v ⟨_, _, kv⟩ =>
      (kv.gpr .x0 (by decide)).trans hc.good.x0
  · exact x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by unfold Checks.zeroMask; taint_decide)

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # g^x and the mask of g^q = 1: correct, and constant time in x

One run through the body's steps (`power_steps`) gives both: what the body
computes (`power_ok`), and, after each step, what the next step's
constant-time lemma starts from (`power_ct`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The public data: the call's (the secret exponent's pointer and length,
the base's, the workspace, the modulus), the public exponent's pointer and
its bytes, of the secret exponent's length, and a width of whole 64-byte
tiles. -/
structure SPub extends PowerCallPublic where
  qp : Addr
  qb : List Byte
  qlen : qb.length = bytes.len
  wide : 8 ≤ bytes.x.wx
  tiles : bytes.x.wx % 8 = 0

/-- The digits' public data. -/
abbrev SPub.g (p : SPub) : GPub := ⟨p.x, p.bytes.ptr, p.qp, p.qb⟩

/-- The body's steps: after each, what the next step's constant-time lemma
starts from, and then the rest of the run. -/
theorem power_steps (M : Mont) (p : SPub) {s : State}
    (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv)
    (hn : wv s.mem (off p.x.B p.x.o) (slot p.x.wx aN) p.x.wx = p.modulus)
    (hinv : ((word s.mem (off p.x.B p.x.o) (slot p.x.wx aN)).toNat * p.minv.toNat + 1) % 2 ^ 64 = 0)
    {bb xb : List Byte}
    (hb : word s.mem p.x.B (8 * arg) = p.base)
    (hblen : word s.mem p.x.B (8 * argLen) = BitVec.ofNat 64 bb.length) (hbl : bb.length = p.baseLen)
    (hbs : Src s p.x.B p.x.Z p.base bb)
    (he : word s.mem p.x.B (8 * arg2) = p.bytes.ptr)
    (helen : word s.mem p.x.B (8 * arg2Len) = BitVec.ofNat 64 xb.length) (hxl : xb.length = p.bytes.len)
    (hes : Src s p.x.B p.x.Z p.bytes.ptr xb)
    (hq : word s.mem p.x.B Field.q.offset = p.qp) (hqs : Src s p.x.B p.x.Z p.qp p.qb)
    {K : State → Prop} (hK : ∀ t,
      SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
      wv t.mem (off p.x.B p.x.o) (slot p.x.wx aY) p.x.wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE xb) p.modulus ∧
      word t.mem (off p.x.B p.x.o) (8 * Crt.sMaskX) =
        mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE p.qb) p.modulus = 1)) ∧
      ModCtx t (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧
      Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem ∧ Keep mmRegs s t → K t) :
    WP isa (Arithmetic.constants M.mm) s fun u => PowerCallPrepared p.toPowerCallPublic u ∧
      WP isa (Arithmetic.load aX arg argLen) u fun v => Reduced [aR2, aOne] p.toPowerPublic.product v ∧
      WP isa (Arithmetic.encodePower M.mm) v fun e => XCtx p.x e ∧
      WP isa (seqs tableInit) e fun t₁ => (∃ minv, SubCtx t₁ p.x.B p.x.Z p.x.o p.x.w p.x.wx minv) ∧
      WP isa (.block SharedPower.expInit) t₁ fun t₂ => (0 < p.g.groups ∧ GInv p.g 0 t₂) ∧
      WP isa (digits M.mm) t₂ fun t₃ => CombPre 8 p.x t₃ ∧
      WP isa (combine M.mm 8) t₃ fun t₄ => OrdPre p.x t₄ ∧
      WP isa orderCheck t₄ fun t₅ => CombPre 0 p.x t₅ ∧
      WP isa (combine M.mm 0) t₅ fun t₆ => FGood (off p.x.B p.x.o) p.x.wx t₆ ∧
      WP isa (seqs (Crt.copyArr aY Crt.aT)) t₆ K := by
  obtain ⟨⟨⟨⟨⟨B, Z, o, w, wx⟩, xp, len⟩, minv, m, hw2, hwx, hw30, hm, hodd⟩, base, baseLen, hw48, hb1', hbw',
    he1', he2'⟩, qp, qb, hql', hw8, hd⟩ := p
  dsimp only at hc hn hinv hb hblen hbl hbs he helen hxl hes hq hqs hK hw2 hwx hw30 hw48 hb1' hbw' he1' he2' hql' hw8 hd
  obtain hb1 : 1 ≤ bb.length := hbl ▸ hb1'
  obtain hbw : (bb.length + 7) / 8 ≤ wx := hbl ▸ hbw'
  obtain he1 : 1 ≤ xb.length := hxl ▸ he1'
  obtain he2 : xb.length ≤ 1024 := hxl ▸ he2'
  obtain hql : qb.length = xb.length := hql'.trans hxl.symm
  obtain hw' : wx < 2 ^ 30 := by omega_arith
  obtain hm0 : 0 < m := by omega_arith
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * wx)
  have hlo := hc.lo
  have hhi := hc.hi
  have hBn := hc.scr.nowrap
  obtain h384 : 384 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have hqo : Field.q.offset = 264 := rfl
  obtain h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have field {t : State} (hf : Frm (off B o) (workRanges wx) s.mem t.mem) :
      word t.mem B Field.q.offset = qp :=
    (hf.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega_arith) (by omega_arith)
      (by omega_arith)).trans hq
  -- The constants, the base and its Montgomery form.
  refine WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv) fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_
  refine ⟨⟨⟨hcu, hmu, bb, xb, (work_parent hc hfu (by decide)).trans hb,
    (work_parent hc hfu (by decide)).trans hblen, (work_parent hc hfu (by decide)).trans he,
    (work_parent hc hfu (by decide)).trans helen, hbl, hxl, work_source hc hfu hku hbs,
    work_source hc hfu hku hes⟩, huone, hur2⟩, ?_⟩
  refine WP.mono (VG.Proof.Dsa.AArch64.load_ok hcu hw2 hwx hw30 (by decide) (by decide) (by decide)
    ((work_parent hc hfu (by decide)).trans hb) ((work_parent hc hfu (by decide)).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega_arith) hbw) fun v ⟨hcv, hvbase, hfv, hkv⟩ => ?_
  obtain hfa : Arrays (off B o) wx [aX] u.mem v.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hfv (Nat.le_refl _) (Nat.le_refl _)
  have hz := hcu.good.scr.nowrap
  obtain vn := (hfa.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  obtain vi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by omega_arith)]
    exact hmu.inverse
  obtain vone := (hfa.wv_of_not_mem (show aOne < 8 by decide) (by decide) hz).trans huone
  obtain vr2 : wv v.mem (off B o) (slot wx aR2) wx = (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [(hfa.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur2, ← Nat.pow_add,
      show 64 * wx + 64 * wx = 128 * wx by omega_arith]
  refine ⟨⟨⟨hcv.good, vn, vi⟩, fun j hj => ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [vr2]; exact Nat.mod_lt _ hm0
    · dsimp only [PowerPublic.product]
      rw [vone]; exact hm
  refine WP.mono (encodePower_ok M ⟨hcv.good, vn, vi⟩ (Nat.le_refl _) hw2 (by omega_arith) hm hodd hvbase vr2 vone)
    fun e ⟨hme, hex, hey, heone, hfe, hke⟩ => ?_
  obtain hce := arrays_context hcv hfe (by decide) hke
  obtain hfE : Frm (off B o) (workRanges wx) s.mem e.mem :=
    (hfu.trans (arrays_work hfa (by decide))).trans (arrays_work hfe (by decide))
  obtain hkE : Keep mmRegs s e := ((hku.trans hkv).trans hke).mono (by decide)
  obtain cE : CExpCtx e (off B o) wx minv m (wv e.mem (off B o) (slot wx Crt.aXc) wx) :=
    ⟨hme.good, hce.scrT, hme.modulus, hme.inverse, rfl⟩
  refine ⟨⟨minv, m, _, cE, by rw [hex]; exact Nat.mod_lt _ hm0, hw2, hw'⟩, ?_⟩
  -- The buckets' start.
  refine WP.mono (tableInit_ok (g := Spec.Rsa.os2ip bb)
    (ex := Spec.Rsa.os2ip xb) (eq := Spec.Rsa.os2ip qb) cE hw2 hw'
    (by rw [hey]; exact Nat.mod_lt _ hm0) (by rw [hey, Nat.mod_mod])
    (by rw [hex]; exact Nat.mod_lt _ hm0) (by rw [hex, Nat.mod_mod]; rfl))
    fun t₁ ⟨hD₁, harr₁, hhdr₁, hf₁, hk₁⟩ => ?_
  obtain hF₁ := hfE.trans hf₁
  obtain hK₁ : Keep mmRegs s t₁ := (hkE.trans hk₁).mono (by decide)
  obtain hc₁ : SubCtx t₁ B Z o w wx minv := hc.of_frmT hF₁ (workRanges_ok wx) hK₁.wr (hK₁.gpr .x0 (by decide))
  refine ⟨⟨minv, hc₁⟩, ?_⟩
  -- The exponents.
  refine WP.mono (expInit_ok hc₁ (xp := xp) (qp := qp) (L := xb.length)
    ((work_parent hc hF₁ (by decide)).trans he) ((work_parent hc hF₁ (by decide)).trans helen) (field hF₁))
    fun t₂ ⟨hm₂, hk₂⟩ => ?_
  obtain o₂ : Outside (off B o) 136 120 t₁.mem t₂.mem := by
    rw [hm₂]
    exact ((fn_outside _ _ _ (by decide) (by decide)).trans (fn_outside _ _ _ (by decide) (by decide))).trans
      (fn_outside _ _ _ (by decide) (by decide))
  obtain hF₂ := hF₁.trans (fn_work o₂)
  obtain hK₂ : Keep mmRegs s t₂ := (hK₁.trans hk₂).mono (by decide)
  obtain hD₂ := hD₁.of_fn o₂ (by
    rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]) hk₂.wr (hk₂.gpr .x0 (by decide))
  have hn₂ := hD₂.ctx.scrT.nowrap
  obtain hc₂ : SubCtx t₂ B Z o w wx minv := hc.of_frmT hF₂ (workRanges_ok wx) hK₂.wr (hK₂.gpr .x0 (by decide))
  obtain sx := work_source hc hF₂ hK₂ hes
  obtain sq := work_source hc hF₂ hK₂ hqs
  obtain hx : Exps t₂ (off B o) wx xp qp xb qb :=
    ⟨sx.rd, sx.val, src_out hc₂ sx, sq.rd, sq.val, src_out hc₂ sq, hql⟩
  obtain G0 : GroupsInv t₂ (off B o) wx minv m (Spec.Rsa.os2ip bb) xp qp xb qb 0 0 t₂ :=
    ⟨hD₂, by rw [Nat.pow_zero, Nat.div_one, Nat.mul_zero, Nat.sub_zero, pre_len],
      by rw [Nat.pow_zero, Nat.div_one, Nat.mul_zero, Nat.sub_zero, ← hql, pre_len],
      by rw [hm₂, word_writeW_self, Nat.mul_zero, Nat.sub_zero],
      by rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
      by rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
      fun _ _ _ _ _ _ _ => rfl, Frm.refl _ _ _, Keep.refl _ _⟩
  refine ⟨⟨show 0 < (qb.length + 2) / 3 by omega_arith, t₂, minv, m, Spec.Rsa.os2ip bb, xb, 0, G0, hx, hw8, hw', hd,
    hR, by omega_arith⟩, ?_⟩
  refine WP.mono (digits_ok M hw8 hw' hd hR hx he1 (by omega_arith) G0) fun t₃ ⟨k, hG⟩ => ?_
  obtain hL0 : xb.length - 3 * ((xb.length + 2) / 3) = 0 := by omega_arith
  obtain hxk : Spec.Rsa.os2ip xb / 8 ^ k = 0 := by rw [hG.xr, hL0, pre_zero]
  obtain hqk : Spec.Rsa.os2ip qb / 8 ^ k = 0 := by rw [hG.qr, hL0, pre_zero]
  obtain hone₃ : wv t₃.mem (off B o) (slot wx aOne) wx = 1 := by
    rw [hG.arr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      fn_arr o₂ hn₂ (by decide), harr₁ _ (by decide)]
    exact heone
  -- `g^q`, and whether it is 1.
  obtain lt₃ : ∀ d < 8, d ≠ 0 → wv t₃.mem (off B o) (slot wx (8 + (8 + d))) wx < m :=
    fun d hd' _ => hG.dig.lt (8 + d) (by omega_arith)
  refine ⟨⟨minv, m, _, Spec.Rsa.os2ip bb, bexp (Spec.Rsa.os2ip qb) k, hG.dig.ctx, hw2, hw', hR, hm, hG.dig.tab,
    lt₃, fun d hd' hd0 => hG.dig.qs d hd' hd0, hone₃⟩, ?_⟩
  refine WP.mono (combine_ok M (b0 := 8) (b := bexp (Spec.Rsa.os2ip qb) k) (g := Spec.Rsa.os2ip bb)
    hG.dig.ctx hw2 hw' hR hm (Or.inr rfl) hG.dig.tab lt₃
    (fun d hd' hd0 => hG.dig.qs d hd' hd0) hone₃) fun t₄ ⟨hc₄, hT₄, c₄⟩ => ?_
  rw [bexp_sum_all hqk] at hT₄
  refine ⟨⟨minv, m, _, hc₄, hw2, hw'⟩, ?_⟩
  refine WP.mono (orderCheck_ok hc₄ hw2 hw') fun t₅ ⟨hc₅, hmask₅, hent₅, harr₅, hhdr₅, hf₅, hk₅⟩ => ?_
  -- `g^x`.
  obtain tab₅ := (hhdr₅ _ (by decide) (by decide)).trans
    ((c₄.hdr _ (by decide) (by decide) (by decide)).trans hG.dig.tab)
  obtain lt₅ : ∀ d < 8, d ≠ 0 → wv t₅.mem (off B o) (slot wx (8 + (0 + d))) wx < m := fun d hd' _ => by
    rw [Nat.zero_add, hent₅ d (by omega_arith), c₄.ent d (by omega_arith)]
    exact hG.dig.lt d (by omega_arith)
  obtain xs₅ : ∀ d < 8, d ≠ 0 → wv t₅.mem (off B o) (slot wx (8 + (0 + d))) wx % m =
      Spec.Rsa.os2ip bb ^ bexp (Spec.Rsa.os2ip xb) k d * 2 ^ (64 * wx) % m := fun d hd' _ => by
    rw [Nat.zero_add, hent₅ d (by omega_arith), c₄.ent d (by omega_arith)]
    exact hG.dig.xs d hd'
  obtain one₅ := (harr₅ _ (by decide) (by decide)).trans
    ((c₄.arr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hone₃)
  refine ⟨⟨minv, m, _, Spec.Rsa.os2ip bb, bexp (Spec.Rsa.os2ip xb) k, hc₅, hw2, hw', hR, hm, tab₅, lt₅, xs₅,
    one₅⟩, ?_⟩
  refine WP.mono (combine_ok M (b0 := 0) (b := bexp (Spec.Rsa.os2ip xb) k) (g := Spec.Rsa.os2ip bb)
    hc₅ hw2 hw' hR hm (Or.inl rfl) tab₅ lt₅ xs₅ one₅) fun t₆ ⟨hc₆, hT₆, c₆⟩ => ?_
  rw [bexp_sum_all hxk] at hT₆
  refine ⟨⟨minv, hc₆.good⟩, ?_⟩
  refine WP.mono (copyArr_ok hc₆.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := Crt.aT)
    (by decide) (by decide) (by decide)) fun t ⟨hY, oY, kY⟩ => hK t ?_
  obtain aY7 : Arrays (off B o) wx [aY] t₆.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) oY (Nat.le_refl _) (by omega_arith)
  obtain hct := ctx_of_arrays hc₆ aY7 (by decide) (by decide) kY.wr (kY.gpr .x0 (by decide))
  obtain hF : Frm (off B o) (workRanges wx) s.mem t.mem :=
    hF₂.trans (hG.frm.trans (c₄.frm.trans (hf₅.trans (c₆.frm.trans (arrays_work aY7 (by decide))))))
  obtain hK' : Keep mmRegs s t :=
    (((((hK₂.trans hG.keep).trans c₄.keep).trans hk₅).trans c₆.keep).trans kY).mono (by decide)
  refine ⟨hc.of_frmT hF (workRanges_ok wx) hK'.wr (hK'.gpr .x0 (by decide)), ?_, ?_,
    ⟨hct.good, hct.n, hct.inv⟩, hF, hK'⟩
  · rw [hY, hT₆, VG.Proof.Dsa.powMod_eq]
    rfl
  · rw [aY7.hslot (by decide), c₆.hdr _ (by decide) (by decide) (by decide), hmask₅, hT₄,
      VG.Proof.Dsa.powMod_eq]
    rfl

/-- `Y := g^x mod m` and the mask of `g^q mod m = 1` into `sMaskX`, in the
workspace of the modulus `m`: for `g` and `x` the call's operands, and `q`
the domain's, of `x`'s length. -/
theorem power_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw8 : 8 ≤ wx) (hw48 : wx ≤ 48) (hd : wx % 8 = 0) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {base xp qp : Addr} {bb xb qb : List Byte}
    (hb : word s.mem B (8 * arg) = base) (hblen : word s.mem B (8 * argLen) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z base bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (he : word s.mem B (8 * arg2) = xp) (helen : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 xb.length)
    (hes : Src s B Z xp xb) (he1 : 1 ≤ xb.length) (he2 : xb.length ≤ 1024)
    (hq : word s.mem B Field.q.offset = qp) (hqs : Src s B Z qp qb) (hql : qb.length = xb.length) :
    WP isa (power M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE xb) m ∧
      word t.mem (off B o) (8 * Crt.sMaskX) =
        mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE qb) m = 1)) ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain h := power_steps M
    { bytes := ⟨⟨B, Z, o, w, wx⟩, xp, xb.length⟩, minv := minv, modulus := m, lower := (show 2 ≤ wx by omega_arith),
      fits := hwx,
      upper := hw30, greater := hm, odd := hodd, base := base, baseLen := bb.length, width48 := hw48,
      basePositive := hb1, baseFits := hbw, expPositive := he1, expLimit := he2, qp := qp, qb := qb, qlen := hql,
      wide := hw8, tiles := hd } hc hn hinv hb hblen rfl hbs he helen rfl hes hq hqs fun _ h => h
  rw [power_eq]
  refine wp_seqs_append (by simp) (by simp [tableInit]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono h fun _ h => WP.seq (WP.mono h.2 fun _ h => WP.mono h.2 fun _ h => ?_))
  refine wp_seqs_append (by simp [tableInit]) (by simp) (WP.mono h.2 fun _ h => ?_)
  refine wp_seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  exact WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h =>
    WP.seq (WP.mono h.2 fun _ h => WP.mono h.2 fun _ h => h.2))))

/-! ## Constant time -/

/-- The body's hypotheses: the call's, and the domain's `q`. -/
def SPre (p : SPub) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ word s.mem p.x.B Field.q.offset = p.qp ∧ Src s p.x.B p.x.Z p.qp p.qb

/-- The body leaks the same in runs with the same workspace, pointers,
lengths, modulus and public exponent, whatever the base and the secret
exponent. -/
theorem power_ct (M : Mont) : RelCT isa (Two SPre) (power M.mm) (fun _ _ => True) := by
  rw [power_eq]
  refine RelCT.seqs_append (by simp) (by simp [tableInit]) ?_
  simp only [seqs]
  refine RelCT.seq (RelCT.seq (two_post (two_map (fun p : SPub => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2.1, p.width48, p.greater, p.odd⟩) (constants_ct M))
    fun p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hq, hqs⟩ =>
      power_steps M p hc hm.modulus hm.inverse hp hl hbl hb hep hel helen he hq hqs (K := fun _ => True)
        fun _ _ => trivial)
    (RelCT.seq (two_post (two_map (fun p : SPub => (⟨p.x, p.base, p.baseLen⟩ : BPub)) (fun p s h => ?_)
        (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
      fun _ _ h => h.2)
    (two_post (two_map (fun p : SPub => p.toPowerPublic.product) (fun _ _ h => h.1) (encodePower_ct M))
      fun _ _ h => h.2))) ?_
  · obtain ⟨⟨⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩, _⟩, _⟩ := h
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    obtain hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  refine RelCT.seqs_append (by simp [tableInit]) (by simp) (RelCT.seq (two_post
    (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) tableInit_ct) fun _ _ h => h.2) ?_)
  refine RelCT.seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  refine RelCT.seq (R := Two fun (p : SPub) s => FGood (off p.x.B p.x.o) p.x.wx s ∧
      WP isa (seqs (Crt.copyArr aY Crt.aT)) s fun _ => True)
    (RelCT.seq (two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) expInit_ct)
      fun _ _ h => h.2) ?_) ?last
  refine RelCT.seq (two_post (two_map (fun p : SPub => p.g) (fun _ _ h => h.1) (digits_ct M))
    fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) (combine_ct M (Or.inr rfl)))
    fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) orderCheck_ct)
    fun _ _ h => h.2) ?_
  exact two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) (combine_ct M (Or.inl rfl)))
    fun _ _ h => h.2
  case last =>
    exact two_map (fun p : SPub => p.x.ws) (fun _ _ h => h.1.goodW)
      (copyArr_ct (o := aY) (a := Crt.aT) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # The shared exponentiation as a call from the parent workspace

`SharedPower.pow` binds its operands, enters the workspace of `p`, computes
`g^x` and the mask of `g^q = 1`, writes `g^x` out, returns to the parent
workspace, and there takes the mask into the acceptance mask. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.AArch64

/-- The call up to its return: besides what `call3_ok` says of it, the mask
of `g^q = 1` is in the child's `sMaskX`, and the acceptance mask is as it was. -/
theorem powCall_ok (M : Mont) {s : State} {B : Addr} {Z w wx m k : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B pWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ pWorkspace) (hhi : pWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw8 : 8 ≤ wx) (hw48 : wx ≤ 48) (hd8 : wx % 8 = 0) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb qb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (hqs : Src s B Z (word s.mem B Field.q.offset) qb) (hql : qb.length = bb.length)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx) (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (seqs (([.block (Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
      Core.operand result resultLen output ++ Core.enter pWorkspace), SharedPower.power M.mm] : List (Prog isa)) ++
        Core.finish)) s fun t =>
      (Good t B Z w parentMinv ∧ ChildReady t.mem B pWorkspace wx m minv ∧
        Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
          Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m) ∧
        CallFrame B pWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t) ∧
      word t.mem B (pWorkspace + 8 * Crt.sMaskX) =
        mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb) m = 1)) ∧
      word t.mem B Field.mask.offset = word s.mem B Field.mask.offset := by
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hn := hg.scr.nowrap
  have hqo : Field.q.offset = 264 := rfl
  have hmo : Field.mask.offset = 360 := rfl
  have hpw : pWorkspace = 3456 := rfl
  have hsm : Crt.sMaskX = 24 := rfl
  -- What the body gives, at any state the call's head leaves.
  have body : ∀ u, SubCtx u B Z pWorkspace w wx minv → ChildReady u.mem B pWorkspace wx m minv →
      Arguments u.mem s.mem B a b output → Frm B argumentRanges s.mem u.mem → Keep coreRegs s u →
      WP isa (SharedPower.power M.mm) u fun v => SubCtx v B Z pWorkspace w wx minv ∧
        wv v.mem (off B pWorkspace) (slot wx aY) wx =
          Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m ∧
        word v.mem (off B pWorkspace) (8 * Crt.sMaskX) =
          mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb) m = 1)) ∧
        ModCtx v (off B pWorkspace) (slot wx 8) wx minv m ∧
        Frm (off B pWorkspace) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v := by
    intro u hc hchild hargs hf hk
    have hqu : word u.mem B Field.q.offset = word s.mem B Field.q.offset :=
      hf.word_eq (fun r hr => by
        simp only [argumentRanges, List.mem_singleton] at hr; subst hr; right; omega_using [hqo])
        (by omega_using [hqo])
    exact power_ok M hc hw8 hw48 hd8 hwx hw30 hm hodd hchild.modulus hchild.inverse
      hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
      hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hb2
      hqu (arguments_source hf hk hz hqs) hql
  refine wp_and (call3_ok hg child hZ hlo hhi (by decide) a b output ha hb houtp hl hk1 hk' hkw hout hprefix
    fun u hc hchild hargs hf hk => WP.mono (body u hc hchild hargs hf hk)
      fun v ⟨hcv, hv, _, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩) ?_
  -- The same run again, for the two words.
  change WP isa (.seq (.block _) (.seq (SharedPower.power M.mm) (seqs Core.finish))) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (arguments_ok hg child hZ (by omega_using [hlo, hslot]) (by omega_using [hhi]) a b output ha hb houtp)
    fun u ⟨hgu, hchild, hargs, hfields, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hchild.header hlo hhi (by decide)) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hfv : Frm B argumentRanges s.mem v.mem := by rw [hmem]; exact hf
  have hav : Arguments v.mem s.mem B a b output := by rw [hmem]; exact hargs
  have hchv : ChildReady v.mem B pWorkspace wx m minv := by rw [hmem]; exact hchild
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.seq (WP.mono (body v hcv hchv hav hfv hks) fun z ⟨hcz, _, hmaskz, _, hfz, hkz⟩ => ?_)
  refine WP.mono (finish_ok (parentMinv := parentMinv) hcz
    ((work_parent hcv hfz (by decide)).trans (by rw [hmem]; exact hgu.hdr.hminv))
    ((work_parent hcv hfz (by decide)).trans hav.2.2.2.2.1)
    ((work_parent hcv hfz (by decide)).trans (hav.2.2.2.2.2.trans hl)) hk1 hk' hkw
    (fun j hj => by rw [hkz.wr, hks.wr]; exact hout j hj) hprefix) fun y ⟨_, _, hyword, _, _⟩ => ⟨?_, ?_⟩
  · rw [hyword _ (by omega_using [hhi, h256, hpw, hsm]), ← word_off]
    exact hmaskz
  · rw [hyword _ (by omega_using [hZ, hmo, hpw]),
      hfz.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega_using [hn, hhi]) (by omega_using [hpw])
        (by omega_using [hmo, hpw]), hmem]
    exact hfields .mask

/-- The whole call, in DSA's execution context: `g^x` at the local `d`, and
`g^q = 1` in the acceptance mask. -/
theorem readySharedPow_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 1 < L.modulus) (hodd : L.modulus % 2 = 1)
    (a b : Operand) {ba bb qb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (hqs : Src s L.base activeBytes (word s.mem L.base Field.q.offset) qb) (hql : qb.length = bb.length)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ L.pWords)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.pLen ≤ usedBytes)
    {valid : Bool} (hmask : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (SharedPower.pow M.mm a b ⟨.local d, .pLen⟩) s fun t => ∃ u,
      CallResult L .p d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) L.modulus) s u ∧
      CheckEffect L (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb) L.modulus = 1) && valid)
        u t := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := ModulusSide.p.bounds L
  have hw8 : 8 ≤ L.pWords ∧ L.pWords % 8 = 0 := by
    rcases L.lengths with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [ExecutionLayout.pWords, h1] <;> decide
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 16
    have : usedBytes < 2 ^ 16 := by decide
    omega_using [hend, this]
  unfold SharedPower.pow
  refine wp_seqs_append (by simp) (by simp) (WP.mono (powCall_ok M h.parent (h.child .p) (by decide) hlo hhi
    hw8.1 hw48 hw8.2 hw48 (by decide) hm hodd a b ⟨.local d, .pLen⟩ ha hb hdp has hbs hqs hql ha1 haw hb1 hb2
    (h.length .p) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_)
  intro u ⟨⟨hp, hc, hv, hf, hk⟩, hq1, hmu⟩
  have hru : Ready L u := h.afterCall .p hp hc hf hk hd hend
  change WP isa (.block _) u _
  rw [WP.block_append_iff]
  have hx0 := hp.x0
  have hld := hp.scr.ld (d := pWorkspace + 8 * Crt.sMaskX) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun v => v.gpr .x3 = word u.mem L.base (pWorkspace + 8 * Crt.sMaskX) ∧
    v.mem = u.mem) (by brun [hx0, hld]) rfl rfl rfl) fun v ⟨⟨h3, hvm⟩, hkv⟩ => ?_
  have hgv : Good v L.base activeBytes outerWords 0 :=
    ⟨hp.scr.congr hkv.wr, (hkv.gpr .x0 (by decide)).trans hp.x0, hvm ▸ hp.hdr⟩
  have hrv : Ready L v := ⟨hgv, hru.scratch.congr hkv.wr, by rw [hvm]; exact hru.fields,
    by rw [hvm]; exact hru.pChild, by rw [hvm]; exact hru.qChild⟩
  refine WP.mono (accumulate_context (a := decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE qb)
      L.modulus = 1)) (b := valid) hgv hrv.pChild (by decide) (by decide)
      (Nat.le_trans (Nat.le_add_right _ _) hhi) (h3.trans hq1) (by rw [hvm]; exact hmu.trans hmask))
    fun t ⟨hgt, _, hmt, hft, hkt⟩ => ?_
  have hkc : Keep coreRegs v t := hkt.mono (by decide)
  have hkuv : Keep coreRegs u v := hkv.mono (by decide)
  have hfu : Outside L.base Field.mask.offset 8 u.mem t.mem := by rw [← hvm]; exact hft
  exact ⟨u, ⟨hru, hv, hf, hk⟩, hrv.afterMask hgt hft hkc, hmt,
    hfu.mono (by decide) (by decide), (hkuv.trans hkc).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.SharedPower
