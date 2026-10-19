module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Ends
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Batch
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Divstep.Alg

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps is sound modulo `p = 2²⁵⁵ - 19`

Untrusted: everything here is checked by Lean. `init` sets up the batches'
invariant (`Inv.init_ok`), each of the ten batches keeps it (`Inv.batch_ok`,
`loop_ok`), and `finish` leaves `±u` by the sign of `f` (`Inv.finish_ok`).
After 590 divsteps from
`(1, p, x)`, `g = 0` and `|f| = gcd(p, x)` (`divsteps_590`), which is `1` for
`0 < x < p` as `p` is prime (`Ed25519.prime_field`); so `x u ≡ f = ±1`, and
`±u` is `x⁻¹ = x^(p - 2)`. This module alone imports the algebra that takes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Inv VG.Spec.X25519
open VG.Proof.Divstep (divsteps divsteps_590)
open VG.Proof.Ed25519.Word64
open VG.Proof.Mont.AArch64 (KeepRegs Keeps.regs)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (G U V TF TG TU TV DSAVE batch init finish)
open VG.Impl.Ed25519.AArch64.Divstep renaming F → oF

variable {large : Bool}

/-- A batch: the invariant one batch on, and the counter one down. Its divsteps are `dsM`
(`pwords_ok`), its rows the matrix's combinations, shifted or reduced (`outs_ok`), so
`step_inv` applies. It writes only bytes 192 to 487. -/
theorem batch_ok {s : State} {base : Addr} (hs : Scr s base large) {x i : Nat} (hx : x < P)
    (hi : i < 10)
    (h : RInv x i (word s.mem base DSAVE) (fe s.mem base oF) (fe s.mem base G) (fe s.mem base U)
      (fe s.mem base V))
    (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block batch) s fun t =>
      RInv x (i + 1) (word t.mem base DSAVE) (fe t.mem base oF) (fe t.mem base G) (fe t.mem base U)
        (fe t.mem base V) ∧
      t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧
      Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  have _hmin := workSize_ge large
  have _hcap := workSize_le large
  obtain ⟨hD, hF, hG, hFl, hGl, hUl, hVl, _, _, _⟩ := id h
  have hd30 : |(dsI x i).1| ≤ 2 ^ 30 := by
    have := dsI_d x i
    have : (59 * i : Int) ≤ 59 * 9 := by exact_mod_cast (by omega : 59 * i ≤ 59 * 9)
    linarith
  obtain ⟨bu, bv, bq, br⟩ := dsM_bnd x i
  simp only [batch, List.append_assoc]
  -- the divsteps
  rw [WP.block_append_iff]
  refine WP.mono (lds3_ok hs) fun a ⟨a1, a2, a3, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.pwords_ok a (f := (dsI x i).2.1) (g := (dsI x i).2.2)
    hd30 (dsI_odd x i).2 (a1.trans hD)
    (by rw [a2]; exact low_rel hF) (by rw [a3]; exact low_rel hG))
    fun b ⟨b1, b4, b5, b6, b7, kb⟩ => ?_
  have hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st_ok hsb (d := DSAVE) (by decide) (by simp only [DSAVE]; omega) .x1)
    fun c ⟨mc, kc⟩ => ?_
  have hsc : Scr c base large := ⟨(kc.gpr _ (by decide)).trans hsb.x0, kc.wr ▸ hsb.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (mat_ok c) fun d ⟨d12, d4, d14, d5, d15, d6, d16, d7, d17, d13, d19, kd⟩ => ?_
  have hsd : Scr d base large := hsc.of_keeps kd (by decide)
  have gc : ∀ r, c.gpr r = b.gpr r := fun r => kc.gpr r (by simp)
  have md : MatRegs (dsM x i) d := ⟨d12, by rw [d4, gc, b4], by rw [d14, gc, b4], by rw [d5, gc, b5],
    by rw [d15, gc, b5], by rw [d6, gc, b6], by rw [d16, gc, b6], by rw [d7, gc, b7],
    by rw [d17, gc, b7], by rw [d13, gc, gc, b4, b5], by rw [d19, gc, gc, b6, b7]⟩
  -- the memory the rows read
  have mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  have mdm : d.mem = s.mem.writeW (off base DSAVE) (BitVec.ofInt 64 (dsM x i).d) := by
    rw [kd.mem, mc, mb, b1]
  have od : Outside base 480 8 s.mem d.mem := by
    rw [mdm]; exact writeW_outside _ _ _ (by decide)
  have fd : ∀ o, o + 32 ≤ 480 → fe d.mem base o = fe s.mem base o := fun o ho =>
    od.fe (Or.inl ho) (by omega)
  -- the rows
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hsd true (t := TF) (xo := oF) (yo := G) (by decide) (by decide) md.z
    (by rw [md.u]; exact absW_le bu) (by rw [md.v]; exact absW_le bv)
    ⟨by decide, by simp only [TF]; omega⟩ ⟨by decide, by simp only [oF]; omega⟩
    ⟨by decide, by simp only [G]; omega⟩ (by decide) (by decide)) fun e1 ⟨r1, o1, k1⟩ => ?_
  have hs1 : Scr e1 base large := ⟨(k1.gpr _ (by decide)).trans hsd.x0, k1.wr ▸ hsd.wr, hs.nowrap⟩
  have m1 := md.keep k1
  rw [md.u, md.su, md.v, md.sv', md.c0] at r1
  have hWF := rowF_rel (m := d.mem) (m' := e1.mem) (base := base) (t := TF) (xo := oF) (yo := G) bu bv r1
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs1 true (t := TG) (xo := oF) (yo := G) (by decide) (by decide) m1.z
    (by rw [m1.q]; exact absW_le bq) (by rw [m1.r]; exact absW_le br)
    ⟨by decide, by simp only [TG]; omega⟩ ⟨by decide, by simp only [oF]; omega⟩
    ⟨by decide, by simp only [G]; omega⟩ (by decide) (by decide)) fun e2 ⟨r2, o2, k2⟩ => ?_
  have hs2 : Scr e2 base large := ⟨(k2.gpr _ (by decide)).trans hs1.x0, k2.wr ▸ hs1.wr, hs.nowrap⟩
  have m2 := m1.keep k2
  rw [m1.q, m1.sq, m1.r, m1.sr, m1.c1] at r2
  have hWG := rowF_rel (m := e1.mem) (m' := e2.mem) (base := base) (t := TG) (xo := oF) (yo := G) bq br r2
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs2 false (t := TU) (xo := U) (yo := V) (by decide) (by decide) m2.z
    (by rw [m2.u]; exact absW_le bu) (by rw [m2.v]; exact absW_le bv)
    ⟨by decide, by simp only [TU]; omega⟩ ⟨by decide, by simp only [U]; omega⟩
    ⟨by decide, by simp only [V]; omega⟩ (by decide) (by decide)) fun e3 ⟨r3, o3, k3⟩ => ?_
  have hs3 : Scr e3 base large := ⟨(k3.gpr _ (by decide)).trans hs2.x0, k3.wr ▸ hs2.wr, hs.nowrap⟩
  have m3 := m2.keep k3
  rw [m2.u, m2.su, m2.v, m2.sv', m2.c0] at r3
  have hWU := rowU_rel (m := e2.mem) (m' := e3.mem) (base := base) (t := TU) (xo := U) (yo := V) bu bv r3
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs3 false (t := TV) (xo := U) (yo := V) (by decide) (by decide) m3.z
    (by rw [m3.q]; exact absW_le bq) (by rw [m3.r]; exact absW_le br)
    ⟨by decide, by simp only [TV]; omega⟩ ⟨by decide, by simp only [U]; omega⟩
    ⟨by decide, by simp only [V]; omega⟩ (by decide) (by decide)) fun e4 ⟨r4, o4, k4⟩ => ?_
  have hs4 : Scr e4 base large := ⟨(k4.gpr _ (by decide)).trans hs3.x0, k4.wr ▸ hs3.wr, hs.nowrap⟩
  have m4 := m3.keep k4
  rw [m3.q, m3.sq, m3.r, m3.sr, m3.c1] at r4
  have hWV := rowU_rel (m := e3.mem) (m' := e4.mem) (base := base) (t := TV) (xo := U) (yo := V) bq br r4
  -- the shifts, the reductions and the counter
  have cnt4 : e4.gpr .x20 = BitVec.ofNat 64 (10 - i) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide),
      kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hc]
  refine WP.mono (outs_ok hs4 m4.z hi cnt4) fun t ⟨tF, tG, tU, tV, t20, tD, ot, kt⟩ => ?_
  -- what the rows read, as it was in `s`
  have f1 : ∀ o, o + 32 ≤ TF → fe e1.mem base o = fe s.mem base o := fun o ho => by
    rw [o1.fe (Or.inl ho) (by simp only [TF] at ho; omega), fd o (by simp only [TF] at ho; omega)]
  have f2 : ∀ o, o + 32 ≤ TF → fe e2.mem base o = fe s.mem base o := fun o ho => by
    rw [o2.fe (Or.inl (by simp only [TF, TG] at ho ⊢; omega)) (by simp only [TF] at ho; omega), f1 o ho]
  rw [f1 _ (by decide), f1 _ (by decide), hF, hG] at hWG
  rw [fd _ (by decide), fd _ (by decide), hF, hG] at hWF
  have f3 : ∀ o, o + 32 ≤ TF → fe e3.mem base o = fe s.mem base o := fun o ho => by
    rw [o3.fe (Or.inl (by simp only [TF, TU] at ho ⊢; omega)) (by simp only [TF] at ho; omega), f2 o ho]
  rw [f2 _ (by decide), f2 _ (by decide)] at hWU
  rw [f3 _ (by decide), f3 _ (by decide)] at hWV
  -- the rows where the shifts and reductions read them
  have vF : val5 e4.mem base TF = val5 e1.mem base TF := by
    rw [val5_out o4 (by decide) (by decide), val5_out o3 (by decide) (by decide),
      val5_out o2 (by decide) (by decide)]
  have vG : val5 e4.mem base TG = val5 e2.mem base TG := by
    rw [val5_out o4 (by decide) (by decide), val5_out o3 (by decide) (by decide)]
  have vU : red5 e4.mem base TU = red5 e3.mem base TU := redV_out o4 (by decide) (by decide)
  have hU := redV_cong _ _ _ _ _ hWU (sum_bnd bu bv hUl hVl)
  have hV := redV_cong _ _ _ _ _ hWV (sum_bnd bq br hUl hVl)
  have hR := step_inv hx h hWF hWG hU (Nat.mod_lt _ (by decide)) hV (Nat.mod_lt _ (by decide))
  have dD : word t.mem base DSAVE = BitVec.ofInt 64 (dsM x i).d := by
    rw [tD, o4.word (by decide) (by decide), o3.word (by decide) (by decide),
      o2.word (by decide) (by decide), o1.word (by decide) (by decide), mdm, word_writeW_self]
  refine ⟨?_, t20, ?_, ?_⟩
  · rw [dD, tF, tG, tU, tV, vF, vG, vU]
    exact hR
  · exact ((((od.mono (by decide) (by decide)).trans (o1.mono (by decide) (by decide))).trans
      (o2.mono (by decide) (by decide))).trans ((o3.mono (by decide) (by decide)).trans
      (o4.mono (by decide) (by decide)))).trans ot
  · exact ((((Keeps.regs ka).mono (by decide)).trans ((Keeps.regs kb).mono (by decide))).trans
      ((kc.mono (by decide)).trans ((Keeps.regs kd).mono (by decide)))).trans
      ((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
        ((k3.mono (by decide)).trans (k4.mono (by decide)))).trans kt)

/-- The ten batches. -/
theorem loop_ok {s : State} {base : Addr} (hs : Scr s base large) {x : Nat} (hx : x < P)
    (h : RInv x 0 (word s.mem base DSAVE) (fe s.mem base oF) (fe s.mem base G) (fe s.mem base U)
      (fe s.mem base V))
    (hc : s.gpr .x20 = BitVec.ofNat 64 10) :
    WP isa (.loop (.block batch) (.nonzero .x .x20)) s fun t =>
      RInv x 10 (word t.mem base DSAVE) (fe t.mem base oF) (fe t.mem base G) (fe t.mem base U)
        (fe t.mem base V) ∧ Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  refine WP.loop (M := isa) (fun k t => 1 ≤ k ∧ k ≤ 10 ∧
    RInv x (10 - k) (word t.mem base DSAVE) (fe t.mem base oF) (fe t.mem base G) (fe t.mem base U)
      (fe t.mem base V) ∧ t.gpr .x20 = BitVec.ofNat 64 k ∧ Outside base 192 296 s.mem t.mem ∧
    KeepRegs batchRegs s t) ?_ 10 s ⟨by decide, le_rfl, by exact h, hc, Outside.refl _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  intro k t ⟨hk, hk10, ht, tc, tO, tk⟩
  refine WP.mono (batch_ok (scr_of hs tk (by decide)) hx (i := 10 - k) (by omega) ht
    (by rw [tc, show 10 - (10 - k) = k by omega])) fun u ⟨ui, uc, uO, uk⟩ => ?_
  rw [show 10 - (10 - k + 1) = k - 1 by omega] at uc
  have hev : isa.eval (.nonzero .x .x20) u = some (BitVec.ofNat 64 (k - 1) != 0) := by
    simp [eval, read_x, uc]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inl ⟨by rw [hev]; rfl, ?_, tO.trans uO, tk.trans uk⟩
    simpa using ui
  · refine .inr ⟨?_, k - 1, by omega, by omega, by omega,
      by rw [show 10 - (k - 1) = 10 - k + 1 by omega]; exact ui, uc, tO.trans uO, tk.trans uk⟩
    rw [hev]
    apply congrArg some
    apply bne_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k - 1 < 2 ^ 64),
      show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega


theorem toZ_toFe (n : Nat) : VG.Proof.Ed25519.toZ (VG.Proof.X25519.toFe n) = (n : ZMod P) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  rfl

theorem sound_eq {x U R : Nat} (hx : x < P)
    (hcu : 2 ^ 590 * (dsI x 10).2.1 ≡ x * 2 ^ 590 * U [ZMOD P])
    (hz : x = 0 → (U : Int) ≡ 0 [ZMOD P])
    (hR : (R : Int) % P = (if (dsI x 10).2.1 < 0 then -(U : Int) else U) % P) :
    VG.Proof.X25519.toFe R = VG.Proof.X25519.invert (VG.Proof.X25519.toFe x) := by
  rw [VG.Proof.X25519.invert_eq, ← VG.Proof.Ed25519.toZ_inj, VG.Proof.Ed25519.toZ_pow, toZ_toFe,
    toZ_toFe]
  have hRz := (ZMod.intCast_eq_intCast_iff' _ _ _).2 hR
  by_cases h0 : x = 0
  · have hU := (ZMod.intCast_eq_intCast_iff _ _ _).2 (hz h0)
    push_cast at hU hRz
    rw [h0]
    simp only [Nat.cast_zero]
    rw [zero_pow (by simp [P]), hRz]
    split <;> simp [hU]
  · -- 590 divsteps end with `g = 0` and `f = ±1`.
    have hdone := divsteps_590 (f := (P : Int)) (g := (x : Int)) P_odd (by positivity)
      (by exact_mod_cast hx.le) (by rw [P_val]; norm_num) (n := 590) le_rfl
    have hcop : Int.gcd (P : Int) (x : Int) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime h0 hx VG.Proof.Ed25519.prime_field
    have hs : dsI x 10 = divsteps 590 (1, (P : Int), (x : Int)) := rfl
    rw [hs] at hcu hRz
    generalize (divsteps 590 (1, (P : Int), (x : Int))).2.1 = f at hdone hcu hRz
    rw [hcop] at hdone
    have hf : f = 1 ∨ f = -1 := by omega
    have hv := v0_spec.trans (by decide : (1 : Int) = 1 % P)
    generalize (2 : Int) ^ 590 = Ki at hcu hv
    have hc := (ZMod.intCast_eq_intCast_iff _ _ _).2 hcu
    have k := (ZMod.intCast_eq_intCast_iff' _ _ _).2 hv
    push_cast at hc k
    generalize (Ki : ZMod P) = K at hc k
    -- `f = x U`
    have hfu : (f : ZMod P) = x * U := by
      calc (f : ZMod P) = (f : ZMod P) * (K * Impl.Ed25519.AArch64.Divstep.v0) := by rw [k, mul_one]
        _ = K * f * Impl.Ed25519.AArch64.Divstep.v0 := by ring
        _ = x * K * U * Impl.Ed25519.AArch64.Divstep.v0 := by rw [hc]
        _ = x * U * (K * Impl.Ed25519.AArch64.Divstep.v0) := by ring
        _ = x * U := by rw [k, mul_one]
    -- `x R = 1`
    have hxr : (x : ZMod P) * R = 1 := by
      rcases hf with rfl | rfl
      · simp only [show ¬ (1 : Int) < 0 by decide, ↓reduceIte] at hRz
        push_cast at hRz hfu
        rw [hRz, ← hfu]
      · simp only [show (-1 : Int) < 0 by decide, ↓reduceIte] at hRz
        push_cast at hRz hfu
        rw [hRz, mul_neg, ← hfu, neg_neg]
    have hX : (x : ZMod P) ≠ 0 := fun h => by rw [h, zero_mul] at hxr; exact zero_ne_one hxr
    calc (R : ZMod P) = (R : ZMod P) * x * (x : ZMod P) ^ (P - 2) :=
          (VG.Proof.Ed25519.mul_pow_inv hX _).symm
      _ = x * R * (x : ZMod P) ^ (P - 2) := by ring
      _ = (x : ZMod P) ^ (P - 2) := by rw [hxr, one_mul]

theorem sv_neg {X : Nat} (h : X < 2 ^ 256) : sv X < 0 ↔ 2 ^ 255 ≤ X := by
  unfold sv; split <;> omega

/-- `[slot 15] = [slot 2]^(p - 2)`. -/
theorem invert_proof {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa VG.Impl.Ed25519.AArch64.Divstep.invert s fun t =>
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      KeepRegs (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ ([.x2, .x20] : List Reg)) s t ∧
      t.gpr .x1 = s.gpr .x1 ∧ Outside base 192 512 s.mem t.mem := by
  refine WP.seq (WP.mono (init_ok hs) fun a ⟨ai, a20, a19, aO, ak⟩ => ?_)
  have hx : fe s.mem base 128 % P < P := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (loop_ok (scr_of hs ak (by decide)) hx ai a20) fun b ⟨bi, bO, bk⟩ => ?_)
  refine WP.mono (finish_ok (scr_of (scr_of hs ak (by decide)) bk (by decide))) fun t ⟨tv, t1, tO, tk⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [env, AArch64.F]
    have e2 : VG.Proof.X25519.toFe (fe s.mem base (VG.Impl.Ed25519.AArch64.offset 2)) =
        VG.Proof.X25519.toFe (fe s.mem base 128 % P) :=
      Fin.ext (by simp only [VG.Proof.X25519.toFe_val, Nat.mod_mod]; rfl)
    rw [e2]
    refine sound_eq hx bi.cu bi.z ?_
    rw [show VG.Impl.Ed25519.AArch64.offset 15 = 544 from rfl, tv, ← bi.f]
    simp only [sv_neg bi.fl]
  · exact ((ak.trans (bk.mono (by decide))).trans (tk.mono (by decide))).mono (by decide)
  · exact t1.trans ((bk.gpr .x19 (by decide)).trans a19)
  · exact ((aO.mono (by decide) (by decide)).trans (bO.mono (by decide) (by decide))).trans
      (tO.mono (by decide) (by decide))

instance sound : Sound := ⟨invert_proof⟩

end VG.Proof.Ed25519.AArch64.Divstep
