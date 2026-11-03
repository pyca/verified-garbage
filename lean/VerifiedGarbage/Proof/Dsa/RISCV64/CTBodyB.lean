module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyA
import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the cuts from `products` on cost more than their imports, which `VerifyCT`'s taint
-- checks then need not re-check

/-!
# DSA verification on RISC-V: constant time, the cuts of `body` from `products`

The cuts of `body`'s list (`FB`) in `products`, `combine` and `compare`
(`pinsB*`), from `body`'s phase `SB`, through the pieces' correctness: the
Montgomery multiplications of `products` (`prod_pre`), `combine`'s loads, joint
table and joint windows (`combG_ok`, `combT_ok`, `combL_ok`), and the P
space's phase `CB` between them.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum.RISCV64.PublicChecked (montOp)

/-! ## `products` -/

/-- `QI` through a change in the Q space's arrays from 1 on that keeps `t1`,
array 24 and `[4] < q`. -/
theorem QI.arr {v : VD} {s t : State} {j n : Nat} (h : QI v s) (h4 : arrQ s.mem v.L 4 < v.q)
    (Q : QS t v.L v.key v.sig) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (ht1 : t.gpr .t1 = s.gpr .t1)
    (o : Outside v.L.Q (slot v.L.wq j) n s.mem t.mem) (hj : slot v.L.wq 1 ≤ slot v.L.wq j)
    (hn : slot v.L.wq j + n ≤ slot v.L.wq 28)
    (h24 : slot v.L.wq j + n ≤ slot v.L.wq 24 ∨ slot v.L.wq 25 ≤ slot v.L.wq j)
    (h4' : slot v.L.wq j + n ≤ slot v.L.wq 4 ∨ slot v.L.wq 5 ≤ slot v.L.wq j) :
    QI v t ∧ arrQ t.mem v.L 4 < v.q := by
  obtain ⟨B, I, q24⟩ := h
  have hL := B.base.ok
  have hwq := hL.wq_ge
  have e := Lay.slot_eq v.L.wq
  have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e25 := e 25; have e28 := e 28
  have e0 := e 0
  have hnw : v.L.Q.toNat + slot v.L.wq 28 ≤ 2 ^ 64 := by
    have := B.qs.inq.env.hs.nowrap; have := B.qs.inq.env.hZ; omega
  have qa : QArr v.L s.mem t.mem := QArr.of o (by omega) hn
  refine ⟨⟨B.stepQ Q hrd hwr (qa.qbuf hL), ?_, ?_⟩, ?_⟩
  · show ((word t.mem v.L.Q (slot v.L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o.word (by omega) (by omega_arith), ht1]; exact I
  · rw [arrQ, o.wordsVal (by omega) (by omega_arith)]; exact q24
  · rw [arrQ, o.wordsVal (by omega) (by omega_arith)]; exact h4

/-- `products` before its stores. -/
theorem prod_pre {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : QI v s) (h4 : arrQ s.mem v.L 4 < v.q)
    (hqb : v.qb ≤ v.L.ql) (hq : 2 ≤ v.q) (hc : ∀ t, QB v t → WP isa c t Q) :
    WP isa (.seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 24) (.seq (montOp 6 6 4)
      (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1) c)))))))) s Q := by
  have hL := h.1.base.ok
  have hwq := hL.wq_ge
  have hql := h.1.base.ql
  have e := Lay.slot_eq v.L.wq
  have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e24 := e 24; have e25 := e 25
  have e28 := e 28
  refine WP.seq (WP.mono (scalar_QI h h4 hqb) fun s₁ ⟨I1, h41⟩ => ?_)
  refine WP.seq (WP.mono (ptrR_ok I1.1.base.scr hL I1.1.base.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  have I2 : QI v s₂ := ⟨I1.1.stepM k2 m2, by
    show ((word s₂.mem v.L.Q (slot v.L.wq 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [m2, k2.gpr (by decide)]; exact I1.2.1, by rw [arrQ, m2]; exact I1.2.2⟩
  have h42 : arrQ s₂.mem v.L 4 < v.q := by rw [arrQ, m2]; exact h41
  refine WP.seq (WP.mono (loadQ_ok (j := 5) I2.1.qs hL (by decide) ((I2.1.base.sg I2.1.vb).sub (o := 0) (k := v.L.ql)
    (by omega)) (by rw [a7, off_zero]) a8 (by omega) (by omega)) fun s₃ ⟨⟨Q3, _, _, o3⟩, k3⟩ => ?_)
  obtain ⟨I3, h43⟩ := I2.arr h42 Q3 k3.2.1 k3.2.2 (k3.gpr (by decide)) o3 (by omega) (by omega) (by omega)
    (by omega)
  refine WP.seq (WP.mono (copy_ok I3.1.qs.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨c1, o4⟩, k4⟩ => ?_)
  obtain ⟨I4, h44⟩ := I3.arr h43 (I3.1.qs.step k4 ((QArr.of o4 (by omega) (by omega)).body hL)) k4.2.1 k4.2.2
    (k4.gpr (by decide)) o4 (Nat.le_refl _) (by omega) (by omega) (by omega)
  have A1 : arrQ s₄.mem v.L 1 = 2 ^ (128 * v.L.wq) % v.q := by
    rw [arrQ, wordsVal_congr (m := s₃.mem) (d := slot v.L.wq 24) fun i hi => c1 i (by omega)]; exact I3.2.2
  have hR : 2 ^ (128 * v.L.wq) % v.q < v.q := Nat.mod_lt _ (by omega)
  -- The four multiplications, each keeping arrays 0, 1 and 4.
  refine WP.seq (WP.mono (qmont_ok hL I4.1.qs I4.2.1 (o := 6) (a := 6) (b := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [I4.1.q0]; exact h44)) fun s₅ ⟨⟨Q5, I5, _, _, k5a, qa5⟩, k5⟩ => ?_)
  have B5 := I4.1.stepQ Q5 k5.2.1 k5.2.2 (qa5.qbuf hL)
  have A51 := (k5a 1 (by decide) (by decide) (by decide) (by decide)).trans A1
  have A54 := (k5a 4 (by decide) (by decide) (by decide) (by decide)).trans (show arrQ s₄.mem v.L 4 = _ from rfl)
  refine WP.seq (WP.mono (qmont_ok hL Q5 I5 (o := 6) (a := 6) (b := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [A51, B5.q0]; exact hR)) fun s₆ ⟨⟨Q6, I6, _, _, k6a, qa6⟩, k6⟩ => ?_)
  have B6 := B5.stepQ Q6 k6.2.1 k6.2.2 (qa6.qbuf hL)
  have A61 := (k6a 1 (by decide) (by decide) (by decide) (by decide)).trans A51
  have A64 := (k6a 4 (by decide) (by decide) (by decide) (by decide)).trans A54
  refine WP.seq (WP.mono (qmont_ok hL Q6 I6 (o := 5) (a := 5) (b := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [A64, B6.q0]; exact h44)) fun s₇ ⟨⟨Q7, I7, _, _, k7a, qa7⟩, k7⟩ => ?_)
  have B7 := B6.stepQ Q7 k7.2.1 k7.2.2 (qa7.qbuf hL)
  have A71 := (k7a 1 (by decide) (by decide) (by decide) (by decide)).trans A61
  refine WP.seq (WP.mono (qmont_ok hL Q7 I7 (o := 5) (a := 5) (b := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [A71, B7.q0]; exact hR)) fun t ⟨⟨Q8, _, _, _, _, qa8⟩, k8⟩ =>
      hc t (B7.stepQ Q8 k8.2.1 k8.2.2 (qa8.qbuf hL)))

/-- The products' stores' first block. -/
theorem pinsB154 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 154) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 24) (.seq (montOp 6 6 4)
      (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1) (.block ptrBuf)))))))))))))) (by decide +kernel)
      (stQ5 (hsem _ _ h) fun _ I h4 _ => prod_pre I h4 (hsem _ _ h).vals.2.2.2.1 (hsem _ _ h).vals.1 fun _ B =>
        WP.mono (ptrBuf_ok B.base.scr B.base.ok B.base.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
          (fix_QB (B.stepM k' m)).app ⟨b7, b8, trivial⟩)

theorem pinsB157 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 157) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.L.Buf 32), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 24) (.seq (montOp 6 6 4)
      (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1) (.seq (.block ptrBuf)
      (.seq (storeBE 6) (.block ptrBuf2)))))))))))))))) (by decide +kernel)
      (stQ5 (hsem _ _ h) fun _ I h4 _ => prod_pre I h4 (hsem _ _ h).vals.2.2.2.1 (hsem _ _ h).vals.1 fun _ B => by
        have hL := B.base.ok
        have hql := B.base.ql
        have hpl := B.base.pl
        have hwq := hL.wq_ge
        refine WP.seq (WP.mono (ptrBuf_ok B.base.scr hL B.base.regs) fun s₉ ⟨⟨b7, b8, m9⟩, k9⟩ => ?_)
        have B9 := B.stepM k9 m9
        refine WP.seq (WP.mono (storeBE_ok (j := 6) (O := v.L.Buf) (k := v.L.ql) B9.qs.inq.env (by decide)
          (by have := ScrL.bufSt B9.base.scr hL (o := 0) (k := v.L.ql) (by omega)
              simpa only [off, BitVec.add_zero] using this)
          (by have := buf_nowrap hL (o := 0) (k := v.L.ql) (by omega) (by omega)
              simpa only [off, BitVec.add_zero] using this)
          b7 b8 (by omega) (by omega) (m2_sep hL)) fun _ ⟨⟨_, ot⟩, k10⟩ => ?_)
        have B10 := B9.step k10 (QBuf.ofBuf hL ot (by omega))
        exact WP.mono (ptrBuf2_ok B10.base.scr hL B10.base.regs) fun _ ⟨⟨c7, c8, m⟩, k'⟩ =>
          (fix_QB (B10.stepM k' m)).app ⟨c7, c8, trivial⟩)

/-- Up to `products`, then `c`. -/
theorem stQ6 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t, QB v t → MW v t → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products c)))))) s
      Q := by
  obtain ⟨hq, hqo, hql, hqb, -⟩ := h.vals
  refine stQ5 h fun t ⟨B, I, h24⟩ h4 mw => ?_
  have hL := B.base.ok
  have h4' : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
  refine WP.seq (WP.mono (products_ok (W := arrQ t.mem v.L 4) hL B.qs I (B.base.sg B.vb) (B.base.dig8 B.vb.1) B.lens hqb h4'
    (B.base.hdg.take (Nat.min_le_left _ _)) (by rw [B.q0]; exact hq) (by rw [B.q0]; exact hqo)
    (by rw [B.q0]; exact hql) (by rw [h24, B.q0]) rfl (by rw [B.q0]; exact h4))
    fun u ⟨⟨Q, _, _, qb⟩, k⟩ => hc u (B.stepQ Q k.2.1 k.2.2 qb) (mw.body (qb.body hL)))

/-! ## `combine` -/

/-- In the P space during `combine`, with p, `-p⁻¹ mod 2⁶⁴` and `R² mod p`. -/
abbrev CB (v : VD) (t : State) : Prop :=
  Base v t ∧ InP t v.L ∧ PInv t v.L ∧ arrP t.mem v.L 0 = v.p ∧ arrP t.mem v.L 24 = 2 ^ (128 * v.L.wp) % v.p

theorem fix_CB {v : VD} {t : State} (h : CB v t) : Fix (fixB v ++ envP v) t := h.1.fixB.app (fix_envP h.2.1)

/-- `combine`'s first block. -/
abbrev HEAD : List Instr := enterP ++ Precompute.minv ++ ptrBuf ++ ([.addi .s9 .s7 0] : List Instr) ++ ptrG

theorem head_QB {v : VD} {s : State} (h : QB v s) (hpo : v.p % 2 = 1) :
    WP isa (.block HEAD) s fun t => CB v t ∧ t.gpr .s7 = off v.key (v.L.pl + v.L.ql) ∧
      t.gpr .s8 = BitVec.ofNat 64 v.L.pl ∧ t.gpr .s9 = off v.L.Buf 0 :=
  WP.mono (combHead_ok h.base.ok h.base.scr h.base.regs h.p0 hpo) fun _ ⟨⟨ip, I, a7, a8, a9, m⟩, k⟩ =>
    ⟨⟨h.base.keepM k m, ip, I, by rw [arrP, m]; exact h.p0, by rw [arrP, m]; exact h.p24⟩, a7, a8, a9⟩

/-- A power's loads (the signature's): the base into array 4, `R² mod p` into array 1, and the
exponent's length. -/
theorem powP_pre {v : VD} {s : State} {N X : Addr} (h : CB v s) (hN : Src s v.L N v.L.pl)
    (h7 : s.gpr .s7 = N) (h9 : s.gpr .s9 = X) :
    WP isa (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24) (.block (getQ .s10))))) s
      (Fix (fixB v ++ envP v ++ [(.s9, X), (.s10, BitVec.ofNat 64 v.L.ql)])) := by
  obtain ⟨B, ip, -⟩ := h
  have hL := B.ok
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hbe := hL.buf_end
  have hqZ : v.L.qOff + 1600 ≤ v.L.Z := by simp only [Lay.bOff] at hbe; omega_arith
  have e := Lay.slot_eq v.L.wp
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  have hq28 : v.L.qOff = slot v.L.wp 28 := rfl
  refine WP.seq (WP.mono (getP_ok B.scr hL B.regs .s8) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_)
  have B1 := B.keepM k1 m1
  have en1 := ip.env.keep k1
  refine WP.seq (WP.mono (loadArr_ok en1 (j := 4) (N := N) (by decide)
      (by rw [k1.gpr (by decide), h7]; exact (BitVec.add_zero _).symm) a8 (by omega) (by omega)
      (by rw [k1.2.1, k1.2.2]; exact hN.rd) (fun i hi x hx => hN.sep i hi x (by omega_arith)))
    fun s₂ ⟨⟨_, _, o2, a7⟩, k2⟩ => ?_)
  have en2 : Env s₂ v.L.S v.L.qOff v.L.wp := ⟨en1.hs.congr k2.2.2, a7, (k2.gpr (by decide)).trans en1.s5,
    (k2.gpr (by decide)).trans en1.t0, en1.w2, en1.w48, en1.hZ⟩
  have B2 := B1.body k2 (Body.ofP hL o2 (by omega) (by omega))
  refine WP.seq (WP.mono (copy_ok en2 (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨_, o3⟩, k3⟩ => ?_)
  have B3 := B2.body k3 (Body.ofP hL o3 (by omega) (by omega))
  exact WP.mono (getQ_ok B3.scr hL B3.regs .s10) fun _ ⟨⟨a10, m4⟩, k4⟩ =>
    ((B3.keepM k4 m4).fixB.app (fix_envP ⟨((en2.keep k3).keep k4), (B3.keepM k4 m4).regs.s6⟩)).app
      ⟨(k4.gpr (r := .s9) (by decide)).trans ((k3.gpr (r := .s9) (by decide)).trans ((k2.gpr (r := .s9) (by decide)).trans
        ((k1.gpr (r := .s9) (by decide)).trans h9))), a10, trivial⟩

theorem pinsB161 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 161) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.L.Buf 0)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.block (getP .s8))))))))) (by decide +kernel) (stQ6 (hsem _ _ h) fun _ B _ =>
      WP.seq (WP.mono (head_QB B (hsem _ _ h).vals.2.2.2.2.2) fun _ ⟨c, a7, _, a9⟩ =>
        WP.mono (getP_ok c.1.scr c.1.ok c.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ => by
          exact ((c.1.keepM k m).fixB.app (fix_envP (c.2.1.keep k))).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩))

/-- `CB` after `combG_ok`'s code. -/
theorem g_CB {v : VD} {s t : State} (h : CB v s) (ip : InP t v.L)
    (o : Outside v.L.S (slot v.L.wp 4) (8 * (v.L.wp + 1)) s.mem t.mem) (k : Keep gRegs s t) : CB v t := by
  obtain ⟨B, -, I, p0, p24⟩ := h
  have hL := B.ok
  have hw := hL.wp_ge
  have e := Lay.slot_eq v.L.wp
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e24 := e 24; have e28 := e 28
  refine ⟨B.body k (Body.ofP hL o (by omega) (by simp only [Lay.qOff]; omega)), ip, ?_,
    by rw [arrP, o.wordsVal (by omega) (by omega_arith)]; exact p0,
    by rw [arrP, o.wordsVal (by omega) (by omega_arith)]; exact p24⟩
  show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [o.word (by omega) (by omega_arith), k.gpr (by decide)]; exact I

/-- `CB` after the joint table's or the joint windows' code. -/
theorem w_CB {v : VD} {s t : State} {rs : List Reg} (h : CB v s) (ip : InP t v.L)
    (o : Outside v.L.S (slot v.L.wp 1) (23 * (8 * (v.L.wp + 2))) s.mem t.mem) (k : Keep rs s t)
    (ht1 : .t1 ∉ rs := by decide) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : CB v t := by
  obtain ⟨B, -, I, p0, p24⟩ := h
  have hL := B.ok
  have hw := hL.wp_ge
  have e := Lay.slot_eq v.L.wp
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have e28 := e 28
  refine ⟨B.body k (Body.ofP hL o (by omega) (by simp only [Lay.qOff]; omega)) hr, ip, ?_,
    by rw [arrP, o.wordsVal (by omega) (by omega_arith)]; exact p0,
    by rw [arrP, o.wordsVal (by omega) (by omega_arith)]; exact p24⟩
  show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [o.word (by omega) (by omega_arith), k.gpr ht1]; exact I

theorem pinsB169 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 169) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.L.Buf 0)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.block ptrY)))))))))) (by decide +kernel)
      (stQ6 (hsem _ _ h) fun _ B _ =>
      WP.seq (WP.mono (head_QB B (hsem _ _ h).vals.2.2.2.2.2) fun _ ⟨c, a7, _, a9⟩ =>
        WP.mono (combG_ok c.1.ok c.1.scr c.1.regs (c.1.hk.take B.ky) c.2.1 a7) fun _ ⟨⟨_, ip, o, b7, b8⟩, k⟩ =>
          (fix_CB (g_CB c ip o k)).app ⟨b7, b8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩))

/-- `combine` up to y's octets, then `c`. -/
theorem stC1 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t, CB v t → Src t v.L v.key (3 * v.L.pl + v.L.ql) → t.gpr .s7 = off v.key (2 * v.L.pl + v.L.ql) →
      t.gpr .s8 = BitVec.ofNat 64 v.L.pl → t.gpr .s9 = off v.L.Buf 0 → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (.block ptrY) c)))))))))) s Q :=
  stQ6 h fun _ B _ => WP.seq (WP.mono (head_QB B h.vals.2.2.2.2.2) fun _ ⟨c1, a7, _, a9⟩ =>
    wp_seq3 (combG_ok c1.1.ok c1.1.scr c1.1.regs (c1.1.hk.take B.ky) c1.2.1 a7) fun t ⟨⟨_, ip, o, b7, b8⟩, k⟩ =>
      hc t (g_CB c1 ip o k) ((c1.1.hk.take B.ky).keep k.2.1 k.2.2) b7 b8 ((k.gpr (r := .s9) (by decide)).trans a9))

theorem pinsB330 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 330) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, off v.L.Buf 0), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (.block ptrY)
      (.seq (loadArr 5) (.seq (copy 1 24) (.seq jointTable (.block (getQ .s10)))))))))))))))
      (by decide +kernel) (stC1 (hsem _ _ h) fun _ c hk a7 a8 a9 => by
      obtain ⟨-, -, -, -, hp, hpo⟩ := (hsem _ _ h).vals
      exact WP.mono (combT_ok c.1.ok c.1.scr c.1.regs hk c.2.1 c.2.2.1 c.2.2.2.1 hp hpo c.2.2.2.2 a7 a8)
        fun _ ⟨⟨_, _, ip, o, a10⟩, k⟩ =>
          (fix_CB (w_CB c ip o k)).app ⟨(k.gpr (r := .s9) (by decide)).trans a9, a10, trivial⟩)

/-- `combine` up to the joint windows, then `c`. -/
theorem stC2 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t G Y, CB v t → JInv t.mem v.L.S v.L.wp v.p G Y (2 ^ (128 * v.L.wp) % v.p) jDone →
      JRun t t t v.L.S v.L.qOff v.L.wp v.p G Y (2 ^ (128 * v.L.wp) % v.p) 0 0 →
      t.gpr .s9 = off v.L.Buf 0 → t.gpr .s10 = BitVec.ofNat 64 v.L.ql → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (.block ptrY)
      (.seq (loadArr 5) (.seq (copy 1 24) (.seq jointTable (.seq (.block (getQ .s10)) c)))))))))))))) s Q := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  exact stC1 h fun _ c hk a7 a8 a9 =>
    wp_seq4 (combT_ok c.1.ok c.1.scr c.1.regs hk c.2.1 c.2.2.1 c.2.2.2.1 hp hpo c.2.2.2.2 a7 a8)
      fun t ⟨⟨J, r, ip, o, a10⟩, k⟩ => hc t _ _ (w_CB c ip o k) J r ((k.gpr (r := .s9) (by decide)).trans a9) a10

theorem pinsB341 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 341) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq products (.seq (.block HEAD) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (.block ptrY)
      (.seq (loadArr 5) (.seq (copy 1 24) (.seq jointTable (.seq (.block (getQ .s10))
      (.seq (.loop (.seq jointByte (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10))
      (.seq (montOp 4 6 7) (.block (bufBase .s7 .t2 ++ getP .s8)))))))))))))))))) (by decide +kernel)
      (stC2 (hsem _ _ h) fun _ _ _ c J r a9 a10 => by
        obtain ⟨-, -, -, -, hp, hpo⟩ := (hsem _ _ h).vals
        exact WP.mono (combL_ok c.1.ok c.1.scr c.1.regs c.2.1 hp hpo J r a9 a10)
          fun _ ⟨⟨_, ip, o, f7, f8⟩, k⟩ => (fix_CB (w_CB c ip o k)).app ⟨f7, f8, trivial⟩)

/-- Up to `combine`, then `c`. -/
theorem stC4 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t, Base v t → arrQ t.mem v.L 0 = v.q → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq combine c))))))) s Q := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  refine stQ6 h fun _ B _ => WP.seq (WP.mono (combine_ok B.base.ok B.base.scr B.base.regs (B.base.hk.take B.ky) B.p0 hp hpo
    B.p24) fun t ⟨⟨_, _, bd, kq⟩, k⟩ => hc t (B.base.body k bd) ((keepQ_arr0 B.base.ok kq).trans B.q0))

/-- `compare`'s first block. -/
abbrev CMP : List Instr := enterQ ++ bufBase .s9 .t2 ++ getP .s10

theorem cmp_pre {v : VD} {s : State} (B : Base v s) :
    WP isa (.block CMP) s fun t => (Base v t ∧ InQ t v.L ∧ t.gpr .s9 = v.L.Buf ∧
      t.gpr .s10 = BitVec.ofNat 64 v.L.pl ∧ t.mem = s.mem) ∧ Keep (enterRegs ++ ([.s9, .t2] : List Reg) ++ ([.s10] : List Reg)) s t := by
  have hL := B.ok
  refine WP.block_append (WP.block_append (WP.mono (enterQ_ok hL B.scr B.regs) fun _ ⟨⟨q1, m1⟩, k1⟩ =>
    WP.mono (bufBase_ok (B.keepM k1 m1).scr hL (B.keepM k1 m1).regs (rd := .s9) (t := .t2) (by decide)
      (by decide) (by decide)) fun _ ⟨⟨a9, m2⟩, k2⟩ => ?_))
  have B2 := (B.keepM k1 m1).keepM k2 m2
  exact WP.mono (getP_ok B2.scr hL B2.regs .s10) fun _ ⟨⟨a10, m3⟩, k3⟩ =>
    ⟨⟨B2.keepM k3 m3, (q1.keep k2).keep k3, (k3.gpr (by decide)).trans a9, a10, by rw [m3, m2, m1]⟩,
      (k1.trans k2).trans k3⟩

theorem pinsB344 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 344) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, v.L.Buf), (.s10, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq products (.seq combine (.block CMP)))))))) (by decide +kernel)
      (stC4 (hsem _ _ h) fun _ B _ => (cmp_pre B).mono fun _ ⟨⟨B', iq, a9, a10, _⟩, _⟩ =>
        (B'.fixB.app (fix_envQ iq)).app ⟨a9, a10, trivial⟩)

theorem pinsB350 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 350) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq products (.seq combine (.seq (.block CMP) (.seq ModArith.reduce64 (.block ptrR)))))))))) (by decide +kernel)
      (stC4 (hsem _ _ h) fun _ B q0 => WP.seq ((cmp_pre B).mono fun s₁ ⟨⟨B1, iq, a9, a10, m1⟩, _⟩ => by
        have hL := B1.ok
        have hwq := hL.wq_ge
        have hqs := hL.qslot
        have hpl := B1.pl
        have e3 := iq.env
        have e4 := Lay.slot_eq v.L.wq 4; have e1 := Lay.slot_eq v.L.wq 1
        have hq0 : 0 < wordsVal s₁.mem v.L.Q (slot v.L.wq 0) v.L.wq := by
          have := (hsem _ _ h).vals.1
          show 0 < arrQ s₁.mem v.L 0
          rw [arrQ, m1]; show 0 < arrQ _ v.L 0; rw [q0]; omega
        exact WP.seq (WP.mono (ModArith.reduce64_ok (D := v.L.Buf) (L := v.L.pl) e3.hs (by omega) (by omega)
          (by omega) e3.a7 e3.s5 e3.t0 hq0 (by rw [a9]; exact (BitVec.add_zero _).symm) a10 (by omega)
          (by omega_arith) (fun i hi => (ScrL.bufN B1.scr hL (n := v.L.pl) (by omega)).ld (show i + 1 ≤ v.L.pl by omega))
          (buf_apartQ v.L (by omega))) fun s₂ ⟨⟨_, o2⟩, k2⟩ => by
            have B2 := B1.body k2 (Body.ofQ hL o2 (by omega))
            exact WP.mono (ptrR_ok B2.scr hL B2.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
              ((B2.keepM k' m).fixB.app (fix_envQ ((iq.keep k2).keep k'))).app ⟨b7, b8, trivial⟩)))

end VG.Proof.Dsa.RISCV64.CT
