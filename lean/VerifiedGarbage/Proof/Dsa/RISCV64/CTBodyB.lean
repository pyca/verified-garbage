module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! ### `Dsa.RISCV64.CTBodyA`, which this module and modules that import it used -/

section

/-!
# DSA verification on RISC-V: constant time, the cuts of `body` in the Q space

`body`'s list (`FB`) is cut after each block that loads the header's words;
here the cuts up to `products`' (`pinsB*`), from `body`'s phase `SB`, through
the pieces' correctness: the Q space's phases (`QB`, `QI`) after `ranges`,
`keepMask`, `rrQ`, `qMinus2`, `inverse` and `products`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-! ## The values -/

theorem Base.q_lt {v : VD} {s : State} (h : Base v s) : v.q < 2 ^ (8 * v.L.ql) := by
  rw [← h.q, qOf, ← VG.Proof.Bignum.pow256_eq]
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off v.key v.L.pl) v.L.ql)
  rwa [VG.Proof.Bignum.bytesAt_length] at this

theorem Base.sg {v : VD} {s : State} (h : Base v s) (hv : VB v) : Src s v.L v.sig (2 * v.L.ql) :=
  hv.2 ▸ h.hsg

/-- The values `body` needs of the key. -/
theorem SB.vals {v : VD} {s : State} (h : SB v s) :
    2 ≤ v.q ∧ v.q % 2 = 1 ∧ v.q < 2 ^ (8 * v.L.ql) ∧ v.qb ≤ v.L.ql ∧ 2 ≤ v.p ∧ v.p % 2 = 1 := by
  obtain ⟨⟨c, ⟨hsz, hp, hq, _⟩, _⟩, _⟩ := h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have hl := c.base.q_lt
  exact ⟨by omega_using [bd], hq, hl, q_bits (by omega_using [hq]) hl, by omega_using [bd], hp⟩

/-! ## The Q space's phases -/

/-- In the Q space during `body`, with q in its array 0, and p and `R² mod p`
in the P space. -/
structure QB (v : VD) (t : State) : Prop where
  base : Base v t
  lens : Lens v v.qb t
  qs : QS t v.L v.key v.sig
  q0 : arrQ t.mem v.L 0 = v.q
  p0 : arrP t.mem v.L 0 = v.p
  p24 : arrP t.mem v.L 24 = 2 ^ (128 * v.L.wp) % v.p
  vb : VB v
  ky : KY v

theorem QB.stepQ {v : VD} {s t : State} (h : QB v s) (Q : QS t v.L v.key v.sig) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (qb : QBuf v.L s.mem t.mem) : QB v t := by
  have hL := h.base.ok
  have hb := qb.body hL
  exact ⟨h.base.step Q.regs hrd hwr (Kept.ofBody hL hb).out (hb.word (by decide)) (hb.word (by decide)),
    by rw [Lens, hb.word (by decide)]; exact h.lens, Q,
    (qb.arr0 hL).trans h.q0, (qb.arrP hL 0 (by decide)).trans h.p0, (qb.arrP hL 24 (by decide)).trans h.p24,
    h.vb, h.ky⟩

theorem QB.step {v : VD} {s t : State} {rs : List Reg} (h : QB v s) (k : Keep rs s t)
    (qb : QBuf v.L s.mem t.mem) (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) : QB v t :=
  h.stepQ (h.qs.step k (qb.body h.base.ok) hr) k.2.1 k.2.2 qb

theorem QB.stepM {v : VD} {s t : State} {rs : List Reg} (h : QB v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) : QB v t :=
  h.step k (by rw [hm]; exact Outside.refl _ _ _ _) hr

theorem fix_QB {v : VD} {t : State} (h : QB v t) : Fix (fixB v ++ envQ v) t :=
  h.base.fixB.app (fix_envQ h.qs.inq)

/-- With `-q⁻¹ mod 2⁶⁴` in `t1` and `R² mod q` in array 24. -/
abbrev QI (v : VD) (t : State) : Prop :=
  QB v t ∧ QInv t v.L ∧ arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q

theorem ranges_SB {v : VD} {s : State} (h : SB v s) : WP isa ranges s fun t => QB v t ∧
    t.gpr .a4 = mask (decide ((0 < rOf s.mem v.L v.sig ∧ rOf s.mem v.L v.sig < v.q) ∧
      (0 < sOf s.mem v.L v.sig ∧ sOf s.mem v.L v.sig < v.q))) := by
  have c := h.1.1
  have hL := c.base.ok
  refine WP.mono (ranges_ok hL c.base.scr c.base.regs (c.base.sg h.2.2)) fun t ⟨⟨Q, _, a4, qa⟩, k⟩ => ?_
  have hb := qa.body hL
  have qb := qa.qbuf hL
  rw [c.q0] at a4
  exact ⟨⟨c.base.body k hb, by rw [Lens, hb.word (by decide)]; exact c.lens, Q, (qa.arr0 hL).trans c.q0,
    (qb.arrP hL 0 (by decide)).trans c.p0, (qb.arrP hL 24 (by decide)).trans c.p24, h.2.2, h.1.2.2.2⟩, a4⟩

/-- The mask of r's and s's ranges is in the header's word `hMask`. -/
abbrev MW (v : VD) (t : State) : Prop := ∃ b, word t.mem v.L.S hMask = mask b

theorem MW.body {v : VD} {s t : State} (h : MW v s) (hb : Body v.L s.mem t.mem) : MW v t :=
  let ⟨b, hm⟩ := h
  ⟨b, by rw [hb.word (by decide)]; exact hm⟩

theorem keepMask_QB {v : VD} {s : State} {b : Bool} (h : QB v s) (h4 : s.gpr .a4 = mask b) :
    WP isa (.block keepMask) s fun t => QB v t ∧ MW v t := by
  have hL := h.base.ok
  have hZ := hL.z256
  have hnw := hL.nowrap
  refine WP.mono (keepMask_ok hL h.qs) fun t ⟨⟨Q, w, o⟩, k⟩ => ?_
  have o' : Outside v.L.S 0 v.L.Z s.mem t.mem := o.mono (Nat.le_refl _) (by simp only [hMask]; omega_using [hZ])
  have w8 : word t.mem v.L.S hDigest = word s.mem v.L.S hDigest :=
    o.word (Or.inr (by decide)) (by simp only [hDigest]; omega_using [])
  have w16 : word t.mem v.L.S hLens = word s.mem v.L.S hLens :=
    o.word (Or.inr (by decide)) (by simp only [hLens]; omega_using [])
  have w24 : word t.mem v.L.S Sign.hOut = word s.mem v.L.S Sign.hOut :=
    o.word (Or.inr (by simp only [hMask, Sign.hOut]; omega_using [])) (by simp only [Sign.hOut]; omega_using [])
  exact ⟨⟨h.base.step Q.regs k.2.1 k.2.2 o' w8 w24, by rw [Lens, w16]; exact h.lens, Q,
    (keepQ_arr0 hL (mask_keepQ hL o)).trans h.q0, (mask_arrP hL o 0 (by decide)).trans h.p0,
    (mask_arrP hL o 24 (by decide)).trans h.p24, h.vb, h.ky⟩, ⟨b, w.trans h4⟩⟩

theorem rrQ_QB {v : VD} {s : State} (h : QB v s) (hq : 2 ≤ v.q) (hqo : v.q % 2 = 1) :
    WP isa rrQ s fun t => (QI v t ∧ QBuf v.L s.mem t.mem) ∧ Keep rrQRegs s t := by
  have hL := h.base.ok
  refine WP.mono (rrQ_ok hL h.qs (by rw [h.q0]; exact hq) (by rw [h.q0]; exact hqo))
    fun t ⟨⟨_, I, _, r24, qa⟩, k⟩ => ⟨⟨⟨h.step k (qa.qbuf hL), I, by rw [r24, h.q0]⟩, qa.qbuf hL⟩, k⟩

theorem qMinus2_QI {v : VD} {s : State} (h : QI v s) (hq : 2 ≤ v.q) (hql : v.q < 2 ^ (8 * v.L.ql)) :
    WP isa qMinus2 s fun t => (QI v t ∧ QBuf v.L s.mem t.mem) ∧ Keep qm2Regs s t := by
  obtain ⟨B, I, h24⟩ := h
  have hL := B.base.ok
  refine WP.mono (qMinus2_ok hL B.qs (by rw [B.q0]; exact hq) (by rw [B.q0]; exact hql))
    fun t ⟨⟨_, _, kj, w0, qb⟩, k⟩ =>
      ⟨⟨⟨B.step k qb, ?_, by rw [kj 24 (by decide) (by decide)]; exact h24⟩, qb⟩, k⟩
  show ((word t.mem v.L.Q (slot v.L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [w0, k.gpr (by decide)]; exact I

theorem inverse_QI {v : VD} {s : State} (h : QI v s) (hq : 2 ≤ v.q) (hqo : v.q % 2 = 1) :
    WP isa inverse s fun t => (QI v t ∧ arrQ t.mem v.L 4 < v.q ∧ QBuf v.L s.mem t.mem) ∧ Keep invRegs s t := by
  obtain ⟨B, I, h24⟩ := h
  have hL := B.base.ok
  refine WP.mono (inverse_ok hL B.qs I (B.base.sg B.vb) (by rw [B.q0]; exact hq) (by rw [B.q0]; exact hqo)
    (by rw [B.q0]; exact h24)) fun t ⟨⟨Q', I', a4, kj, qa⟩, k⟩ =>
      ⟨⟨⟨B.stepQ Q' k.2.1 k.2.2 (qa.qbuf hL), I', by rw [kj 24 (by decide) (by decide)]; exact h24⟩,
        by rw [a4, B.q0]; exact Nat.mod_lt _ (by omega_using [hq]), qa.qbuf hL⟩, k⟩

/-! ## The cuts in `ranges` and `qMinus2` -/

theorem enterQ_SB {v : VD} {s : State} (h : SB v s) :
    WP isa (.block (enterQ ++ ptrR)) s fun t => (Base v t ∧ InQ t v.L ∧ t.gpr .s7 = v.sig ∧
      t.gpr .s8 = BitVec.ofNat 64 v.L.ql) ∧ Keep (enterRegs ++ ([.s7, .s8] : List Reg)) s t := by
  have B := h.1.1.base
  refine WP.block_append (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => ?_)
  have B1 := B.keepM k m
  exact WP.mono (ptrR_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
    ⟨⟨B1.keepM k' m', iq.keep k', a7, a8⟩, k.trans k'⟩

theorem pinsB1 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 1) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .block (enterQ ++ ptrR)) rfl ((enterQ_SB (hsem _ _ h)).mono
      fun _ ⟨⟨B, iq, a7, a8⟩, _⟩ => (B.fixB.app (fix_envQ iq)).app ⟨a7, a8, trivial⟩)

theorem pinsB9 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 9) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.sig v.L.ql), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    have hql := (hsem _ _ h).1.1.base.ql
    refine WP.of_flat (c := .seq (.block (enterQ ++ ptrR)) (.seq (loadArr 5) (.block ptrS))) rfl
      (WP.seq (WP.mono (enterQ_SB (hsem _ _ h)) fun _ ⟨⟨B, iq, a7, a8⟩, _⟩ => ?_))
    have Q : QS _ _ _ _ := ⟨iq, B.scr, B.regs⟩
    have hL := B.ok
    refine WP.seq (WP.mono (loadQ_ok (j := 5) Q hL (by decide) ((B.sg (hsem _ _ h).2.2).sub (o := 0) (k := v.L.ql) (by omega_using []))
      (by rw [a7, off_zero]) a8 (by omega_using [hql]) (by have := hL.wq_ge; omega_using [this])) fun _ ⟨⟨Q', _, _, o⟩, k⟩ => ?_)
    have qa : QArr v.L _ _ := QArr.of o (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using [])
    have B' := B.body k (qa.body hL)
    exact WP.mono (ptrS_ok Q'.scr hL Q'.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
      ((B'.keepM k' m).fixB.app (fix_envQ (Q'.inq.keep k'))).app ⟨b7, b8, trivial⟩

/-- `ranges`, `keepMask` and `rrQ`, then `c`. -/
theorem stQ3 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t, QI v t → MW v t → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ c))) s Q := by
  obtain ⟨hq, hqo, -⟩ := h.vals
  refine WP.seq (WP.mono (ranges_SB h) fun _ ⟨B, a4⟩ => WP.seq (WP.mono (keepMask_QB B a4)
    fun _ ⟨B', mw⟩ => WP.seq (WP.mono (rrQ_QB B' hq hqo) fun t ⟨⟨I, qb⟩, _⟩ =>
      hc t I (mw.body (qb.body B'.base.ok)))))

theorem pinsB50 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 50) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    have hq := (hsem _ _ h).vals.1
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq minus2 (.block ptrBuf))))) rfl
      (stQ3 (hsem _ _ h) fun _ ⟨B, _, _⟩ _ => ?_)
    have hL := B.base.ok
    refine WP.seq (WP.mono (minus2_ok B.qs.inq.env (show 2 ≤ arrQ _ v.L 0 by rw [B.q0]; exact hq))
      fun _ ⟨⟨_, o⟩, k⟩ => ?_)
    have qa : QArr v.L _ _ := QArr.of o (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using [])
    have B' := B.step k (qa.qbuf hL)
    exact WP.mono (ptrBuf_ok B'.base.scr hL B'.base.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
      (fix_QB (B'.stepM k' m)).app ⟨b7, b8, trivial⟩

/-- Up to `qMinus2`, then `c`. -/
theorem stQ4 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t, QI v t → MW v t → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 c)))) s Q := by
  obtain ⟨hq, _, hql, -⟩ := h.vals
  exact stQ3 h fun _ I mw => WP.seq (WP.mono (qMinus2_QI I hq hql) fun t ⟨⟨I', qb⟩, _⟩ =>
    hc t I' (mw.body (qb.body I.1.base.ok)))

theorem pinsB53 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.sig v.L.ql), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.block ptrS))))) rfl
      (stQ4 (hsem _ _ h) fun _ ⟨B, _, _⟩ _ => WP.mono (ptrS_ok B.base.scr B.base.ok B.base.regs)
        fun _ ⟨⟨b7, b8, m⟩, k'⟩ => (fix_QB (B.stepM k' m)).app ⟨b7, b8, trivial⟩)

theorem pinsB63 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 63) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, off v.L.Buf 0), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq (.block ptrS)
      (.seq (loadArr 4) (.seq (copy 1 24) (.block (ptrBuf ++ [.addi .s9 .s7 0, .addi .s10 .s8 0]))))))))) rfl
      (stQ4 (hsem _ _ h) fun _ ⟨B, _, _⟩ _ => ?_)
    have hL := B.base.ok
    have hql := B.base.ql
    have hwq := hL.wq_ge
    refine WP.seq (WP.mono (ptrS_ok B.base.scr hL B.base.regs) fun _ ⟨⟨a7, a8, m⟩, k⟩ => ?_)
    have B1 := B.stepM k m
    refine WP.seq (WP.mono (loadQ_ok (j := 4) B1.qs hL (by decide) ((B1.base.sg B1.vb).sub (o := v.L.ql) (k := v.L.ql)
      (by omega_using [])) a7 a8 (by omega_using [hql]) (by omega_using [hwq])) fun _ ⟨⟨Q2, _, _, o2⟩, k2⟩ => ?_)
    have B2 := B1.stepQ Q2 k2.2.1 k2.2.2
      (QArr.of o2 (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using []) |>.qbuf hL)
    refine WP.seq (WP.mono (copy_ok B2.qs.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
      fun _ ⟨⟨_, o3⟩, k3⟩ => ?_)
    have B3 := B2.step k3 (QArr.of o3 (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using [])
      |>.qbuf hL)
    refine WP.block_append (WP.mono (ptrBuf_ok B3.base.scr hL B3.base.regs) fun t ⟨⟨b7, b8, m4⟩, k4⟩ =>
      WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off v.L.Buf 0 ∧
        u.gpr .s10 = BitVec.ofNat 64 v.L.ql ∧ u.mem = t.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide)
        (by rfl)) fun _ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_)
    exact (fix_QB ((B3.stepM k4 m4).stepM k5 m5)).app ⟨c9, c10, trivial⟩

/-- Up to `inverse`, then `c`. -/
theorem stQ5 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SB v s)
    (hc : ∀ t, QI v t → arrQ t.mem v.L 4 < v.q → MW v t → WP isa c t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse c))))) s Q := by
  obtain ⟨hq, hqo, -⟩ := h.vals
  exact stQ4 h fun _ I mw => WP.seq (WP.mono (inverse_QI I hq hqo) fun t ⟨⟨I', h4, qb⟩, _⟩ =>
    hc t I' h4 (mw.body (qb.body I.1.base.ok)))

/-! ## The cuts in `products` -/

/-- `scalarLen`'s block. -/
abbrev SLB : List Instr := getQb .s8 ++ getD .t3 ++ [.sub .a0 .s8 .t3, .shift .srl .d .a0 .a0 63]

theorem pinsB104 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 104) [.s6, .s11, .ra, .a7, .s5, .t0, .s8, .t3, .a0] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s8, BitVec.ofNat 64 v.qb), (.t3, BitVec.ofNat 64 v.d),
      (.a0, BitVec.ofNat 64 (if v.qb < v.d then 1 else 0))]) (fun _ => rfl) fun v _ h => by
    have hqb := (hsem _ _ h).vals.2.2.2.1
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.block SLB)))))) rfl (stQ5 (hsem _ _ h) fun _ ⟨B, _, _⟩ _ _ => ?_)
    have hL := B.base.ok
    have hp : v.L.pl < 2 ^ 16 := by have := B.base.pl; simp only [Nat.reducePow]; omega_using [this]
    have hq : v.L.ql < 2 ^ 16 := by have := B.base.ql; simp only [Nat.reducePow]; omega_using [this]
    have h3 : v.qb < 2 ^ 16 := by have := B.base.ql; simp only [Nat.reducePow]; omega_using [hqb, hq]
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
    refine WP.block_append (WP.block_append (WP.mono (getQb_ok B.base.scr hL B.base.regs.s6 .s8)
      fun u ⟨⟨a8, mu⟩, ku⟩ => WP.mono (getD_ok (B.base.scr.congr ku.2.2) hL
        (by rw [ku.gpr (by decide)]; exact B.base.regs.s6) .t3) fun w ⟨⟨b3, mw⟩, kw⟩ => ?_))
    have l := B.lens
    rw [Lens] at l
    rw [l, pack_qb hp hq h3 h4] at a8
    rw [mu, l, pack_d hp hq h3 h4] at b3
    have a8' : w.gpr .s8 = BitVec.ofNat 64 v.qb := (kw.gpr (by decide)).trans a8
    have hsub := sub_shr63 (a := v.qb) (b := v.d) (by simp only [Nat.reducePow] at *; omega_using [h3])
      (by simp only [Nat.reducePow] at *; omega_using [h4])
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 (if v.qb < v.d then 1 else 0) ∧
      t.mem = w.mem) (by brun [a8', b3, exec_shift_d (show 63 < 64 by decide), hsub]) (by decide) (by rfl))
      fun t ⟨⟨c0, mt⟩, kt⟩ => ?_
    have B' := (B.stepM ku mu |>.stepM kw mw).stepM kt mt
    exact (fix_QB B').app ⟨(kt.gpr (r := .s8) (by decide)).trans a8', (kt.gpr (r := .t3) (by decide)).trans b3, c0,
      trivial⟩

theorem pinsB106 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 106) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.dig), (.s8, BitVec.ofNat 64 (min v.d v.qb))])
    (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq scalarLen (.block [.load .d .s7 .s6 hDigest]))))))) rfl (stQ5 (hsem _ _ h) fun _ ⟨B, _, _⟩ _ _ => ?_)
    have hL := B.base.ok
    have h3 : v.qb < 2 ^ 16 := by have := B.base.ql; have := (hsem _ _ h).vals.2.2.2.1; simp only [Nat.reducePow]; omega_arith
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
    refine WP.seq (WP.mono (scalarLen_ok B.base.scr hL B.base.regs.s6 B.lens h3 h4) fun s₀ ⟨⟨a8, m0⟩, k0⟩ => ?_)
    have B0 := B.stepM k0 m0
    obtain ⟨hin, hal⟩ := ScrL.hdr B0.base.scr hL (d := 8) (by decide) (by decide)
    refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = v.dig ∧ u.mem = s₀.mem)
      (by brun [hDigest, B0.base.regs.s6, hin, hal]; exact B0.base.dig8 B0.vb.1) (by rfl) (by rfl)) fun _ ⟨⟨a7, m1⟩, k1⟩ => ?_
    exact (fix_QB (B0.stepM k1 m1)).app ⟨a7, (k1.gpr (r := .s8) (by decide)).trans a8, trivial⟩

/-- `scalar`, in the Q space. -/
theorem scalar_QI {v : VD} {s : State} (h : QI v s) (h4 : arrQ s.mem v.L 4 < v.q) (hqb : v.qb ≤ v.L.ql) :
    WP isa scalar s fun t => QI v t ∧ arrQ t.mem v.L 4 < v.q := by
  obtain ⟨B, I, h24⟩ := h
  have hL := B.base.ok
  have h4' : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
  refine WP.mono (scalar_ok hL B.qs (B.base.dig8 B.vb.1) B.lens hqb h4' (B.base.hdg.take (Nat.min_le_left _ _)))
    fun t ⟨⟨Q, _, o⟩, k⟩ => ?_
  have e1 := Lay.slot_eq v.L.wq 1; have e4 := Lay.slot_eq v.L.wq 4; have e6 := Lay.slot_eq v.L.wq 6
  have e7 := Lay.slot_eq v.L.wq 7; have e24 := Lay.slot_eq v.L.wq 24; have e0 := Lay.slot_eq v.L.wq 0
  have e28 := Lay.slot_eq v.L.wq 28
  have hwq := hL.wq_ge
  have hnw : v.L.Q.toNat + slot v.L.wq 28 ≤ 2 ^ 64 := by have := B.qs.inq.env.hs.nowrap; have := B.qs.inq.env.hZ; omega_arith
  have qa : QArr v.L s.mem t.mem := QArr.of o (by omega_using [e1, e6]) (by omega_using [e6, e28])
  refine ⟨⟨B.stepQ Q k.2.1 k.2.2 (qa.qbuf hL), ?_, ?_⟩, ?_⟩
  · show ((word t.mem v.L.Q (slot v.L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o.word (by omega_using [e6, e0]) (by omega_arith), k.gpr (by decide)]; exact I
  · rw [arrQ, o.wordsVal (by omega_using [e6, e24]) (by omega_arith)]; exact h24
  · rw [arrQ, o.wordsVal (by omega_using [e4, e6]) (by omega_arith)]; exact h4

theorem pinsB108 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 108) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq scalar (.block ptrR))))))) rfl (stQ5 (hsem _ _ h) fun _ I h4 _ =>
      WP.seq (WP.mono (scalar_QI I h4 (hsem _ _ h).vals.2.2.2.1) fun _ ⟨⟨B, _, _⟩, _⟩ =>
        WP.mono (ptrR_ok B.base.scr B.base.ok B.base.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
          (fix_QB (B.stepM k' m)).app ⟨b7, b8, trivial⟩))

end VG.Proof.Dsa.RISCV64.CT

end

end

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
  obtain e := Lay.slot_eq v.L.wq
  obtain e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e25 := e 25; have e28 := e 28
  obtain e0 := e 0
  obtain hnw : v.L.Q.toNat + slot v.L.wq 28 ≤ 2 ^ 64 := by
    have := B.qs.inq.env.hs.nowrap; have := B.qs.inq.env.hZ; omega_arith
  obtain qa : QArr v.L s.mem t.mem := QArr.of o (by omega_using [hj]) hn
  refine ⟨⟨B.stepQ Q hrd hwr (qa.qbuf hL), ?_, ?_⟩, ?_⟩
  · show ((word t.mem v.L.Q (slot v.L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o.word (by omega_using [hj, hn, h24, h4', hwq, e1, e4, e5, e24, e25, e28, e0, hnw]) (by omega_arith), ht1]; exact I
  · rw [arrQ, o.wordsVal (by omega_using [h24, e24, e25]) (by omega_arith)]; exact q24
  · rw [arrQ, o.wordsVal (by omega_using [h4', e4, e5]) (by omega_arith)]; exact h4

/-- `products` before its stores. -/
theorem prod_pre {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : QI v s) (h4 : arrQ s.mem v.L 4 < v.q)
    (hqb : v.qb ≤ v.L.ql) (hq : 2 ≤ v.q) (hc : ∀ t, QB v t → WP isa c t Q) :
    WP isa (.seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 24) (.seq (montOp 6 6 4)
      (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1) c)))))))) s Q := by
  have hL := h.1.base.ok
  have hwq := hL.wq_ge
  have hql := h.1.base.ql
  obtain e := Lay.slot_eq v.L.wq
  obtain e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e24 := e 24; have e25 := e 25
  obtain e28 := e 28
  refine WP.seq (WP.mono (scalar_QI h h4 hqb) fun s₁ ⟨I1, h41⟩ => ?_)
  refine WP.seq (WP.mono (ptrR_ok I1.1.base.scr hL I1.1.base.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  obtain I2 : QI v s₂ := ⟨I1.1.stepM k2 m2, by
    show ((word s₂.mem v.L.Q (slot v.L.wq 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [m2, k2.gpr (by decide)]; exact I1.2.1, by rw [arrQ, m2]; exact I1.2.2⟩
  obtain h42 : arrQ s₂.mem v.L 4 < v.q := by rw [arrQ, m2]; exact h41
  refine WP.seq (WP.mono (loadQ_ok (j := 5) I2.1.qs hL (by decide) ((I2.1.base.sg I2.1.vb).sub (o := 0) (k := v.L.ql)
    (by omega)) (by rw [a7, off_zero]) a8 (by omega) (by omega)) fun s₃ ⟨⟨Q3, _, _, o3⟩, k3⟩ => ?_)
  obtain ⟨I3, h43⟩ := I2.arr h42 Q3 k3.2.1 k3.2.2 (k3.gpr (by decide)) o3 (by omega) (by omega) (by omega)
    (by omega)
  refine WP.seq (WP.mono (copy_ok I3.1.qs.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨c1, o4⟩, k4⟩ => ?_)
  obtain ⟨I4, h44⟩ := I3.arr h43 (I3.1.qs.step k4 ((QArr.of o4 (by omega) (by omega)).body hL)) k4.2.1 k4.2.2
    (k4.gpr (by decide)) o4 (Nat.le_refl _) (by omega) (by omega) (by omega)
  obtain A1 : arrQ s₄.mem v.L 1 = 2 ^ (128 * v.L.wq) % v.q := by
    rw [arrQ, wordsVal_congr (m := s₃.mem) (d := slot v.L.wq 24) fun i hi => c1 i (by omega)]; exact I3.2.2
  obtain hR : 2 ^ (128 * v.L.wq) % v.q < v.q := Nat.mod_lt _ (by omega)
  -- The four multiplications, each keeping arrays 0, 1 and 4.
  refine WP.seq (WP.mono (qmont_ok hL I4.1.qs I4.2.1 (o := 6) (a := 6) (b := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [I4.1.q0]; exact h44)) fun s₅ ⟨⟨Q5, I5, _, _, k5a, qa5⟩, k5⟩ => ?_)
  obtain B5 := I4.1.stepQ Q5 k5.2.1 k5.2.2 (qa5.qbuf hL)
  obtain A51 := (k5a 1 (by decide) (by decide) (by decide) (by decide)).trans A1
  obtain A54 := (k5a 4 (by decide) (by decide) (by decide) (by decide)).trans (show arrQ s₄.mem v.L 4 = _ from rfl)
  refine WP.seq (WP.mono (qmont_ok hL Q5 I5 (o := 6) (a := 6) (b := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [A51, B5.q0]; exact hR)) fun s₆ ⟨⟨Q6, I6, _, _, k6a, qa6⟩, k6⟩ => ?_)
  obtain B6 := B5.stepQ Q6 k6.2.1 k6.2.2 (qa6.qbuf hL)
  obtain A61 := (k6a 1 (by decide) (by decide) (by decide) (by decide)).trans A51
  obtain A64 := (k6a 4 (by decide) (by decide) (by decide) (by decide)).trans A54
  refine WP.seq (WP.mono (qmont_ok hL Q6 I6 (o := 5) (a := 5) (b := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [A64, B6.q0]; exact h44)) fun s₇ ⟨⟨Q7, I7, _, _, k7a, qa7⟩, k7⟩ => ?_)
  obtain B7 := B6.stepQ Q7 k7.2.1 k7.2.2 (qa7.qbuf hL)
  obtain A71 := (k7a 1 (by decide) (by decide) (by decide) (by decide)).trans A61
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
      (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1) (.block ptrBuf)))))))))))))) (by kernel_rfl)
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
      (.seq (storeBE 6) (.block ptrBuf2)))))))))))))))) (by kernel_rfl)
      (stQ5 (hsem _ _ h) fun _ I h4 _ => prod_pre I h4 (hsem _ _ h).vals.2.2.2.1 (hsem _ _ h).vals.1 fun _ B => by
        have hL := B.base.ok
        have hql := B.base.ql
        have hpl := B.base.pl
        have hwq := hL.wq_ge
        refine WP.seq (WP.mono (ptrBuf_ok B.base.scr hL B.base.regs) fun s₉ ⟨⟨b7, b8, m9⟩, k9⟩ => ?_)
        obtain B9 := B.stepM k9 m9
        refine WP.seq (WP.mono (storeBE_ok (j := 6) (O := v.L.Buf) (k := v.L.ql) B9.qs.inq.env (by decide)
          (by have := ScrL.bufSt B9.base.scr hL (o := 0) (k := v.L.ql) (by omega_using [hql, hpl])
              simpa only [off, BitVec.add_zero] using this)
          (by have := buf_nowrap hL (o := 0) (k := v.L.ql) (by omega_using [hql, hpl]) (by omega_using [hql])
              simpa only [off, BitVec.add_zero] using this)
          b7 b8 (by omega_using [hql]) (by omega_using [hwq]) (m2_sep hL)) fun _ ⟨⟨_, ot⟩, k10⟩ => ?_)
        obtain B10 := B9.step k10 (QBuf.ofBuf hL ot (by omega_using [hql, hpl]))
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
  obtain h4' : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
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
  obtain hqZ : v.L.qOff + 1600 ≤ v.L.Z := by simp only [Lay.bOff] at hbe; omega_arith
  obtain e := Lay.slot_eq v.L.wp
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  have hq28 : v.L.qOff = slot v.L.wp 28 := rfl
  refine WP.seq (WP.mono (getP_ok B.scr hL B.regs .s8) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_)
  obtain B1 := B.keepM k1 m1
  obtain en1 := ip.env.keep k1
  refine WP.seq (WP.mono (loadArr_ok en1 (j := 4) (N := N) (by decide)
      (by rw [k1.gpr (by decide), h7]; exact (BitVec.add_zero _).symm) a8 (by omega_using [hw, hw8]) (by omega_using [hw8])
      (by rw [k1.2.1, k1.2.2]; exact hN.rd) (fun i hi x hx => hN.sep i hi x (by omega_arith)))
    fun s₂ ⟨⟨_, _, o2, a7⟩, k2⟩ => ?_)
  obtain en2 : Env s₂ v.L.S v.L.qOff v.L.wp := ⟨en1.hs.congr k2.2.2, a7, (k2.gpr (by decide)).trans en1.s5,
    (k2.gpr (by decide)).trans en1.t0, en1.w2, en1.w48, en1.hZ⟩
  obtain B2 := B1.body k2 (Body.ofP hL o2 (by omega_using [e4]) (by omega_using [e4, e28, hq28]))
  refine WP.seq (WP.mono (copy_ok en2 (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨_, o3⟩, k3⟩ => ?_)
  obtain B3 := B2.body k3 (Body.ofP hL o3 (by omega_using [e1]) (by omega_using [e1, e28, hq28]))
  exact WP.mono (getQ_ok B3.scr hL B3.regs .s10) fun _ ⟨⟨a10, m4⟩, k4⟩ =>
    ((B3.keepM k4 m4).fixB.app (fix_envP ⟨((en2.keep k3).keep k4), (B3.keepM k4 m4).regs.s6⟩)).app
      ⟨(k4.gpr (r := .s9) (by decide)).trans ((k3.gpr (r := .s9) (by decide)).trans ((k2.gpr (r := .s9) (by decide)).trans
        ((k1.gpr (r := .s9) (by decide)).trans h9))), a10, trivial⟩

theorem pinsB161 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 161) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.L.Buf 0)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.block (getP .s8))))))))) (by kernel_rfl) (stQ6 (hsem _ _ h) fun _ B _ =>
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
  obtain e := Lay.slot_eq v.L.wp
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e24 := e 24; have e28 := e 28
  refine ⟨B.body k (Body.ofP hL o (by omega_using [e4]) (by simp only [Lay.qOff]; omega_using [e4, e28])), ip, ?_,
    by rw [arrP, o.wordsVal (by omega_using [e0, e4]) (by omega_arith)]; exact p0,
    by rw [arrP, o.wordsVal (by omega_using [e4, e24]) (by omega_arith)]; exact p24⟩
  show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [o.word (by omega_using [e0, e4]) (by omega_arith), k.gpr (by decide)]; exact I

/-- `CB` after the joint table's or the joint windows' code. -/
theorem w_CB {v : VD} {s t : State} {rs : List Reg} (h : CB v s) (ip : InP t v.L)
    (o : Outside v.L.S (slot v.L.wp 1) (23 * (8 * (v.L.wp + 2))) s.mem t.mem) (k : Keep rs s t)
    (ht1 : .t1 ∉ rs := by decide) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : CB v t := by
  obtain ⟨B, -, I, p0, p24⟩ := h
  have hL := B.ok
  have hw := hL.wp_ge
  obtain e := Lay.slot_eq v.L.wp
  obtain e0 := e 0; have e1 := e 1; have e24 := e 24; have e28 := e 28
  refine ⟨B.body k (Body.ofP hL o (by omega_using [e1]) (by simp only [Lay.qOff]; omega_using [e1, e28])) hr, ip, ?_,
    by rw [arrP, o.wordsVal (by omega_using [e0, e1]) (by omega_arith)]; exact p0,
    by rw [arrP, o.wordsVal (by omega_using [e1, e24]) (by omega_arith)]; exact p24⟩
  show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [o.word (by omega_using [e0, e1]) (by omega_arith), k.gpr ht1]; exact I

theorem pinsB169 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 169) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.L.Buf 0)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products
      (.seq (.block HEAD) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.block ptrY)))))))))) (by kernel_rfl)
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
      (by kernel_rfl) (stC1 (hsem _ _ h) fun _ c hk a7 a8 a9 => by
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
      (.seq (montOp 4 6 7) (.block (bufBase .s7 .t2 ++ getP .s8)))))))))))))))))) (by kernel_rfl)
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
  obtain B2 := (B.keepM k1 m1).keepM k2 m2
  exact WP.mono (getP_ok B2.scr hL B2.regs .s10) fun _ ⟨⟨a10, m3⟩, k3⟩ =>
    ⟨⟨B2.keepM k3 m3, (q1.keep k2).keep k3, (k3.gpr (by decide)).trans a9, a10, by rw [m3, m2, m1]⟩,
      (k1.trans k2).trans k3⟩

theorem pinsB344 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 344) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, v.L.Buf), (.s10, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq products (.seq combine (.block CMP)))))))) (by kernel_rfl)
      (stC4 (hsem _ _ h) fun _ B _ => (cmp_pre B).mono fun _ ⟨⟨B', iq, a9, a10, _⟩, _⟩ =>
        (B'.fixB.app (fix_envQ iq)).app ⟨a9, a10, trivial⟩)

theorem pinsB350 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) :
    Pins (At Φ FB 350) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq products (.seq combine (.seq (.block CMP) (.seq ModArith.reduce64 (.block ptrR)))))))))) (by kernel_rfl)
      (stC4 (hsem _ _ h) fun _ B q0 => WP.seq ((cmp_pre B).mono fun s₁ ⟨⟨B1, iq, a9, a10, m1⟩, _⟩ => by
        have hL := B1.ok
        have hwq := hL.wq_ge
        have hqs := hL.qslot
        have hpl := B1.pl
        have e3 := iq.env
        obtain e4 := Lay.slot_eq v.L.wq 4; have e1 := Lay.slot_eq v.L.wq 1
        obtain hq0 : 0 < wordsVal s₁.mem v.L.Q (slot v.L.wq 0) v.L.wq := by
          have := (hsem _ _ h).vals.1
          show 0 < arrQ s₁.mem v.L 0
          rw [arrQ, m1]; show 0 < arrQ _ v.L 0; rw [q0]; omega_using [this]
        exact WP.seq (WP.mono (ModArith.reduce64_ok (D := v.L.Buf) (L := v.L.pl) e3.hs (by omega_using [hwq]) (by omega_using [hwq])
          (by omega_using [hwq, e4]) e3.a7 e3.s5 e3.t0 hq0 (by rw [a9]; exact (BitVec.add_zero _).symm) a10 (by omega_using [hpl])
          (by omega_arith) (fun i hi => (ScrL.bufN B1.scr hL (n := v.L.pl) (by omega_using [])).ld (show i + 1 ≤ v.L.pl by omega_using [hi]))
          (buf_apartQ v.L (by omega_using [hpl]))) fun s₂ ⟨⟨_, o2⟩, k2⟩ => by
            obtain B2 := B1.body k2 (Body.ofQ hL o2 (by omega_using [hwq, e1]))
            exact WP.mono (ptrR_ok B2.scr hL B2.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
              ((B2.keepM k' m).fixB.app (fix_envQ ((iq.keep k2).keep k'))).app ⟨b7, b8, trivial⟩)))

end VG.Proof.Dsa.RISCV64.CT
