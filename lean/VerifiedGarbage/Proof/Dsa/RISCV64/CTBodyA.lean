module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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

/-- The values `body` needs of the key. -/
theorem SB.vals {v : VD} {s : State} (h : SB v s) :
    2 ≤ v.q ∧ v.q % 2 = 1 ∧ v.q < 2 ^ (8 * v.L.ql) ∧ v.qb ≤ v.L.ql ∧ 2 ≤ v.p ∧ v.p % 2 = 1 := by
  obtain ⟨⟨c, ⟨hsz, hp, hq, _⟩, _⟩, _⟩ := h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have hl := c.base.q_lt
  exact ⟨by omega, hq, hl, q_bits (by omega) hl, by omega, hp⟩

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

theorem QB.stepQ {v : VD} {s t : State} (h : QB v s) (Q : QS t v.L v.key v.sig) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (qb : QBuf v.L s.mem t.mem) : QB v t := by
  have hL := h.base.ok
  have hb := qb.body hL
  exact ⟨h.base.step Q.regs hrd hwr (Kept.ofBody hL hb).out (hb.word (by decide)),
    by rw [Lens, hb.word (by decide)]; exact h.lens, Q,
    (qb.arr0 hL).trans h.q0, (qb.arrP hL 0 (by decide)).trans h.p0, (qb.arrP hL 24 (by decide)).trans h.p24⟩

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
  refine WP.mono (ranges_ok hL c.base.scr c.base.regs c.base.hsg) fun t ⟨⟨Q, _, a4, qa⟩, k⟩ => ?_
  have hb := qa.body hL
  have qb := qa.qbuf hL
  rw [c.q0] at a4
  exact ⟨⟨c.base.body k hb, by rw [Lens, hb.word (by decide)]; exact c.lens, Q, (qa.arr0 hL).trans c.q0,
    (qb.arrP hL 0 (by decide)).trans c.p0, (qb.arrP hL 24 (by decide)).trans c.p24⟩, a4⟩

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
  have o' : Outside v.L.S 0 v.L.Z s.mem t.mem := o.mono (Nat.le_refl _) (by simp only [hMask]; omega)
  have w8 : word t.mem v.L.S hDigest = word s.mem v.L.S hDigest :=
    o.word (Or.inr (by decide)) (by simp only [hDigest]; omega)
  have w16 : word t.mem v.L.S hLens = word s.mem v.L.S hLens :=
    o.word (Or.inr (by decide)) (by simp only [hLens]; omega)
  exact ⟨⟨h.base.step Q.regs k.2.1 k.2.2 o' w8, by rw [Lens, w16]; exact h.lens, Q,
    (keepQ_arr0 hL (mask_keepQ hL o)).trans h.q0, (mask_arrP hL o 0 (by decide)).trans h.p0,
    (mask_arrP hL o 24 (by decide)).trans h.p24⟩, ⟨b, w.trans h4⟩⟩

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
  refine WP.mono (inverse_ok hL B.qs I B.base.hsg (by rw [B.q0]; exact hq) (by rw [B.q0]; exact hqo)
    (by rw [B.q0]; exact h24)) fun t ⟨⟨Q', I', a4, kj, qa⟩, k⟩ =>
      ⟨⟨⟨B.stepQ Q' k.2.1 k.2.2 (qa.qbuf hL), I', by rw [kj 24 (by decide) (by decide)]; exact h24⟩,
        by rw [a4, B.q0]; exact Nat.mod_lt _ (by omega), qa.qbuf hL⟩, k⟩

/-! ## The cuts in `ranges` and `qMinus2` -/

theorem enterQ_SB {v : VD} {s : State} (h : SB v s) :
    WP isa (.block (enterQ ++ ptrR)) s fun t => (Base v t ∧ InQ t v.L ∧ t.gpr .s7 = v.sig ∧
      t.gpr .s8 = BitVec.ofNat 64 v.L.ql) ∧ Keep (enterRegs ++ ([.s7, .s8] : List Reg)) s t := by
  have B := h.1.1.base
  refine WP.block_append (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => ?_)
  have B1 := B.keepM k m
  exact WP.mono (ptrR_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
    ⟨⟨B1.keepM k' m', iq.keep k', a7, a8⟩, k.trans k'⟩

theorem pinsB1 : Pins (At ΦB FB 1) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .block (enterQ ++ ptrR)) rfl ((enterQ_SB (semB h)).mono
      fun _ ⟨⟨B, iq, a7, a8⟩, _⟩ => (B.fixB.app (fix_envQ iq)).app ⟨a7, a8, trivial⟩)

theorem pinsB9 : Pins (At ΦB FB 9) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.sig v.L.ql), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    have hql := h |> semB |>.1.1.base.ql
    refine WP.of_flat (c := .seq (.block (enterQ ++ ptrR)) (.seq (loadArr 5) (.block ptrS))) rfl
      (WP.seq (WP.mono (enterQ_SB (semB h)) fun _ ⟨⟨B, iq, a7, a8⟩, _⟩ => ?_))
    have Q : QS _ _ _ _ := ⟨iq, B.scr, B.regs⟩
    have hL := B.ok
    refine WP.seq (WP.mono (loadQ_ok (j := 5) Q hL (by decide) (B.hsg.sub (o := 0) (k := v.L.ql) (by omega))
      (by rw [a7, off_zero]) a8 (by omega) (by have := hL.wq_ge; omega)) fun _ ⟨⟨Q', _, _, o⟩, k⟩ => ?_)
    have qa : QArr v.L _ _ := QArr.of o (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)
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

theorem pinsB50 : Pins (At ΦB FB 50) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    have hq := (semB h).vals.1
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq minus2 (.block ptrBuf))))) rfl
      (stQ3 (semB h) fun _ ⟨B, _, _⟩ _ => ?_)
    have hL := B.base.ok
    refine WP.seq (WP.mono (minus2_ok B.qs.inq.env (show 2 ≤ arrQ _ v.L 0 by rw [B.q0]; exact hq))
      fun _ ⟨⟨_, o⟩, k⟩ => ?_)
    have qa : QArr v.L _ _ := QArr.of o (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)
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

theorem pinsB53 : Pins (At ΦB FB 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.sig v.L.ql), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.block ptrS))))) rfl
      (stQ4 (semB h) fun _ ⟨B, _, _⟩ _ => WP.mono (ptrS_ok B.base.scr B.base.ok B.base.regs)
        fun _ ⟨⟨b7, b8, m⟩, k'⟩ => (fix_QB (B.stepM k' m)).app ⟨b7, b8, trivial⟩)

theorem pinsB63 : Pins (At ΦB FB 63) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, off v.L.Buf 0), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq (.block ptrS)
      (.seq (loadArr 4) (.seq (copy 1 24) (.block (ptrBuf ++ [.addi .s9 .s7 0, .addi .s10 .s8 0]))))))))) rfl
      (stQ4 (semB h) fun _ ⟨B, _, _⟩ _ => ?_)
    have hL := B.base.ok
    have hql := B.base.ql
    have hwq := hL.wq_ge
    refine WP.seq (WP.mono (ptrS_ok B.base.scr hL B.base.regs) fun _ ⟨⟨a7, a8, m⟩, k⟩ => ?_)
    have B1 := B.stepM k m
    refine WP.seq (WP.mono (loadQ_ok (j := 4) B1.qs hL (by decide) (B1.base.hsg.sub (o := v.L.ql) (k := v.L.ql)
      (by omega)) a7 a8 (by omega) (by omega)) fun _ ⟨⟨Q2, _, _, o2⟩, k2⟩ => ?_)
    have B2 := B1.stepQ Q2 k2.2.1 k2.2.2
      (QArr.of o2 (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega) |>.qbuf hL)
    refine WP.seq (WP.mono (copy_ok B2.qs.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
      fun _ ⟨⟨_, o3⟩, k3⟩ => ?_)
    have B3 := B2.step k3 (QArr.of o3 (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)
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

theorem pinsB104 : Pins (At ΦB FB 104) [.s6, .s11, .ra, .a7, .s5, .t0, .s8, .t3, .a0] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s8, BitVec.ofNat 64 v.qb), (.t3, BitVec.ofNat 64 v.d),
      (.a0, BitVec.ofNat 64 (if v.qb < v.d then 1 else 0))]) (fun _ => rfl) fun v _ h => by
    have hqb := (semB h).vals.2.2.2.1
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.block SLB)))))) rfl (stQ5 (semB h) fun _ ⟨B, _, _⟩ _ _ => ?_)
    have hL := B.base.ok
    have hp : v.L.pl < 2 ^ 16 := by have := B.base.pl; simp only [Nat.reducePow]; omega
    have hq : v.L.ql < 2 ^ 16 := by have := B.base.ql; simp only [Nat.reducePow]; omega
    have h3 : v.qb < 2 ^ 16 := by have := B.base.ql; simp only [Nat.reducePow]; omega
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
    refine WP.block_append (WP.block_append (WP.mono (getQb_ok B.base.scr hL B.base.regs.s6 .s8)
      fun u ⟨⟨a8, mu⟩, ku⟩ => WP.mono (getD_ok (B.base.scr.congr ku.2.2) hL
        (by rw [ku.gpr (by decide)]; exact B.base.regs.s6) .t3) fun w ⟨⟨b3, mw⟩, kw⟩ => ?_))
    have l := B.lens
    rw [Lens] at l
    rw [l, pack_qb hp hq h3 h4] at a8
    rw [mu, l, pack_d hp hq h3 h4] at b3
    have a8' : w.gpr .s8 = BitVec.ofNat 64 v.qb := (kw.gpr (by decide)).trans a8
    have hsub := sub_shr63 (a := v.qb) (b := v.d) (by simp only [Nat.reducePow] at *; omega)
      (by simp only [Nat.reducePow] at *; omega)
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 (if v.qb < v.d then 1 else 0) ∧
      t.mem = w.mem) (by brun [a8', b3, exec_shift_d (show 63 < 64 by decide), hsub]) (by decide) (by rfl))
      fun t ⟨⟨c0, mt⟩, kt⟩ => ?_
    have B' := (B.stepM ku mu |>.stepM kw mw).stepM kt mt
    exact (fix_QB B').app ⟨(kt.gpr (r := .s8) (by decide)).trans a8', (kt.gpr (r := .t3) (by decide)).trans b3, c0,
      trivial⟩

theorem pinsB106 : Pins (At ΦB FB 106) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.dig), (.s8, BitVec.ofNat 64 (min v.d v.qb))])
    (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq scalarLen (.block [.load .d .s7 .s6 hDigest]))))))) rfl (stQ5 (semB h) fun _ ⟨B, _, _⟩ _ _ => ?_)
    have hL := B.base.ok
    have h3 : v.qb < 2 ^ 16 := by have := B.base.ql; have := (semB h).vals.2.2.2.1; simp only [Nat.reducePow]; omega
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
    refine WP.seq (WP.mono (scalarLen_ok B.base.scr hL B.base.regs.s6 B.lens h3 h4) fun s₀ ⟨⟨a8, m0⟩, k0⟩ => ?_)
    have B0 := B.stepM k0 m0
    obtain ⟨hin, hal⟩ := ScrL.hdr B0.base.scr hL (d := 8) (by decide) (by decide)
    refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = v.dig ∧ u.mem = s₀.mem)
      (by brun [hDigest, B0.base.regs.s6, hin, hal]; exact B0.base.dig8) (by rfl) (by rfl)) fun _ ⟨⟨a7, m1⟩, k1⟩ => ?_
    exact (fix_QB (B0.stepM k1 m1)).app ⟨a7, (k1.gpr (r := .s8) (by decide)).trans a8, trivial⟩

/-- `scalar`, in the Q space. -/
theorem scalar_QI {v : VD} {s : State} (h : QI v s) (h4 : arrQ s.mem v.L 4 < v.q) (hqb : v.qb ≤ v.L.ql) :
    WP isa scalar s fun t => QI v t ∧ arrQ t.mem v.L 4 < v.q := by
  obtain ⟨B, I, h24⟩ := h
  have hL := B.base.ok
  have h4' : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
  refine WP.mono (scalar_ok hL B.qs B.base.dig8 B.lens hqb h4' (B.base.hdg.take (Nat.min_le_left _ _)))
    fun t ⟨⟨Q, _, o⟩, k⟩ => ?_
  have e1 := Lay.slot_eq v.L.wq 1; have e4 := Lay.slot_eq v.L.wq 4; have e6 := Lay.slot_eq v.L.wq 6
  have e7 := Lay.slot_eq v.L.wq 7; have e24 := Lay.slot_eq v.L.wq 24; have e0 := Lay.slot_eq v.L.wq 0
  have e28 := Lay.slot_eq v.L.wq 28
  have hwq := hL.wq_ge
  have hnw : v.L.Q.toNat + slot v.L.wq 28 ≤ 2 ^ 64 := by have := B.qs.inq.env.hs.nowrap; have := B.qs.inq.env.hZ; omega
  have qa : QArr v.L s.mem t.mem := QArr.of o (by omega) (by omega)
  refine ⟨⟨B.stepQ Q k.2.1 k.2.2 (qa.qbuf hL), ?_, ?_⟩, ?_⟩
  · show ((word t.mem v.L.Q (slot v.L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o.word (by omega) (by omega_arith), k.gpr (by decide)]; exact I
  · rw [arrQ, o.wordsVal (by omega) (by omega_arith)]; exact h24
  · rw [arrQ, o.wordsVal (by omega) (by omega_arith)]; exact h4

theorem pinsB108 : Pins (At ΦB FB 108) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse
      (.seq scalar (.block ptrR))))))) rfl (stQ5 (semB h) fun _ I h4 _ =>
      WP.seq (WP.mono (scalar_QI I h4 (semB h).vals.2.2.2.1) fun _ ⟨⟨B, _, _⟩, _⟩ =>
        WP.mono (ptrR_ok B.base.scr B.base.ok B.base.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
          (fix_QB (B.stepM k' m)).app ⟨b7, b8, trivial⟩))

end VG.Proof.Dsa.RISCV64.CT
