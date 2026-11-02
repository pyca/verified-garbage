module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

-- separate module: `body`'s cuts and the taint checks of every level cost more than their imports, and
-- `DeriveVerified` states the result without them

/-!
# DSA key derivation on RISC-V: constant time

`derive_ct`: two runs of `vg_dsa_derive_key` from states that satisfy
`dContract` and agree on its public data leak the same trace. The levels up
to g's check are `DeriveCT.lean`'s; `Derive.body`'s list (`FBd`) is cut
after each block that loads the header's words (2, 12, 71, 74, 94, 96, 98):
in `yValue` after g's pointer and the power's loads, after the buffer's
pointer; in `xRange` after the Q space's pointers; in `output` after each
block before a `maskCopy`. The cuts in `output` follow its `maskCopy`s
(`maskCopy_ok`), which need `out`'s permission and its separation from the
domain, x and `scratch`: the contract's, kept by every run (`ow_at`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv take_split)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-! ## `out` -/

/-- `out`'s octets. -/
abbrev oN (v : VD) : Nat := 3 * v.L.pl + 2 * v.L.ql

/-- What derivation's public data satisfies: x's length, the domain's, and
`out`'s range, apart from the domain and x. -/
structure GD (v : VD) : Prop where
  sgl : v.sgl = v.L.ql
  kn : v.kn = 2 * v.L.pl + v.L.ql
  no : (oOf v).toNat + oN v ≤ 2 ^ 64
  ko : ∀ i < 2 * v.L.pl + v.L.ql, ∀ y, ofs (oOf v) y < oN v → off v.key i ≠ y
  xo : ∀ i < v.L.ql, ∀ y, ofs (oOf v) y < oN v → off v.sig i ≠ y
  out : v.out = some (oOf v)

/-- `out` may be written, and is apart from `scratch`. -/
structure OW (v : VD) (u : State) : Prop where
  wr : ∀ i < oN v, InRegions u.wr (off (oOf v) i) 1
  src : Src u v.L (oOf v) (oN v)

theorem OW.keep {v : VD} {s t : State} (h : OW v s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : OW v t :=
  ⟨by rw [hwr]; exact h.wr, h.src.keep hrd hwr⟩

/-- `OW` holds of the states of a level whose starts satisfy it. -/
theorem ow_at {α : Type} {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {o : α → VD}
    (h : ∀ a s, Φ a s → OW (o a) s) {a : α} {u : State} (hu : At Φ F n a u) : OW (o a) u := by
  obtain ⟨s₀, t, h₀, e⟩ := hu
  obtain ⟨hr, hw, -⟩ := Exec.rdwr e
  exact (h a s₀ h₀).keep hr hw

theorem gC0d : ∀ v s, C0d v s → GD v := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨-, -, dOP, dOX, -, -, -, -, -, nwO, -, -, -, -, hol, hpl, -, -, -⟩ := h
  have h1 : (s.gpr .a1).toNat = 3 * (dlayOf s).pl + 2 * (dlayOf s).ql := hol
  refine ⟨rfl, hpl, by show (s.gpr .a0).toNat + (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) ≤ _; rw [← h1]; exact nwO,
    fun i hi y hy => ?_, fun i hi y hy => ?_, ?_⟩
  · exact Pub.ne_of_disjoint (Region.Disjoint.symm dOP) (by omega) i (by simp only [vdD, dlayOf] at hi ⊢; omega) y
      (by rw [h1]; exact hy)
  · exact Pub.ne_of_disjoint (Region.Disjoint.symm dOX) (by omega) i (by simp only [vdD, dlayOf] at hi ⊢; omega) y
      (by rw [h1]; exact hy)
  · rfl

theorem owC0d : ∀ v s, C0d v s → OW v s := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨-, hwr, -, -, dOS, -, -, -, -, nwO, -, -, -, -, hol, -, -, -, -⟩ := h
  have h1 : (s.gpr .a1).toNat = 3 * (dlayOf s).pl + 2 * (dlayOf s).ql := hol
  refine ⟨fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by
      simp only [vdD, oN] at hi; omega) (by simp only [vdD, oN] at hi ⊢; omega)⟩,
    ⟨fun i hi => ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..),
      Offset.contains_base _ (by simp only [vdD, oN] at hi; omega) (by simp only [vdD, oN] at hi ⊢; omega)⟩,
    fun i hi => Pub.ne_of_disjoint dOS (by omega) i (by simp only [vdD, oN] at hi; omega)⟩⟩

theorem gBd : ∀ v u, ΦBd v u → GD v := fun _ _ h =>
  at_pure (G := GD) (fun _ _ h => at_pure (G := GD) (fun _ _ h => at_pure (G := GD) (fun _ _ h =>
    at_pure (G := GD) (fun _ _ h => at_pure (G := GD) (fun _ _ h => at_pure (G := GD) (fun _ _ h =>
      at_pure (G := GD) gC0d h.1) h.1) h.1) h.1) h.1) h.1) h.1

theorem owBd : ∀ v u, ΦBd v u → OW v u := fun _ _ h =>
  ow_at (o := id) (fun _ _ h => ow_at (o := id) (fun _ _ h => ow_at (o := id) (fun _ _ h =>
    ow_at (o := id) (fun _ _ h => ow_at (o := id) (fun _ _ h => ow_at (o := id) (fun _ _ h =>
      ow_at (o := id) owC0d h.1) h.1) h.1) h.1) h.1) h.1) h.1

/-- `body`'s phase, with `out`'s. -/
abbrev DB (v : VD) (u : State) : Prop := SD v u ∧ GD v ∧ OW v u

theorem onDB : ∀ v u, ΦBd v u → DB v u := fun _ _ h => ⟨onBd _ _ h, gBd _ _ h, owBd _ _ h⟩

/-! ## `body`'s cuts in `yValue` -/

theorem DB.vals {v : VD} {s : State} (h : DB v s) : 2 ≤ v.p ∧ v.p % 2 = 1 := by
  obtain ⟨⟨_, ⟨hsz, hp, _, _⟩, _⟩, _⟩ := h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  exact ⟨by omega, hp⟩

theorem Base.xs {v : VD} {s : State} (h : Base v s) (hg : GD v) : Src s v.L v.sig v.L.ql := by
  rw [← hg.sgl]; exact h.hsg

theorem Base.ks {v : VD} {s : State} (h : Base v s) (hg : GD v) : Src s v.L v.key (2 * v.L.pl + v.L.ql) := by
  rw [← hg.kn]; exact h.hk

/-- `yValue`'s first block: x's and g's pointers. -/
abbrev Y0 : List Instr := [.addi .s9 .ra 0] ++ ptrG

theorem stY0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : CK v s) (ow : OW v s)
    (hc : ∀ t, CB v t → OW v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = v.sig → WP isa c t Q) :
    WP isa (.seq (.block Y0) c) s Q := by
  have B := h.base
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = v.sig ∧ u.mem = s.mem)
    (by brun [B.regs.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ =>
    WP.mono (ptrG_ok (B.scr.congr k1.2.2) hL (B.regs.keepM k1 m1)) fun s₂ ⟨⟨b7, b8, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  exact hc s₂ ⟨B.keepM k12 hm2, h.inp.keep k12, by
      show ((word s₂.mem v.L.S (slot v.L.wp 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
      rw [hm2, k12.gpr (by decide)]; exact h.inv,
    by rw [arrP, hm2]; exact h.p0, by rw [arrP, hm2]; exact h.p24⟩ (ow.keep k12.2.1 k12.2.2) b7 b8
    ((k2.gpr (by decide)).trans a9)

theorem pinsBd0 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, fix_CK (hsem _ _ h).1.1⟩

theorem pinsBd2 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, v.sig)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block Y0) (.block (getP .s8))) (by decide +kernel)
      (stY0 (hsem _ _ h).1.1 (hsem _ _ h).2.2 fun _ c _ a7 _ a9 =>
        WP.mono (getP_ok c.1.scr c.1.ok c.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          ((c.1.keepM k m).fixB.app (fix_envP (c.2.1.keep k))).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsBd12 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 12) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, v.sig), (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h =>
    WP.of_flat (c := .seq (.block Y0) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24)
      (.block (getQ .s10)))))) (by decide +kernel)
      (stY0 (hsem _ _ h).1.1 (hsem _ _ h).2.2 fun _ c _ a7 _ a9 =>
        powP_pre c (c.1.hk.sub (by have := c.1.kn; omega)) a7 a9)

/-- `yValue` up to the buffer's pointer, then `c`. -/
theorem stY7 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : DB v s)
    (hc : ∀ t, Base v t → InP t v.L → OW v t → WP isa c t Q) :
    WP isa (.seq (.block Y0) (.seq Verify.powP (.seq (zeroArr 7) (.seq (.block [.li .a4 (-1)])
      (.seq (Sign.nonZero 4) (.seq PublicChecked.one (.seq (Sign.nonZero 4) c))))))) s Q := by
  obtain ⟨hp, hpo⟩ := h.vals
  have hg := h.2.1
  refine stY0 h.1.1 h.2.2 fun s₂ cb ow₂ b7 _ a9 => ?_
  obtain ⟨B, ip, I, p0, p24⟩ := cb
  have hL := B.ok
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hpl := B.pl
  refine WP.seq (WP.mono (powSrc_ok (N := off v.key (v.L.pl + v.L.ql)) (E := v.sig) (p := v.p) hL B.scr B.regs ip I
      (B.hk.sub (by have := B.kn; omega)) b7 (B.xs hg) a9 p0 hp hpo p24)
    fun s₃ ⟨⟨_, in3, _, o3⟩, k3⟩ => ?_)
  have B3 := B.body k3 (Body.ofP hL o3 (yv_b1 v.L).1 (yv_b1 v.L).2)
  refine WP.seq (WP.mono (zeroArr_ok in3.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have B4 := B3.body k4 (Body.ofP hL o4 (yv_b7 v.L).1 (yv_b7 v.L).2.1)
  have en4 := in3.env.keep k4
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask true ∧ u.mem = s₄.mem)
    (by brun [exec_li (show imm12 (-1) by decide)]; rfl) (by decide) (by rfl)) fun s₅ ⟨⟨a4, m5⟩, k5⟩ => ?_)
  have en5 := en4.keep k5
  have B5 := B4.keepM k5 m5
  refine WP.seq (WP.mono (nonZero_ok en5 (a := 4) (c := 0) (by decide) (by rw [m5]; exact z7) a4)
    fun s₆ ⟨⟨b4, m6⟩, k6⟩ => ?_)
  have en6 := en5.keep k6
  have B6 := B5.keepM k6 m6
  refine WP.seq (WP.mono (Pub.oneP_ok en6.hs (by omega) (by omega) (yv_b7 v.L).2.2 en6.a7 en6.s5 en6.t0)
    fun s₇ ⟨⟨v7, o7'⟩, k7⟩ => ?_)
  have o7 : Outside v.L.S (slot v.L.wp 7) (8 * v.L.wp) s₆.mem s₇.mem := o7'
  have en7 := en6.keep k7
  have B7 := B6.body k7 (Body.ofP hL o7 (yv_b7 v.L).1 (yv_b7 v.L).2.1)
  refine WP.seq (WP.mono (nonZero_ok en7 (a := 4) (c := 1) (by decide) v7 ((k7.gpr (by decide)).trans b4))
    fun s₈ ⟨⟨_, m8⟩, k8⟩ => ?_)
  have kall := ((((k3.trans k4).trans k5).trans k6).trans k7).trans k8
  exact hc s₈ (B7.keepM k8 m8) ⟨en7.keep k8, (B7.keepM k8 m8).regs.s6⟩ (ow₂.keep kall.2.1 kall.2.2)

theorem pinsBd71 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 71) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h =>
    WP.of_flat (c := .seq (.block Y0) (.seq Verify.powP (.seq (zeroArr 7) (.seq (.block [.li .a4 (-1)])
      (.seq (Sign.nonZero 4) (.seq PublicChecked.one (.seq (Sign.nonZero 4)
        (.block (bufBase .s7 .t2 ++ getP .s8))))))))) (by decide +kernel)
      (stY7 (hsem _ _ h) fun _ B ip _ => WP.block_append (WP.mono (bufBase_ok B.scr B.ok B.regs (rd := .s7) (t := .t2)
        (by decide) (by decide) (by decide)) fun _ ⟨⟨f7, mu⟩, ku⟩ =>
        WP.mono (getP_ok (B.keepM ku mu).scr B.ok (B.keepM ku mu).regs .s8) fun _ ⟨⟨f8, m9⟩, k9⟩ =>
          (((B.keepM ku mu).keepM k9 m9).fixB.app (fix_envP ((ip.keep ku).keep k9))).app
            ⟨(k9.gpr (r := .s7) (by decide)).trans f7, f8, trivial⟩))

/-- `yValue`, then `c`. -/
theorem stY {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : DB v s)
    (hc : ∀ t b, Base v t → InP t v.L → OW v t → t.gpr .a4 = mask b → WP isa c t Q) :
    WP isa (.seq Derive.yValue c) s Q := by
  obtain ⟨hp, hpo⟩ := h.vals
  have C := h.1.1
  have B := C.base
  exact WP.seq (WP.mono (yValue_ok B.ok B.scr B.regs C.inp C.inv (B.ks h.2.1) (B.xs h.2.1) C.p0 hp hpo C.p24)
    fun t ⟨⟨_, a4, ip, bd, _⟩, k⟩ => hc t _ (B.body k bd) ip (h.2.2.keep k.2.1 k.2.2) a4)

theorem pinsBd74 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 74) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h =>
    WP.of_flat (c := .seq Derive.yValue (.block (enterQ ++ Verify.ptrR))) (by decide +kernel)
      (stY (hsem _ _ h) fun _ _ B _ _ _ => WP.block_append (WP.mono (enterQ_ok B.ok B.scr B.regs)
        fun _ ⟨⟨iq, mu⟩, ku⟩ => WP.mono (ptrR_ok (B.keepM ku mu).scr B.ok (B.keepM ku mu).regs)
          fun _ ⟨⟨b7, b8, m⟩, k'⟩ => (((B.keepM ku mu).keepM k' m).fixB.app (fix_envQ (iq.keep k'))).app
            ⟨b7, b8, trivial⟩))

/-! ## `body`'s cuts in `output` -/

/-- `xRange` after `yValue`, then `c`. -/
theorem stX {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : DB v s)
    (hc : ∀ t b, Base v t → OW v t → t.gpr .a4 = mask b → WP isa c t Q) :
    WP isa (.seq Derive.yValue (.seq Derive.xRange c)) s Q :=
  stY h fun t _ B _ ow a4 => WP.seq (WP.mono (xRange_ok B.ok B.scr B.regs (B.xs h.2.1) a4)
    fun u ⟨⟨a4', _, qa⟩, k⟩ => hc u _ (B.body k (qa.body B.ok)) (ow.keep k.2.1 k.2.2) a4')

/-- `output`'s first block. -/
abbrev OH : List Instr :=
  [.load .d .t4 .s6 Sign.hOut, .addi .t3 .s11 0] ++ getP .t5 ++ getQ .t2 ++ ([.add .t5 .t5 .t5, .add .t5 .t5 .t2] : List Instr)

theorem ohead_ok {v : VD} {s : State} (B : Base v s) (ho : v.out = some (oOf v)) :
    WP isa (.block OH) s fun t => (Base v t ∧ t.gpr .t4 = oOf v ∧ t.gpr .t3 = v.key ∧
      t.gpr .t5 = BitVec.ofNat 64 (2 * v.L.pl + v.L.ql)) ∧ Keep [.t4, .t3, .t5, .t2] s t := by
  have hL := B.ok
  obtain ⟨hin24, hal24⟩ := ScrL.hdr B.scr hL (d := 24) (by decide) (by decide)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4, .t3] (Q := fun u => u.gpr .t4 = oOf v ∧ u.gpr .t3 = v.key ∧ u.mem = s.mem)
    (by brun [Sign.hOut, B.regs.s6, B.regs.s11, hin24, hal24, BitVec.add_zero]; exact B.hout _ ho) (by decide)
      (by rfl)) fun u ⟨⟨a4, a3, mu⟩, ku⟩ => ?_
  have Bu := B.keepM ku mu
  refine WP.mono (getP_ok Bu.scr hL Bu.regs .t5) fun w ⟨⟨b5, mw⟩, kw⟩ => ?_
  have Bw := Bu.keepM kw mw
  refine WP.mono (getQ_ok Bw.scr hL Bw.regs .t2) fun x ⟨⟨b2, mx⟩, kx⟩ => ?_
  have Bx := Bw.keepM kx mx
  refine WP.mono (WP.keep [.t5] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (2 * v.L.pl + v.L.ql) ∧ u.mem = x.mem)
    (by
      brun [kx.gpr (r := .t5) (by decide), b5, b2]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide) (by rfl)) fun t ⟨⟨a5, mt⟩, kt⟩ => ?_
  have kwt := (kw.trans kx).trans kt
  exact ⟨⟨Bx.keepM kt mt, (kwt.gpr (by decide)).trans a4, (kwt.gpr (by decide)).trans a3, a5⟩,
    (((ku.trans kw).trans kx).trans kt).mono (by decide)⟩

/-- The buffer is apart from `out`. -/
theorem buf_out {v : VD} {s : State} (hL : v.L.Ok) (ow : OW v s) :
    ∀ i < v.L.pl, ∀ y, ofs (oOf v) y < oN v → off v.L.Buf i ≠ y := by
  have hbe := hL.buf_end
  have hpl : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  intro i hi y hy he
  subst he
  refine ow.src.sep (ofs (oOf v) (off v.L.Buf i)) hy (off v.L.Buf i) ?_ (off_ofs _ _)
  rw [(bufAt hL (d := i) (by omega)).2]
  simp only [Lay.bOff] at hbe ⊢; omega

/-- `output` up to its second `maskCopy`, then `c`. -/
theorem stO {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : DB v s)
    (hc : ∀ t b, v.L.Ok → ScrL t v.L → Regs t v.L v.key v.sig → OW v t →
      t.gpr .t4 = off (oOf v) (2 * v.L.pl + v.L.ql) → t.gpr .a4 = mask b → WP isa c t Q) :
    WP isa (.seq Derive.yValue (.seq Derive.xRange (.seq (.block OH) (.seq Derive.maskCopy c)))) s Q := by
  have hg := h.2.1
  have hO : v.out = some (oOf v) := h.2.1.out
  refine stX h fun t b B ow a4 => WP.seq (WP.mono (ohead_ok B hO) fun s₁ ⟨⟨B1, e4, e3, e5⟩, k1⟩ => ?_)
  have hL := B1.ok
  have hpl := B1.pl
  have hql := B1.ql
  have hno : (oOf v).toNat + (3 * v.L.pl + 2 * v.L.ql) ≤ 2 ^ 64 := hg.no
  have ow1 := ow.keep k1.2.1 k1.2.2
  refine WP.seq (WP.mono (maskCopy_ok (c := b) (N := 2 * v.L.pl + v.L.ql) (src := v.key) (dst := oOf v)
      (by omega) (by omega) (fun i hi => ow1.wr i (show i < 3 * v.L.pl + 2 * v.L.ql by omega)) (by omega)
      (fun i hi => (B1.ks hg).rd i hi) (fun i hi y hy => hg.ko i hi y (show _ < 3 * v.L.pl + 2 * v.L.ql by omega))
      e3 e4 e5 ((k1.gpr (by decide)).trans a4))
    fun s₂ ⟨⟨_, o2, _, b4⟩, k2⟩ => ?_)
  have in2 : ∀ y, ofs v.L.S y < v.L.Z → s₂.mem y = s₁.mem y :=
    out_in (o := 0) (N := 3 * v.L.pl + 2 * v.L.ql) (by simpa only [off, BitVec.add_zero] using o2) (by omega)
      (by omega) ow1.src.sep
  exact hc s₂ b hL (B1.scr.congr k2.2.2) (Regs.ofIn hL B1.regs k2 in2) (ow1.keep k2.2.1 k2.2.2) b4
    ((k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans a4))

theorem pinsBd94 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 94) [.s6, .s11, .ra, .t4, .t3, .t5] :=
  pins_at_fix (fun v => fixB v ++ [(.t4, oOf v), (.t3, v.key), (.t5, BitVec.ofNat 64 (2 * v.L.pl + v.L.ql))])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq Derive.yValue (.seq Derive.xRange (.block OH))) (by decide +kernel)
      (stX (hsem _ _ h) fun _ _ B _ _ => (ohead_ok B (hsem _ _ h).2.1.out).mono
        fun _ ⟨⟨B', e4, e3, e5⟩, _⟩ => B'.fixB.app ⟨e4, e3, e5, trivial⟩)

theorem pinsBd96 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 96) [.s6, .s11, .ra, .t4, .t3, .t5] :=
  pins_at_fix (fun v => fixB v ++ [(.t4, off (oOf v) (2 * v.L.pl + v.L.ql)), (.t3, v.L.Buf),
      (.t5, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq Derive.yValue (.seq Derive.xRange (.seq (.block OH) (.seq Derive.maskCopy
      (.block (bufBase .t3 .t2 ++ getP .t5)))))) (by decide +kernel)
      (stO (hsem _ _ h) fun _ _ hL hs hr _ e4 _ => WP.block_append (WP.mono (bufBase_ok hs hL hr (rd := .t3) (t := .t2)
        (by decide) (by decide) (by decide)) fun _ ⟨⟨c3, mu⟩, ku⟩ =>
        WP.mono (getP_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t5) fun _ ⟨⟨c5, mw⟩, kw⟩ => by
          have r := (hr.keepM ku mu).keepM kw mw
          exact Fix.app ⟨r.s6, r.s11, r.ra, trivial⟩ ⟨(kw.gpr (r := .t4) (by decide)).trans
            ((ku.gpr (r := .t4) (by decide)).trans e4), (kw.gpr (r := .t3) (by decide)).trans c3, c5, trivial⟩))

theorem pinsBd98 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → DB v u) :
    Pins (At Φ FBd 98) [.t3, .t4, .t5] :=
  pins_at_fix (fun v => [(.t3, v.sig), (.t4, off (off (oOf v) (2 * v.L.pl + v.L.ql)) v.L.pl),
      (.t5, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := .seq Derive.yValue (.seq Derive.xRange (.seq (.block OH) (.seq Derive.maskCopy
      (.seq (.block (bufBase .t3 .t2 ++ getP .t5)) (.seq Derive.maskCopy
        (.block ([.addi .t3 .ra 0] ++ getQ .t5)))))))) (by decide +kernel)
      (stO (hsem _ _ h) fun s₁ _ hL hs hr ow e4 a4 => by
        have hpl : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
        have hql : 20 ≤ v.L.ql ∧ v.L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
        have hno : (oOf v).toNat + (3 * v.L.pl + 2 * v.L.ql) ≤ 2 ^ 64 := (hsem _ _ h).2.1.no
        refine WP.seq (WP.block_append (WP.mono (bufBase_ok hs hL hr (rd := .t3) (t := .t2) (by decide) (by decide)
          (by decide)) fun s₂ ⟨⟨c3, m2⟩, k2⟩ => WP.mono (getP_ok (hs.congr k2.2.2) hL (hr.keepM k2 m2) .t5)
          fun s₃ ⟨⟨c5, m3⟩, k3⟩ => ?_))
        have k13 := k2.trans k3
        have hm3 : s₃.mem = s₁.mem := by rw [m3, m2]
        have hoa : (off (oOf v) (2 * v.L.pl + v.L.ql)).toNat = (oOf v).toNat + (2 * v.L.pl + v.L.ql) :=
          off_toNat (by omega)
        refine WP.seq (WP.mono (maskCopy_ok (N := v.L.pl) (src := v.L.Buf) (dst := off (oOf v) (2 * v.L.pl + v.L.ql))
            (by omega) (by omega)
            (fun i hi => by rw [k13.2.2, off_off]; exact ow.wr _ (show _ < 3 * v.L.pl + 2 * v.L.ql by omega))
            (by omega)
            (by have := bufRd hL (hs.congr k13.2.2) (o := 0) (k := v.L.pl) (by omega)
                simpa only [off, BitVec.add_zero] using this)
            (sep_part (show 2 * v.L.pl + v.L.ql + v.L.pl ≤ 3 * v.L.pl + 2 * v.L.ql by omega)
              (show 3 * v.L.pl + 2 * v.L.ql < 2 ^ 64 by omega) (buf_out hL ow)) ((k3.gpr (by decide)).trans c3)
            ((k13.gpr (by decide)).trans e4) c5 ((k13.gpr (by decide)).trans a4))
          fun s₄ ⟨⟨_, o4, _, d4⟩, k4⟩ => ?_)
        have in4 : ∀ y, ofs v.L.S y < v.L.Z → s₄.mem y = s₃.mem y :=
          out_in (o := 2 * v.L.pl + v.L.ql) (N := 3 * v.L.pl + 2 * v.L.ql) o4 (by omega) (by omega) ow.src.sep
        have r4 : Regs s₄ v.L v.key v.sig := Regs.ofIn hL ((hr.keepM k2 m2).keepM k3 m3) k4 in4
        rw [WP.block_append_iff]
        refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = v.sig ∧ u.mem = s₄.mem)
          (by brun [r4.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₅ ⟨⟨e3, m5⟩, k5⟩ => ?_
        refine WP.mono (getQ_ok ((hs.congr ((k13.trans k4).trans k5).2.2)) hL (r4.keepM k5 m5) .t5)
          fun _ ⟨⟨e5, _⟩, k6⟩ => ?_
        exact ⟨(k6.gpr (r := .t3) (by decide)).trans e3, (k6.gpr (r := .t4) (by decide)).trans
          ((k5.gpr (r := .t4) (by decide)).trans d4), e5, trivial⟩)

/-! ## The relations -/

/-- `body`, from a level whose states are in its phase. -/
theorem body_relD {Φ : VD → State → Prop} (runB : ∀ v s, Φ v s → WP isa (Code.seqL FBd) s fun _ => True)
    (hsem : ∀ v u, Φ v u → DB v u) : RelCT isa (Two Φ) Derive.body fun _ _ => True := by
  refine chain_start (chain_cons runB (m := 2) (by decide) (two_taint _ (pinsBd0 hsem) (by taint_decide)) ?_)
  refine chain_cons runB (m := 12) (by decide) (two_taint _ (pinsBd2 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 71) (by decide) (two_taint _ (pinsBd12 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 74) (by decide) (two_taint _ (pinsBd71 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 94) (by decide) (two_taint _ (pinsBd74 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 96) (by decide) (two_taint _ (pinsBd94 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 98) (by decide) (two_taint _ (pinsBd96 hsem) (by taint_decide)) ?_
  exact two_taint _ (pinsBd98 hsem) (by taint_decide)

theorem s6_keptd : ∀ i ∈ instrs (seg FTd 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTd 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTd6 : Pins (At C0d FTd 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTd (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0d) (F := FTd) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Derive.entry) rfl (frontD _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptd e₂ rfl).trans h₁, trivial⟩

theorem derive_rel : RelCT isa (Two C0d) Derive.derive fun _ _ => True := by
  refine chain_start (chain_cons runTd (m := 1) (by decide)
    (two_taint _ (pins_mono pins_a7 fun _ _ h => at_zero_inv h) (by taint_decide)) ?_)
  refine chain_cons runTd (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontD)) (by taint_decide)) ?_
  refine chain_cons runTd (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontD)) (by taint_decide)) ?_
  refine chain_cons runTd (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontD)) (by taint_decide)) ?_
  refine chain_cons runTd (m := 6) (by decide) (rel_ite_at hFTd (zeroL rfl (zeroT frontD))
    (X1d_rel (body_relD runBd onDB))
    (zero_rel (run_else runTd hFTd) (fun _ _ h => (at_sem (Φ := C0d) (F := TF Derive.entry) (n := 5) (M := MT)
        (fun _ _ h => midT frontD h) (atL rfl h.1)).1.1)
      fun _ _ h => at_pure outD h.1)) ?_
  exact two_taint _ pinsTd6 (by taint_decide)

/-- Runs that agree on the contract's public data have the same public data `vdD`. -/
theorem vdD_eq {s t : State} (hp : dContract.pub s t) : vdD s = vdD t := by
  obtain ⟨-, e0, -, e2, e3, e4, e5, e6, e7, sa0, hl⟩ := hp
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  have e := (List.map_inj_right fun _ _ h => BitVec.eq_of_toNat_eq h).mp e
  simp only [vdD, dlayOf]
  rw [e, e0, e2, e3, e4, e5, e6, e7, sa0]

theorem derive_ct : ConstantTime isa dContract.pre dContract.pub Derive.derive :=
  RelCT.constantTime (derive_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdD s, ⟨hs, rfl⟩, ⟨ht, (vdD_eq hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
