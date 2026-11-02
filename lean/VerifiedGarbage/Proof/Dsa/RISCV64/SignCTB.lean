module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

-- separate module: `body`'s cuts and their taint checks cost more than their imports, and `SignVerified`
-- states the result without them

/-!
# DSA signing on RISC-V: constant time, `body`

`sign_ct`: two runs of `vg_dsa_sign` from states that satisfy `sContract`
and agree on its public data leak the same trace. The levels are
`SignCT.lean`'s; `Sign.body`'s list (`FBs`) is cut after each block that
loads the header's words: in `keyPair` (2, 12, 53), `gk` (66, 76, 117),
`rRanges` (120, 131, 139), `qMinus2` (182), `inverseK` (185, 195), `sValue`
(236, 238, 252) and `output` (323). Between them the phases carry the key's
and `out`'s regions (`OS`, the contract's, kept by every run), the header's
words and the arrays' facts the pieces need.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-! ## The regions -/

/-- What signing's public data satisfies. -/
structure GS (v : VD) : Prop where
  sgl : v.sgl = v.L.ql
  kn : v.kn = 3 * v.L.pl + v.L.ql
  no : (oOf v).toNat + 2 * v.L.ql ≤ 2 ^ 64
  out : v.out = some (oOf v)
  full : v.full = true

/-- The key (x too) may be read, `out` written, both apart from `scratch`. -/
structure OS (v : VD) (u : State) : Prop where
  key : Src u v.L v.key (3 * v.L.pl + 2 * v.L.ql)
  wr : ∀ i < 2 * v.L.ql, InRegions u.wr (off (oOf v) i) 1
  src : Src u v.L (oOf v) (2 * v.L.ql)

theorem OS.keep {v : VD} {s t : State} (h : OS v s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : OS v t :=
  ⟨h.key.keep hrd hwr, by rw [hwr]; exact h.wr, h.src.keep hrd hwr⟩

theorem os_at {Φ : VD → State → Prop} {F : List (Prog isa)} {n : Nat} (h : ∀ v s, Φ v s → OS v s) {v : VD}
    {u : State} (hu : At Φ F n v u) : OS v u := by
  obtain ⟨s₀, t, h₀, e⟩ := hu
  obtain ⟨hr, hw, -⟩ := Exec.rdwr e
  exact (h v s₀ h₀).keep hr hw

theorem gC0s : ∀ v s, C0s v s → GS v := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, nwO, -, -, -, -, -, hol, -, -, -, -⟩ := h
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  exact ⟨rfl, rfl, by show (s.gpr .a0).toNat + 2 * (slayOf s).ql ≤ _; rw [← h1]; exact nwO, rfl, rfl⟩

theorem osC0s : ∀ v s, C0s v s → OS v s := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨hrd, hwr, -, -, -, dOS, -, dKS, -, -, -, nwO, nwK, -, -, -, -, hol, hkl, -, -, -⟩ := h
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  refine ⟨ssrc (by rw [hrd]; simp) dKS (s.gpr .a3).isLt (by simp only [vdS]; omega) rfl rfl,
    fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by
      simp only [vdS] at hi; omega) (by simp only [vdS] at hi ⊢; omega)⟩,
    ⟨fun i hi => ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..),
      Offset.contains_base _ (by simp only [vdS] at hi; omega) (by simp only [vdS] at hi ⊢; omega)⟩,
    fun i hi => Pub.ne_of_disjoint dOS (by omega) i (by simp only [vdS] at hi; omega)⟩⟩

theorem gBs : ∀ v u, ΦBs v u → GS v := fun _ _ h =>
  at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h =>
    at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h =>
      at_pure (G := GS) (fun _ _ h => at_pure (G := GS) gC0s h.1) h.1) h.1) h.1) h.1) h.1) h.1) h.1

theorem osBs : ∀ v u, ΦBs v u → OS v u := fun _ _ h =>
  os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h =>
    os_at (fun _ _ h => os_at (fun _ _ h => os_at osC0s h.1) h.1) h.1) h.1) h.1) h.1) h.1) h.1

/-- `body`'s phase, with the regions. -/
abbrev SBs (v : VD) (u : State) : Prop := SS v u ∧ GS v ∧ OS v u

theorem onSBs : ∀ v u, ΦBs v u → SBs v u := fun _ _ h => ⟨onBs _ _ h, gBs _ _ h, osBs _ _ h⟩

theorem SBs.vals {v : VD} {s : State} (h : SBs v s) :
    2 ≤ v.q ∧ v.q % 2 = 1 ∧ v.q < 2 ^ (8 * v.L.ql) ∧ v.qb ≤ v.L.ql ∧ 2 ≤ v.p ∧ v.p % 2 = 1 := by
  obtain ⟨⟨⟨c, ⟨hsz, hp, hq, _⟩, _⟩, _⟩, _⟩ := h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have hl := c.base.q_lt
  exact ⟨by omega, hq, hl, q_bits (by omega) hl, by omega, hp⟩

/-! ## The P space -/

/-- In the P space during `body`. -/
structure PK (v : VD) (t : State) : Prop where
  cb : CB v t
  lens : Lens v v.qb t
  q0 : arrQ t.mem v.L 0 = v.q
  os : OS v t

theorem PK.frame {v : VD} {s t : State} {rs : List Reg} (h : PK v s) (k : Keep rs s t)
    (ip : InP t v.L) (I : PInv t v.L) (K : BKept v.L s.mem t.mem) (hp0 : arrP t.mem v.L 0 = arrP s.mem v.L 0)
    (hp24 : arrP t.mem v.L 24 = arrP s.mem v.L 24) (hq0 : arrQ t.mem v.L 0 = arrQ s.mem v.L 0)
    (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : PK v t :=
  ⟨⟨h.cb.1.step (h.cb.1.regs.ofBKept k K hr) k.2.1 k.2.2 K.out (K.word (by decide) (by decide))
      (K.word (by decide) (by decide)), ip, I, hp0.trans h.cb.2.2.2.1, hp24.trans h.cb.2.2.2.2⟩,
    by rw [Lens, K.word (by decide) (by decide)]; exact h.lens, hq0.trans h.q0, h.os.keep k.2.1 k.2.2⟩

theorem PK.keepM {v : VD} {s t : State} {rs : List Reg} (h : PK v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs ++ [.t1], r ∉ rs := by decide) : PK v t :=
  h.frame k (h.cb.2.1.keep k fun r hm' => hr r (by simp [hm'])) (by
      show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
      rw [hm, k.gpr (fun hm' => hr .t1 (by simp) hm')]; exact h.cb.2.2.1)
    (by rw [hm]; exact BKept.refl _ _) (by rw [arrP, hm]) (by rw [arrP, hm]) (by rw [arrQ, hm])
    fun r hm' => hr r (by simp [hm'])

theorem sbs_PK {v : VD} {s : State} (h : SBs v s) : PK v s :=
  let c := h.1.1.1
  ⟨⟨c.base, c.inp, c.inv, c.p0, c.p24⟩, c.lens, c.q0, h.2.2⟩

theorem fix_PK {v : VD} {t : State} (h : PK v t) : Fix (fixB v ++ envP v) t := fix_CB h.cb

/-- `keyPair`'s first block: x's and g's pointers. -/
abbrev KP0 : List Instr := Sign.ptrX ++ ([.addi .s9 .s7 0] : List Instr) ++ ptrG

theorem stKP0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : PK v s)
    (hc : ∀ t, PK v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) → WP isa c t Q) :
    WP isa (.seq (.block KP0) c) s Q := by
  have B := h.cb.1
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (ptrX_ok B.scr hL B.regs) fun s₁ ⟨⟨a7, _, m1⟩, k1⟩ =>
    WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) ∧ u.mem = s₁.mem)
      (by brun [a7, BitVec.add_zero]) (by decide) (by rfl)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)))
  have h2 := (h.keepM k1 m1).keepM k2 m2
  exact WP.mono (ptrG_ok h2.cb.1.scr hL h2.cb.1.regs) fun t ⟨⟨b7, b8, m3⟩, k3⟩ =>
    hc t (h2.keepM k3 m3) b7 b8 ((k3.gpr (by decide)).trans a9)

theorem pinsBs0 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, fix_PK (sbs_PK (hsem _ _ h))⟩

theorem pinsBs2 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.key (3 * v.L.pl + v.L.ql))]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.block (getP .s8))) (by decide +kernel)
      (stKP0 (sbs_PK (hsem _ _ h)) fun _ c a7 _ a9 =>
        WP.mono (getP_ok c.cb.1.scr c.cb.1.ok c.cb.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          (fix_PK (c.keepM k m)).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsBs12 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 12) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, off v.key (3 * v.L.pl + v.L.ql)), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24)
      (.block (getQ .s10)))))) (by decide +kernel)
      (stKP0 (sbs_PK (hsem _ _ h)) fun _ c a7 _ a9 =>
        powP_pre c.cb (c.cb.1.hk.sub (by have := c.cb.1.kn; omega)) a7 a9)

/-- A power in the P space, from its pointers. -/
theorem powK {v : VD} {s : State} {N E : Addr} (h : PK v s) (hN : Src s v.L N v.L.pl) (h7 : s.gpr .s7 = N)
    (hE : Src s v.L E v.L.ql) (h9 : s.gpr .s9 = E) (hp : 2 ≤ v.p) (hpo : v.p % 2 = 1) :
    WP isa Verify.powP s fun t => PK v t := by
  have B := h.cb.1; have ip := h.cb.2.1; have I := h.cb.2.2.1; have p0 := h.cb.2.2.2.1
  have p24 := h.cb.2.2.2.2
  have hL := B.ok
  have e := Lay.slot_eq v.L.wp
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have hw := hL.wp_ge
  refine WP.mono (powSrc_ok hL B.scr B.regs ip I hN h7 hE h9 p0 hp hpo p24) fun t ⟨⟨_, ip', I', o⟩, k⟩ =>
    h.frame k ip' I' (BKept.ofBody hL (p_arrays_body hL o)) (o.wordsVal (by omega) (by omega_arith))
      (o.wordsVal (by omega) (by omega_arith)) (keepQ_arr0 hL ((PLow.keepQ hL o)))

theorem pinsBs53 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h => by
    obtain ⟨-, -, -, -, hp, hpo⟩ := (hsem _ _ h).vals
    exact WP.of_flat (c := .seq (.block KP0) (.seq Verify.powP (.block ptrY))) (by decide +kernel)
      (stKP0 (sbs_PK (hsem _ _ h)) fun _ c a7 _ a9 => WP.seq (WP.mono (powK c
        (c.cb.1.hk.sub (by have := c.cb.1.kn; omega)) a7 (c.os.key.sub (by omega)) a9 hp hpo) fun _ c' =>
        WP.mono (ptrY_ok c'.cb.1.scr c'.cb.1.ok c'.cb.1.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ =>
          (fix_PK (c'.keepM k m)).app ⟨b7, b8, trivial⟩))

/-- The mask of the key's checks is in the header's word `hMask`. -/
abbrev MWs (v : VD) (t : State) : Prop := ∃ b, word t.mem v.L.S hMask = mask b

/-- `keyPair`, then `c`. -/
theorem stKP {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, PK v t → MWs v t → WP isa c t Q) : WP isa (.seq Sign.keyPair c) s Q := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  have P := sbs_PK h
  have B := P.cb.1; have ip := P.cb.2.1; have I := P.cb.2.2.1; have p0 := P.cb.2.2.2.1
  have p24 := P.cb.2.2.2.2; have os := P.os
  have hL := B.ok
  refine WP.seq (WP.mono (keyPair_ok hL B.scr B.regs ip I os.key p0 hp hpo p24)
    fun t ⟨⟨mx, ip', I', m, o, w⟩, k⟩ => hc t (P.frame k ip' I' ((BKept.ofBody hL (PLow.body hL o)).trans
      (BKept.ofMask hL w)) (by rw [mask_arrP hL w 0 (by decide), PLow.arr hL o (by decide) (.inl rfl)])
      (by rw [mask_arrP hL w 24 (by decide), PLow.arr hL o (by decide) (.inr (by decide))])
      (by rw [keepQ_arr0 hL (mask_keepQ hL w), keepQ_arr0 hL (PLow.keepQ hL o)])) ⟨_, mx⟩)

/-- `gk`'s first block: the nonce's and g's pointers. -/
abbrev G0 : List Instr := [.addi .s9 .ra 0] ++ ptrG

theorem stG0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : PK v s)
    (hc : ∀ t, PK v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = v.sig → WP isa c t Q) :
    WP isa (.seq (.block G0) c) s Q := by
  have B := h.cb.1
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = v.sig ∧ u.mem = s.mem)
    (by brun [B.regs.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_))
  have h1 := h.keepM k1 m1
  exact WP.mono (ptrG_ok h1.cb.1.scr hL h1.cb.1.regs) fun t ⟨⟨b7, b8, m2⟩, k2⟩ =>
    hc t (h1.keepM k2 m2) b7 b8 ((k2.gpr (by decide)).trans a9)

theorem pinsBs66 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 66) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, v.sig)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq Sign.keyPair (.seq (.block G0) (.block (getP .s8)))) (by decide +kernel)
      (stKP (hsem _ _ h) fun _ P _ => stG0 P fun _ c a7 _ a9 =>
        WP.mono (getP_ok c.cb.1.scr c.cb.1.ok c.cb.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          (fix_PK (c.keepM k m)).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsBs76 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 76) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, v.sig), (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h =>
    WP.of_flat (c := .seq Sign.keyPair (.seq (.block G0) (.seq (.block (getP .s8)) (.seq (loadArr 4)
      (.seq (copy 1 24) (.block (getQ .s10))))))) (by decide +kernel)
      (stKP (hsem _ _ h) fun _ P _ => stG0 P fun _ c a7 _ a9 =>
        powP_pre c.cb (c.cb.1.hk.sub (by have := c.cb.1.kn; omega)) a7 a9)

theorem Base.ns {v : VD} {s : State} (h : Base v s) (hg : GS v) : Src s v.L v.sig v.L.ql := by
  rw [← hg.sgl]; exact h.hsg

theorem pinsBs117 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 117) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => by
    obtain ⟨-, -, -, -, hp, hpo⟩ := (hsem _ _ h).vals
    exact WP.of_flat (c := .seq Sign.keyPair (.seq (.block G0) (.seq Verify.powP
      (.block (bufBase .s7 .t2 ++ getP .s8))))) (by decide +kernel)
      (stKP (hsem _ _ h) fun _ P _ => stG0 P fun _ c a7 _ a9 => WP.seq (WP.mono (powK c
        (c.cb.1.hk.sub (by have := c.cb.1.kn; omega)) a7 (c.cb.1.ns (hsem _ _ h).2.1) a9 hp hpo) fun _ c' =>
        WP.block_append (WP.mono (bufBase_ok c'.cb.1.scr c'.cb.1.ok c'.cb.1.regs (rd := .s7) (t := .t2)
          (by decide) (by decide) (by decide)) fun _ ⟨⟨f7, mu⟩, ku⟩ =>
          WP.mono (getP_ok (c'.keepM ku mu).cb.1.scr c'.cb.1.ok (c'.keepM ku mu).cb.1.regs .s8)
            fun _ ⟨⟨f8, m9⟩, k9⟩ => (fix_PK ((c'.keepM ku mu).keepM k9 m9)).app
              ⟨(k9.gpr (r := .s7) (by decide)).trans f7, f8, trivial⟩)))

/-- `keyPair` and `gk`, then `c`. -/
theorem stGK {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, Base v t → Lens v v.qb t → arrQ t.mem v.L 0 = v.q → OS v t → MWs v t → WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk c)) s Q := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  refine stKP h fun t P ⟨b, mw⟩ => ?_
  obtain ⟨⟨B, ip, I, p0, p24⟩, l, q0, os⟩ := P
  have hL := B.ok
  refine WP.seq (WP.mono (gk_ok hL B.scr B.regs ip I (B.hk.take (by have := B.kn; omega)) (B.ns h.2.1) p0 hp hpo
    p24) fun u ⟨⟨_, _, _, m, o, b'⟩, k⟩ => ?_)
  have hb : Body v.L t.mem u.mem := (PLow.body hL o).trans (Body.ofBuf hL b' (by omega))
  have K := BKept.ofBody hL hb
  exact hc u (B.step (B.regs.ofBKept k K) k.2.1 k.2.2 K.out (K.word (by decide) (by decide))
      (K.word (by decide) (by decide))) (by rw [Lens, K.word (by decide) (by decide)]; exact l)
    (by rw [keepQ_arr0 hL (bufKeepQ b' (by rcases hL.pl with e | e | e <;> rw [e] <;> decide)),
      keepQ_arr0 hL (PLow.keepQ hL o)]; exact q0) (os.keep k.2.1 k.2.2) ⟨b, by rw [hb.word (by decide)]; exact mw⟩

theorem pinsBs120 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 120) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, v.L.Buf), (.s10, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.block CMP))) (by decide +kernel)
      (stGK (hsem _ _ h) fun _ B _ _ _ _ => (cmp_pre B).mono fun _ ⟨⟨B', iq, a9, a10, _⟩, _⟩ =>
        (B'.fixB.app (fix_envQ iq)).app ⟨a9, a10, trivial⟩)

/-! ## The Q space -/

/-- In the Q space during `body`, with q in its array 0. -/
structure QK (v : VD) (t : State) : Prop where
  base : Base v t
  lens : Lens v v.qb t
  qs : QS t v.L v.key v.sig
  q0 : arrQ t.mem v.L 0 = v.q
  os : OS v t
  mw : MWs v t

theorem QK.frame {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (Q : QS t v.L v.key v.sig) (k : Keep rs s t)
    (K : BKept v.L s.mem t.mem) (hq0 : arrQ t.mem v.L 0 = arrQ s.mem v.L 0) (mw : MWs v t) : QK v t :=
  ⟨h.base.step Q.regs k.2.1 k.2.2 K.out (K.word (by decide) (by decide)) (K.word (by decide) (by decide)),
    by rw [Lens, K.word (by decide) (by decide)]; exact h.lens, Q, hq0.trans h.q0, h.os.keep k.2.1 k.2.2, mw⟩

theorem QK.withQ {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (Q : QS t v.L v.key v.sig) (k : Keep rs s t)
    (qa : QArr v.L s.mem t.mem) : QK v t :=
  have hL := h.base.ok
  h.frame Q k (BKept.ofBody hL (qa.body hL)) (qa.arr0 hL)
    (let ⟨b, w⟩ := h.mw; ⟨b, by rw [(qa.body hL).word (by decide)]; exact w⟩)

theorem QK.qarr {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (k : Keep rs s t) (qa : QArr v.L s.mem t.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) : QK v t :=
  h.withQ (h.qs.step k (qa.body h.base.ok) hr) k qa

theorem QK.keepM {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) : QK v t :=
  h.qarr k (by rw [hm]; exact Outside.refl _ _ _ _) hr

theorem fix_QK {v : VD} {t : State} (h : QK v t) : Fix (fixB v ++ envQ v) t := h.base.fixB.app (fix_envQ h.qs.inq)

/-- Up to `rRanges`' first block, then `c`. -/
theorem stCMP {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → t.gpr .s9 = v.L.Buf → t.gpr .s10 = BitVec.ofNat 64 v.L.pl → WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq (.block CMP) c))) s Q :=
  stGK h fun _ B l q0 os mw => WP.seq ((cmp_pre B).mono fun t ⟨⟨B', iq, a9, a10, m⟩, k⟩ =>
    hc t ⟨B', by rw [Lens, m]; exact l, ⟨iq, B'.scr, B'.regs⟩, by rw [arrQ, m]; exact q0, os.keep k.2.1 k.2.2,
      let ⟨b, w⟩ := mw; ⟨b, by rw [m]; exact w⟩⟩ a9 a10)

/-- `rRanges` up to the nonce's pointer, then `c`. -/
theorem stR6 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq (.block CMP) (.seq ModArith.reduce64 (.seq (copy 25 1)
      (.seq (zeroArr 7) c)))))) s Q := by
  have hq := h.vals.1
  refine stCMP h fun s₂ K a9 a10 => ?_
  have hL := K.base.ok
  have hql : 20 ≤ v.L.ql ∧ v.L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e7 := e 7; have e8 := e 8; have e25 := e 25
  have e26 := e 26; have e28 := e 28
  have e2 := K.qs.inq.env
  refine WP.seq (WP.mono (ModArith.reduce64_ok (B := v.L.Q) (Z := 1600) (w := v.L.wq) (D := v.L.Buf) (L := v.L.pl)
    e2.hs (by omega) (by omega) (by omega) e2.a7 e2.s5 e2.t0
    (by show 0 < arrQ s₂.mem v.L 0; rw [K.q0]; omega) (by rw [a9]; exact (BitVec.add_zero _).symm) a10 (by omega)
    (by omega)
    (by have := bufRd hL K.base.scr (o := 0) (k := v.L.pl) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (buf_apartQ v.L (n := v.L.pl) (by omega))) fun s₃ ⟨⟨_, o3⟩, k3⟩ => ?_)
  have K3 := K.qarr k3 (QArr.of o3 (by omega) (by omega))
  refine WP.seq (WP.mono (copy_ok K3.qs.inq.env (o := 25) (a := 1) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨_, o4⟩, k4⟩ => ?_)
  have K4 := K3.qarr k4 (QArr.of o4 (by omega) (by omega))
  exact WP.seq (WP.mono (zeroArr_ok K4.qs.inq.env (j := 7) (by decide)) fun s₅ ⟨⟨_, o5⟩, k5⟩ =>
    hc s₅ (K4.qarr k5 (QArr.of o5 (by omega) (by omega))))

theorem pinsBs131 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 131) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq (.block CMP) (.seq ModArith.reduce64
      (.seq (copy 25 1) (.seq (zeroArr 7) (.block Verify.ptrR))))))) (by decide +kernel)
      (stR6 (hsem _ _ h) fun _ K => WP.mono (ptrR_ok K.qs.scr K.base.ok K.qs.regs)
        fun _ ⟨⟨b7, b8, m⟩, k⟩ => (fix_QK (K.keepM k m)).app ⟨b7, b8, trivial⟩)

theorem pinsBs139 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 139) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key (3 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h => WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq (.block CMP)
      (.seq ModArith.reduce64 (.seq (copy 25 1) (.seq (zeroArr 7) (.seq (.block Verify.ptrR) (.seq (loadArr 6)
        (.block Sign.ptrX))))))))) (by decide +kernel)
      (stR6 (hsem _ _ h) fun _ K => by
        have hL := K.base.ok
        have hql : 20 ≤ _ ∧ _ ≤ 32 := K.base.ql
        have hwq := hL.wq_ge
        refine WP.seq (WP.mono (ptrR_ok K.qs.scr hL K.qs.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ => ?_)
        have K1 := K.keepM k m
        refine WP.seq (WP.mono (loadQ_ok (j := 6) K1.qs hL (by decide) (K1.base.ns (hsem _ _ h).2.1) b7 b8
          (by omega) (by omega)) fun _ ⟨⟨Q2, _, _, o2⟩, k2⟩ => ?_)
        have K2 := K1.withQ Q2 k2 (QArr.of o2 (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))
        exact WP.mono (ptrX_ok K2.qs.scr hL K2.qs.regs) fun _ ⟨⟨c7, c8, m'⟩, k'⟩ =>
          (fix_QK (K2.keepM k' m')).app ⟨c7, c8, trivial⟩)

/-- `rRanges` after `gk`, then `c`. -/
theorem stRR {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → arrQ t.mem v.L 25 < v.q → WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges c))) s Q := by
  have hq := h.vals.1
  refine stGK h fun t B l q0 os ⟨b, mw⟩ => ?_
  have hL := B.ok
  refine WP.seq (WP.mono (rRanges_ok hL B.scr B.regs os.key (B.ns h.2.1) (by rw [q0]; omega) mw)
    fun u ⟨⟨Q, r25, m, ⟨m₁, fa, fb⟩⟩, k⟩ => hc u ⟨B.step Q.regs k.2.1 k.2.2 ?_ ?_ ?_, ?_, Q, ?_, os.keep k.2.1 k.2.2,
      ⟨_, m⟩⟩ (by rw [r25, q0]; exact Nat.mod_lt _ (by omega)))
  all_goals have K : BKept v.L t.mem u.mem := (BKept.ofBody hL (fa.body hL)).trans (BKept.ofMask hL fb)
  · exact K.out
  · exact K.word (by decide) (by decide)
  · exact K.word (by decide) (by decide)
  · rw [Lens, K.word (by decide) (by decide)]; exact l
  · exact (mask_keepQ' hL fa fb).trans q0

/-- `rrQ` after `rRanges`, then `c`. -/
theorem stRQ {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → QInv t v.L → arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q → arrQ t.mem v.L 25 < v.q →
      WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ c)))) s Q := by
  obtain ⟨hq, hqo, -⟩ := h.vals
  refine stRR h fun t K r25 => ?_
  have hL := K.base.ok
  exact WP.seq (WP.mono (rrQ25_ok hL K.qs (by rw [K.q0]; exact hq) (by rw [K.q0]; exact hqo))
    fun u ⟨⟨Q, I, h24, a25, qa⟩, k⟩ => hc u (K.frame Q k (BKept.ofBody hL (qa.body hL)) (qa.arr0 hL)
      (let ⟨b, w⟩ := K.mw; ⟨b, by rw [(qa.body hL).word (by decide)]; exact w⟩)) I (by rw [h24, K.q0])
      (by rw [a25 25 (by decide) (by decide)]; exact r25))

theorem pinsBs182 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 182) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.minus2 (.block Verify.ptrBuf)))))) (by decide +kernel)
      (stRQ (hsem _ _ h) fun _ K _ _ _ => by
        have hL := K.base.ok
        refine WP.seq (WP.mono (minus2_ok K.qs.inq.env (show 2 ≤ arrQ _ v.L 0 by rw [K.q0]; exact (hsem _ _ h).vals.1))
          fun _ ⟨⟨_, o⟩, k⟩ => ?_)
        have K' := K.qarr k (QArr.of o (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))
        exact WP.mono (ptrBuf_ok K'.qs.scr hL K'.qs.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
          (fix_QK (K'.keepM k' m)).app ⟨b7, b8, trivial⟩)

/-- `qMinus2` after `rrQ`, then `c`. -/
theorem stQM {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → QInv t v.L → arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q → arrQ t.mem v.L 25 < v.q →
      WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 c))))) s Q := by
  obtain ⟨hq, -, hql, -⟩ := h.vals
  refine stRQ h fun t K I h24 r25 => ?_
  have hL := K.base.ok
  exact WP.seq (WP.mono (qMinus2_ok hL K.qs (by rw [K.q0]; exact hq) (by rw [K.q0]; exact hql))
    fun u ⟨⟨Q, _, kj, w0, qb⟩, k⟩ => hc u (K.frame Q k (BKept.ofBody hL (qb.body hL)) (qb.arr0 hL)
      (let ⟨b, w⟩ := K.mw; ⟨b, by rw [(qb.body hL).word (by decide)]; exact w⟩)) (I.keepW w0 (k.gpr (by decide)))
      (by rw [kj 24 (by decide) (by decide)]; exact h24) (by rw [kj 25 (by decide) (by decide)]; exact r25))

theorem pinsBs185 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 185) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.block Verify.ptrR)))))) (by decide +kernel)
      (stQM (hsem _ _ h) fun _ K _ _ _ => WP.mono (ptrR_ok K.qs.scr K.base.ok K.qs.regs)
        fun _ ⟨⟨b7, b8, m⟩, k⟩ => (fix_QK (K.keepM k m)).app ⟨b7, b8, trivial⟩)

theorem pinsBs195 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 195) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql), (.s9, off v.L.Buf 0),
      (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq (.block Verify.ptrR) (.seq (loadArr 4) (.seq (copy 1 24)
        (.block (Verify.ptrBuf ++ [.addi .s9 .s7 0, .addi .s10 .s8 0])))))))))) (by decide +kernel)
      (stQM (hsem _ _ h) fun _ K _ _ _ => by
        have hL := K.base.ok
        have hql : 20 ≤ _ ∧ _ ≤ 32 := K.base.ql
        have hwq := hL.wq_ge
        refine WP.seq (WP.mono (ptrR_ok K.qs.scr hL K.qs.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ => ?_)
        have K1 := K.keepM k m
        refine WP.seq (WP.mono (loadQ_ok (j := 4) K1.qs hL (by decide) (K1.base.ns (hsem _ _ h).2.1) b7 b8
          (by omega) (by omega)) fun _ ⟨⟨Q2, _, _, o2⟩, k2⟩ => ?_)
        have K2 := K1.withQ Q2 k2 (QArr.of o2 (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))
        refine WP.seq (WP.mono (copy_ok K2.qs.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
          fun _ ⟨⟨_, o3⟩, k3⟩ => ?_)
        have K3 := K2.qarr k3 (QArr.of o3 (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))
        refine WP.block_append (WP.mono (ptrBuf_ok K3.qs.scr hL K3.qs.regs) fun t ⟨⟨c7, c8, m4⟩, k4⟩ =>
          WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off v.L.Buf 0 ∧
            u.gpr .s10 = BitVec.ofNat 64 v.L.ql ∧ u.mem = t.mem) (by brun [c7, c8, BitVec.add_zero]) (by decide)
            (by rfl)) fun _ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_)
        exact (fix_QK ((K3.keepM k4 m4).keepM k5 m5)).app ⟨(k5.gpr (r := .s7) (by decide)).trans c7,
          (k5.gpr (r := .s8) (by decide)).trans c8, c9, c10, trivial⟩)

end VG.Proof.Dsa.RISCV64.CT
