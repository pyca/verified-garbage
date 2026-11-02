module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
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
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.Octets
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
    (hr : ∀ r ∈ inRegs ++ regsRegs ++ ([.t1] : List Reg), r ∉ rs := by decide) : PK v t :=
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

/-- `inverseK` after `qMinus2`, then `c`. -/
theorem stINV {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → QInv t v.L → arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q → arrQ t.mem v.L 4 < v.q →
      arrQ t.mem v.L 25 < v.q → WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ (.seq Verify.qMinus2
      (.seq Sign.inverseK c)))))) s Q := by
  obtain ⟨hq, hqo, -⟩ := h.vals
  refine stQM h fun t K I h24 r25 => ?_
  have hL := K.base.ok
  exact WP.seq (WP.mono (inverseK_ok hL K.qs I (K.base.ns h.2.1) (by rw [K.q0]; exact hq) (by rw [K.q0]; exact hqo)
      (by rw [K.q0]; exact h24))
    fun u ⟨⟨Q, I', w4, k24, qa⟩, k⟩ => hc u (K.withQ Q k qa) I' (by rw [k24 24 (by decide) (by decide)]; exact h24)
      (by rw [w4, K.q0]; exact Nat.mod_lt _ (by omega)) (by rw [k24 25 (by decide) (by decide)]; exact r25))

theorem pinsBs236 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 236) [.s6, .s11, .ra, .a7, .s5, .t0, .s8, .t3, .a0] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s8, BitVec.ofNat 64 v.qb), (.t3, BitVec.ofNat 64 v.d),
      (.a0, BitVec.ofNat 64 (if v.qb < v.d then 1 else 0))]) (fun _ => rfl) fun v _ h => by
    have hqb := (hsem _ _ h).vals.2.2.2.1
    refine WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.block SLB))))))) (by decide +kernel)
      (stINV (hsem _ _ h) fun _ K _ _ _ _ => ?_)
    have hL := K.base.ok
    have hp : v.L.pl < 2 ^ 16 := by have := K.base.pl; simp only [Nat.reducePow]; omega
    have hq : v.L.ql < 2 ^ 16 := by have := K.base.ql; simp only [Nat.reducePow]; omega
    have h3 : v.qb < 2 ^ 16 := by have := K.base.ql; simp only [Nat.reducePow]; omega
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
    refine WP.block_append (WP.block_append (WP.mono (getQb_ok K.base.scr hL K.base.regs.s6 .s8)
      fun u ⟨⟨a8, mu⟩, ku⟩ => WP.mono (getD_ok (K.base.scr.congr ku.2.2) hL
        (by rw [ku.gpr (by decide)]; exact K.base.regs.s6) .t3) fun w ⟨⟨b3, mw⟩, kw⟩ => ?_))
    have l := K.lens
    rw [Lens] at l
    rw [l, pack_qb hp hq h3 h4] at a8
    rw [mu, l, pack_d hp hq h3 h4] at b3
    have a8' : w.gpr .s8 = BitVec.ofNat 64 v.qb := (kw.gpr (by decide)).trans a8
    have hsub := sub_shr63 (a := v.qb) (b := v.d) (by simp only [Nat.reducePow] at *; omega)
      (by simp only [Nat.reducePow] at *; omega)
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 (if v.qb < v.d then 1 else 0) ∧
      t.mem = w.mem) (by brun [a8', b3, exec_shift_d (show 63 < 64 by decide), hsub]) (by decide) (by rfl))
      fun t ⟨⟨c0, mt⟩, kt⟩ => ?_
    have K' := ((K.keepM ku mu).keepM kw mw).keepM kt mt
    exact (fix_QK K').app ⟨(kt.gpr (r := .s8) (by decide)).trans a8', (kt.gpr (r := .t3) (by decide)).trans b3, c0,
      trivial⟩

theorem pinsBs238 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 238) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.dig), (.s8, BitVec.ofNat 64 (min v.d v.qb))])
    (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.seq Verify.scalarLen (.block [.load .d .s7 .s6 hDigest])))))))) (by decide +kernel)
      (stINV (hsem _ _ h) fun _ K _ _ _ _ => ?_)
    have hL := K.base.ok
    have h3 : v.qb < 2 ^ 16 := by
      have := K.base.ql; have := (hsem _ _ h).vals.2.2.2.1; simp only [Nat.reducePow]; omega
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
    refine WP.seq (WP.mono (scalarLen_ok K.base.scr hL K.base.regs.s6 K.lens h3 h4) fun s₀ ⟨⟨a8, m0⟩, k0⟩ => ?_)
    have K0 := K.keepM k0 m0
    obtain ⟨hin, hal⟩ := ScrL.hdr K0.base.scr hL (d := 8) (by decide) (by decide)
    refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = v.dig ∧ u.mem = s₀.mem)
      (by brun [hDigest, K0.base.regs.s6, hin, hal]; exact K0.base.dig8 (hsem _ _ h).2.1.full) (by rfl) (by rfl))
      fun _ ⟨⟨a7, m1⟩, k1⟩ => ?_
    exact (fix_QK (K0.keepM k1 m1)).app ⟨a7, (k1.gpr (r := .s8) (by decide)).trans a8, trivial⟩

/-- The digest's scalar is below `2 q`. -/
theorem SBs.hz {v : VD} {s : State} (h : SBs v s) (m : Mem) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m v.dig (min v.d v.qb)) < 2 * v.q := by
  obtain ⟨⟨⟨_, ⟨hsz, _, _, _⟩, _⟩, _⟩, _⟩ := h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have hq8 : Spec.Dsa.bitLength v.q = 8 * (Spec.Dsa.bitLength v.q / 8) := by
    have : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength v.p) (Spec.Dsa.bitLength v.q) := hsz
    unfold Spec.Dsa.supportedSizes at this; omega
  refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
  rw [VG.Proof.Bignum.bytesAt_length]
  refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)) ?_
  have := pow_bitLength_le (q := v.q) (by omega)
  rw [hq8, Nat.pow_mul] at this
  exact this

theorem pinsBs252 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 252) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key (3 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.ql),
      (.s9, off v.key (3 * v.L.pl + v.L.ql)), (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.seq Verify.scalar (.seq (zeroArr 7) (.seq (Sign.addMod 6 6 7)
        (.block (Sign.ptrX ++ [.addi .s9 .s7 0, .addi .s10 .s8 0]))))))))))) (by decide +kernel)
      (stINV (hsem _ _ h) fun _ K _ _ _ _ => ?_)
    have hL := K.base.ok
    have hwq := hL.wq_ge
    have hqs := hL.qslot
    have e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
    have e0 := e 0; have e1 := e 1; have e6 := e 6; have e7 := e 7; have e8 := e 8; have e28 := e 28
    have hqb := (hsem _ _ h).vals.2.2.2.1
    have h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
    refine WP.seq (WP.mono (scalar_ok hL K.qs (K.base.dig8 (hsem _ _ h).2.1.full) K.lens hqb h4
      (K.base.hdg.take (Nat.min_le_left _ _))) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
    have K1 := K.withQ Q1 k1 (QArr.of o1 (by omega) (by omega))
    refine WP.seq (WP.mono (zeroArr_ok K1.qs.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
    have K2 := K1.qarr k2 (QArr.of o2 (by omega) (by omega))
    have z2 : arrQ s₂.mem v.L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt _ v.dig (min v.d v.qb)) :=
      (o2.wordsVal (by omega) (by omega)).trans v6
    refine WP.seq (WP.mono (addMod_ok K2.qs.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by show arrQ s₂.mem v.L 6 + arrQ s₂.mem v.L 7 < 2 * arrQ s₂.mem v.L 0
          rw [z2, show arrQ s₂.mem v.L 7 = 0 from z7, K2.q0, Nat.add_zero]; exact (hsem _ _ h).hz _))
      fun s₃ ⟨⟨_, fr3⟩, k3⟩ => ?_)
    have K3 := K2.qarr k3 (fr3.qarr (by decide) (by decide))
    refine WP.block_append (WP.mono (ptrX_ok K3.qs.scr hL K3.qs.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
      WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) ∧
        u.gpr .s10 = BitVec.ofNat 64 v.L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
      fun _ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_)
    exact (fix_QK ((K3.keepM k4 m4).keepM k5 m5)).app ⟨(k5.gpr (r := .s7) (by decide)).trans b7,
      (k5.gpr (r := .s8) (by decide)).trans b8, c9, c10, trivial⟩

/-- `sValue` after `inverseK`, then `c`. -/
theorem stSV {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, QK v t → WP isa c t Q) :
    WP isa (.seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ (.seq Verify.qMinus2
      (.seq Sign.inverseK (.seq Sign.sValue c))))))) s Q := by
  obtain ⟨hq, hqo, -, hqb, -⟩ := h.vals
  have bd := VG.Proof.Dsa.supported_bounds h.1.1.2.1.1
  refine stINV h fun t K I h24 h4 r25 => ?_
  have hL := K.base.ok
  have hd : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
  exact WP.seq (WP.mono (sValue_ok hL K.qs I (K.base.dig8 h.2.1.full) K.lens hqb hd
      (K.base.hdg.take (Nat.min_le_left _ _)) K.os.key (by rw [K.q0]; omega) (by rw [K.q0]; exact hqo)
      (by rw [K.q0]; exact h24) (by rw [K.q0]; exact h4) (by rw [K.q0]; exact r25) (by rw [K.q0]; exact h.hz _))
    fun u ⟨⟨Q, _, _, _, qa⟩, k⟩ => hc u (K.withQ Q k qa))

theorem pinsBs323 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 323) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, oOf v), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => by
    refine WP.of_flat (c := .seq Sign.keyPair (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.seq Sign.sValue (.seq (zeroArr 7)
        (.seq (.block [.load .d .a4 .s6 hMask]) (.seq (Sign.nonZero 6) (.seq (.block [.addi .s4 .a4 0])
          (.seq (Sign.sel 1 25 7) (.seq (Sign.sel 2 6 7) (.block ([.load .d .s7 .s6 Sign.hOut] ++ getQ .s8)))))))))))))))
      (by decide +kernel) (stSV (hsem _ _ h) fun _ K => ?_)
    have hL := K.base.ok
    have hwq := hL.wq_ge
    have hqs := hL.qslot
    have e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
    have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e6 := e 6; have e7 := e 7
    have e8 := e 8; have e25 := e 25; have e26 := e 26; have e28 := e 28
    obtain ⟨b, hm⟩ := K.mw
    refine WP.seq (WP.mono (zeroArr_ok K.qs.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
    have qa1 : QArr v.L _ s₁.mem := QArr.of o1 (by omega) (by omega)
    have K1 := K.qarr k1 qa1
    obtain ⟨hld, hal⟩ := ScrL.hdr K1.qs.scr hL (d := 0) (by decide) (by decide)
    have hw1 : word s₁.mem v.L.S hMask = mask b := by rw [(qa1.body hL).word (by decide)]; exact hm
    refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₁.mem)
      (by brun [hMask, K1.qs.regs.s6, hld, hal]; exact hw1) (by decide) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
    have K2 := K1.keepM k2 m2
    refine WP.seq (WP.mono (nonZero_ok K2.qs.inq.env (a := 6) (c := 0) (by decide) (by rw [m2]; exact z7) a4)
      fun s₃ ⟨⟨b4, m3⟩, k3⟩ => ?_)
    have K3 := K2.keepM k3 m3
    refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = mask (b && decide (wordsVal s₂.mem v.L.Q
        (slot v.L.wq 6) v.L.wq ≠ 0)) ∧ u.mem = s₃.mem)
      (by brun [b4, BitVec.add_zero]) (by decide) (by rfl)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
    have K4 := K3.keepM k4 m4
    refine WP.seq (WP.mono (sel_ok K4.qs.inq.env (o := 1) (a := 25) (t := 7) (by decide) (by decide)
      (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨_, o5⟩, k5⟩ => ?_)
    have K5 := K4.qarr k5 (QArr.of o5 (by omega) (by omega))
    refine WP.seq (WP.mono (sel_ok K5.qs.inq.env (o := 2) (a := 6) (t := 7) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((k5.gpr (by decide)).trans a20)) fun s₆ ⟨⟨_, o6⟩, k6⟩ => ?_)
    have K6 := K5.qarr k6 (QArr.of o6 (by omega) (by omega))
    obtain ⟨hld', hal'⟩ := ScrL.hdr K6.qs.scr hL (d := 24) (by decide) (by decide)
    refine WP.block_append (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = oOf v ∧ u.mem = s₆.mem)
      (by brun [Sign.hOut, K6.qs.regs.s6, hld', hal']; exact K6.base.hout _ (hsem _ _ h).2.1.out) (by decide) (by rfl))
      fun s₇ ⟨⟨a7, m7⟩, k7⟩ => WP.mono (getQ_ok (K6.qs.scr.congr k7.2.2) hL (K6.qs.regs.keepM k7 m7) .s8)
        fun _ ⟨⟨a8, m8⟩, k8⟩ => ?_)
    exact (fix_QK ((K6.keepM k7 m7).keepM k8 m8)).app ⟨(k8.gpr (r := .s7) (by decide)).trans a7, a8, trivial⟩

/-! ## The relations -/

/-- `body`, from a level whose states are in its phase. -/
theorem body_relS {Φ : VD → State → Prop} (runB : ∀ v s, Φ v s → WP isa (Code.seqL FBs) s fun _ => True)
    (hsem : ∀ v u, Φ v u → SBs v u) : RelCT isa (Two Φ) Sign.body fun _ _ => True := by
  refine chain_start (chain_cons runB (m := 2) (by decide) (two_taint _ (pinsBs0 hsem) (by taint_decide)) ?_)
  refine chain_cons runB (m := 12) (by decide) (two_taint _ (pinsBs2 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 53) (by decide) (two_taint _ (pinsBs12 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 66) (by decide) (two_taint _ (pinsBs53 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 76) (by decide) (two_taint _ (pinsBs66 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 117) (by decide) (two_taint _ (pinsBs76 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 120) (by decide) (two_taint _ (pinsBs117 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 131) (by decide) (two_taint _ (pinsBs120 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 139) (by decide) (two_taint _ (pinsBs131 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 182) (by decide) (two_taint _ (pinsBs139 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 185) (by decide) (two_taint _ (pinsBs182 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 195) (by decide) (two_taint _ (pinsBs185 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 236) (by decide) (two_taint _ (pinsBs195 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 238) (by decide) (two_taint _ (pinsBs236 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 252) (by decide) (two_taint _ (pinsBs238 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 323) (by decide) (two_taint _ (pinsBs252 hsem) (by taint_decide)) ?_
  exact two_taint _ (pinsBs323 hsem) (by taint_decide)

theorem sign_ct : ConstantTime isa sContract.pre sContract.pub Sign.sign :=
  RelCT.constantTime ((sign_rel (body_relS runBs onSBs)).mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdS s, ⟨hs, rfl⟩, ⟨ht, (vdS_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
