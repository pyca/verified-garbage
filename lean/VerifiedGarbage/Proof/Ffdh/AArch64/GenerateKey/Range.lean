module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Stages
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# `vg_ffdh_generate_key` on AArch64: the scalar's range

As in `vg_ffdh_check_private`, the scalar in `aXm` is tested against 0 and
its bound, and the test is `privateValid` of the attempt's scalar
(`g7_g8`): the cut octets are `scalarOfOctets` of the random ones (`x_eq`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.Ffdh.AArch64.CheckPrivate (bit_iff)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The scalar is the attempt's. -/
theorem x_eq {p : GkP} {rb : List Byte} {t : State} (hb : Base (p.D₁ rb) t) (hm : (p.D₁ rb).mv = true)
    (ho : Ok p rb) : p.X rb = p.s rb := by
  have hk1 : 64 ≤ p.k := hb.k1
  have hdl := hb.doml
  have hl := hb.bb_length
  have hne : (p.D₁ rb).bb ≠ [] := by intro he; rw [he] at hl; simp at hl; omega
  have hL := lead_lt hne
  obtain ⟨hodd, h1, -⟩ := valid_facts hm hb.k1
  have hc : (p.D₁ rb).bc = (p.D₁ rb).bb[(p.D₁ rb).bl]'hL := by
    simp only [FD.bc, FD.bl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL, Option.getD_some]
  have hc8 := ((p.D₁ rb).bc).isLt
  unfold GkP.X GkP.xo
  have hdl' : p.dom.length = p.dl := hdl
  have hd : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k := by rw [hdl']; exact hb.dl
  refine KeyScalar.cut_eq (k := p.k) (dom := p.dom) (by omega) hd (fun _ => ⟨hodd, h1⟩) ho.1 ?_
  show ((BitVec.ofNat 64 (KeyScalar.smearN (p.D₁ rb).bc.toNat)).setWidth 8).toNat = _
  have key : ∀ n : Nat, n = (p.D₁ rb).bc.toNat →
      (2 ^ Spec.RsaKeyGen.bitLength (p.D₁ rb).bc.toNat - 1) % 2 ^ 64 % 2 ^ 8 = 2 ^ Spec.RsaKeyGen.bitLength n - 1 := by
    intro n hn
    subst hn
    have := KeyScalar.smearN_lt _ hc8
    rw [KeyScalar.smearN_eq _ hc8] at this
    omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, KeyScalar.smearN_eq _ hc8]
  exact key _ (congrArg BitVec.toNat hc).symm

/-- The scalar below its bound, as the code compares. -/
def xr (p : GkP) (rb : List Byte) : Prop :=
  if p.dl = 3 * p.k then p.X rb < Spec.Rsa.os2ip (p.D₁ rb).qb else 2 * (p.X rb / 2) + 1 < (p.D₁ rb).P

instance (p : GkP) (rb : List Byte) : Decidable (xr p rb) := by unfold xr; infer_instance

/-- After the test of x against 0. -/
def G4 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aXm) (p.D₁ rb).w = p.X rb ∧
    t.gpr .x9 = bit (¬ p.X rb < 1)) ∧ Ok p rb

theorem g3_g4 (p : GkP) (rb : List Byte) (t : State) (h : G3 p rb t) :
    WP isa (seqs (isNonzero aXm)) t fun u => G4 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hx⟩, ho⟩ := h
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact WP.mono (geArr_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D₁ rb).w by omega)
    (show (p.D₁ rb).w < 2 ^ 31 by omega) (show aXm < 8 by decide) (show aOne < 8 by decide))
    fun u ⟨h9, hm, k⟩ => ⟨⟨⟨mi, hI.keep hm k (by decide), by rw [hm]; exact hx, by rw [h9, hx, hI.2.2.1.one]⟩, ho⟩,
      k.mono (by decide)⟩

/-- Back in the outer workspace, with the test in `sF`. -/
def G5 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aXm) (p.D₁ rb).w = p.X rb ∧
    word t.mem (p.G rb) (8 * sF) = bit (¬ p.X rb < 1)) ∧ Ok p rb

theorem g4_g5 (p : GkP) (rb : List Byte) (t : State) (h : G4 p rb t) :
    WP isa (.block [sth .x9 sF, leave]) t fun u => G5 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hx, h9⟩, ho⟩ := h
  have hG := hI.2.1.good.scr.nowrap
  have sX := slot_le (w := (p.D₁ rb).w) (show aXm < 8 by decide)
  have hX0 := hdr_lt_slot (p.D₁ rb).w aXm (show sF < 32 by decide)
  exact WP.mono hI.stLeave fun u ⟨⟨hP, hF, o⟩, k⟩ => ⟨⟨⟨mi, hP, by rw [o.wv (Or.inr (by omega)) (by omega)]; exact hx,
    by rw [hF, h9]⟩, ho⟩, k⟩

/-- After the test of the domain's length. -/
def G6 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aXm) (p.D₁ rb).w = p.X rb ∧
    word t.mem (p.G rb) (8 * sF) = bit (¬ p.X rb < 1) ∧ t.gpr .x3 = BitVec.ofNat 64 (p.dl - 2 * p.k)) ∧ Ok p rb

theorem g5_g6 (p : GkP) (rb : List Byte) (t : State) (h : G5 p rb t) :
    WP isa (.block qTest) t fun u => G6 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hx, hF⟩, ho⟩ := h
  exact WP.mono hP.qtest fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨⟨mi, hP.outside (o := 256) (n := 0) (by decide)
    (by simp only [inner, slot, hdrBytes]; omega) (fun x _ => by rw [hm]) k.rd k.wr ((k.gpr .x0 (by decide)).trans
      hP.2.2.2.2.2.2), by rw [hm]; exact hx, by rw [hm]; exact hF, h3⟩, ho⟩, k.mono (by decide)⟩

theorem g6_eval {p : GkP} {rb : List Byte} {t : State} (h : G6 p rb t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) := by
  obtain ⟨⟨_, _, _, _, h3⟩, _⟩ := h
  rw [eval_zero, h3]

/-- After the comparison with x's bound. -/
def G7 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ word t.mem (p.G rb) (8 * sF) = bit (¬ p.X rb < 1) ∧ t.gpr .x9 = bit (xr p rb)) ∧
    Ok p rb

/-- Back in the inner workspace, with x and the test in `sF`. -/
def G6e (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aXm) (p.D₁ rb).w = p.X rb ∧
    word t.mem (p.G rb) (8 * sF) = bit (¬ p.X rb < 1)) ∧ Ok p rb

theorem g6_e (p : GkP) (rb : List Byte) (t : State) (h : G6 p rb t) :
    WP isa (.block [enter]) t fun u => G6e p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hx, hF, -⟩, ho⟩ := h
  exact WP.mono hP.enterM fun u ⟨⟨hI, hm⟩, k⟩ => ⟨⟨⟨mi, hI, by rw [hm]; exact hx, by rw [hm]; exact hF⟩, ho⟩, k⟩

theorem e_g7n (p : GkP) (rb : List Byte) (t : State) (h : G6e p rb t) (h2 : p.dl = 2 * p.k) :
    WP isa (seqs (ltP aXm)) t fun u => G7 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hx, hF⟩, ho⟩ := h
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  have hT0 := hdr_lt_slot (p.D₁ rb).w aTmp (show sF < 32 by decide)
  have hG := hI.2.1.good.scr.nowrap
  refine WP.mono (ltP_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D₁ rb).w by omega)
    (show (p.D₁ rb).w < 2 ^ 31 by omega) (show aXm < 8 by decide) (by decide)) fun v ⟨h9, o, k'⟩ => ?_
  have hT := hdr_lt_slot (p.D₁ rb).w aTmp (show 31 < 32 by decide)
  refine ⟨⟨⟨mi, hI.step (rs := [(slot (p.D₁ rb).w aTmp, 8 * (p.D₁ rb).w)]) (Frm.of_outside o (by simp)) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      have := slot_le (w := (p.D₁ rb).w) (show aTmp < 8 by decide)
      have s1 := slot_sep (w := (p.D₁ rb).w) (show aTmp ≠ aN by decide)
      have s2 := slot_sep (w := (p.D₁ rb).w) (show aTmp ≠ aOne by decide)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega) k'.rd k'.wr (k'.gpr .x0 (by decide)),
    by rw [o.word (Or.inl hT0) (show 8 * sF + 8 ≤ 2 ^ 64 by decide), hF], ?_⟩, ho⟩, k'.mono (by decide)⟩
  rw [h9, hx, hI.2.2.1.n]
  refine bit_iff ?_
  unfold xr
  have hk1 : 64 ≤ p.k := hb.k1
  rw [ite_eq_right (by omega)]

/-- With q in `aY`. -/
def G6q (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aXm) (p.D₁ rb).w = p.X rb ∧
    word t.mem (p.G rb) (8 * sF) = bit (¬ p.X rb < 1) ∧
    wv t.mem (p.G rb) (slot (p.D₁ rb).w aY) (p.D₁ rb).w = Spec.Rsa.os2ip (p.D₁ rb).qb) ∧ Ok p rb ∧ p.dl = 3 * p.k

theorem e_lpreQ (p : GkP) (rb : List Byte) (t : State) (h : G6e p rb t) (hq : p.dl = 3 * p.k) :
    LPre aY sQ sK ((p.D₁ rb).ld (p.dp + BitVec.ofNat 64 (2 * p.k)) p.k) t := by
  obtain ⟨⟨mi, hI, -⟩, -⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hl := hb.qlen hq
  have := hb.k1
  have := hI.lpre (sp := sQ) (sl := sK) (show aY < 8 by decide) (by decide) (by decide)
    (hs.get (i := sQ) (v := (p.D₁ rb).dp + BitVec.ofNat 64 (2 * (p.D₁ rb).k)) (by simp))
    (by rw [hl]; exact hs.get (i := sK) (by simp)) hb.qsrc (by rw [hl]; simp at this ⊢; omega) (by rw [hl])
  rw [hl] at this
  exact this

theorem e_q (p : GkP) (rb : List Byte) (t : State) (h : G6e p rb t) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (Crt.loadArr aY sQ sK)) t fun u => G6q p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hx, hF⟩, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hl := hb.qlen hq
  have := hb.k1
  refine WP.mono (hI.load (show aY < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sQ) (v := (p.D₁ rb).dp + BitVec.ofNat 64 (2 * (p.D₁ rb).k)) (by simp))
    (by rw [hl]; exact hs.get (i := sK) (by simp)) hb.qsrc (by rw [hl]; simp at this ⊢; omega) (by rw [hl]))
    fun v ⟨⟨hv, hQ, o⟩, k'⟩ => ?_
  have hG := hI.2.1.good.scr.nowrap
  have sY := slot_le (w := (p.D₁ rb).w) (show aY < 8 by decide)
  have sYX := slot_sep (w := (p.D₁ rb).w) (show aY ≠ aXm by decide)
  have hY0 := hdr_lt_slot (p.D₁ rb).w aY (show sF < 32 by decide)
  have sX := slot_le (w := (p.D₁ rb).w) (show aXm < 8 by decide)
  exact ⟨⟨⟨mi, hv, by rw [o.wv (by omega) (by omega), hx],
    by rw [o.word (Or.inl hY0) (show 8 * sF + 8 ≤ 2 ^ 64 by decide), hF], hQ⟩, ho, hq⟩, k'⟩

theorem q_g7 (p : GkP) (rb : List Byte) (t : State) (h : G6q p rb t) :
    WP isa (seqs (ltArr aXm aY)) t fun u => G7 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hv, hx, hF, hQ⟩, ho, hq⟩ := h
  have hb := hv.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  refine WP.mono (ltArr_ok hv.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D₁ rb).w by omega)
    (show (p.D₁ rb).w < 2 ^ 31 by omega) (show aXm < 8 by decide) (show aY < 8 by decide)) fun w' ⟨h9, hm', k''⟩ =>
      ⟨⟨⟨mi, hv.keep hm' k'' (by decide), by rw [hm']; exact hF, ?_⟩, ho⟩, k''.mono (by decide)⟩
  rw [h9, hx, hQ]
  refine bit_iff ?_
  unfold xr
  rw [ite_eq_left hq]

theorem g6_g7n (p : GkP) (rb : List Byte) (t : State) (h : G6 p rb t)
    (he : isa.eval (.zero .x .x3) t = some true) :
    WP isa (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm)) t fun u => G7 p rb u ∧ KX t u := by
  have h2 := h.1.choose_spec.1.1.noq (by rw [g6_eval h] at he; simpa using he)
  exact wp_seqs_cons (by simp [ltP, Crt.copyArr]) (WP.mono (g6_e p rb t h) fun u ⟨hu, k⟩ =>
    WP.mono (e_g7n p rb u hu h2) fun v ⟨hv, k'⟩ => ⟨hv, keep_trans k k'⟩)

theorem g6_g7q (p : GkP) (rb : List Byte) (t : State) (h : G6 p rb t)
    (he : isa.eval (.zero .x .x3) t = some false) :
    WP isa (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY)) t fun u => G7 p rb u ∧ KX t u := by
  have hq := h.1.choose_spec.1.1.q (by rw [g6_eval h] at he; simpa using he)
  simp only [List.cons_append, List.nil_append]
  exact wp_seqs_cons (by simp [Crt.loadArr]) (WP.mono (g6_e p rb t h) fun u ⟨hu, k⟩ =>
    wp_seqs_append (by simp [Crt.loadArr]) (by simp [ltArr, cmpArr]) (WP.mono (e_q p rb u hu hq) fun v ⟨hv, k'⟩ =>
      WP.mono (q_g7 p rb v hv) fun w' ⟨hw, k''⟩ => ⟨hw, keep_trans k (keep_trans k' k'')⟩))


/-- The scalar's range, as the code computes it. -/
theorem xr_iff {p : GkP} {rb : List Byte} {t : State} (hb : Base (p.D₁ rb) t) (hm : (p.D₁ rb).mv = true) :
    (xr p rb ∧ ¬ p.X rb < 1) ↔ Spec.Ffdh.privateValid p.a (p.X rb) = true := by
  have hodd := (valid_facts hm hb.k1).1
  have hdl : p.dom.length = p.dl := hb.doml
  unfold xr Spec.Ffdh.privateValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, Spec.Ffdh.domainOf, hdl]
  by_cases hq : p.dl = 3 * p.k
  · rw [ite_eq_left hq, ite_eq_left hq]
    simp only [Option.getD_some]
    have e : Spec.Rsa.os2ip (p.D₁ rb).qb = Spec.Rsa.os2ip (List.take p.k (List.drop (2 * p.k) p.dom)) := rfl
    omega
  · rw [ite_eq_right hq, ite_eq_right hq]
    simp only [Option.getD_none]
    have := (lt_pm1 hodd (p.X rb))
    constructor
    · rintro ⟨a, b⟩; exact ⟨by omega, this.mp a⟩
    · rintro ⟨a, b⟩; exact ⟨this.mpr b, by omega⟩

/-- After the test of x's range. -/
def G8 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ t.gpr .x9 = bit (p.pv = true)) ∧ Ok p rb

theorem g7_g8 (p : GkP) (rb : List Byte) (t : State) (h : G7 p rb t) :
    WP isa (.block andF) t fun u => G8 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hF, h9⟩, ho⟩ := h
  refine WP.mono hI.andFlag fun u ⟨hu, h9', _, _, k⟩ => ⟨⟨⟨mi, hu, ?_⟩, ho⟩, k⟩
  rw [h9', h9, hF, bit_and, ho.2.2, ← x_eq hI.1 hI.2.2.2.2.2 ho]
  exact bit_iff ((xr_iff hI.1 hI.2.2.2.2.2).trans (by simp))

theorem g8_eval {p : GkP} {rb : List Byte} {t : State} (h : G8 p rb t) :
    isa.eval (.zero .x .x9) t = some (bit (p.pv = true) == 0) := by
  obtain ⟨⟨_, _, h9⟩, _⟩ := h
  rw [eval_zero, h9]

end VG.Proof.Ffdh.AArch64.GenerateKey
