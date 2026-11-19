module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Out
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Ffdh.AArch64.ScalarRange`, which this module and modules that import it used -/

section

/-!
# FFDH on AArch64: an imported scalar's range

`CheckPrivate.scalarRange` tests the number `X` in `aXm` of the inner
workspace for p against 0 and against its bound (q, or `p − 1` without q),
for any run's data `D` (`scalarRange_ok`): it leaves `privateValid` of `X`
in `x9`. `vg_ffdh_check_private` and `vg_ffdh_derive_public` run it on the
imported x.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem bit_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : bit P = bit Q := by
  by_cases hp : P
  · simp [bit, hp, h.mp hp]
  · simp [bit, hp, mt h.mpr hp]

namespace ScalarRange

/-- The inner workspace's base. -/
abbrev FD.G (D : FD) : Addr := off D.B (inner D.w)

/-- `X` below its bound, as the code compares. -/
def xr (D : FD) (X : Nat) : Prop :=
  if D.dl = 3 * D.k then X < Spec.Rsa.os2ip D.qb else 2 * (X / 2) + 1 < D.P

instance (D : FD) (X : Nat) : Decidable (xr D X) := by unfold xr; infer_instance

/-- `privateValid` of `X`, for the run's domain. -/
abbrev pv (D : FD) (X : Nat) : Bool := Spec.Ffdh.privateValid (Spec.Ffdh.domainOf D.k D.dom) X

/-- With `X` in `aXm`. -/
def S2 (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, In D mi t ∧ wv t.mem (FD.G D) (slot D.w aXm) D.w = X

/-- After the test of `X` against 0. -/
def S3 (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, In D mi t ∧ wv t.mem (FD.G D) (slot D.w aXm) D.w = X ∧ t.gpr .x9 = bit (¬ X < 1)

theorem s2_s3 {D : FD} {X : Nat} {t : State} (h : S2 D X t) :
    WP isa (seqs (isNonzero aXm)) t fun u => S3 D X u ∧ KX t u := by
  obtain ⟨mi, hI, hx⟩ := h
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact WP.mono (geArr_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ D.w by omega_arith)
    (show D.w < 2 ^ 31 by omega_arith) (show aXm < 8 by decide) (show aOne < 8 by decide))
    fun u ⟨h9, hm, k⟩ => ⟨⟨mi, hI.keep hm k (by decide), by rw [hm]; exact hx, by rw [h9, hx, hI.2.2.1.one]⟩,
      k.mono (by decide)⟩

/-- Back in the outer workspace, with the test in `sF`. -/
def S4 (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, Pa D mi t ∧ wv t.mem (FD.G D) (slot D.w aXm) D.w = X ∧ word t.mem (FD.G D) (8 * sF) = bit (¬ X < 1)

theorem s3_s4 {D : FD} {X : Nat} {t : State} (h : S3 D X t) :
    WP isa (.block [sth .x9 sF, leave]) t fun u => S4 D X u ∧ KX t u := by
  obtain ⟨mi, hI, hx, h9⟩ := h
  have hG := hI.2.1.good.scr.nowrap
  have sX := slot_le (w := D.w) (show aXm < 8 by decide)
  have hX0 := hdr_lt_slot D.w aXm (show sF < 32 by decide)
  exact WP.mono hI.stLeave fun u ⟨⟨hP, hF, o⟩, k⟩ =>
    ⟨⟨mi, hP, by rw [o.wv (Or.inr (by omega_arith)) (by omega_arith)]; exact hx, by rw [hF, h9]⟩, k⟩

/-- After the test of the domain's length. -/
def S5 (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, Pa D mi t ∧ wv t.mem (FD.G D) (slot D.w aXm) D.w = X ∧ word t.mem (FD.G D) (8 * sF) = bit (¬ X < 1) ∧
    t.gpr .x3 = BitVec.ofNat 64 (D.dl - 2 * D.k)

theorem s4_s5 {D : FD} {X : Nat} {t : State} (h : S4 D X t) :
    WP isa (.block qTest) t fun u => S5 D X u ∧ KX t u := by
  obtain ⟨mi, hP, hx, hF⟩ := h
  exact WP.mono hP.qtest fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨mi, hP.outside (o := 256) (n := 0) (by decide)
    (by simp only [inner, slot, hdrBytes]; omega_arith) (fun x _ => by rw [hm]) k.rd k.wr ((k.gpr .x0 (by decide)).trans
      hP.2.2.2.2.2.2), by rw [hm]; exact hx, by rw [hm]; exact hF, h3⟩, k.mono (by decide)⟩

theorem s5_eval {D : FD} {X : Nat} {t : State} (h : S5 D X t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) := by
  obtain ⟨_, _, _, _, h3⟩ := h
  rw [eval_zero, h3]

/-- After the comparison with `X`'s bound. -/
def S6 (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, In D mi t ∧ word t.mem (FD.G D) (8 * sF) = bit (¬ X < 1) ∧ t.gpr .x9 = bit (xr D X)

/-- Back in the inner workspace, with `X` and the test in `sF`. -/
def S5e (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, In D mi t ∧ wv t.mem (FD.G D) (slot D.w aXm) D.w = X ∧ word t.mem (FD.G D) (8 * sF) = bit (¬ X < 1)

theorem s5_e {D : FD} {X : Nat} {t : State} (h : S5 D X t) :
    WP isa (.block [enter]) t fun u => S5e D X u ∧ KX t u := by
  obtain ⟨mi, hP, hx, hF, -⟩ := h
  exact WP.mono hP.enterM fun u ⟨⟨hI, hm⟩, k⟩ => ⟨⟨mi, hI, by rw [hm]; exact hx, by rw [hm]; exact hF⟩, k⟩

theorem e_s6n {D : FD} {X : Nat} {t : State} (h : S5e D X t) (h2 : D.dl = 2 * D.k) :
    WP isa (seqs (ltP aXm)) t fun u => S6 D X u ∧ KX t u := by
  obtain ⟨mi, hI, hx, hF⟩ := h
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  have hT0 := hdr_lt_slot D.w aTmp (show sF < 32 by decide)
  have hG := hI.2.1.good.scr.nowrap
  refine WP.mono (ltP_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ D.w by omega_arith)
    (show D.w < 2 ^ 31 by omega_arith) (show aXm < 8 by decide) (by decide)) fun v ⟨h9, o, k'⟩ => ?_
  have hT := hdr_lt_slot D.w aTmp (show 31 < 32 by decide)
  refine ⟨⟨mi, hI.step (rs := [(slot D.w aTmp, 8 * D.w)]) (Frm.of_outside o (by simp)) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      have := slot_le (w := D.w) (show aTmp < 8 by decide)
      have s1 := slot_sep (w := D.w) (show aTmp ≠ aN by decide)
      have s2 := slot_sep (w := D.w) (show aTmp ≠ aOne by decide)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega_arith) k'.rd k'.wr (k'.gpr .x0 (by decide)),
    by rw [o.word (Or.inl hT0) (show 8 * sF + 8 ≤ 2 ^ 64 by decide), hF], ?_⟩, k'.mono (by decide)⟩
  rw [h9, hx, hI.2.2.1.n]
  refine bit_iff ?_
  unfold xr
  have hk1 : 64 ≤ D.k := hb.k1
  rw [ite_eq_right (by omega_arith)]

/-- With q in `aY`. -/
def S5q (D : FD) (X : Nat) (t : State) : Prop :=
  (∃ mi, In D mi t ∧ wv t.mem (FD.G D) (slot D.w aXm) D.w = X ∧
    word t.mem (FD.G D) (8 * sF) = bit (¬ X < 1) ∧
    wv t.mem (FD.G D) (slot D.w aY) D.w = Spec.Rsa.os2ip D.qb) ∧ D.dl = 3 * D.k

theorem e_lpreQ {D : FD} {X : Nat} {t : State} (h : S5e D X t) (hq : D.dl = 3 * D.k) :
    LPre aY sQ sK (D.ld (D.dp + BitVec.ofNat 64 (2 * D.k)) D.k) t := by
  obtain ⟨mi, hI, -⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hl := hb.qlen hq
  have := hb.k1
  have := hI.lpre (sp := sQ) (sl := sK) (show aY < 8 by decide) (by decide) (by decide)
    (hs.get (i := sQ) (v := D.dp + BitVec.ofNat 64 (2 * D.k)) (by simp))
    (by rw [hl]; exact hs.get (i := sK) (by simp)) hb.qsrc (by rw [hl]; omega_arith) (by rw [hl])
  rw [hl] at this
  exact this

theorem e_q {D : FD} {X : Nat} {t : State} (h : S5e D X t) (hq : D.dl = 3 * D.k) :
    WP isa (seqs (Crt.loadArr aY sQ sK)) t fun u => S5q D X u ∧ KX t u := by
  obtain ⟨mi, hI, hx, hF⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hl := hb.qlen hq
  have := hb.k1
  refine WP.mono (hI.load (show aY < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sQ) (v := D.dp + BitVec.ofNat 64 (2 * D.k)) (by simp))
    (by rw [hl]; exact hs.get (i := sK) (by simp)) hb.qsrc (by rw [hl]; omega_arith) (by rw [hl]))
    fun v ⟨⟨hv, hQ, o⟩, k'⟩ => ?_
  have hG := hI.2.1.good.scr.nowrap
  have sY := slot_le (w := D.w) (show aY < 8 by decide)
  have sYX := slot_sep (w := D.w) (show aY ≠ aXm by decide)
  have hY0 := hdr_lt_slot D.w aY (show sF < 32 by decide)
  have sX := slot_le (w := D.w) (show aXm < 8 by decide)
  exact ⟨⟨⟨mi, hv, by rw [o.wv (by omega_arith) (by omega_arith), hx],
    by rw [o.word (Or.inl hY0) (show 8 * sF + 8 ≤ 2 ^ 64 by decide), hF], hQ⟩, hq⟩, k'⟩

theorem q_s6 {D : FD} {X : Nat} {t : State} (h : S5q D X t) :
    WP isa (seqs (ltArr aXm aY)) t fun u => S6 D X u ∧ KX t u := by
  obtain ⟨⟨mi, hv, hx, hF, hQ⟩, hq⟩ := h
  have hb := hv.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  refine WP.mono (ltArr_ok hv.2.1.good (Nat.le_refl _) (show 1 ≤ D.w by omega_arith)
    (show D.w < 2 ^ 31 by omega_arith) (show aXm < 8 by decide) (show aY < 8 by decide)) fun w' ⟨h9, hm', k''⟩ =>
      ⟨⟨mi, hv.keep hm' k'' (by decide), by rw [hm']; exact hF, ?_⟩, k''.mono (by decide)⟩
  rw [h9, hx, hQ]
  refine bit_iff ?_
  unfold xr
  rw [ite_eq_left hq]

theorem s5_s6n {D : FD} {X : Nat} {t : State} (h : S5 D X t) (he : isa.eval (.zero .x .x3) t = some true) :
    WP isa (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm)) t fun u => S6 D X u ∧ KX t u := by
  have h2 := h.choose_spec.1.1.noq (by rw [s5_eval h] at he; simpa using he)
  exact wp_seqs_cons (by simp [ltP, Crt.copyArr]) (WP.mono (s5_e h) fun u ⟨hu, k⟩ =>
    WP.mono (e_s6n hu h2) fun v ⟨hv, k'⟩ => ⟨hv, keep_trans k k'⟩)

theorem s5_s6q {D : FD} {X : Nat} {t : State} (h : S5 D X t) (he : isa.eval (.zero .x .x3) t = some false) :
    WP isa (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY)) t
      fun u => S6 D X u ∧ KX t u := by
  have hq := h.choose_spec.1.1.q (by rw [s5_eval h] at he; simpa using he)
  simp only [List.cons_append, List.nil_append]
  exact wp_seqs_cons (by simp [Crt.loadArr]) (WP.mono (s5_e h) fun u ⟨hu, k⟩ =>
    wp_seqs_append (by simp [Crt.loadArr]) (by simp [ltArr, cmpArr]) (WP.mono (e_q hu hq) fun v ⟨hv, k'⟩ =>
      WP.mono (q_s6 hv) fun w' ⟨hw, k''⟩ => ⟨hw, keep_trans k (keep_trans k' k'')⟩))

/-- `X`'s bound. -/
theorem s5_s6 {D : FD} {X : Nat} {t : State} (h : S5 D X t) :
    WP isa (.ite (.zero .x .x3) (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY))) t
      fun u => S6 D X u ∧ KX t u :=
  WP.ite (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) (s5_eval h) (fun hb => s5_s6n h (by rw [s5_eval h, hb]))
    (fun hb => s5_s6q h (by rw [s5_eval h, hb]))

/-- `X`'s range, as the code computes it. -/
theorem xr_iff {D : FD} {X : Nat} {t : State} (hb : Base D t) (hm : D.mv = true) :
    (xr D X ∧ ¬ X < 1) ↔ pv D X = true := by
  have hodd := (valid_facts hm hb.k1).1
  have hdl : D.dom.length = D.dl := hb.doml
  unfold xr pv Spec.Ffdh.privateValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, Spec.Ffdh.domainOf, hdl]
  by_cases hq : D.dl = 3 * D.k
  · rw [ite_eq_left hq, ite_eq_left hq]
    simp only [Option.getD_some]
    have e : Spec.Rsa.os2ip D.qb = Spec.Rsa.os2ip (List.take D.k (List.drop (2 * D.k) D.dom)) := rfl
    omega_arith
  · rw [ite_eq_right hq, ite_eq_right hq]
    simp only [Option.getD_none]
    have := (lt_pm1 hodd X)
    constructor
    · rintro ⟨a, b⟩; exact ⟨by omega_arith, this.mp a⟩
    · rintro ⟨a, b⟩; exact ⟨this.mpr b, by omega_arith⟩

/-- After the test of `X`'s range. -/
def S7 (D : FD) (X : Nat) (t : State) : Prop :=
  ∃ mi, In D mi t ∧ t.gpr .x9 = bit (pv D X = true)

theorem s6_s7 {D : FD} {X : Nat} {t : State} (h : S6 D X t) :
    WP isa (.block andF) t fun u => S7 D X u ∧ KX t u := by
  obtain ⟨mi, hI, hF, h9⟩ := h
  refine WP.mono hI.andFlag fun u ⟨hu, h9', _, _, k⟩ => ⟨⟨mi, hu, ?_⟩, k⟩
  rw [h9', h9, hF, bit_and]
  exact bit_iff (xr_iff hI.1 hI.2.2.2.2.2)

theorem scalarRange_eq : CheckPrivate.scalarRange = isNonzero aXm ++ (.block [sth .x9 sF, leave] ::
    .block qTest :: [.ite (.zero .x .x3) (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY)), .block andF]) := rfl

/-- `CheckPrivate.scalarRange`: `privateValid` of the number in `aXm`, in `x9`. -/
theorem scalarRange_ok {D : FD} {X : Nat} {t : State} (h : S2 D X t) :
    WP isa (seqs CheckPrivate.scalarRange) t fun u => S7 D X u ∧ KX t u := by
  rw [scalarRange_eq]
  refine wp_seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (WP.mono (s2_s3 h) fun t₁ ⟨h₁, k₁⟩ => ?_)
  refine wp_seqs_cons (by simp) (WP.mono (s3_s4 h₁) fun t₂ ⟨h₂, k₂⟩ => ?_)
  refine wp_seqs_cons (by simp) (WP.mono (s4_s5 h₂) fun t₃ ⟨h₃, k₃⟩ => ?_)
  refine wp_seqs_cons (by simp) (WP.mono (s5_s6 h₃) fun t₄ ⟨h₄, k₄⟩ => ?_)
  rw [seqs_one]
  exact WP.mono (s6_s7 h₄) fun u ⟨hu, k⟩ =>
    ⟨hu, keep_trans k₁ (keep_trans k₂ (keep_trans k₃ (keep_trans k₄ k)))⟩

end ScalarRange

end VG.Proof.Ffdh.AArch64

end

end

/-!
# FFDH on AArch64: an imported scalar's range, in constant time

Runs whose data have the same public part (`FD.pub`: all but the other
inputs' octets) leak the same through `CheckPrivate.scalarRange`
(`scalarRange_ct`), whatever the number tested: its comparisons run over
all the words, and its one branch is on the domain's length.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)

/-- A run's data without the octets of its other inputs: what two runs share. -/
abbrev FD.pub (D : FD) : FD := D.withSrcs []

/-- A stage of some run's data with the public part `a`, and some value. -/
def On (S : FD → Nat → State → Prop) (a : FD) (t : State) : Prop := ∃ D X, D.pub = a ∧ S D X t

theorem on_post {S T : FD → Nat → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (On S)) c fun _ _ => True)
    (hw : ∀ D X t, S D X t → WP isa c t fun u => T D X u ∧ KX t u) : RelCT isa (Two (On S)) c (Two (On T)) :=
  two_post hct fun _ _ ⟨D, X, hD, h⟩ => WP.mono (hw D X _ h) fun _ h => ⟨D, X, hD, h.1⟩

theorem on_post' {S T : FD → Nat → State → Prop} {c : Prog isa} {P : FD → State → Prop}
    (hct : RelCT isa (Two fun a s => On S a s ∧ P a s) c fun _ _ => True)
    (hw : ∀ D X t, S D X t → P D.pub t → WP isa c t fun u => T D X u ∧ KX t u) :
    RelCT isa (Two fun a s => On S a s ∧ P a s) c (Two (On T)) :=
  two_post hct fun _ _ ⟨⟨D, X, hD, h⟩, hp⟩ => WP.mono (hw D X _ h (by rw [hD]; exact hp)) fun _ h => ⟨D, X, hD, h.1⟩

theorem pub_eq {D₁ D₂ : FD} {a : FD} (h₁ : D₁.pub = a) (h₂ : D₂.pub = a) :
    D₁.pub = D₂.pub := h₁.trans h₂.symm

namespace ScalarRange

/-- `CheckPrivate.scalarRange`. -/
theorem scalarRange_ct : RelCT isa (Two (On S2)) (seqs CheckPrivate.scalarRange) (Two (On S7)) := by
  rw [scalarRange_eq]
  refine RelCT.seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (RelCT.seq (R := Two (On S3))
    (on_post (two_map FD.ws (fun a s ⟨D, X, hD, mi, hI, _⟩ => by subst hD; exact hI.goodW1.1)
      (geArr_ct (by decide) (by decide) (by taint_decide))) fun _ _ _ h => s2_s3 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (On S4)) (on_post (two_taint [.x0]
    (pins_x0B FD.G fun a s h => by obtain ⟨D, X, hD, mi, hI, _⟩ := h; subst hD; exact hI.2.1.x0)
      (by taint_decide)) fun _ _ _ h => s3_s4 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (On S5)) (on_post (two_taint [.x0]
    (pins_x0B FD.B fun a s h => by obtain ⟨D, X, hD, mi, hP, _⟩ := h; subst hD; exact hP.2.2.2.2.2.2)
      (by taint_decide)) fun _ _ _ h => s4_s5 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (On S6)) (two_ite
    (fun a s₁ s₂ ⟨D₁, _, h₁, H₁⟩ ⟨D₂, _, h₂, H₂⟩ => by
      have e := pub_eq h₁ h₂
      have edl : D₁.dl = D₂.dl := by have := congrArg FD.dl e; exact this
      have ek : D₁.k = D₂.k := by have := congrArg FD.k e; exact this
      rw [s5_eval H₁, s5_eval H₂, edl, ek]) ?_ ?_) ?_)
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [ltP, Crt.copyArr]) (RelCT.seq
      (R := Two (On fun D X t => S5e D X t ∧ D.dl = 2 * D.k)) (on_post' (two_taint [.x0]
        (pins_x0B FD.B fun a s (h : On S5 a s ∧ _) => by
          obtain ⟨⟨D, X, hD, mi, hP, _⟩, _⟩ := h; subst hD; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun D X s h he => WP.mono (s5_e h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.choose_spec.1.1.noq (Option.some.inj ((s5_eval h).symm.trans he))⟩, k⟩) ?_)
    exact on_post (two_map FD.ws (fun a s ⟨D, X, hD, ⟨mi, hI, _⟩, _⟩ => by subst hD; exact hI.goodW1)
      (ltP_ct (by decide) (by decide) (by taint_decide) (by taint_decide))) fun _ _ _ h => e_s6n h.1 h.2
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq
      (R := Two (On fun D X t => S5e D X t ∧ D.dl = 3 * D.k)) (on_post' (two_taint [.x0]
        (pins_x0B FD.B fun a s (h : On S5 a s ∧ _) => by
          obtain ⟨⟨D, X, hD, mi, hP, _⟩, _⟩ := h; subst hD; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun D X s h he => WP.mono (s5_e h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.choose_spec.1.1.q (Option.some.inj ((s5_eval h).symm.trans he))⟩, k⟩) ?_)
    refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [ltArr, cmpArr]) (RelCT.seq (R := Two (On S5q))
      (on_post (two_map (fun a : FD => a.ld (a.dp + BitVec.ofNat 64 (2 * a.k)) a.k)
          (fun a s ⟨D, X, hD, h⟩ => by subst hD; exact (e_lpreQ h.1 h.2 :))
        (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun _ _ _ h => e_q h.1 h.2) ?_)
    exact on_post (two_map FD.ws (fun a s ⟨D, X, hD, ⟨mi, hI, _⟩, _⟩ => by subst hD; exact hI.goodW1.1)
      (ltArr_ct (by decide) (by decide) (by taint_decide))) fun _ _ _ h => q_s6 h
  rw [seqs_one]
  exact on_post (two_taint [.x0] (pins_x0B FD.G fun a s h => by
    obtain ⟨D, X, hD, mi, hI, _⟩ := h; subst hD; exact hI.2.1.x0) (by taint_decide)) fun _ _ _ h => s6_s7 h

end ScalarRange

end VG.Proof.Ffdh.AArch64
