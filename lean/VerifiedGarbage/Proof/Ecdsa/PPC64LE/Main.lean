module

import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps

/-! ### `Ecdsa.PPC64LE.Middle`, which this module and modules that import it used -/

section

/-!
# ECDSA on PPC64LE: the field operations after the ladder

As on 32-bit ARM (`Proof/Ecdsa/Arm/Middle.lean`): `midOps_ok`, the four
field operations of `middle`: `x = X Z^(p-2)` out of Montgomery's form from
the power in `ACC`, `r = x mod n` (`x + 0 mod n`), and `k R mod n`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass

variable {c : Cfg}

theorem middle_eq (c : Cfg) : c.middle = .seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (addCall c.SN (c.sl RR) (c.sl X) (c.sl ZERO))
    (.seq (mulCall c.SN (c.sl KM) (c.sl K) (c.sl R2N))
    (.block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR)))))) := rfl

/-- What `middle`'s field operations leave. -/
structure MidPost (c : Cfg) (s₀ : State) (base : Addr) (s s' : State) : Prop extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ [XM, X, RR, KM] → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  tbl : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
    s'.mem (off base (bitsAt c.n j + t)) = s.mem (off base (bitsAt c.n j + t))
  x_lt : sv c base s' X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s' X) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  rr : sv c base s' RR = sv c base s' X % c.C.n
  km_lt : sv c base s' KM < c.C.n
  km : toM c.C.n (2 ^ (64 * c.n)) (sv c base s' KM) = Fin.ofNat c.C.n (sv c base s K)

/-- One call, from what the stages keep. -/
theorem Keep.call {s₀ : State} {base : Addr} {s s' : State} (K : Keep c s₀ base s) (h0 : 0 < c.n) (h7 : c.n < 10)
    {o : Nat} (ho : o < 45) (hoF : o = TMP ∨ 12 ≤ o) (hof : FLAG ≠ o) (k : Rk fnClob s s') (U : Unch base (callW c o) s.mem s'.mem) :
    Keep c s₀ base s' ∧ flagW c base s' = flagW c base s ∧
      (∀ {j}, j < 3 → ∀ t < 64 * c.n,
        s'.mem (off base (bitsAt c.n j + t)) = s.mem (off base (bitsAt c.n j + t))) ∧
      ∀ {i}, i < 45 → i ≠ o → sv c base s' i = sv c base s i :=
  ⟨K.step h7 k (hU := U) (hW := fixedOk_callW h7 hoF) (hWs := callW_le h7 ho),
    flag_callW h0 h7 hof U |> fun h => by
      simp only [flagW]; exact h,
    fun hj t ht => tbl_unch U h7 hj ht (tbl_apart_callW h7 ho _ t),
    fun hi hio => sv_unch U h7 K.ws.nowrap hi (apart_callW h7 hi hio)⟩

/-- The four field operations of `middle`. -/
theorem midOps_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    (hacc : sv c base s ACC < c.C.p) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', MidPost c s₀ base s s' → WP isa rest s' Q) :
    WP isa (.seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
      (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
      (.seq (addCall c.SN (c.sl RR) (c.sl X) (c.sl ZERO))
      (.seq (mulCall c.SN (c.sl KM) (c.sl K) (c.sl R2N)) rest)))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  have hpn := hc.p_lt_2n
  have hone : sv c base s ONE = 1 := K₀.fixed.one
  have hzero : sv c base s ZERO = 0 := K₀.fixed.zero
  have hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := K₀.fixed.r2n
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₀.ws (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, U₁, _, e₁⟩ => ?_)
  obtain ⟨K₁, f₁, t₁, v₁⟩ := K₀.call h0 h7 (o := XM) (by decide) (by decide) (by decide) k₁ U₁
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₁.ws (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hone]; omega_arith)) fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => ?_)
  obtain ⟨K₂, f₂, t₂, v₂⟩ := K₁.call h0 h7 (o := X) (by decide) (by decide) (by decide) k₂ U₂
  obtain x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide), hone]), toM_mul hpR e₁]
  -- `RR = X mod n`.
  obtain z₂ : sv c base s₂ ZERO = 0 := by rw [v₂ (by decide) (by decide), v₁ (by decide) (by decide), hzero]
  refine WP.seq (WP.mono (slAdd_ok hc.fn hc.fnk hc.fnm h7 K₂.ws (o := RR) (a := X) (b := ZERO) (by decide)
    (by decide) (by decide) (by rw [z₂]; omega_arith)) fun s₃ ⟨k₃, U₃, e₃⟩ => ?_)
  obtain ⟨K₃, f₃, t₃, v₃⟩ := K₂.call h0 h7 (o := RR) (by decide) (by decide) (by decide) k₃ U₃
  obtain back₃ : ∀ {i}, i < 45 → i ∉ [XM, X, RR] → sv c base s₃ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₃ hi hl.2.2, v₂ hi hl.2.1, v₁ hi hl.1]
  -- `KM = K · R² mod n`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₃.ws (o := KM) (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [back₃ (by decide) (by decide), hr2]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => h s₄ ?_)
  obtain ⟨K₄, f₄, t₄, v₄⟩ := K₃.call h0 h7 (o := KM) (by decide) (by decide) (by decide) k₄ U₄
  obtain X₄ : sv c base s₄ X = sv c base s₂ X := by rw [v₄ (by decide) (by decide), v₃ (by decide) (by decide)]
  refine ⟨K₄, fun hi hl => ?_, by rw [f₄, f₃, f₂, f₁], fun hj t ht => by
      rw [t₄ hj t ht, t₃ hj t ht, t₂ hj t ht, t₁ hj t ht],
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, ?_, lt₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₄ hi hl.2.2.2, back₃ hi (by simp [hl.1, hl.2.1, hl.2.2.1])]
  · rw [v₄ (by decide) (by decide), e₃, z₂, Nat.add_zero, X₄]
  · rw [toM_r2 hnR (by rw [e₄, back₃ (i := R2N) (by decide) (by decide), hr2]),
      back₃ (i := K) (by decide) (by decide)]

/-- After `[k]P`, `x`, `r`, the checks of `d`, `k` and `r`, and `k^(n-2)`. -/
structure St₃ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (F : BitVec 64) (P : Point c.C) (s : State) : Prop
    extends Keep c s₀ base s where
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) P)
  x_lt : sv c base s X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s X) =
    tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rr : sv c base s RR = sv c base s X % c.C.n
  flag : flagW c base s = F &&&
    mask64 (0 < dv c A s₀ ∧ dv c A s₀ < c.C.n) &&& mask64 (0 < kv c A s₀ ∧ kv c A s₀ < c.C.n) &&&
    mask64 (sv c base s X % c.C.n ≠ 0)
  acc : toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) = Fin.ofNat c.C.n (kv c A s₀) ^ (c.C.n - 2)

/-- `x`, `r`, `k R mod n` and the checks, then `k^(n-2)`. -/
theorem stage₃ (hc : CfgOk c) {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64} {P : Point c.C} {s : State}
    (S : St₂ c A s₀ base F P s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', St₃ c A s₀ base F P s' → WP isa rest s' Q) :
    WP isa (.seq c.middle (.seq c.invN rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hsz : size = 8192 := rfl
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  obtain hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hl : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => by have := sl_le c h7 hi; omega_arith
  obtain flagWs : ∀ w ∈ [(c.sl FLAG, 8)], w.1 + w.2 ≤ size := fun w hw => by
    rw [List.mem_singleton.mp hw]; exact hfl
  refine WP.seq ?_
  rw [middle_eq]
  refine midOps_ok hc S.toKeep S.acc_lt fun s₄ Mp => ?_
  rw [List.append_assoc]
  -- The checks.
  refine wp_append (WP.mono (checkRange_ok c Mp.ws.ws Mp.ws.at3 (sl_al c D) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₅ ⟨f₅, k₅, O₅⟩ => ?_)
  obtain K₅ := Mp.toKeep.step h7 (k₅.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₅.unch)
    (hW := fixedOk_flag) (hWs := flagWs)
  refine wp_append (WP.mono (checkRange_ok c K₅.ws.ws K₅.ws.at3 (sl_al c K) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  obtain K₆ := K₅.step h7 (k₆.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₆.unch)
    (hW := fixedOk_flag) (hWs := flagWs)
  refine WP.mono (checkNonzero_ok c K₆.ws.ws K₆.ws.at3 (sl_al c RR) h0 (hl (by decide)) hfl)
    fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  obtain K₇ := K₆.step h7 (k₇.rk (rs' := [.r4, .r5])) (hU := O₇.unch) (hW := fixedOk_flag) (hWs := flagWs)
  obtain e₇ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₇ i = sv c base s₄ i := fun hi hf =>
    ((sv_unch O₇.unch h7 hn hi (apart_flag h0 hf)).trans (sv_unch O₆.unch h7 hn hi (apart_flag h0 hf))).trans
      (sv_unch O₅.unch h7 hn hi (apart_flag h0 hf))
  obtain t₇ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₇.mem (off base (bitsAt c.n j + t)) = s₄.mem (off base (bitsAt c.n j + t)) := fun hj t ht => by
    rw [tbl_unch O₇.unch h7 hj ht (tbl_apart_flag h7 h0 _ t), tbl_unch O₆.unch h7 hj ht (tbl_apart_flag h7 h0 _ t),
      tbl_unch O₅.unch h7 hj ht (tbl_apart_flag h7 h0 _ t)]
  -- `k^(n-2)`.
  refine WP.seq (WP.mono (chainPow_ok (P := c.chainN) (S := c.SN) (e := c.C.n - 2) hc.fnk hc.fnm (modN hc)
    (chainLayN hc) hnR K₇.ws (show sv c base s₇ KM < c.C.n by rw [e₇ (i := KM) (by decide) (by decide)]; exact Mp.km_lt)
    hc.chainN) fun s₈ ⟨k₈, U₈, lt₈, v₈⟩ => h s₈ ?_)
  rw [chainWN_eq] at U₈
  obtain K₈ := K₇.step h7 k₈ (hU := U₈) (hW := fixedOk_chainW h7) (hWs := chainW_le h7)
  obtain e₈ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₈ i = sv c base s₇ i := fun hi hr ht =>
    sv_unch U₈ h7 hn hi (apart_chainW h7 hi hr ht)
  -- What reaches `s₈` from before the middle.
  obtain b₈ : ∀ {i}, i < 45 → i ∉ [ACC, PT, XM, X, RR, KM, FLAG] → (i < DX ∨ T2 < i) →
      sv c base s₈ i = sv c base s i := fun hi hl ht => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [e₈ hi hl.1 ht, e₇ hi hl.2.2.2.2.2.2, Mp.same hi (by simp [hl.2.2.1, hl.2.2.2.1,
      hl.2.2.2.2.1, hl.2.2.2.2.2.1])]
  obtain m₈ : ∀ {i}, i ∈ [X, RR] → sv c base s₈ i = sv c base s₄ i := fun hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rw [e₈ (by decide) (by decide) (by decide), e₇ (by decide) (by decide)]
  obtain tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₈ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₈ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [b₈ (by decide) (by decide) (by decide)]
  have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := Mp.fixed.mn
  obtain hMN₅ : wordsVal s₅.mem base (c.sl MN) c.n = c.C.n :=
    (sv_unch O₅.unch h7 hn (i := MN) (by decide) (apart_flag h0 (by decide))).trans hMN
  obtain d₄ : wordsVal s₄.mem base (c.sl D) c.n = dv c A s₀ := (Mp.same (by decide) (by decide)).trans S.d
  obtain k₅' : wordsVal s₅.mem base (c.sl K) c.n = kv c A s₀ :=
    ((sv_unch O₅.unch h7 hn (i := K) (by decide) (apart_flag h0 (by decide))).trans
      (Mp.same (by decide) (by decide))).trans S.k
  obtain rr₆ : wordsVal s₆.mem base (c.sl RR) c.n = sv c base s₄ X % c.C.n :=
    ((sv_unch O₆.unch h7 hn (i := RR) (by decide) (apart_flag h0 (by decide))).trans
      (sv_unch O₅.unch h7 hn (i := RR) (by decide) (apart_flag h0 (by decide)))).trans Mp.rr
  refine ⟨K₈, by rw [b₈ (by decide) (by decide) (by decide)]; exact S.d, by rw [b₈ (by decide) (by decide) (by decide)]; exact S.e,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact S.rep,
    by rw [m₈ (by simp)]; exact Mp.x_lt,
    by rw [m₈ (by simp), Mp.x, tR RZ (by simp), tR RX (by simp), S.acc],
    by rw [m₈ (by simp), m₈ (by simp)]; exact Mp.rr, ?_, ?_⟩
  · have fl₈ : flagW c base s₈ = flagW c base s₇ := by
      obtain apF : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl DX, 9 * (8 * c.n)), (own c.n, 64 * c.n)],
          c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
        rcases apart_chainW h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
        · exact Or.inl (by omega_arith)
        · exact Or.inr h
      simp only [flagW]; exact U₈.word apF (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)
    rw [fl₈, f₇, f₆, f₅, Mp.flag, S.flag, hMN, d₄, hMN₅, k₅', rr₆, m₈ (i := X) (by simp)]
  · refine v₈.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₇ KM) ^ _ = _
    rw [e₇ (i := KM) (by decide) (by decide), Mp.km, S.k]

end VG.Proof.Ecdsa.PPC64LE

end

end

/-! ### `Ecdsa.PPC64LE.Scalar`, which only this module used -/

section

/-!
# ECDSA on PPC64LE: `s`

As on 32-bit ARM (`Proof/Ecdsa/Arm/Scalar.lean`): `scOps_ok`, the seven
field operations of `scalar` modulo `n`: `r`, `d` and `e` into Montgomery's
form, `s = k^(n-2) (e + r d)`, and `s` out of it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Spec.Weierstrass

variable {c : Cfg}

theorem scalar_eq (c : Cfg) : c.scalar =
    .seq (mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N)) (.seq (mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N))
    (.seq (mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N)) (.seq (mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM))
    (.seq (addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM)) (.seq (mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT))
    (.seq (mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE)) (.block (c.checkNonzero (c.sl SS) ++ c.finish)))))))) :=
  rfl

/-- What `scalar`'s field operations leave. -/
structure ScPost (c : Cfg) (s₀ : State) (base : Addr) (s s' : State) : Prop extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ [RM, DM, EM, TT, SM, SS] → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  ss_lt : sv c base s' SS < c.C.n
  ss : Fin.ofNat c.C.n (sv c base s' SS) = toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
    (Fin.ofNat c.C.n (sv c base s E) + Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D))

/-- The seven field operations of `scalar`. -/
theorem scOps_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', ScPost c s₀ base s s' → WP isa rest s' Q) :
    WP isa (.seq (mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N)) (.seq (mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N))
      (.seq (mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N)) (.seq (mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM))
      (.seq (addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM)) (.seq (mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT))
      (.seq (mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE)) rest))))))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have hone : sv c base s ONE = 1 := K₀.fixed.one
  have hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := K₀.fixed.r2n
  obtain hr2lt : 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n < c.C.n := Nat.mod_lt _ (by omega_using [hn3])
  -- `RM = RR · R²`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₀.ws (o := RM) (a := RR) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [hr2]; exact hr2lt)) fun s₁ ⟨k₁, U₁, _, e₁⟩ => ?_)
  obtain ⟨K₁, f₁, -, v₁⟩ := K₀.call h0 h7 (o := RM) (by decide) (by decide) (by decide) k₁ U₁
  obtain rm₁ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₁ RM) = Fin.ofNat c.C.n (sv c base s RR) :=
    toM_r2 hnR (by rw [e₁, hr2])
  -- `DM = D · R²`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₁.ws (o := DM) (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hr2]; exact hr2lt)) fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => ?_)
  obtain ⟨K₂, f₂, -, v₂⟩ := K₁.call h0 h7 (o := DM) (by decide) (by decide) (by decide) k₂ U₂
  obtain b₂ : ∀ {i}, i < 45 → i ∉ [RM, DM] → sv c base s₂ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₂ hi hl.2, v₁ hi hl.1]
  obtain dm₂ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₂ DM) = Fin.ofNat c.C.n (sv c base s D) :=
    toM_r2 hnR (by rw [e₂, v₁ (i := D) (by decide) (by decide), v₁ (i := R2N) (by decide) (by decide), hr2])
  -- `EM = E · R²`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₂.ws (o := EM) (a := E) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [b₂ (by decide) (by decide), hr2]; exact hr2lt)) fun s₃ ⟨k₃, U₃, lt₃, e₃⟩ => ?_)
  obtain ⟨K₃, f₃, -, v₃⟩ := K₂.call h0 h7 (o := EM) (by decide) (by decide) (by decide) k₃ U₃
  obtain b₃ : ∀ {i}, i < 45 → i ∉ [RM, DM, EM] → sv c base s₃ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₃ hi hl.2.2, b₂ hi (by simp [hl.1, hl.2.1])]
  obtain em₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ EM) = Fin.ofNat c.C.n (sv c base s E) :=
    toM_r2 hnR (by rw [e₃, b₂ (i := E) (by decide) (by decide), b₂ (i := R2N) (by decide) (by decide), hr2])
  -- `TT = RM · DM`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₃.ws (o := TT) (a := RM) (b := DM) (by decide)
    (by decide) (by decide) (by rw [v₃ (by decide) (by decide)]; exact lt₂)) fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => ?_)
  obtain ⟨K₄, f₄, -, v₄⟩ := K₃.call h0 h7 (o := TT) (by decide) (by decide) (by decide) k₄ U₄
  obtain tt₄ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ TT) =
      Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D) := by
    rw [toM_mul hnR e₄, v₃ (i := RM) (by decide) (by decide), v₂ (i := RM) (by decide) (by decide), rm₁,
      v₃ (i := DM) (by decide) (by decide), dm₂]
  -- `TT = TT + EM`.
  obtain em₄ : sv c base s₄ EM = sv c base s₃ EM := v₄ (by decide) (by decide)
  refine WP.seq (WP.mono (slAdd_ok hc.fn hc.fnk hc.fnm h7 K₄.ws (o := TT) (a := TT) (b := EM) (by decide)
    (by decide) (by decide) (by rw [em₄]; omega_using [lt₃, lt₄])) fun s₅ ⟨k₅, U₅, e₅⟩ => ?_)
  obtain ⟨K₅, f₅, -, v₅⟩ := K₄.call h0 h7 (o := TT) (by decide) (by decide) (by decide) k₅ U₅
  obtain tt₅ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₅ TT) =
      Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D) + Fin.ofNat c.C.n (sv c base s E) := by
    rw [e₅, toM_add, tt₄, em₄, em₃]
  obtain tt₅lt : sv c base s₅ TT < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega_using [hn3])
  -- `SM = ACC · TT`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₅.ws (o := SM) (a := ACC) (b := TT) (by decide)
    (by decide) (by decide) tt₅lt) fun s₆ ⟨k₆, U₆, _, e₆⟩ => ?_)
  obtain ⟨K₆, f₆, -, v₆⟩ := K₅.call h0 h7 (o := SM) (by decide) (by decide) (by decide) k₆ U₆
  obtain b₅ : ∀ {i}, i < 45 → i ∉ [RM, DM, EM, TT] → sv c base s₅ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₅ hi hl.2.2.2, v₄ hi hl.2.2.2, b₃ hi (by simp [hl.1, hl.2.1, hl.2.2.1])]
  obtain sm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ SM) =
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
        (Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D) + Fin.ofNat c.C.n (sv c base s E)) := by
    rw [toM_mul hnR e₆, b₅ (i := ACC) (by decide) (by decide), tt₅]
  -- `SS = SM · 1`.
  obtain one₆ : sv c base s₆ ONE = 1 := by rw [v₆ (by decide) (by decide), b₅ (by decide) (by decide), hone]
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₆.ws (o := SS) (a := SM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [one₆]; omega_arith)) fun s₇ ⟨k₇, U₇, lt₇, e₇⟩ => h s₇ ?_)
  obtain ⟨K₇, f₇, -, v₇⟩ := K₆.call h0 h7 (o := SS) (by decide) (by decide) (by decide) k₇ U₇
  refine ⟨K₇, fun hi hl => ?_, by rw [f₇, f₆, f₅, f₄, f₃, f₂, f₁], lt₇, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₇ hi hl.2.2.2.2.2, v₆ hi hl.2.2.2.2.1, b₅ hi (by simp [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1])]
  · rw [toM_one_mul hnR (by rw [e₇, one₆]), sm₆, Lean.Grind.AddCommMonoid.add_comm]

end VG.Proof.Ecdsa.PPC64LE

end

end


/-!
# ECDSA signatures on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdsa/Arm/Main.lean`). `signFinish_ok`: `r ‖ s`
or zeros to `out`, the return value and the callee-saved registers;
`stage₄`: `s`, its check and the result; `sign_ok`: `Cfg.sign` computes
the specification's signature, for any curve the proof of the code supports
(`CfgOk`, coordinates of 3 to 6 words) whose group law the proofs support
(`Law`), restores the callee-saved registers and `lr`, and changes memory
only in the working space and `out`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass
open VG.Proof.EcKey.PPC64LE (toNat_add_of)

variable {c : Cfg}

theorem finish_eq' (c : Cfg) : c.finish =
    ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++ (storeBytes c.C.len c.n .r14 0 (c.sl RR) ++
    (storeBytes c.C.len c.n .r14 c.C.len (c.sl SS) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4])))) := by
  simp only [Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- The signature, the return value and the callee-saved registers. -/
theorem signFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + 2 * c.C.len ≤ 2 ^ 64)
    (hwr : (⟨out, 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 2 * c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (2 * c.C.len) =
        (if b then toBytes c.C.len (sv c base s RR) ++ toBytes c.C.len (sv c base s SS)
          else List.replicate (2 * c.C.len) 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 (2 * c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  obtain hX := sl_le c h7 (i := RR) (by decide)
  obtain hY := sl_le c h7 (i := SS) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  obtain hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  obtain hin : ∀ {d e m : Nat}, d + e + m ≤ 2 * c.C.len →
      InRegions s.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m := fun hd' =>
    ⟨_, hwr, by rw [Offset.add_add]; exact Offset.contains_base out hd' (by omega_arith)⟩
  rw [finish_eq', List.singleton_append]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  obtain hs₁ := hs.write .r10 (word s.mem base (c.sl FLAG))
  obtain h3₁ := h3.write (d := .r10) (word s.mem base (c.sl FLAG))
  obtain hc₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r10 = if b then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true]; rw [← flagW, hf]
  obtain hb₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r14 = out := by
    simp only [write_gpr, reduceCtorEq, ite_false]; exact h14
  -- `r`, from `out`.
  refine wp_append (WP.mono (storeBytes_ok hs₁ h3₁ (dst := .r14) (d := 0) (a := c.sl RR) (by decide) (by decide)
    (by decide) (by decide) b hc₁ (by omega_arith) (sl_al c RR) (by omega_arith) (by omega_arith) hlhi (by omega_arith)
    (by rw [hb₁, toNat_add_of (by omega_arith)]; omega_arith) (fun e m he => by rw [hb₁]; exact hin (by omega_arith))
    (by rw [hb₁]; exact hdsc (by omega_arith) (by omega_arith))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  rw [hb₁] at e₂ O₂
  obtain U₂ := O₂.unch_far (hd.symm.sub_right (Offset.sub_base out (d := 0) (n := c.C.len) (by omega_arith)))
  obtain hb₂ : s₂.gpr .r14 = out := by rw [k₂.g, hb₁]
  obtain hc₂ : s₂.gpr .r10 = if b then BitVec.allOnes 64 else 0 := by rw [k₂.g, hc₁]
  obtain y₂ : wordsVal s₂.mem base (c.sl SS) c.n = sv c base s SS :=
    U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith)
  -- `s`, from `out + len`.
  refine wp_append (WP.mono (storeBytes_ok (k₂.ws hs₁) (k₂.at h3₁) (dst := .r14) (d := c.C.len) (a := c.sl SS)
    (by decide) (by decide) (by decide) (by decide) b hc₂ (by omega_arith) (sl_al c SS) (by omega_arith) (by omega_arith) hlhi (by omega_arith)
    (by rw [hb₂, toNat_add_of (by omega_arith)]; omega_arith) (fun e m he => by rw [k₂.wr, hb₂]; exact hin (by omega_arith))
    (by rw [hb₂]; exact hdsc (by omega_arith) (by omega_arith))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  rw [hb₂, y₂] at e₃
  rw [hb₂] at O₃
  obtain U₃ := O₃.unch_far (hd.symm.sub_right (Offset.sub_base out (d := c.C.len) (n := c.C.len) (by omega_arith)))
  obtain hsv : ∀ d, d + 8 ≤ 24 → word s₃.mem base d = word s.mem base d := fun d hd' => by
    rw [U₃.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith),
      U₂.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith)]
    rfl
  obtain hs₃ := k₃.ws (k₂.ws hs₁)
  obtain h3₃ := k₃.at (k₂.at h3₁)
  -- The return value and the callee-saved registers.
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₃.write _ _).write _ _) ((h3₃.write _).write _) (by omega_arith) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · have rs : Spec.Ecdsa.bytesAt s₃.mem out c.C.len =
        if b then toBytes c.C.len (sv c base s RR) else List.replicate c.C.len 0 := by
      rw [bytesAt_keep O₃ (Offset.base_disjoint out (Nat.le_refl _) (by omega_arith)) (by omega_arith) (by omega_arith)]
      rw [BitVec.add_zero] at e₂; exact e₂
    simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [show 2 * c.C.len = c.C.len + c.C.len by omega_arith, bytesAt_add, rs, e₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
    · simp only [ite_true]
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₃.g, hc₂, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₃ :=
      (((Kp.write s (d := .r10) _ (rs := [.r10]) (by decide)).rk).trans
        (k₂.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))).trans
        (k₃.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₃ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [BitVec.add_zero] at O₂
    exact (O₂.mono (Nat.zero_le _) (by omega_arith)).trans ((outside_shift O₃ (by omega_arith)).mono (Nat.zero_le _)
      (by omega_arith))

/-- What the function needs: `d`, the hash and `k` readable, `out` and the
working space writable, the working space apart from all of them. -/
structure Pre (c : Cfg) (s : State) (extra : List Region := []) : Prop where
  rd : s.rd = [⟨s.gpr .r4, c.C.len⟩, ⟨s.gpr .r5, c.C.len⟩, ⟨s.gpr .r6, c.C.len⟩] ++ extra
  wr : s.wr = [⟨s.gpr .r3, 2 * c.C.len⟩, ⟨s.gpr .r7, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 2 * c.C.len⟩ ⟨s.gpr .r7, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .r4, c.C.len⟩ ⟨s.gpr .r7, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .r5, c.C.len⟩ ⟨s.gpr .r7, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .r6, c.C.len⟩ ⟨s.gpr .r7, size⟩
  out_fit : (s.gpr .r3).toNat + 2 * c.C.len ≤ 2 ^ 64
  d_fit : (s.gpr .r4).toNat + c.C.len ≤ 2 ^ 64
  digest_fit : (s.gpr .r5).toNat + c.C.len ≤ 2 ^ 64
  k_fit : (s.gpr .r6).toNat + c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .r7).toNat + size ≤ 2 ^ 64

theorem Pre.setup {s : State} {extra : List Region} (hp : Pre c s extra) : SetupPre c Args.sign s where
  shift := .inr (.inr rfl)
  k_reg := by decide
  d_reg := by decide
  e_reg := by decide
  sc_reg := by decide
  wr := by show (⟨s.gpr .r7, size⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  sc_fit := hp.sc_fit
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.k_fit; omega_arith)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.digest_fit; omega_arith)
  k_sc := hp.k_sc
  d_sc := hp.d_sc
  e_sc := hp.digest_sc
  k_fit := hp.k_fit
  d_fit := hp.d_fit
  e_fit := hp.digest_fit

/-- The hash's integer is the bytes shifted as the setup shifts them. -/
theorem hashToInt_eq (c : Cfg) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q c.C.len) =
      ofBytes (Spec.Ecdsa.bytesAt m q c.C.len) >>> c.sh := by
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt, Cfg.sh]
  split
  · rw [show 8 * c.C.len - Spec.Ecdsa.nBits c.C = 0 by omega_arith, Nat.shiftRight_zero]
  · rfl

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) c.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r6) c.C.len)) with
  | some rs => s'.gpr .r3 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (2 * c.C.len) = Spec.Ecdsa.encode c.C rs
  | none => s'.gpr .r3 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (2 * c.C.len) = List.replicate (2 * c.C.len) 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space and `out`. -/
structure SignKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : ∃ m : Mem, Unch (s₀.gpr .r7) [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 (2 * c.C.len) m s'.mem

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra)
    {s : State} (S : St₃ c .sign s₀ (s₀.gpr .r7) (BitVec.allOnes 64) (G c.C) s) :
    WP isa c.scalar s fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hsz : size = 8192 := rfl
  obtain hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [scalar_eq]
  refine scOps_ok hc S.toKeep fun s₇ Sc => ?_
  refine wp_append (WP.mono (checkNonzero_ok c Sc.ws.ws Sc.ws.at3 (sl_al c SS) h0
    (by have := sl_le c h7 (i := SS) (by decide); omega_arith) hfl) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_)
  obtain K₈ := Sc.toKeep.step h7 (k₈.rk (rs' := [.r4, .r5])) (hU := O₈.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  obtain e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c (s₀.gpr .r7) s₈ i = sv c (s₀.gpr .r7) s₇ i := fun hi hf =>
    sv_unch O₈.unch h7 hn hi (apart_flag h0 hf)
  -- The flag.
  obtain hflag : flagW c (s₀.gpr .r7) s₈ =
      mask64 (decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r7) s X % c.C.n ≠ 0) ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0) = true) := by
    rw [f₈, Sc.flag, S.flag, BitVec.allOnes_and, mask64_and, mask64_and, mask64_and]
    simp only [mask64, decide_eq_true_eq]
  obtain hw : (⟨s₀.gpr .r3, 2 * c.C.len⟩ : Region) ∈ s₈.wr := by
    rw [K₈.rk.wr, hp.wr]; simp
  refine WP.mono (signFinish_ok hc K₈.ws (by rw [K₈.r14]) hp.out_fit hw hp.out_sc _ hflag)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, out⟩ => ⟨⟨?_, by rw [rk.sp, K₈.rk.sp],
      by rw [lr, K₈.fixed.savedLr], s₈.mem, K₈.whole, out⟩, ?_⟩
  · intro r hr
    obtain hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14]; exact K₈.fixed.saved (.r14, 0) (by decide)
    · rw [r31]; exact K₈.fixed.saved (.r31, 8) (by decide)
    · rw [rk.gpr r h₁, K₈.rk.gpr r h₂]
  -- The specification.
  obtain hsig := signWith_eq hC (C := c.C) (d := dv c .sign s₀) (e := ev c .sign s₀) (k := kv c .sign s₀) S.rep
    S.x_lt S.x (s := sv c (s₀.gpr .r7) s₇ SS) Sc.ss_lt (by rw [Sc.ss, S.acc, S.rr, S.d, S.e])
  unfold SignPost
  have hd : dv c .sign s₀ = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len) := Nat.shiftRight_zero
  have hk : kv c .sign s₀ = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r6) c.C.len) := Nat.shiftRight_zero
  obtain he : ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) c.C.len) >>> c.sh = ev c .sign s₀ :=
    congrArg (_ >>> ·) (shAt_self c E).symm
  rw [← hd, ← hk, hashToInt_eq c, he, hsig]
  obtain rr₈ : sv c (s₀.gpr .r7) s₈ RR = sv c (s₀.gpr .r7) s X % c.C.n := by
    rw [e₈ (by decide) (by decide), Sc.same (by decide) (by decide), S.rr]
  obtain ss₈ : sv c (s₀.gpr .r7) s₈ SS = sv c (s₀.gpr .r7) s₇ SS := e₈ (by decide) (by decide)
  rw [ss₈, rr₈] at bytes
  by_cases hP : 1 ≤ dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n ∧ 1 ≤ kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n ∧
      sv c (s₀.gpr .r7) s X % c.C.n ≠ 0 ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0
  · have hdc : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r7) s X % c.C.n ≠ 0) ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega_arith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [r3, hdc]; rfl, ?_⟩
    rw [bytes, hdc, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode]
  · have hdc : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r7) s X % c.C.n ≠ 0) ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega_arith
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [r3, hdc]; rfl, ?_⟩
    rw [bytes, hdc]; rfl

theorem sign_eq (c : Cfg) : c.sign = .seq (.block (c.setupWith Args.sign))
    (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq (c.qMul GX GY) (.seq c.invP (.seq c.middle
      (.seq c.invN c.scalar))))))) := rfl

theorem signWith_eq (c : Cfg) (generator : Prog isa) : c.signWith generator = .seq (.block (c.setupWith Args.sign))
    (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq generator (.seq c.invP (.seq c.middle
      (.seq c.invN c.scalar))))))) := rfl

/-- `vg_ecdsa_<curve>_sign` with `R = [k]G` by any `generator` meeting
`GeneratorPost` after the setup and the tables computes the specification's
signature, restores the callee-saved registers and `lr`, and changes only
the working space and `out`. -/
theorem signWith_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {extra : List Region}
    (hp : Pre c s₀ extra) {generator : Prog isa}
    (hMul : ∀ s, St₁ c .sign s₀ (s₀.gpr .r7) (BitVec.allOnes 64) s → s.syms = s₀.syms →
      WP isa generator s (GeneratorPost c (s₀.gpr .r7) (kv c .sign s₀) (G c.C) s)) :
    WP isa (c.signWith generator) s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  obtain setupRun := stage₁ hc hp.setup (A := .sign) (rest := .block [])
    (Q := fun s => St₁ c .sign s₀ (s₀.gpr .r7) (BitVec.allOnes 64) s) (fun _ S => WP.block_nil S)
  obtain run := VG.PPC64LE.WP.mono_syms setupRun fun s₁ S₁ sy => stage₂With hc h3 S₁ (hMul s₁ S₁ sy)
    (rest := .seq c.middle (.seq c.invN c.scalar)) fun s₂ S₂ =>
      stage₃ hc S₂ fun s₃ S₃ => stage₄ hc hC hp S₃
  rw [signWith_eq]
  simpa only [WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using run

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature, restores
the callee-saved registers and `lr`, and changes only the working space and
`out`. -/
theorem sign_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {extra : List Region}
    (hp : Pre c s₀ extra) :
    WP isa c.sign s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  rw [sign_eq]
  refine stage₁ hc hp.setup fun s₁ S₁ => ?_
  have F := S₁.fixed
  obtain hG : Rep c.C (tmv c.C c.n (s₀.gpr .r7) s₁ (c.sl GX)) (tmv c.C c.n (s₀.gpr .r7) s₁ (c.sl GY))
      (tmv c.C c.n (s₀.gpr .r7) s₁ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₁.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₁.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₁.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  exact stage₂ hc h3 hC (gx := GX) (gy := GY) (by decide) (by decide) (by decide) (by decide) S₁ hc.onG hG
    (lt_of_eq_of_lt F.gx (hmont _)) (lt_of_eq_of_lt F.gy (hmont _)) fun s₂ S₂ =>
      stage₃ hc S₂ fun s₃ S₃ => stage₄ hc hC hp S₃

end VG.Proof.Ecdsa.PPC64LE
