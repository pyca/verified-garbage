module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Mont.PPC64LE.Row

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
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
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
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide), hone]), toM_mul hpR e₁]
  -- `RR = X mod n`.
  have z₂ : sv c base s₂ ZERO = 0 := by rw [v₂ (by decide) (by decide), v₁ (by decide) (by decide), hzero]
  refine WP.seq (WP.mono (slAdd_ok hc.fn hc.fnk hc.fnm h7 K₂.ws (o := RR) (a := X) (b := ZERO) (by decide)
    (by decide) (by decide) (by rw [z₂]; omega_arith)) fun s₃ ⟨k₃, U₃, e₃⟩ => ?_)
  obtain ⟨K₃, f₃, t₃, v₃⟩ := K₂.call h0 h7 (o := RR) (by decide) (by decide) (by decide) k₃ U₃
  have back₃ : ∀ {i}, i < 45 → i ∉ [XM, X, RR] → sv c base s₃ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₃ hi hl.2.2, v₂ hi hl.2.1, v₁ hi hl.1]
  -- `KM = K · R² mod n`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₃.ws (o := KM) (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [back₃ (by decide) (by decide), hr2]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => h s₄ ?_)
  obtain ⟨K₄, f₄, t₄, v₄⟩ := K₃.call h0 h7 (o := KM) (by decide) (by decide) (by decide) k₄ U₄
  have X₄ : sv c base s₄ X = sv c base s₂ X := by rw [v₄ (by decide) (by decide), v₃ (by decide) (by decide)]
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
    WP isa (.seq c.middle (.seq (pow c.powN c.SN) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hsz : size = 8192 := rfl
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hl : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => by have := sl_le c h7 hi; omega_arith
  have flagWs : ∀ w ∈ [(c.sl FLAG, 8)], w.1 + w.2 ≤ size := fun w hw => by
    rw [List.mem_singleton.mp hw]; exact hfl
  refine WP.seq ?_
  rw [middle_eq]
  refine midOps_ok hc S.toKeep S.acc_lt fun s₄ Mp => ?_
  rw [List.append_assoc]
  -- The checks.
  refine wp_append (WP.mono (checkRange_ok c Mp.ws.ws Mp.ws.at3 (sl_al c D) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₅ ⟨f₅, k₅, O₅⟩ => ?_)
  have K₅ := Mp.toKeep.step h7 (k₅.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₅.unch)
    (hW := fixedOk_flag) (hWs := flagWs)
  refine wp_append (WP.mono (checkRange_ok c K₅.ws.ws K₅.ws.at3 (sl_al c K) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  have K₆ := K₅.step h7 (k₆.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₆.unch)
    (hW := fixedOk_flag) (hWs := flagWs)
  refine WP.mono (checkNonzero_ok c K₆.ws.ws K₆.ws.at3 (sl_al c RR) h0 (hl (by decide)) hfl)
    fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  have K₇ := K₆.step h7 (k₇.rk (rs' := [.r4, .r5])) (hU := O₇.unch) (hW := fixedOk_flag) (hWs := flagWs)
  have e₇ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₇ i = sv c base s₄ i := fun hi hf =>
    ((sv_unch O₇.unch h7 hn hi (apart_flag h0 hf)).trans (sv_unch O₆.unch h7 hn hi (apart_flag h0 hf))).trans
      (sv_unch O₅.unch h7 hn hi (apart_flag h0 hf))
  have t₇ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₇.mem (off base (bitsAt c.n j + t)) = s₄.mem (off base (bitsAt c.n j + t)) := fun hj t ht => by
    rw [tbl_unch O₇.unch h7 hj ht (tbl_apart_flag h7 h0 _ t), tbl_unch O₆.unch h7 hj ht (tbl_apart_flag h7 h0 _ t),
      tbl_unch O₅.unch h7 hj ht (tbl_apart_flag h7 h0 _ t)]
  -- `k^(n-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (S := c.SN) (e := c.C.n - 2) hc.fnk hc.fnm (modN hc) rfl
    (powLayN hc) hnR K₇.ws (show sv c base s₇ KM < c.C.n by rw [e₇ (i := KM) (by decide) (by decide)]; exact Mp.km_lt) K₇.fixed.onen
    (fun t ht => by
      show s₇.mem (off base (bitsAt c.n 2 + t)) = _
      rw [t₇ (j := 2) (by decide) t ht, Mp.tbl (j := 2) (by decide) t ht]
      exact S.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith)) fun s₈ ⟨k₈, U₈, lt₈, v₈⟩ => h s₈ ?_)
  rw [powWxN_eq] at U₈
  have K₈ := K₇.step h7 k₈ (hU := U₈) (hW := fixedOk_powWx h7) (hWs := powWx_le h7)
  have e₈ : ∀ {i}, i < 45 → i ∉ [ACC, PT] → sv c base s₈ i = sv c base s₇ i := fun hi hr =>
    sv_unch U₈ h7 hn hi (apart_powWx h7 hi hr)
  -- What reaches `s₈` from before the middle.
  have b₈ : ∀ {i}, i < 45 → i ∉ [ACC, PT, XM, X, RR, KM, FLAG] → sv c base s₈ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [e₈ hi (by simp [hl.1, hl.2.1]), e₇ hi hl.2.2.2.2.2.2, Mp.same hi (by simp [hl.2.2.1, hl.2.2.2.1,
      hl.2.2.2.2.1, hl.2.2.2.2.2.1])]
  have m₈ : ∀ {i}, i ∈ [X, RR] → sv c base s₈ i = sv c base s₄ i := fun hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rw [e₈ (by decide) (by decide), e₇ (by decide) (by decide)]
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₈ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₈ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [b₈ (by decide) (by decide)]
  have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := Mp.fixed.mn
  have hMN₅ : wordsVal s₅.mem base (c.sl MN) c.n = c.C.n :=
    (sv_unch O₅.unch h7 hn (i := MN) (by decide) (apart_flag h0 (by decide))).trans hMN
  have d₄ : wordsVal s₄.mem base (c.sl D) c.n = dv c A s₀ := (Mp.same (by decide) (by decide)).trans S.d
  have k₅' : wordsVal s₅.mem base (c.sl K) c.n = kv c A s₀ :=
    ((sv_unch O₅.unch h7 hn (i := K) (by decide) (apart_flag h0 (by decide))).trans
      (Mp.same (by decide) (by decide))).trans S.k
  have rr₆ : wordsVal s₆.mem base (c.sl RR) c.n = sv c base s₄ X % c.C.n :=
    ((sv_unch O₆.unch h7 hn (i := RR) (by decide) (apart_flag h0 (by decide))).trans
      (sv_unch O₅.unch h7 hn (i := RR) (by decide) (apart_flag h0 (by decide)))).trans Mp.rr
  refine ⟨K₈, by rw [b₈ (by decide) (by decide)]; exact S.d, by rw [b₈ (by decide) (by decide)]; exact S.e,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact S.rep,
    by rw [m₈ (by simp)]; exact Mp.x_lt,
    by rw [m₈ (by simp), Mp.x, tR RZ (by simp), tR RX (by simp), S.acc],
    by rw [m₈ (by simp), m₈ (by simp)]; exact Mp.rr, ?_, ?_⟩
  · have fl₈ : flagW c base s₈ = flagW c base s₇ := by
      have apF : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)],
          c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
        rcases apart_powWx h7 (i := FLAG) (by decide) (by decide) w hw with h | h
        · exact Or.inl (by omega_arith)
        · exact Or.inr h
      simp only [flagW]; exact U₈.word apF (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)
    rw [fl₈, f₇, f₆, f₅, Mp.flag, S.flag, hMN, d₄, hMN₅, k₅', rr₆, m₈ (i := X) (by simp)]
  · refine v₈.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₇ KM) ^ _ = _
    rw [e₇ (i := KM) (by decide) (by decide), Mp.km, S.k]

end VG.Proof.Ecdsa.PPC64LE
