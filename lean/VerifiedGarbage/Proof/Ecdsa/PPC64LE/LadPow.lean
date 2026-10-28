module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulFn
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Rep
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Lays
public import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# ECDSA on PPC64LE: `[k]P` and `Z^(p-2)`

`ladPow_ok`: `[k]P` for the point at two numbered slots (`qMul`: a call of
`vg_<curve>_mul`, or the ladder inline), then `Z^(p-2)` by the power, and
what they keep; `stage₂`: the same after the setup and the tables.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass

variable {c : Cfg} {A : Args}

/-- What the ladder and the power leave, from `s`: `R` holds `[k]P`, `ACC`
`Z^(p-2)`, and the other slots, the flag and the table of `n - 2` are
unchanged. -/
structure LadPost (c : Cfg) (s₀ : State) (base : Addr) (k : Nat) (P : Point c.C) (s s' : State) : Prop
    extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  t₂ : ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 2 + t)) = s.mem (off base (bitsAt c.n 2 + t))
  rep : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  rx_lt : sv c base s' RX < c.C.p
  ry_lt : sv c base s' RY < c.C.p
  rz_lt : sv c base s' RZ < c.C.p
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)

/-- `[k]P` by the ladder over the point functions, for the point `P` the
slots `gx`, `gy` and `ONEP` represent and the table of bits of any `k` of
`8 len` bits, from `R = O`, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {s : State} (S : Keep c s₀ base s) {k : Nat}
    (hkl : k < 2 ^ (8 * c.C.len)) (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1)
    (hrz : sv c base s RZ = 0) (hk : c.mul.isSome → sv c base s K = k)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', LadPost c s₀ base k P s s' → WP isa rest s' Q) :
    WP isa (.seq (c.qMul gx gy) (.seq (pow c.powP c.SP) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F' := S.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hstep := step_rep (L := ladderAt c gx gy) (k := k) hC hP (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F'.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F'.b3p]; exact toM_cmont hc _) hG
  have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (k >>> (8 * c.C.len)) P) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hz : sv c base s ZERO = 0 := F'.zero
  have hone : sv c base s ONEP = c.mont 1 := by
    rw [show sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p from F'.onep, Cfg.mont, Cfg.R, Nat.one_mul]
  have hO : Rep c.C (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO)) (mul (k >>> (8 * c.C.len)) P) := by
    show Rep c.C (toM _ _ (sv c base s ZERO)) (toM _ _ (sv c base s ONEP)) (toM _ _ (sv c base s ZERO)) _
    rw [hz, hone, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  refine WP.seq (WP.mono (qMul_ok hc h3 hc.mulNf hgx hgy hgw hgw' S.ws
    (lt_of_eq_of_lt F'.ap (hmont _)) (lt_of_eq_of_lt F'.b3p (hmont _)) (by rw [hone]; exact hmont _)
    (by rw [hz]; omega_arith) hlx hly (by rw [hrx]; omega_arith) (by rw [hry]; exact hmont _)
    (by rw [hrz]; omega_arith) hstep hR hO hk fun _ => ht₀) fun s₅ ⟨K₅, U₅, L₅, R₅⟩ => ?_)
  rw [Nat.shiftRight_zero] at R₅
  have hW₅ : FixedOk c (ladWp (ladderAt c gx gy) ++ genX c) := (fixedOk_ladWp h3 h7 gx gy).append (fixedOk_genX h7)
  have hWs₅ : ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c, w.1 + w.2 ≤ size := fun w hw =>
    (List.mem_append.mp hw).elim (ladWp_le h3 h7 gx gy w) (genX_le h7 w)
  have K₅' : Keep c s₀ base s₅ := S.step h7 K₅ (hU := U₅) (hW := hW₅) (hWs := hWs₅)
  have e₅ : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s₅ i = sv c base s i := fun hi hr =>
    sv_unch U₅ h7 hn hi (apart_append (apart_ladWp h3 h7 hi (nmem_of hr (by decide)))
      (apart_genX h7 hi (nmem_of hr (by decide))))
  have tA₅ : ∀ {j t : Nat}, j ≠ 0 → t < 64 * c.n → ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c,
      bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := fun hj ht w hw =>
    (List.mem_append.mp hw).elim (tbl_apart_ladWp h3 h7 gx gy _ _ w) (tbl_apart_genX h7 hj ht w)
  have lx₅ : sv c base s₅ RX < c.C.p := L₅ _ (List.mem_cons_self ..)
  have ly₅ : sv c base s₅ RY < c.C.p := L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have lz₅ : sv c base s₅ RZ < c.C.p :=
    L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc) rfl
    (powLayP hc) hpR K₅'.ws lz₅ K₅'.fixed.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tA₅ (by decide) ht)]
      exact ht₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_arith)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWxP_eq] at U₆
  have K₆' : Keep c s₀ base s₆ := K₅'.step h7 K₆ (hU := U₆) (hW := fixedOk_powWx h7) (hWs := powWx_le h7)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT] → sv c base s₆ i = sv c base s₅ i := fun hi hr =>
    sv_unch U₆ h7 hn hi (apart_powWx h7 hi hr)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have apF₅ : ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_append (apart_ladWp h3 h7 (i := FLAG) (gx := gx) (gy := gy) (by decide) (by decide))
      (apart_genX h7 (i := FLAG) (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  have apF₆ : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)],
      c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_powWx h7 (i := FLAG) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s₅ (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₆ i) = toM _ _ (sv c base s₅ i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₆ (by decide) (by decide)]
  refine ⟨K₆', fun hi hl => ?_, by rw [flagW, U₆.word apF₆ (by omega_arith), U₅.word apF₅ (by omega_arith), ← flagW], ?_,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact R₅,
    by rw [e₆ (by decide) (by decide)]; exact lx₅,
    by rw [e₆ (by decide) (by decide)]; exact ly₅,
    by rw [e₆ (by decide) (by decide)]; exact lz₅, lt₆, ?_⟩
  · rw [e₆ hi (nmem_of hl (by decide)), e₅ hi hl]
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_powWx h7 2 t),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tA₅ (by decide) ht)]
  · rw [tR RZ (by simp)]; exact v₆

/-- `[k]P` and `Z^(p-2)`, after the setup and the tables. -/
theorem stage₂ (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {F : BitVec 64} {s : State} (S : St₁ c A s₀ base F s)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base F P s' → WP isa rest s' Q) :
    WP isa (.seq (c.qMul gx gy) (.seq (pow c.powP c.SP) rest)) s Q :=
  ladPow_ok hc h3 hC hgx hgy hgw hgw' S.toKeep (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _))
    S.rx S.ry S.rz (fun _ => S.k) S.t₀ S.t₁ hP hG hlx hly fun s' L => h s'
      ⟨L.toKeep, by rw [L.same (by decide) (by decide), S.k], by rw [L.same (by decide) (by decide), S.d],
        by rw [L.same (by decide) (by decide), S.e], by rw [L.flag, S.flag],
        fun t ht => by rw [L.t₂ t ht, S.t₂ t ht], L.rep, L.rx_lt, L.ry_lt, L.rz_lt, L.acc_lt, L.acc⟩

end VG.Proof.Ecdsa.PPC64LE
