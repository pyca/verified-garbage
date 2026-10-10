import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Ecdsa.Sign

/-!
# ECDSA on x86 (32-bit): the whole function

`sign_ok`: `Cfg.sign` computes the specification's signature of the hash
with `d` and `k`, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and changes memory only in the working space and `out`. Four
stages, each a lemma, as on AArch64 (`Proof/Ecdsa/AArch64/Main.lean`): the
setup and the tables of bits (`stage₁`, in `Stages.lean`), `[k]G` and
`Z^(p-2)` (`stage₂`), `x`, `r`, the checks and `k^(n-2)` (`stage₃`), and
`s`, its check and the result (`stage₄`); `signWith_eq` connects what they
compute to the specification.
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg} {A : Args}

/-- The ranges of numbered slots and of the accumulator. -/
abbrev slWk (c : Cfg) (l : List Nat) : List (Nat × Nat) := slW c l ++ wkW c

theorem apart_slWk {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWk c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_wk hi)

theorem tbl_apart_slWk {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWk c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW hl j t) (tbl_apart_wk hj ht)

theorem fixedOk_slWk {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) (hn : c.n < 10 := by n10) :
    FixedOk c (slWk c l) :=
  (fixedOk_slW hl).append fixedOk_wk

/-- What the ladder writes: numbered slots, the accumulator and the point
functions' slots. -/
abbrev slWkP (c : Cfg) (l : List Nat) : List (Nat × Nat) := slWk c l ++ Point.ptW c.n

theorem apart_slWkP {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWkP c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slWk hi hl) (apart_ptW hi)

theorem tbl_apart_slWkP {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWkP c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slWk hl hj ht) (tbl_apart_ptW j t)

theorem fixedOk_slWkP {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) (hn : c.n < 10 := by n10) :
    FixedOk c (slWkP c l) :=
  (fixedOk_slWk hl).append fixedOk_ptW

/-- The flag word apart from what the ladder writes. -/
theorem flag_unchP {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (slWkP c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega)
  rcases apart_slWkP (c := c) (i := FLAG) (by decide) hl h7 w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- After `[k]G` and `Z^(p-2)`. -/
structure St₂ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  flag : flagW c base s = BitVec.allOnes 32
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  acc_lt : sv c base s ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s RZ < c.C.p

/-- `[k]G`, then `Z^(p-2)`. -/
theorem stage₂ (hc : CfgOk c) (hC : Law c.C) (hcomb : c.comb = none) {s₀ : State} {base : Addr} {s : State}
    (hS : St₁ c A s₀ base s)
    (hsp₁ : SpOk (Point.ladderP c.ladderCfg c.SP A.ao) c.stk) (hsp₂ : SpOk c.pPow c.stk)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (Point.ladderP c.ladderCfg c.SP A.ao) (.seq c.pPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  have hkl : kv c A s₀ < 2 ^ (64 * c.n) := hS.k ▸ wordsVal_lt _ _ _ _
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hlt : ∀ x ∈ ladR c.ladderCfg, wordsVal s.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt F.b3p (hmont _)
    · exact lt_of_eq_of_lt F.gx (hmont _)
    · exact lt_of_eq_of_lt F.gy (hmont _)
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
    · exact lt_of_eq_of_lt hS.rx (by omega)
    · exact lt_of_eq_of_lt hS.ry (hmont _)
    · exact lt_of_eq_of_lt hS.rz (by omega)
  have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀ >>> (64 * c.n)) (G c.C)) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hS.rx, hS.ry, hS.rz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hstep := step_rep (L := c.ladderCfg) (k := kv c A s₀) hC hc.onG (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F.b3p]; exact toM_cmont hc _) hG
  refine WP.seq (hS.withSp hsp₁ (WP.mono (Point.ladderP_ok (ladLay hc) (ladWk hc) ladPt hpR hS.scr
    (fun h => hS.arg (Cfg.stk_28 hcomb h.2)) (modP_of hc F.mp) hlt
    hstep hR hS.t₀) fun s₅ ⟨K₅, U₅, M₅, L₅, R₅, _⟩ f₅ => ?_))
  rw [Nat.shiftRight_zero] at R₅
  rw [Point.ladWp, ladWx_eq] at U₅
  have hs₅ := hS.scr.of_keeps K₅ (by decide)
  have F₅ := F.unch h7 hn (fixedOk_slWkP (by decide)) U₅
  have k₅ : Keep c s₀ base s₅ := ⟨hs₅, by rw [K₅.1 _ (by decide), hS.esp], by rw [K₅.2.1, hS.rd],
    by rw [K₅.2.2, hS.wr], F₅, f₅, hS.sp_lo⟩
  refine WP.seq (k₅.withSp hsp₂ (WP.mono (pPow_ok hc hs₅ M₅
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tbl_apart_slWkP (by decide) (by decide) ht)]
      exact hS.t₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ f₆ => h s₆ ?_))
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] →
      i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] →
      sv c base s₆ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_pwW hi h₁)).trans (sv_unch U₅ h7 hn hi (apart_slWkP hi h₂))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_pwW hi h₁)
  refine ⟨⟨hs₅.of_keeps K₆ (by decide), by rw [K₆.1 _ (by decide), k₅.esp],
    by rw [K₆.2.1, k₅.rd], by rw [K₆.2.2, k₅.wr], F₅.unch h7 hn fixedOk_pwW U₆, f₆, hS.sp_lo⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flagW, flag_unch_pwW U₆ h7 h0 hn, flag_unchP U₅ h7 h0 hn (by decide), ← flagW, hS.flag],
    ?_, ?_, lt₆, ?_, ?_⟩
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_pwW (by decide) ht),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tbl_apart_slWkP (by decide) (by decide) ht)]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- After `x`, `r`, the checks and `k^(n-2)`. -/
structure St₃ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  x_lt : sv c base s X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s X) =
    tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rr : sv c base s RR = sv c base s X % c.C.n
  flag : flagW c base s = BitVec.allOnes 32 &&&
    mask32 (0 < dv c A s₀ ∧ dv c A s₀ < c.C.n) &&& mask32 (0 < kv c A s₀ ∧ kv c A s₀ < c.C.n) &&&
    mask32 (sv c base s X % c.C.n ≠ 0)
  acc : toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) = Fin.ofNat c.C.n (kv c A s₀) ^ (c.C.n - 2)

/-- `x`, `r`, `k R mod n` and the checks, then `k^(n-2)`. -/
theorem stage₃ (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₂ c A s₀ base s)
    (hsp₁ : SpOk c.middle c.stk) (hsp₂ : SpOk c.nPow c.stk) {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₃ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq c.middle (.seq c.nPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  refine WP.seq (hS.withSp hsp₁ ?_)
  rw [middle_eq]
  refine midOps_ok hc hS.scr (modP_of hc F.mp) (modN_of hc F.mn) hS.acc_lt F.one F.zero F.r2n
    fun s₇ Mp => ?_
  have F₇ := F.unch h7 hn (fixedOk_slWk (l := [XM, X, RR, KM, TMP]) (by decide)) Mp.unch
  refine WP.mono (checks_ok hc Mp.scr F₇.mn) fun s₈ ⟨f₈, k₈, O₈⟩ w₈ => ?_
  have hs₈ := Mp.scr.of_keeps k₈ (by decide)
  have F₈ := F₇.unch h7 hn fixedOk_flag O₈.unch
  have e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₇ i := fun hi hf =>
    sv_flag O₈ h0 h7 hn hi hf
  have e₇ : ∀ {i}, i < 45 → i ∉ [XM, X, RR, KM, TMP] → sv c base s₇ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slWk hi hl)
  have K₈ : Keep c s₀ base s₈ := ⟨hs₈, by rw [k₈.1 _ (by decide), Mp.gpr _ (by decide), hS.esp],
    by rw [k₈.2.1, Mp.rd, hS.rd], by rw [k₈.2.2, Mp.wr, hS.wr], F₈, w₈, hS.sp_lo⟩
  refine WP.seq (K₈.withSp hsp₂ (WP.mono (nPow_ok hc hs₈
    (modN_of hc F₈.mn) (lt_of_eq_of_lt (e₈ (i := KM) (by decide) (by decide)) Mp.km_lt) F₈.onen
    (fun t ht => by
      show s₈.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch O₈.unch h7 (j := 2) (by decide) ht (tbl_apart_flag h0 2 t),
        tbl_unch Mp.unch h7 (j := 2) (by decide) ht (tbl_apart_slWk (by decide) (by decide) ht)]
      exact hS.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega)) fun s₉ ⟨K₉, U₉, lt₉, v₉⟩ w₉ => h s₉ ?_))
  have e₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₉ i = sv c base s₈ i := fun hi hl =>
    sv_unch U₉ h7 hn hi (apart_pwW hi hl)
  -- The slots `middle` and the power do not write.
  have a₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → i ≠ FLAG → i ∉ [XM, X, RR, KM, TMP] →
      sv c base s₉ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    ((e₉ hi h₁).trans (e₈ hi h₂)).trans (e₇ hi h₃)
  have x₉ : sv c base s₉ X = sv c base s₇ X :=
    (e₉ (i := X) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  have rr₉ : sv c base s₉ RR = sv c base s₇ RR :=
    (e₉ (i := RR) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₉ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₉ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [a₉ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨hs₈.of_keeps K₉ (by decide), by rw [K₉.1 _ (by decide), K₈.esp], by rw [K₉.2.1, K₈.rd],
    by rw [K₉.2.2, K₈.wr], F₈.unch h7 hn fixedOk_pwW U₉, w₉, hS.sp_lo⟩,
    by rw [a₉ (i := D) (by decide) (by decide) (by decide) (by decide), hS.d],
    by rw [a₉ (i := E) (by decide) (by decide) (by decide) (by decide), hS.e],
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact hS.rep,
    by rw [x₉]; exact Mp.x_lt,
    by rw [x₉, Mp.x, tR RX (by simp), tR RZ (by simp), hS.acc],
    by rw [rr₉, x₉]; exact Mp.rr, ?_, ?_⟩
  · rw [flagW, flag_unch_pwW U₉ h7 h0 hn, ← flagW, f₈, flagW, flag_unch Mp.unch h7 h0 hn (by decide),
      ← flagW, hS.flag, e₇ (i := D) (by decide) (by decide), e₇ (i := K) (by decide) (by decide), hS.d, hS.k,
      Mp.rr, x₉]
  · refine v₉.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ KM) ^ _ = _
    rw [e₈ (i := KM) (by decide) (by decide), Mp.km, hS.k]

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) c.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 3) c.C.len)) with
  | some rs => s'.gpr .eax = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (2 * c.C.len) = Spec.Ecdsa.encode c.C rs
  | none => s'.gpr .eax = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (2 * c.C.len) = List.replicate (2 * c.C.len) 0

/-- What the ABI asks for, but the return address: the callee-saved
registers restored, `esp` kept; and memory changed only in the writable
regions and the stack below `esp` that the calls use. -/
structure SignKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  esp : s'.gpr .esp = s₀.gpr .esp
  frame : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem

/-- Memory the code does not write: a region apart from the writable regions
and the stack the calls use. -/
theorem Pre.frame_readW {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra) {m : Mem}
    (hf : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem m) {a : Addr} (hb : (⟨a, 4⟩ : Region).Disjoint (outR c s₀))
    (hs : (⟨a, 4⟩ : Region).Disjoint (scR s₀)) (hl : (⟨a, 4⟩ : Region).Disjoint (below (s₀.gpr .esp) c.stk)) :
    m.readW a 32 = s₀.mem.readW a 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hp.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hb
  · exact hs
  · exact hl

/-- The return address is kept. -/
theorem SignKeep.ret {s₀ s' : State} {extra : List Region} (hp : Pre c s₀ extra) (K : SignKeep c s₀ s') :
    s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
  hp.frame_readW K.frame hp.ret_out hp.ret_sc (below_disjoint_ret hp.sp_lo).symm

/-- The calls of `scalar`, before its checks. -/
abbrev scalarOps (c : Cfg) : Prog isa :=
  [Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N), Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N), Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM),
    Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM), Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT)].foldr
    .seq (Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE))

theorem scalar_split (c : Cfg) : c.scalar =
    [Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N), Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N), Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM),
    Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM), Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT)].foldr
    .seq (.seq (Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE))
      (.block (c.checkNonzero (c.sl SS) ++ c.finish))) := rfl

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra) {base : Addr} (hb : base = ptr s₀ 4)
    {s : State} (hS : St₃ c .sign s₀ base s) (hsp : SpOk (scalarOps c) c.stk) :
    WP isa c.scalar s fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  rw [scalar_split, WP.split]
  refine WP.seq (hS.withSp hsp ?_)
  rw [← WP.seq_nil, ← WP.split]
  refine scalarIn_ok hc hS.scr (modN_of hc F.mn) F.r2n
    fun s₁₀ hs₁₀ hM₁₀ g₁₀ rd₁₀ wr₁₀ U₁₀ _ dm em trm tdm tem => ?_
  have F₁₀ := F.unch h7 hn (fixedOk_slWk (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₀
  refine scalarOut_ok hc hs₁₀ hM₁₀ F₁₀.one dm em
    fun s₁₁ hs₁₁ g₁₁ rd₁₁ wr₁₁ U₁₁ ss_lt ss => WP.block_nil fun w₁₁ => ?_
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine WP.block_append (WP.mono (checkNonzero_ok c hs₁₁ h0 (sl_le c h7 (i := SS) (by decide)) (by omega))
    fun s₁₂ ⟨f₁₂, k₁₂, O₁₂⟩ => ?_)
  have hs₁₂ := hs₁₁.of_keeps k₁₂ (by decide)
  have F₁₂ := (F₁₀.unch h7 hn (fixedOk_slWk (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₁).unch
    h7 hn fixedOk_flag O₁₂.unch
  have hsc : (⟨base, size⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk] :=
    List.mem_append_left _ (by rw [hp.wr, hb]; simp)
  have W₁₂ : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s₁₂.mem :=
    w₁₁.trans (frame_of_unch O₁₂.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; omega) hsc)
  have acc₁₀ : sv c base s₁₀ ACC = sv c base s ACC :=
    sv_unch U₁₀ h7 hn (by decide) (apart_slWk (by decide) (by decide))
  have rr₁₂ : sv c base s₁₂ RR = sv c base s RR :=
    ((sv_flag O₁₂ h0 h7 hn (i := RR) (by decide) (by decide)).trans
      (sv_unch U₁₁ h7 hn (by decide) (apart_slWk (by decide) (by decide)))).trans
      (sv_unch U₁₀ h7 hn (by decide) (apart_slWk (by decide) (by decide)))
  have ss₁₂ : sv c base s₁₂ SS = sv c base s₁₁ SS := sv_flag O₁₂ h0 h7 hn (by decide) (by decide)
  -- The flag.
  have hflag : flagW c base s₁₂ =
      mask32 (decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true) := by
    rw [f₁₂, flagW, flag_unch U₁₁ h7 h0 hn (by decide), flag_unch U₁₀ h7 h0 hn (by decide), ← flagW, hS.flag,
      BitVec.allOnes_and, mask32_and, mask32_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  have hesp : s₁₂.gpr .esp = s₀.gpr .esp := by
    rw [k₁₂.1 _ (by decide), g₁₁ _ (by decide), g₁₀ _ (by decide), hS.esp]
  have hrw : s₁₂.rd ++ s₁₂.wr = s₀.rd ++ s₀.wr := by
    rw [k₁₂.2.1, k₁₂.2.2, rd₁₁, wr₁₁, rd₁₀, wr₁₀, hS.rd, hS.wr]
  have hout := argLoad_frame (i := 0) ⟨argsR s₀, by rw [hp.rd]; simp, arg_contains hp.sp_fit (by decide)⟩
    (by
      rw [hp.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hp.args_out.sub_left (arg_sub hp.sp_fit (by decide))
      · exact hp.args_sc.sub_left (arg_sub hp.sp_fit (by decide))
      · exact (below_disjoint_args hp.sp_lo (by have := hp.sp_fit; omega) (by decide)).symm)
    hesp hrw W₁₂
  have hw : (⟨(arg s₀ 0).setWidth 64, 2 * c.C.len⟩ : Region) ∈ s₁₂.wr := by
    rw [k₁₂.2.2, wr₁₁, wr₁₀, hS.wr, hp.wr]; simp
  refine WP.mono (finish_ok hc hs₁₂ hout hp.out_fit hw (hb ▸ hp.out_sc) F₁₂.saved _ hflag)
    fun s' ⟨bytes, ret, saved, others, Oout⟩ => ⟨⟨saved, by rw [others _ (by decide), hesp],
      W₁₂.trans (frame_of_outside Oout (List.mem_append_left _ (by rw [hp.wr]; simp)))⟩, ?_⟩
  -- The specification.
  have hsig := signWith_eq hC (C := c.C) (d := dv c .sign s₀) (e := ev c .sign s₀) (k := kv c .sign s₀) hS.rep hS.x_lt hS.x
    (s := wordsVal s₁₁.mem base (c.sl SS) c.n) ss_lt (by
      rw [ss, trm, tdm, tem, acc₁₀, hS.acc, hS.rr, hS.d, hS.e, Lean.Grind.AddCommMonoid.add_comm])
  unfold SignPost
  have he : ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) c.C.len) >>> c.sh = ev c .sign s₀ :=
    congrArg (_ >>> ·) (shAt_self c E).symm
  rw [← dv_eq (A := .sign) (shAt_E_D c), ← kv_eq (A := .sign) (shAt_E_K c), hashToInt_eq c, he, hsig]
  rw [ss₁₂, rr₁₂, hS.rr] at bytes
  by_cases hP : 1 ≤ dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n ∧ 1 ≤ kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n ∧
      sv c base s X % c.C.n ≠ 0 ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode]
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd]; rfl

theorem sign_eq (c : Cfg) : c.sign = .seq (.block c.setup) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq (Point.ladderP c.ladderCfg c.SP Args.sign.ao) (.seq c.pPow (.seq c.middle
      (.seq c.nPow c.scalar))))))) := rfl

/-- The stack the parts of `sign` use: no write of `esp`, and at most
`c.stk` bytes below it. -/
structure SignSp (c : Cfg) : Prop where
  ladder : SpOk (Point.ladderP c.ladderCfg c.SP Args.sign.ao) c.stk
  pPow : SpOk c.pPow c.stk
  middle : SpOk c.middle c.stk
  nPow : SpOk c.nPow c.stk
  scalar : SpOk (scalarOps c) c.stk

/-- `SignSp` from the whole code's. -/
theorem SignSp.of (h : SpOk c.sign c.stk) : SignSp c := by
  rw [sign_eq] at h
  have h₁ := h.right.right.right.right
  have h₂ := h₁.right.right.right
  refine ⟨h₁.left, h₁.right.left, h₁.right.right.left, h₂.left, ?_⟩
  have h₃ := h₂.right
  rw [scalar_split] at h₃
  exact (SpOk.split _ _ _ h₃).1

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature, restores
the callee-saved registers and changes only the working space and `out`. -/
theorem sign_ok (hc : CfgOk c) (hC : Law c.C) (hcomb : c.comb = none) (hsp : SpOk c.sign c.stk) {s₀ : State}
    (hp : Pre c s₀) :
    WP isa c.sign s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have H := SignSp.of hsp
  rw [sign_eq]
  exact stage₁ hc hp.setup fun _ S₁ => stage₂ hc hC hcomb S₁ H.ladder H.pPow fun _ S₂ =>
    stage₃ hc S₂ H.middle H.nPow fun _ S₃ => stage₄ hc hC hp rfl S₃ H.scalar

end VG.Proof.Ecdsa.X86
