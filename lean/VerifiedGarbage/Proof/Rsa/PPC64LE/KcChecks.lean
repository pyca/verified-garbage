module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KcOps
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.MulMod
public import VerifiedGarbage.Proof.Rsa.MontCheckMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey

/-! # The checks of an RSA key on PPC64LE

As on ARMv7 (`Proof/Rsa/Arm/KcStart.lean`, `KcChecks.lean`, `KcBody.lean`):
from the arrays read (`vals`), `start_ok`: `1`, the mask of `p` odd, `p q mod
2^(32 w)`, `p | 1` and Montgomery's `n 2^(-32 w) mod (p | 1)`; `crtChecks_ok`:
the checks of `vg_rsa_check_crt_key` and'ed into the mask (`crtBitsM`);
`dChecks_ok`: those of `d` (`keyBitsM`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs setOne bitOf sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)
open VG.Proof.Rsa.PPC64LE.MontKey (mulLo_ok montMul_ok mkRegs val32_low)

/-! ## The products

The product truncated to `w` digits (`Stg.mulLo_ok`) and Montgomery's
multiplication modulo `p | 1`, in `aVD` (`Stg.montP_ok`). -/

theorem mkRegs_body : ∀ x ∈ mkRegs, x ∈ bodyRegs := by decide

/-- `orOne j`. -/
theorem Stg.orOne_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.orOne j)) s (Stg g s0 (upd A j (2 * (A j / 2) + 1)) live c) := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.orOne j)]
  refine orOne_top_ok h.ws (h.live_lt j hj) (by decide) fun t ht k e r top => WP.block_nil ?_
  refine h.next ht k (by simpa using h.live_lt j hj) (by simp) r KeyCheck.opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt ?_ (h.mask_keep k (by simp))
  by_cases hv : j = aVD
  · subst hv; rw [top, h.vdTop]
  · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `mulLo o x y r19`: `[o] := [x] [y] mod 2^(32 w)`, for `[x] < 2^(8 L)`,
`L = p_len` in `r19`. -/
theorem Stg.mulLo_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o x y : Nat} (ho : o < nArr) (hx : x ∈ live) (hy : y ∈ live)
    (hfree : ∀ j ∈ live, j ≠ o) (hoVD : o ≠ aVD) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * g.w) (hxL : A x < 2 ^ (8 * L)) :
    WP isa (VG.Impl.Rsa.PPC64LE.MontKey.mulLo o x y .r19) s
      (Stg g s0 (upd A o (A x * A y % 2 ^ (32 * g.w))) (o :: live) c) := by
  have nx := h.live_lt x hx
  have ny := h.live_lt y hy
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulLo_ok h.ws (by decide) ho nx ny (fun e => hfree x hx e.symm) (fun e => hfree y hy e.symm)
    hl hL1 hLw (by decide) (by decide)) fun t ⟨ht, k, v, r⟩ => ?_
  have vx : val32 s.mem g.B (arr g.w x) ((L + 3) / 4) = A x :=
    val32_low (h.arrs.get hx) (by omega) (Nat.lt_of_lt_of_le hxL (Nat.pow_le_pow_right (by decide) (by omega)))
  have e : num t.mem g.B g.w o = A x * A y % 2 ^ (32 * g.w) := by rw [v, vx, h.arrs.get hy]
  refine h.next ht k (by simpa using ho) (by simp) r mkRegs_body
    ((h.arrs_write k e (fun j hj => .inr (by simpa using hfree j hj)) (by simp)).cons (by rw [upd_self]; exact e))
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j)) (h.vd_keep k (by simpa using hoVD) (by simp))
    (h.mask_keep k (by simp))

/-- `montP a x y`: `[a] := [x] [y] 2^(-32 w) mod (p | 1)`, the modulus in
`aVD`: for `[y] < (p | 1)`, below it and congruent. -/
theorem Stg.montP_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a x y : Nat} (ha : a < nArr) (hx : x ∈ live) (hy : y ∈ live) (hVD : aVD ∈ live)
    (hfree : ∀ j ∈ live, j ≠ a ∧ j ≠ aT) (haT : a ≠ aT) (hyVD : aVD ≠ y) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ g.w) (hodd : A aVD % 2 = 1) (hmt : A aVD < 2 ^ (32 * ((L + 3) / 4)))
    (hYt : A y < 2 ^ (32 * ((L + 3) / 4))) :
    WP isa (montP a x y) s fun t => ∃ R, (A y < A aVD → R < A aVD ∧
      R * 2 ^ (32 * g.w) % A aVD = A x * A y % A aVD) ∧ Stg g s0 (upd A a R) (a :: live) c t := by
  have nx := h.live_lt x hx
  have ny := h.live_lt y hy
  have nm := h.live_lt aVD hVD
  have hax : a ≠ x := fun e => (hfree x hx).1 e.symm
  have hay : a ≠ y := fun e => (hfree y hy).1 e.symm
  have ham : a ≠ aVD := fun e => (hfree aVD hVD).1 e.symm
  have htx : aT ≠ x := fun e => (hfree x hx).2 e.symm
  have hty : aT ≠ y := fun e => (hfree y hy).2 e.symm
  refine WP.mono (montMul_ok h.ws (by decide) ha nx ny nm (by decide) hax hay ham haT
    htx hty (by decide) hyVD hl hL1 hLw (by decide) (by decide) (h.arrs.get hVD) hmt hodd (h.arrs.get hy) hYt)
    fun t ⟨ht, k, nmv, nY, top, cg, r⟩ => ⟨num t.mem g.B g.w a, fun hlt => by
      have := cg hlt; rw [h.arrs.get hx] at this; exact this, ?_⟩
  have hnl : ∀ j ∈ [a, aT, aVD, y], j < nArr := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ha
    · decide
    · exact nm
    · exact ny
  refine h.next ht k hnl (by simp) r mkRegs_body ?_ ?_ top (h.mask_keep k (by simp))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [upd_self]
    · obtain ⟨hja, hjt⟩ := hfree j hj'
      rw [upd_ne _ _ hja]
      by_cases e1 : j = aVD
      · subst e1; exact nmv
      · by_cases e2 : j = y
        · subst e2; exact nY
        · rw [k.num (by
            intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> omega) (by simp) (h.ws.fit64 (h.live_lt j hj')),
            h.arrs.get hj']
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ha
    · exact h.live_lt j hj'

/-! ## The checks -/


/-- The arrays the checks start from. -/
abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

/-- The arrays after `start`: `p q mod 2^(32 w)` in `aVQ`, `p | 1` in `aVD` and
Montgomery's `n` in `aVR`. -/
abbrev aStart (v : Vals) (L M : Nat) : Nat → Nat :=
  upd (upd (upd (upd (vals v) aOne 1) aVQ L) aVD (2 * (v.p / 2) + 1)) aVR M
abbrev liveS : List Nat := aVR :: aVD :: aVQ :: live0

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

theorem mulIdx_m1 : MulIdx nArr aZ aY aX aA aM1 aT := by decide
theorem mulIdx_m2 : MulIdx nArr aZ aY aX aA aM2 aT := by decide
theorem mulIdx_p : MulIdx nArr aZ aY aX aA aP aT := by decide

theorem mask_mod2 (x : Nat) : x % 2 = if decide (x % 2 = 1) then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with e | e <;> simp [e]

/-- `p | 1` is odd, and below `2^(8 a)` with `p`. -/
theorem or1_lt {p a : Nat} (h : p < 2 ^ (8 * a)) (ha : 1 ≤ a) : 2 * (p / 2) + 1 < 2 ^ (8 * a) := by
  have : 2 ^ (8 * a) = 2 * 2 ^ (8 * a - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  omega

theorem pow8_le (a : Nat) : 2 ^ (8 * a) ≤ 2 ^ (32 * ((a + 3) / 4)) :=
  Nat.pow_le_pow_right (by decide) (by omega)

/-- `p | 1` is `p` for an odd `p`. -/
theorem or1_odd {p : Nat} (h : p % 2 = 1) : 2 * (p / 2) + 1 = p := by omega

/-- `start`: `1`, the mask of `p` odd, `p q mod 2^(32 w)`, `p | 1` and
Montgomery's `n` modulo it. -/
theorem start_ok {g : Geo} {s0 : State} {v : Vals} (hw : Ws s0 g.B g.Z g.w nArr)
    (ha : Arrs s0.mem g.B g.w (vals v) live0) (vd : w32 s0.mem g.B (arr g.w aVD + 4 * g.w) = 0)
    (hp : ∃ a, 1 ≤ a ∧ a ≤ 4 * g.w ∧ v.p < 2 ^ (8 * a) ∧ s0.gpr .r19 = BitVec.ofNat 64 a) :
    WP isa (seqs start) s0 fun t => ∃ L M, L = v.p * v.q % 2 ^ (32 * g.w) ∧
      (v.p % 2 = 1 → 2 ≤ v.p → (M = 0 ↔ v.n % v.p = 0)) ∧
      Stg g s0 (aStart v L M) liveS (decide (v.p % 2 = 1)) t := by
  have fit : ∀ j < nArr, arr g.w j + S g.w ≤ 2 ^ 64 := fun j hj => hw.fit64 hj
  obtain ⟨pa, pa1, paw, plt, p19⟩ := hp
  rw [start, wp_seqs_cons (by simp)]
  refine setOne_ok hw (j := aOne) (by decide) (by decide) fun t1 h1 k1 e1 r1 => ?_
  rw [← List.append_nil (bitOf sMask aP)]
  refine bitOf_ok h1 (j := aP) (sl := sMask) (by decide) (by decide) (by decide)
    fun t2 h2 k2 e2 r2 => WP.block_nil ?_
  have o1 : num s0.mem g.B g.w aOne = 0 := by rw [ha.get (by decide)]; rfl
  have p1 : num t1.mem g.B g.w aP = v.p := by
    rw [k1.num (by decide) (by simp) (fit _ (by decide)), ha.get (by decide)]; rfl
  have hl0 : ∀ j ∈ live0, j < nArr := by decide
  have g2 : Stg g s0 (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1)) t2 := by
    refine ⟨h2, ?_, (r1.trans r2).mono, ?_, ?_, ?_, ?_⟩
    · exact (k1.mono (js' := List.range nArr) (ds' := bodySlots)
        (fun j hj => by rw [List.mem_singleton.mp hj]; decide) (by simp)).trans
        (k2.mono (js' := List.range nArr) (ds' := bodySlots) (by simp) (by decide))
    · intro j hj
      by_cases e : j = aOne
      · subst e
        rw [upd_self, k2.num (by simp) (by simp; decide) (fit _ (by decide)), e1, o1]
      · have hjn : j < nArr := hl0 j hj
        rw [upd_ne _ _ e, k2.num (by simp) (by simp; decide) (fit _ hjn),
          k1.num (fun k hk ek => e (by rw [List.mem_singleton.mp hk] at ek; exact ek.symm)) (by simp)
            (fit _ hjn), ha.get hj]
    · exact hl0
    · rw [k2.word (by simp only [S]; omega) (by simp) (by simp; decide) (fit _ (by decide)),
        k1.word (by simp only [S]; omega) (by simp; decide) (by simp) (fit _ (by decide)), vd]
    · rw [e2, p1]; exact mask_mod2 v.p
  have r19 : ∀ {t : State} {A live c}, Stg g s0 A live c t → t.gpr .r19 = BitVec.ofNat 64 pa :=
    fun h => (h.regs.gpr _ (by decide)).trans p19
  -- `p q mod 2^(32 w)`.
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (g2.mulLo_ok (o := aVQ) (x := aP) (y := aQ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (r19 g2) pa1 paw (by rw [upd_ne _ _ (by decide)]; exact plt)) fun t3 g3 => ?_
  -- `p | 1`.
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (g3.copy_ok (o := aVD) (a := aP) (by decide) (by decide) (by decide)) fun t4 g4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (g4.orOne_ok (j := aVD) (by decide)) fun t5 g5 => ?_
  -- Montgomery's `n`.
  have hm := or1_lt plt pa1
  refine WP.mono (g5.montP_ok (a := aVR) (x := aN) (y := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (r19 g5) pa1 (by omega) (by show (2 * (v.p / 2) + 1) % 2 = 1; omega)
    (by show 2 * (v.p / 2) + 1 < _; exact Nat.lt_of_lt_of_le hm (pow8_le pa))
    (by show 1 < _; exact Nat.one_lt_two_pow (by omega))) fun t ⟨M, hM, g6⟩ => ?_
  refine ⟨v.p * v.q % 2 ^ (32 * g.w), M, rfl, fun podd p2 => ?_, g6.congr' fun j hj => ?_⟩
  · have hM' : 1 < 2 * (v.p / 2) + 1 → M < 2 * (v.p / 2) + 1 ∧
        M * 2 ^ (32 * g.w) % (2 * (v.p / 2) + 1) = v.n * 1 % (2 * (v.p / 2) + 1) := hM
    have e1 : 2 * (v.p / 2) + 1 = v.p := or1_odd podd
    rw [e1, Nat.mul_one] at hM'
    obtain ⟨Mlt, Mc⟩ := hM' (by omega)
    exact VG.Proof.Rsa.mont_zero_iff podd Mlt Mc
  · simp only [live0, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The checks of `vg_rsa_check_crt_key`. -/
theorem crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {L M : Nat}
    (h : Stg g s0 (aStart v L M) liveS (decide (v.p % 2 = 1)) s)
    (hp : ∃ a, 1 ≤ a ∧ a ≤ 4 * g.w ∧ v.p < 2 ^ (8 * a) ∧ v.qI < 2 ^ (8 * a) ∧
      s0.gpr .r19 = BitVec.ofNat 64 a) :
    WP isa (seqs crtChecks) s fun t => ∃ R₁ R₂ A₁ A₂ : Nat,
      (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
        R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
      (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
        R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
      (v.qI < v.p → v.p % 2 = 1 → 2 ≤ v.p → (A₁ = A₂ ↔ v.q * v.qI % v.p = 1)) ∧
      Stg g s0 (aFin v) liveFin
        (VG.Proof.Rsa.crtBitsM v.n v.p v.q v.dP v.dQ v.qI L M R₁ R₂ A₁ A₂) t := by
  obtain ⟨pa, pa1, paw, plt, qlt, p19⟩ := hp
  have wpos := h.ws.wpos
  have wle := h.ws.wle
  have r19 : ∀ {t : State} {A live c}, Stg g s0 A live c t → t.gpr .r19 = BitVec.ofNat 64 pa :=
    fun h => (h.regs.gpr _ (by decide)).trans p19
  unfold crtChecks
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h.eqA_ok (a := aVQ) (b := aN) (by decide) (by decide)) fun t1 h1 => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (h1.eqA_ok (a := aVR) (b := aZ) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp [ltA])]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m1 (by decide) (by decide) (by decide) (by decide) fun u _ _ => cnt33_ok u)
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m2 (by decide) (by decide) (by decide) (by decide) fun u _ _ => cnt33_ok u)
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`: Montgomery's `q qInv` and `1 · 1` compared.
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  have h13' := h13.sub (live' := aVD :: aOne :: aQ :: aQI :: aN :: aZ :: aD :: aDP :: aDQ :: aM1 :: aM2 :: aP :: [])
    (by decide)
  have hm := or1_lt plt pa1
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h13'.montP_ok (a := aA) (x := aQ) (y := aQI) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (r19 h13') pa1 (by omega) (by show (2 * (v.p / 2) + 1) % 2 = 1; omega)
    (by show 2 * (v.p / 2) + 1 < _; exact Nat.lt_of_lt_of_le hm (pow8_le pa))
    (by show v.qI < _; exact Nat.lt_of_lt_of_le qlt (pow8_le pa))) fun t14 ⟨A₁, hA₁, h14⟩ => ?_
  rw [wp_seqs_cons (by simp [eqA])]
  refine WP.mono (h14.montP_ok (a := aY) (x := aOne) (y := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (r19 h14) pa1 (by omega) (by show (2 * (v.p / 2) + 1) % 2 = 1; omega)
    (by show 2 * (v.p / 2) + 1 < _; exact Nat.lt_of_lt_of_le hm (pow8_le pa))
    (by show 1 < _; exact Nat.one_lt_two_pow (by omega))) fun t15 ⟨A₂, hA₂, h15⟩ => ?_
  refine WP.mono (h15.eqA_ok (a := aA) (b := aY) (by decide) (by decide)) fun t h16 => ?_
  refine ⟨R₁, R₂, A₁, A₂, hR₁, hR₂, fun hlt podd p2 => ?_,
    (h16.sub (live' := liveFin) (by decide)).congr' fun j hj => ?_⟩
  · have hA₁' : v.qI < 2 * (v.p / 2) + 1 → A₁ < 2 * (v.p / 2) + 1 ∧
        A₁ * 2 ^ (32 * g.w) % (2 * (v.p / 2) + 1) = v.q * v.qI % (2 * (v.p / 2) + 1) := hA₁
    have hA₂' : 1 < 2 * (v.p / 2) + 1 → A₂ < 2 * (v.p / 2) + 1 ∧
        A₂ * 2 ^ (32 * g.w) % (2 * (v.p / 2) + 1) = 1 * 1 % (2 * (v.p / 2) + 1) := hA₂
    have e1 : 2 * (v.p / 2) + 1 = v.p := or1_odd podd
    rw [e1] at hA₁' hA₂'
    obtain ⟨l1, c1⟩ := hA₁' hlt
    obtain ⟨l2, c2⟩ := hA₂' (by omega)
    rw [Nat.one_mul] at c2
    exact VG.Proof.Rsa.mont_eq_iff podd p2 l1 l2 c1 c2
  · simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem aFin_d (v : Vals) : aFin v aD = v.d := rfl
theorem aFin_n (v : Vals) : aFin v aN = v.n := rfl
theorem aFin_m1 (v : Vals) : aFin v aM1 = 2 * (v.p / 2) := rfl
theorem aFin_m2 (v : Vals) : aFin v aM2 = 2 * (v.q / 2) := rfl

/-- The checks of `d`: `d < n`, and its remainders modulo `p - 1` and `q - 1`
compared with `dP` and `dQ`. -/
theorem dChecks_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s)
    (hp : ∃ a, 1 ≤ a ∧ a < 2 ^ 32 ∧ v.p < 2 ^ (8 * a) ∧ s0.gpr .r19 = BitVec.ofNat 64 a)
    (hq : ∃ a, 1 ≤ a ∧ a < 2 ^ 32 ∧ v.q < 2 ^ (8 * a) ∧ s0.gpr .r21 = BitVec.ofNat 64 a) :
    WP isa (seqs dChecks) s fun t => ∃ Y₁ Y₂,
      (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  unfold dChecks
  simp only [List.append_assoc]
  rw [wp_seqs_append (by simp [ltA]) (by simp [divA])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [aFin_d, aFin_n] at h1
  rw [wp_seqs_append (by simp [divA]) (by simp [eqA])]
  obtain ⟨pa, pa1, pa2, plt, p19⟩ := hp
  obtain ⟨qa, qa1, qa2, qlt, q21⟩ := hq
  refine WP.mono (h1.divA_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide) (len := .r19) (by decide)
    (by decide) ((h1.regs.gpr _ (by decide)).trans p19) pa1 pa2 (by rw [aFin_m1]; omega))
    fun t2 ⟨Xq, Y₁, hv1, h2⟩ => ?_
  rw [aFin_d, aFin_m1] at hv1
  rw [wp_seqs_append (by simp [eqA]) (by simp [divA])]
  refine WP.mono (h2.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide)) fun t3 h3 => ?_
  have h3' : Stg g s0 (aFin v) liveFin (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t3 := by
    have e : upd (upd (aFin v) aVQ Xq) aVR Y₁ aVR = Y₁ := by rw [upd_self]
    have e2 : upd (upd (aFin v) aVQ Xq) aVR Y₁ aDP = v.dP := rfl
    rw [e, e2] at h3
    exact (h3.sub (live' := liveFin) (by decide)).congr' fun j hj => by
      simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [wp_seqs_append (by simp [divA]) (by simp [eqA])]
  refine WP.mono (h3'.divA_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide) (len := .r21) (by decide)
    (by decide) ((h3'.regs.gpr _ (by decide)).trans q21) qa1 qa2 (by rw [aFin_m2]; omega))
    fun t4 ⟨Xq', Y₂, hv2, h4⟩ => ?_
  rw [aFin_d, aFin_m2] at hv2
  refine WP.mono (h4.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide)) fun t h5 => ?_
  have e : upd (upd (aFin v) aVQ Xq') aVR Y₂ aVR = Y₂ := by rw [upd_self]
  have e2 : upd (upd (aFin v) aVQ Xq') aVR Y₂ aDQ = v.dQ := rfl
  rw [e, e2] at h5
  exact ⟨Y₁, Y₂, fun hp => (hv1 hp).1, fun hq => (hv2 hq).1, _, _, h5⟩

end VG.Proof.Rsa.PPC64LE.KeyCheck
