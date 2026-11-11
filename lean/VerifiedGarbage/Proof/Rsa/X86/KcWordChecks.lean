module

public import VerifiedGarbage.Proof.Rsa.X86.KcStart
public import VerifiedGarbage.Proof.Rsa.X86.KcWord
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Framework.Omega

/-! # The checks of an RSA key on i686: the checks by word steps

`Stg.crtChecks_ok`: `p - 1` and `q - 1`, then the guard, under which the
word steps run (`WordOk`: `p`'s length, and, where `p q = n`, the top bits
of `p`, `p - 1` and `q - 1` set, so that the word steps leave them as they
are). `wordProducts_ok`: the products `e dP`, `e dQ` and `q qInv` reduced
by word steps; `dWords_ok`: `d < n` and the remainders of `d`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top top_iff val32_low)

/-! ## The guard -/

/-- What the word steps need. -/
structure WordOk (g : Geo) (s0 : State) (v : Vals) (ap : Nat) : Prop where
  len : MLen s0 g.B g.Z (pLenArg g.full) ap
  four : 4 ≤ wq ap
  room : wq ap + 2 ≤ g.w
  top : v.p * v.q = v.n → Top (wq ap) v.p ∧ Top (wq ap) (2 * (v.p / 2)) ∧ Top (wq ap) (2 * (v.q / 2))

/-- A factor of a number of `2 K` bits, the other below `2^K`, is above `2^(K - 1)`. -/
theorem factor_top {K p q n : Nat} (hn : 2 ^ (2 * K - 1) ≤ n) (hq : q < 2 ^ K)
    (hpq : p * q = n) : 2 ^ (K - 1) < p := by
  refine Nat.lt_of_not_le fun hle => ?_
  have e : 2 ^ (2 * K - 1) = 2 ^ (K - 1) * 2 ^ K := by rw [← Nat.pow_add]; congr 1; omega
  have : p * q < 2 ^ (K - 1) * 2 ^ K :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right q hle) (Nat.mul_lt_mul_of_pos_left hq (Nat.two_pow_pos _))
  omega

theorem top_factor {K p : Nat} (lo : 2 ^ (K - 1) < p) (hi : p < 2 ^ K) :
    (2 ^ (K - 1) ≤ p ∧ p < 2 ^ K) ∧ (2 ^ (K - 1) ≤ 2 * (p / 2) ∧ 2 * (p / 2) < 2 ^ K) :=
  ⟨⟨Nat.le_of_lt lo, hi⟩, ⟨by omega, by omega⟩⟩

theorem wordOk_of {g : Geo} {s0 : State} {v : Vals} {an ap aq top : Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (hp : v.p < 2 ^ (8 * ap)) (hq : v.q < 2 ^ (8 * aq))
    (hkw : VG.Proof.Rsa.X86.KeyRt.kw an = g.w) (htop : 2 ^ 31 ≤ top ↔ 2 ^ (32 * g.w - 1) ≤ v.n)
    (bal : Bal an ap aq top) : WordOk g s0 v ap := by
  obtain ⟨h8, hpa, hqa, h128, ht⟩ := bal
  have hw : g.w = an / 4 := by
    rw [← hkw]; simp only [VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega
  have hwq : wq ap = ap / 4 := by simp only [wq]; omega
  have hK : 32 * wq ap = 8 * ap := by rw [hwq]; omega
  have hn : 2 ^ (2 * (8 * ap) - 1) ≤ v.n := by
    have := htop.mp ht
    rwa [show 32 * g.w = 2 * (8 * ap) by rw [hw]; omega] at this
  have hq' : v.q < 2 ^ (8 * ap) := by rwa [show 8 * aq = 8 * ap by omega] at hq
  refine ⟨hm, by omega, by omega, fun hpq => ?_⟩
  simp only [Top, hK]
  have pt := top_factor (factor_top hn hq' hpq) hp
  have qt := top_factor (factor_top hn hp (by rw [Nat.mul_comm]; exact hpq)) hq'
  exact ⟨pt.1, pt.2, qt.2⟩

/-! ## `p - 1`, `q - 1`, the guard, and the branch on it -/

/-- The arrays the checks use after `p - 1` and `q - 1`. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (aStart v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := aM2 :: aM1 :: live0

theorem Stg.crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool}
    (h : Stg g s0 (aStart v) live0 c s)
    (hp : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.p < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (pLenArg g.full) (BitVec.ofNat 32 a))
    (hq : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a))
    {W O : Prog isa} {Q : State → Prop}
    (hW : ∀ ap, WordOk g s0 v ap → ∀ u, Stg g s0 (aFin v) liveFin c u → WP isa W u Q)
    (hO : ∀ u, Stg g s0 (aFin v) liveFin c u → WP isa O u Q) :
    WP isa (crtChecks g.full W O) s Q := by
  obtain ⟨ap, -, hap, plt, parg⟩ := hp
  obtain ⟨aq, -, haq, qlt, qarg⟩ := hq
  unfold crtChecks
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  have h6' : Stg g s0 (aFin v) liveFin c t6 := h6.congr rfl
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h6'.balanced_ok (h6'.arg parg) (h6'.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, _, _, hkw, hg⟩ => ?_
  have nv : num t6.mem g.B g.w aN = v.n := h6'.arrs.get (by decide)
  have htop : 2 ^ 31 ≤ mw t6.mem g.B g.w aN (g.w - 1) ↔ 2 ^ (32 * g.w - 1) ≤ v.n := by
    rw [← nv]; exact top_iff h7.ws.ws.wpos
  exact h7.ifBalanced_ok hg (fun bal u hu => hW ap (wordOk_of ⟨parg, hap⟩ plt qlt hkw htop bal) u hu)
    (fun _ u hu => hO u hu)

/-! ## The product checks by word steps -/

/-- `eWord x m`: `[x] < [m]` and `e [x] mod [m] = 1`, `m` left as it was where its top bit is set. -/
theorem Stg.eWord_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {x m ap : Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (h4 : 4 ≤ wq ap) (hw : wq ap + 2 ≤ g.w)
    (hx : x ∈ live) (hmL : m ∈ live) (hE : aE ∈ live) (hO : aOne ∈ live) (one : A aOne = 1)
    (hfree : ∀ j ∈ live, j ≠ aY ∧ j ≠ aX ∧ j ≠ aA ∧ j ≠ aT ∧ j ≠ aW)
    (hmv : m ≠ aVD) (hmO : m ≠ aOne) :
    WP isa (seqs (eWord g.full x m)) s fun t => ∃ M R,
      (Top (wq ap) (A m) → M = A m) ∧
      (Top (wq ap) (A m) → A x < A m → A aE < 2 ^ 33 → R = A aE * A x % A m) ∧
      Stg g s0 (upd A m M) live ((c && decide (A x < A m)) && decide (R = 1)) t := by
  have nW : aW ∉ live := fun hw' => (hfree aW hw').2.2.2.2 rfl
  unfold eWord
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h.ltA_ok hx hmL nW) fun t1 h1 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h1.mulShort_ok (o := aY) (a := x) (b := aE) (by decide) hx hE
    (fun j hj => ⟨(hfree j hj).1, (hfree j hj).2.1⟩) (by decide) (by omega)) fun t2 ⟨h2, e2⟩ => ?_
  rw [wp_seqs_cons (by simp [eqA])]
  have hmY : m ≠ aY := (hfree m hmL).1
  have hmT : m ≠ aT := (hfree m hmL).2.2.2.1
  have hmX : m ≠ aX := (hfree m hmL).2.1
  refine WP.mono (h2.wordMod_ok (x := aY) (r := aA) (m := m) (wide := false) hm h4 (by omega) (by decide)
    (by decide) hmL (fun j hj => ⟨(hfree j hj).2.2.1, (hfree j hj).2.2.2.1⟩) (fun e => (hfree m hmL).2.2.1 e.symm)
    (by decide) hmT (by decide) (by decide) hmY (fun e => absurd e (by decide)) (fun e => absurd e (by decide))
    (fun e => absurd e (by decide)) ⟨hmv, by decide⟩) fun t3 ⟨M, R, hMR, h3⟩ => ?_
  have nA : aA ∉ live := fun ha => (hfree aA ha).2.2.1 rfl
  refine WP.mono (h3.eqA_ok (a := aA) (b := aOne) (by simp) (by simp [hO]) (by simp [nW]; decide))
    fun t ht => ⟨M, R, fun tp => (hMR tp).1, fun tp hlt he => ?_, ?_⟩
  · obtain ⟨-, eR⟩ := hMR tp
    simp only [Bool.false_eq_true, ↓reduceIte] at eR
    have big : A x * A aE < 2 ^ (32 * g.w) :=
      calc A x * A aE < 2 ^ (32 * wq ap) * 2 ^ 64 :=
            Nat.mul_lt_mul'' (Nat.lt_trans hlt tp.2) (Nat.lt_trans he (by decide))
        _ = 2 ^ (32 * wq ap + 64) := by rw [Nat.pow_add]
        _ ≤ 2 ^ (32 * g.w) := Nat.pow_le_pow_right (by decide) (by omega)
    have full := e2 (Nat.lt_trans he (by decide))
    rw [eR, val32_low (Nat.le_add_right g.w 2) (by rw [full]; exact big), full, Nat.mul_comm]
  · have v1 : upd (upd A m M) aA R aOne = 1 := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm hmO), one]
    rw [upd_self, v1] at ht
    exact (ht.sub (live' := live) fun j hj => by simp [hj]).congr' fun j hj => by
      rw [upd_ne _ _ (by rintro rfl; exact nA hj)]

/-- `qInvWord`: `qInv < p` and `q qInv mod p = 1`, `p` left as it was where its top bit is set. -/
theorem Stg.qInvWord_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {ap : Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (h4 : 4 ≤ wq ap) (hw : wq ap + 2 ≤ g.w)
    (hI : aQI ∈ live) (hP : aP ∈ live) (hQ : aQ ∈ live) (hO : aOne ∈ live) (one : A aOne = 1)
    (hfree : ∀ j ∈ live, j ≠ aY ∧ j ≠ aX ∧ j ≠ aA ∧ j ≠ aT ∧ j ≠ aW) :
    WP isa (seqs (qInvWord g.full)) s fun t => ∃ M R,
      (Top (wq ap) (A aP) → M = A aP) ∧
      (Top (wq ap) (A aP) → R = A aQ * A aQI % A aP) ∧
      Stg g s0 (upd A aP M) live ((c && decide (A aQI < A aP)) && decide (R = 1)) t := by
  have nW : aW ∉ live := fun hw' => (hfree aW hw').2.2.2.2 rfl
  unfold qInvWord
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h.ltA_ok hI hP nW) fun t1 h1 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h1.mulWide_ok (o := aY) (a := aQ) (b := aQI) (by decide) hQ hI
    (fun j hj => ⟨(hfree j hj).1, (hfree j hj).2.1⟩) (by decide)) fun t2 ⟨h2, e2⟩ => ?_
  rw [wp_seqs_cons (by simp [eqA])]
  refine WP.mono (h2.wordMod_ok (x := aY) (r := aA) (m := aP) (wide := true) hm h4 (by omega) (by decide)
    (by decide) hP (fun j hj => ⟨(hfree j hj).2.2.1, (hfree j hj).2.2.2.1⟩) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) (fun _ => by decide)
    (fun _ => by decide) ⟨by decide, by decide⟩) fun t3 ⟨M, R, hMR, h3⟩ => ?_
  have nA : aA ∉ live := fun ha => (hfree aA ha).2.2.1 rfl
  refine WP.mono (h3.eqA_ok (a := aA) (b := aOne) (by simp) (by simp [hO]) (by simp [nW]; decide))
    fun t ht => ⟨M, R, fun tp => (hMR tp).1, fun tp => ?_, ?_⟩
  · obtain ⟨-, eR⟩ := hMR tp
    simp only [↓reduceIte] at eR
    rw [eR, e2]
  · have v1 : upd (upd A aP M) aA R aOne = 1 := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), one]
    rw [upd_self, v1] at ht
    exact (ht.sub (live' := live) fun j hj => by simp [hj]).congr' fun j hj => by
      rw [upd_ne _ _ (by rintro rfl; exact nA hj)]

/-- The arrays after the product checks by word steps: `p - 1`, `q - 1` and `p` as they were
where `p q = n`. -/
abbrev aWord (v : Vals) (M₁ M₂ M₃ : Nat) : Nat → Nat := upd (upd (upd (aFin v) aM1 M₁) aM2 M₂) aP M₃

/-- The three product checks by word steps. -/
theorem Stg.wordProducts_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} {ap : Nat}
    (h : Stg g s0 (aFin v) liveFin c s) (wo : WordOk g s0 v ap) :
    WP isa (wordProducts g.full) s fun t => ∃ M₁ M₂ M₃ R₁ R₂ R₃,
      (v.p * v.q = v.n → M₁ = 2 * (v.p / 2) ∧ M₂ = 2 * (v.q / 2) ∧ M₃ = v.p) ∧
      (v.e < 2 ^ 33 → v.p * v.q = v.n →
        (v.dP < 2 * (v.p / 2) → R₁ = v.e * v.dP % (2 * (v.p / 2))) ∧
        (v.dQ < 2 * (v.q / 2) → R₂ = v.e * v.dQ % (2 * (v.q / 2))) ∧
        (v.qI < v.p → R₃ = v.q * v.qI % v.p)) ∧
      Stg g s0 (aWord v M₁ M₂ M₃) liveFin
        ((((((c && decide (v.dP < 2 * (v.p / 2))) && decide (R₁ = 1)) && decide (v.dQ < 2 * (v.q / 2))) &&
          decide (R₂ = 1)) && decide (v.qI < v.p)) && decide (R₃ = 1)) t := by
  have fr : ∀ j ∈ liveFin, j ≠ aY ∧ j ≠ aX ∧ j ≠ aA ∧ j ≠ aT ∧ j ≠ aW := by decide
  unfold wordProducts
  rw [List.append_assoc, wp_seqs_append (by simp [eWord, ltA]) (by simp [eWord, ltA])]
  refine WP.mono (h.eWord_ok (x := aDP) (m := aM1) wo.len wo.four wo.room (by decide) (by decide) (by decide)
    (by decide) rfl fr (by decide) (by decide)) fun t1 ⟨M₁, R₁, eM₁, eR₁, h1⟩ => ?_
  rw [wp_seqs_append (by simp [eWord, ltA]) (by simp [ltA, qInvWord])]
  refine WP.mono (h1.eWord_ok (x := aDQ) (m := aM2) wo.len wo.four wo.room (by decide) (by decide) (by decide)
    (by decide) rfl fr (by decide) (by decide)) fun t2 ⟨M₂, R₂, eM₂, eR₂, h2⟩ => ?_
  refine WP.mono (h2.qInvWord_ok wo.len wo.four wo.room (by decide) (by decide) (by decide) (by decide) rfl fr)
    fun t ⟨M₃, R₃, eM₃, eR₃, h3⟩ => ⟨M₁, M₂, M₃, R₁, R₂, R₃, fun hpq => ?_, fun he hpq => ?_, h3⟩
  · obtain ⟨tp, tp1, tq1⟩ := wo.top hpq
    exact ⟨eM₁ tp1, eM₂ tq1, eM₃ tp⟩
  · obtain ⟨tp, tp1, tq1⟩ := wo.top hpq
    exact ⟨fun hlt => eR₁ tp1 hlt he, fun hlt => eR₂ tq1 hlt he, fun _ => eR₃ tp⟩

/-- `dWords`: `d < n`, and the remainders of `d` modulo `[aM1]` and `[aM2]` by word steps, compared
with `dP` and `dQ`. -/
theorem Stg.dWords_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool} {ap : Nat}
    (h : Stg g s0 A live c s) (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (h4 : 4 ≤ wq ap) (hw : wq ap ≤ g.w)
    (hl : ∀ j ∈ [aD, aN, aDP, aDQ, aM1, aM2], j ∈ live) (fr : ∀ j ∈ live, j ≠ aVR ∧ j ≠ aT ∧ j ≠ aW) :
    WP isa (dWords g.full) s fun t => ∃ Y₁ Y₂,
      (Top (wq ap) (A aM1) → Y₁ = A aD % A aM1) ∧ (Top (wq ap) (A aM2) → Y₂ = A aD % A aM2) ∧
      ∃ A' live', Stg g s0 A' live'
        (((c && decide (A aD < A aN)) && decide (Y₁ = A aDP)) && decide (Y₂ = A aDQ)) t := by
  have nW : aW ∉ live := fun hw' => (fr aW hw').2.2 rfl
  have nR : aVR ∉ live := fun hw' => (fr aVR hw').1 rfl
  have hD := hl aD (by decide)
  have hM1 := hl aM1 (by decide)
  have hM2 := hl aM2 (by decide)
  unfold dWords
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h.ltA_ok hD (hl aN (by decide)) nW) fun t1 h1 => ?_
  rw [wp_seqs_cons (by simp [eqA])]
  have gd1 := h1.arrs.get hD
  refine WP.mono (h1.wordMod_ok (x := aD) (r := aVR) (m := aM1) (wide := false) hm h4 hw (by decide)
    (by decide) hM1 (fun j hj => ⟨(fr j hj).1, (fr j hj).2.1⟩) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun e => absurd e (by decide)) (fun e => absurd e (by decide))
    (fun e => absurd e (by decide)) ⟨by decide, by decide⟩) fun t2 ⟨M, Y₁, eY₁, h2⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h2.eqA_ok (a := aVR) (b := aDP) (by simp) (by simp [hl aDP (by decide)])
    (by simp [nW]; decide)) fun t3 h3 => ?_
  rw [upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide)] at h3
  have h3' := h3.sub (live' := live) fun j hj => by simp [hj]
  rw [wp_seqs_cons (by simp [eqA])]
  have gd3 := h3'.arrs.get hD
  refine WP.mono (h3'.wordMod_ok (x := aD) (r := aVR) (m := aM2) (wide := false) hm h4 hw (by decide)
    (by decide) hM2 (fun j hj => ⟨(fr j hj).1, (fr j hj).2.1⟩) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun e => absurd e (by decide)) (fun e => absurd e (by decide))
    (fun e => absurd e (by decide)) ⟨by decide, by decide⟩) fun t4 ⟨M', Y₂, eY₂, h4'⟩ => ?_
  refine WP.mono (h4'.eqA_ok (a := aVR) (b := aDQ) (by simp) (by simp [hl aDQ (by decide)])
    (by simp [nW]; decide)) fun t ht => ⟨Y₁, Y₂, fun tp => ?_, fun tp => ?_, ?_⟩
  · obtain ⟨-, e⟩ := eY₁ tp
    simp only [Bool.false_eq_true, ↓reduceIte] at e
    rw [e]; exact congrArg (· % A aM1) gd1
  · have a2 : upd (upd A aM1 M) aVR Y₁ aM2 = A aM2 := by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    rw [a2] at eY₂
    obtain ⟨-, e⟩ := eY₂ tp
    simp only [Bool.false_eq_true, ↓reduceIte] at e
    have d3 : num t3.mem g.B g.w aD = A aD := by rw [gd3, upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    rw [e]; exact congrArg (· % A aM2) d3
  · rw [upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide),
      upd_ne _ _ (by decide)] at ht
    exact ⟨_, _, ht⟩

end VG.Proof.Rsa.X86.KeyCheck
