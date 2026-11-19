module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Rsa.X86.KcStart
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop

/-! ### `Rsa.X86.KcWordChecks`, which this module and modules that import it used -/

section

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
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top top_iff val32_low factor_top top_factor)

/-! ## The guard -/

/-- What the word steps need. -/
structure WordOk (g : Geo) (s0 : State) (v : Vals) (ap : Nat) : Prop where
  len : MLen s0 g.B g.Z (pLenArg g.full) ap
  four : 4 ≤ wq ap
  room : wq ap + 2 ≤ g.w
  top : v.p * v.q = v.n → Top (wq ap) v.p ∧ Top (wq ap) (2 * (v.p / 2)) ∧ Top (wq ap) (2 * (v.q / 2))
  /-- The primes' words, half the modulus's. -/
  half : 2 * wq ap = g.w

theorem wordOk_of {g : Geo} {s0 : State} {v : Vals} {an ap aq top : Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (hp : v.p < 2 ^ (8 * ap)) (hq : v.q < 2 ^ (8 * aq))
    (hkw : VG.Proof.Rsa.X86.KeyRt.kw an = g.w) (htop : 2 ^ 31 ≤ top ↔ 2 ^ (32 * g.w - 1) ≤ v.n)
    (bal : Bal an ap aq top) : WordOk g s0 v ap := by
  obtain ⟨h8, hpa, hqa, h128, ht⟩ := bal
  have hw : g.w = an / 4 := by
    rw [← hkw]; simp only [VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega_using [h8]
  have hwq : wq ap = ap / 4 := by simp only [wq]; omega_using [h8, hpa]
  have hK : 32 * wq ap = 8 * ap := by rw [hwq]; omega_using [h8, hpa]
  have hn : 2 ^ (2 * (8 * ap) - 1) ≤ v.n := by
    have := htop.mp ht
    rwa [show 32 * g.w = 2 * (8 * ap) by rw [hw]; omega_using [h8, hpa]] at this
  have hq' : v.q < 2 ^ (8 * ap) := by rwa [show 8 * aq = 8 * ap by omega_using [hpa, hqa]] at hq
  refine ⟨hm, by omega_using [hpa, h128, hwq], by omega_using [hpa, h128, hw, hwq], fun hpq => ?_, by omega_using [h8, hpa, hw, hwq]⟩
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
    (fun j hj => ⟨(hfree j hj).1, (hfree j hj).2.1⟩) (by decide) (by omega_using [hw])) fun t2 ⟨h2, e2⟩ => ?_
  rw [wp_seqs_cons (by simp [eqA])]
  have hmY : m ≠ aY := (hfree m hmL).1
  have hmT : m ≠ aT := (hfree m hmL).2.2.2.1
  have hmX : m ≠ aX := (hfree m hmL).2.1
  refine WP.mono (h2.wordMod_ok (x := aY) (r := aA) (m := m) (top := some 2) hm h4 (by omega_using [hw])
    (fun k e => by obtain rfl := Option.some.inj e; omega_using [hw]) (by decide)
    (by decide) hmL (fun j hj => ⟨(hfree j hj).2.2.1, (hfree j hj).2.2.2.1⟩) (fun e => (hfree m hmL).2.2.1 e.symm)
    (by decide) hmT (by decide) (by decide) hmY ⟨hmv, by decide⟩) fun t3 ⟨M, R, hMR, h3⟩ => ?_
  have nA : aA ∉ live := fun ha => (hfree aA ha).2.2.1 rfl
  refine WP.mono (h3.eqA_ok (a := aA) (b := aOne) (by simp) (by simp [hO]) (by simp [nW]; decide))
    fun t ht => ⟨M, R, fun tp => (hMR tp).1, fun tp hlt he => ?_, ?_⟩
  · obtain ⟨-, eR⟩ := hMR tp
    have big : A x * A aE < 2 ^ (32 * (wq ap + 2)) :=
      calc A x * A aE < 2 ^ (32 * wq ap) * 2 ^ 64 :=
            Nat.mul_lt_mul'' (Nat.lt_trans hlt tp.2) (Nat.lt_trans he (by decide))
        _ = 2 ^ (32 * (wq ap + 2)) := by rw [← Nat.pow_add]; congr 1
    have full := e2 (Nat.lt_trans he (by decide))
    rw [eR, show VG.Proof.Rsa.X86.WordRt.xw g.len ap (some 2) = wq ap + 2 from rfl,
      val32_low (k := wq ap + 2) (w := g.w + 2) (by omega_using [hw]) (by rw [full]; exact big), full, Nat.mul_comm]
  · have v1 : upd (upd A m M) aA R aOne = 1 := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm hmO), one]
    rw [upd_self, v1] at ht
    exact (ht.sub (live' := live) fun j hj => by simp [hj]).congr' fun j hj => by
      rw [upd_ne _ _ (by rintro rfl; exact nA hj)]

/-- `qInvWord`: `qInv < p` and `q qInv mod p = 1`, `p` left as it was where its top bit is set. -/
theorem Stg.qInvWord_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {ap : Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (h4 : 4 ≤ wq ap) (hh : 2 * wq ap = g.w)
    (hI : aQI ∈ live) (hP : aP ∈ live) (hQ : aQ ∈ live) (hO : aOne ∈ live) (one : A aOne = 1)
    (hfree : ∀ j ∈ live, j ≠ aY ∧ j ≠ aX ∧ j ≠ aA ∧ j ≠ aT ∧ j ≠ aW) :
    WP isa (seqs (qInvWord g.full)) s fun t => ∃ M R,
      (Top (wq ap) (A aP) → M = A aP) ∧
      (Top (wq ap) (A aP) → A aQ < 2 ^ (32 * wq ap) → A aQI < A aP → R = A aQ * A aQI % A aP) ∧
      Stg g s0 (upd A aP M) live ((c && decide (A aQI < A aP)) && decide (R = 1)) t := by
  have nW : aW ∉ live := fun hw' => (hfree aW hw').2.2.2.2 rfl
  have hh2 : g.w / 2 = wq ap := by omega_using [hh]
  unfold qInvWord
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (h.ltA_ok hI hP nW) fun t1 h1 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h1.mulHalf_if_ok (o := aY) (a := aQ) (b := aQI) (by decide) hQ hI
    (fun j hj => ⟨(hfree j hj).1, (hfree j hj).2.1⟩) (by decide)) fun t2 ⟨h2, e2⟩ => ?_
  rw [wp_seqs_cons (by simp [eqA])]
  refine WP.mono (h2.wordMod_ok (x := aY) (r := aA) (m := aP) (top := none) hm h4 (by omega_using [hh]) (by simp) (by decide)
    (by decide) hP (fun j hj => ⟨(hfree j hj).2.2.1, (hfree j hj).2.2.2.1⟩) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide⟩) fun t3 ⟨M, R, hMR, h3⟩ => ?_
  have nA : aA ∉ live := fun ha => (hfree aA ha).2.2.1 rfl
  refine WP.mono (h3.eqA_ok (a := aA) (b := aOne) (by simp) (by simp [hO]) (by simp [nW]; decide))
    fun t ht => ⟨M, R, fun tp => (hMR tp).1, fun tp hq hlt => ?_, ?_⟩
  · obtain ⟨-, eR⟩ := hMR tp
    simp only [VG.Proof.Rsa.X86.WordRt.xw] at eR
    have hi : A aQI < 2 ^ (32 * wq ap) := Nat.lt_trans hlt tp.2
    have full := e2 (by rw [hh2]; exact hq) (by rw [hh2]; exact hi)
    have big : A aQ * A aQI < 2 ^ (32 * g.w) :=
      calc A aQ * A aQI < 2 ^ (32 * wq ap) * 2 ^ (32 * wq ap) := Nat.mul_lt_mul'' hq hi
        _ = 2 ^ (32 * g.w) := by rw [← Nat.pow_add, ← hh]; congr 1; omega_using []
    rw [eR, val32_low (k := g.w) (w := 2 * g.w) (by omega_using []) (by rw [full]; exact big), full]
  · have v1 : upd (upd A aP M) aA R aOne = 1 := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), one]
    rw [upd_self, v1] at ht
    exact (ht.sub (live' := live) fun j hj => by simp [hj]).congr' fun j hj => by
      rw [upd_ne _ _ (by rintro rfl; exact nA hj)]

/-- Below `2^(32 k)` where twice its half is (`k ≥ 1`). -/
theorem lt_of_half_lt {x k : Nat} (hk : 1 ≤ k) (h : 2 * (x / 2) < 2 ^ (32 * k)) : x < 2 ^ (32 * k) := by
  have e : 2 ^ (32 * k) = 2 * 2 ^ (32 * k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega_using [hk]
  omega_using [h, e]

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
  refine WP.mono (h2.qInvWord_ok wo.len wo.four wo.half (by decide) (by decide) (by decide) (by decide) rfl fr)
    fun t ⟨M₃, R₃, eM₃, eR₃, h3⟩ => ⟨M₁, M₂, M₃, R₁, R₂, R₃, fun hpq => ?_, fun he hpq => ?_, h3⟩
  · obtain ⟨tp, tp1, tq1⟩ := wo.top hpq
    exact ⟨eM₁ tp1, eM₂ tq1, eM₃ tp⟩
  · obtain ⟨tp, tp1, tq1⟩ := wo.top hpq
    exact ⟨fun hlt => eR₁ tp1 hlt he, fun hlt => eR₂ tq1 hlt he,
      fun hlt => eR₃ tp (lt_of_half_lt (by have := wo.four; omega_using [this]) tq1.2) hlt⟩

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
  refine WP.mono (h1.wordMod_ok (x := aD) (r := aVR) (m := aM1) (top := none) hm h4 hw (by simp) (by decide)
    (by decide) hM1 (fun j hj => ⟨(fr j hj).1, (fr j hj).2.1⟩) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨by decide, by decide⟩) fun t2 ⟨M, Y₁, eY₁, h2⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h2.eqA_ok (a := aVR) (b := aDP) (by simp) (by simp [hl aDP (by decide)])
    (by simp [nW]; decide)) fun t3 h3 => ?_
  rw [upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide)] at h3
  have h3' := h3.sub (live' := live) fun j hj => by simp [hj]
  rw [wp_seqs_cons (by simp [eqA])]
  have gd3 := h3'.arrs.get hD
  refine WP.mono (h3'.wordMod_ok (x := aD) (r := aVR) (m := aM2) (top := none) hm h4 hw (by simp) (by decide)
    (by decide) hM2 (fun j hj => ⟨(fr j hj).1, (fr j hj).2.1⟩) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨by decide, by decide⟩) fun t4 ⟨M', Y₂, eY₂, h4'⟩ => ?_
  refine WP.mono (h4'.eqA_ok (a := aVR) (b := aDQ) (by simp) (by simp [hl aDQ (by decide)])
    (by simp [nW]; decide)) fun t ht => ⟨Y₁, Y₂, fun tp => ?_, fun tp => ?_, ?_⟩
  · obtain ⟨-, e⟩ := eY₁ tp
    simp only [VG.Proof.Rsa.X86.WordRt.xw] at e
    rw [e]; exact congrArg (· % A aM1) gd1
  · have a2 : upd (upd A aM1 M) aVR Y₁ aM2 = A aM2 := by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    rw [a2] at eY₂
    obtain ⟨-, e⟩ := eY₂ tp
    simp only [VG.Proof.Rsa.X86.WordRt.xw] at e
    have d3 : num t3.mem g.B g.w aD = A aD := by rw [gd3, upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    rw [e]; exact congrArg (· % A aM2) d3
  · rw [upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide),
      upd_ne _ _ (by decide)] at ht
    exact ⟨_, _, ht⟩

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcChecks`, which only this module used -/

section

/-! # The checks of an RSA key on i686: the checks after the division of `n` by `p`

`crtChecks_ok`: from the quotient `X₁` and remainder `X₂` of `n / p`, the
mask is and'ed with `n / p = q`, `n mod p = 0`, `dP < p - 1`, `e dP ≡ 1`,
`dQ < q - 1`, `e dQ ≡ 1`, `qInv < p` and `q qInv ≡ 1` (`crtBits`), the
products known when their factor is below their modulus; `p - 1` and `q - 1`
are left in `aM1` and `aM2`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (MulIdx)

/-! ## `mulMod` counting in `esi`'s high half -/

section MulHi
open VG.Proof.Rsa.X86.KeyRt (RtWs kw MulIdx mulArrs nm1 nm4 mulHead_ok addMod_ok half_ok)
open VG.Impl.Rsa.X86.Keys (sB sC)
open VG.Impl.Rsa.X86.KeyCheckRt (lay stepUnit mulTailHi mulModStepHi mulModHi)

variable {B : Addr} {Z len N : Nat}

/-- `mulTailHi`: `[y]` halved, `esi` less `2^16`. -/
theorem mulTailHi_ok {full : Bool} {s : State} (h : RtWs (lay full) s B Z len N) {y : Nat} (hy : y < N) :
    WP isa (mulTailHi full y) s fun u => RtWs (lay full) u B Z len N ∧ Keep B (kw len) [y] [] s.mem u.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s u ∧
      u.gpr .esi = s.gpr .esi - BitVec.ofNat 32 stepUnit ∧
      u.cf = some (decide ((s.gpr .esi - BitVec.ofNat 32 stepUnit).toNat < stepUnit)) ∧
      num u.mem B (kw len) y = num s.mem B (kw len) y / 2 := by
  rw [mulTailHi, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_movS rfl fun t5 U _ => WP.block_nil ?_
  obtain h5 : RtWs (lay full) t5 B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact fun _ _ => rfl)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h5 (j := y) hy (by rw [U.gpr]; decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine wp_subS rfl fun t7 T7 _ => wp_cmpi fun u T cf _ => WP.block_nil ?_
  obtain countEq : t6.gpr .esi = s.gpr .esi := (r6.1 _ (by decide)).trans (U.other _ (by decide))
  obtain rest : Keeps [.esi] t6 u := T7.keeps.trans (T.keeps _)
  obtain mem : u.mem = t6.mem := T.mem.trans T7.mem
  rw [U.gpr, U.mem] at e6
  rw [U.mem] at k6
  refine ⟨h6.keep rest (by decide) (by decide) (by rw [mem]; exact fun _ _ => rfl), by rw [mem]; exact k6,
    (U.keeps.mono (by simp)).trans ((r6.mono (by simp)).trans (rest.mono (by simp))),
    by rw [T.gpr, T7.gpr, countEq], by rw [cf, T7.gpr, countEq]; rfl, ?_⟩
  rw [mem, e6, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- One step. -/
theorem mulModStepHi_ok {full : Bool} {s : State} (h : RtWs (lay full) s B Z len N) {z y x a m t : Nat}
    (hi : MulIdx N z y x a m t) :
    WP isa (mulModStepHi full z y x a m t) s fun u => RtWs (lay full) u B Z len N ∧
      Keep B (kw len) (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s u ∧
      u.gpr .esi = s.gpr .esi - BitVec.ofNat 32 stepUnit ∧
      u.cf = some (decide ((s.gpr .esi - BitVec.ofNat 32 stepUnit).toNat < stepUnit)) ∧
      num u.mem B (kw len) y = num s.mem B (kw len) y / 2 ∧
      (num s.mem B (kw len) z = 0 → num s.mem B (kw len) a < num s.mem B (kw len) m →
        num s.mem B (kw len) x < num s.mem B (kw len) m → 2 * num s.mem B (kw len) m ≤ 2 ^ (32 * kw len) →
        num u.mem B (kw len) a =
          (num s.mem B (kw len) a + num s.mem B (kw len) y % 2 * num s.mem B (kw len) x) % num s.mem B (kw len) m ∧
        num u.mem B (kw len) x = (num s.mem B (kw len) x + num s.mem B (kw len) x) % num s.mem B (kw len) m) := by
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi
  -- The indices' facts, while the context is small.
  obtain zN : z < N := by omega_arith
  obtain yN : y < N := by omega_arith
  obtain xN : x < N := by omega_arith
  obtain aN : a < N := by omega_arith
  obtain mN : m < N := by omega_arith
  obtain tN : t < N := by omega_arith
  obtain t1N : t + 1 + 2 < N := by omega_arith
  obtain at0 : a ≠ t := by omega_arith
  obtain at1 : a ≠ t + 1 := by omega_arith
  obtain at2 : a ≠ t + 1 + 1 := by omega_arith
  obtain at3 : a ≠ t + 1 + 2 := by omega_arith
  obtain xt1 : x ≠ t + 1 := by omega_arith
  obtain xt2 : x ≠ t + 1 + 1 := by omega_arith
  obtain xt3 : x ≠ t + 1 + 2 := by omega_arith
  obtain mt1 : m ≠ t + 1 := by omega_arith
  obtain mt2 : m ≠ t + 1 + 1 := by omega_arith
  obtain mt3 : m ≠ t + 1 + 2 := by omega_arith
  obtain yt0 : y ≠ t := by omega_arith
  obtain yt1 : y ≠ t + 1 := by omega_arith
  obtain yt2 : y ≠ t + 1 + 1 := by omega_arith
  obtain yt3 : y ≠ t + 1 + 2 := by omega_arith
  obtain zt1 : z ≠ t + 1 := by omega_arith
  obtain zt2 : z ≠ t + 1 + 1 := by omega_arith
  obtain zt3 : z ≠ t + 1 + 2 := by omega_arith
  obtain mt0 : m ≠ t := by omega_arith
  obtain xt0 : x ≠ t := by omega_arith
  obtain zt0 : z ≠ t := by omega_arith
  obtain fz := h.ws.fit64 zN
  obtain fy := h.ws.fit64 yN
  obtain fx := h.ws.fit64 xN
  obtain fa := h.ws.fit64 aN
  obtain fm := h.ws.fit64 mN
  rw [mulModStepHi, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulHead_ok h tN zN yN xN zt0.symm) fun t2 ⟨h2, k2, r2, e2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h2 (o := a) (a := a) (b := t) (m := m) (z := z) (t := t + 1) aN aN tN mN zN t1N
    at1 mt1 mt2 at3) fun t3 ⟨h3, k3, r3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addMod_ok h3 (o := x) (a := x) (b := x) (m := m) (z := z) (t := t + 1) xN xN xN mN zN t1N
    xt1 mt1 mt2 xt3) fun t4 ⟨h4, k4, r4, e4⟩ => ?_
  refine WP.mono (mulTailHi_ok h4 yN) fun u ⟨hu, k6, esi, c6, z6, e6⟩ => ?_
  obtain esieq : t4.gpr .esi = s.gpr .esi := by
    rw [r4.1 _ (by decide), r3.1 _ (by decide), r2.1 _ (by decide)]
  refine ⟨hu, ((k2.mono.trans k3.mono).trans k4.mono).trans k6.mono,
    (r2.mono (by simp)).trans ((r3.mono (by simp)).trans ((r4.mono (by simp)).trans esi)),
    by rw [c6, esieq], by rw [z6, esieq], ?_, fun hZ hA hX hM => ?_⟩
  · rw [e6, k4.num (nm4 yt1 yt2 yt3 hyx) (by decide) fy, k3.num (nm4 yt1 yt2 yt3 hya) (by decide) fy,
      k2.num (nm1 yt0) (by decide) fy]
  · -- The values each step reads.
    obtain z2 : num t2.mem B (kw len) z = 0 := by rw [k2.num (nm1 zt0) (by decide) fz, hZ]
    obtain mm2 : num t2.mem B (kw len) m = num s.mem B (kw len) m := k2.num (nm1 mt0) (by decide) fm
    obtain a2 : num t2.mem B (kw len) a = num s.mem B (kw len) a := k2.num (nm1 at0) (by decide) fa
    obtain x2 : num t2.mem B (kw len) x = num s.mem B (kw len) x := k2.num (nm1 xt0) (by decide) fx
    obtain d2 : num t2.mem B (kw len) t = num s.mem B (kw len) y % 2 * num s.mem B (kw len) x := by
      rw [e2, hZ]
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B (kw len) y) with e | e <;> simp [e]
    obtain dlt : num t2.mem B (kw len) t < num s.mem B (kw len) m := by
      rw [d2]; rcases Nat.mod_two_eq_zero_or_one (num s.mem B (kw len) y) with e | e <;> simp [e] <;> omega_arith
    obtain A3 := e3 z2 (by rw [a2, mm2]; exact hA) (by rw [mm2]; exact dlt) (by rw [mm2]; exact hM)
    rw [a2, mm2, d2] at A3
    obtain z3 : num t3.mem B (kw len) z = 0 := by rw [k3.num (nm4 zt1 zt2 zt3 hza) (by decide) fz, z2]
    obtain mm3 : num t3.mem B (kw len) m = num s.mem B (kw len) m := by
      rw [k3.num (nm4 mt1 mt2 mt3 ham.symm) (by decide) fm, mm2]
    obtain x3 : num t3.mem B (kw len) x = num s.mem B (kw len) x := by
      rw [k3.num (nm4 xt1 xt2 xt3 hxa) (by decide) fx, x2]
    obtain X4 := e4 z3 (by rw [x3, mm3]; exact hX) (by rw [x3, mm3]; exact hX) (by rw [mm3]; exact hM)
    rw [x3, mm3] at X4
    refine ⟨?_, ?_⟩
    · rw [k6.num (nm1 hya.symm) (by decide) fa, k4.num (nm4 at1 at2 at3 hxa.symm) (by decide) fa, A3]
    · rw [k6.num (nm1 hyx.symm) (by decide) fx, X4]

/-- The state after `i` of the `k` steps, with `o` in `esi`'s low half. -/
structure MulHiI (full : Bool) (s0 : State) (B : Addr) (Z len N z y x a m t k o i : Nat) (u : State) : Prop where
  ws : RtWs (lay full) u B Z len N
  keep : Keep B (kw len) (mulArrs y x a t) [sB, sC] s0.mem u.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 u
  count : u.gpr .esi = BitVec.ofNat 32 ((k - i) * stepUnit + o)
  yv : num u.mem B (kw len) y = num s0.mem B (kw len) y / 2 ^ i
  value : num s0.mem B (kw len) z = 0 → num s0.mem B (kw len) a < num s0.mem B (kw len) m →
    num s0.mem B (kw len) x < num s0.mem B (kw len) m → 2 * num s0.mem B (kw len) m ≤ 2 ^ (32 * kw len) →
    num u.mem B (kw len) a =
      (num s0.mem B (kw len) a + num s0.mem B (kw len) y % 2 ^ i * num s0.mem B (kw len) x) % num s0.mem B (kw len) m ∧
    num u.mem B (kw len) x = 2 ^ i * num s0.mem B (kw len) x % num s0.mem B (kw len) m

theorem mulModHiBody_ok {full : Bool} {s0 u : State} {z y x a m t k o i : Nat}
    (hi : MulIdx N z y x a m t) (hk : k * stepUnit + o < 2 ^ 32) (ho : o < stepUnit)
    (inv : MulHiI full s0 B Z len N z y x a m t k o i u) (hik : i < k) :
    WP isa (mulModStepHi full z y x a m t) u fun u' =>
      MulHiI full s0 B Z len N z y x a m t k o (i + 1) u' ∧ u'.cf = some (decide (i + 1 = k)) := by
  have h := inv.ws
  have hi' := hi
  obtain ⟨ht, hz, hy, hx, ha, hm, hzy, hzx, hza, hzm, hyx, hya, hym, hxa, hxm, ham⟩ := hi'
  obtain fz := h.ws.fit64 (j := z) (by omega_arith)
  obtain fm := h.ws.fit64 (j := m) (by omega_arith)
  obtain zk : num u.mem B (kw len) z = num s0.mem B (kw len) z := inv.keep.num (by simp; omega_arith) (by decide) fz
  obtain mk : num u.mem B (kw len) m = num s0.mem B (kw len) m := inv.keep.num (by simp; omega_arith) (by decide) fm
  refine WP.mono (mulModStepHi_ok h hi) fun u' ⟨h', k', r', c', f', y', v'⟩ => ?_
  obtain le : (k - (i + 1)) * stepUnit + o + stepUnit = (k - i) * stepUnit + o := by
    have : k - i = k - (i + 1) + 1 := by omega_using [hik]
    rw [this, Nat.succ_mul]; omega_using []
  obtain bound : (k - i) * stepUnit + o < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _) hk
  obtain cnt : u.gpr .esi - BitVec.ofNat 32 stepUnit = BitVec.ofNat 32 ((k - (i + 1)) * stepUnit + o) := by
    rw [inv.count, ← le, BitVec.ofNat_sub_ofNat_of_le _ _ (by unfold stepUnit; omega_using []) (by omega_using []),
      Nat.add_sub_cancel]
  refine ⟨⟨h', inv.keep.trans k', inv.rest.trans r', by rw [c', cnt], ?_, fun hZ hA hX hM => ?_⟩, ?_⟩
  · rw [y', inv.yv, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · obtain ⟨va, vx⟩ := inv.value hZ hA hX hM
    obtain M0 : 0 < num s0.mem B (kw len) m := by omega_arith
    obtain aLt : num u.mem B (kw len) a < num u.mem B (kw len) m := by rw [va, mk]; exact Nat.mod_lt _ M0
    obtain xLt : num u.mem B (kw len) x < num u.mem B (kw len) m := by rw [vx, mk]; exact Nat.mod_lt _ M0
    obtain ⟨va', vx'⟩ := v' (by rw [zk, hZ]) aLt xLt (by rw [mk]; exact hM)
    rw [va', vx', va, vx, inv.yv, mk]
    exact ⟨VG.Proof.Rsa.mulMod_arith, VG.Proof.Rsa.double_arith⟩
  · rw [f', cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [le, bound])]
    congr 1
    simp only [decide_eq_decide]
    constructor
    · intro hlt
      rcases Nat.eq_zero_or_pos (k - (i + 1)) with e | e
      · omega_using [hik, e]
      · have := Nat.mul_le_mul_right stepUnit e; omega_using [hlt, this]
    · intro e
      rw [show k - (i + 1) = 0 by omega_using [e], Nat.zero_mul, Nat.zero_add]
      exact ho

/-- `mulModHi z y x a m t` with `esi = 2^16 k + o`, `k > 0` and `o < 2^16`: `mulMod`'s product, and
`esi = o`. -/
theorem mulModHi_ok {full : Bool} {s : State} (h : RtWs (lay full) s B Z len N) {z y x a m t k o : Nat}
    (hi : MulIdx N z y x a m t) (hk : 0 < k) (hk' : k * stepUnit + o < 2 ^ 32) (ho : o < stepUnit)
    (c : s.gpr .esi = BitVec.ofNat 32 (k * stepUnit + o)) :
    WP isa (mulModHi full z y x a m t) s fun u => RtWs (lay full) u B Z len N ∧
      Keep B (kw len) (mulArrs y x a t) [sB, sC] s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s u ∧
      u.gpr .esi = BitVec.ofNat 32 o ∧
      (num s.mem B (kw len) z = 0 → num s.mem B (kw len) a < num s.mem B (kw len) m →
        num s.mem B (kw len) x < num s.mem B (kw len) m → 2 * num s.mem B (kw len) m ≤ 2 ^ (32 * kw len) →
        num u.mem B (kw len) a =
          (num s.mem B (kw len) a + num s.mem B (kw len) y % 2 ^ k * num s.mem B (kw len) x) %
            num s.mem B (kw len) m) := by
  obtain start : MulHiI full s B Z len N z y x a m t k o 0 s :=
    ⟨h, Keep.refl _ _ _ _ _, Keeps.refl _ _, by rw [c, Nat.sub_zero], by rw [Nat.pow_zero, Nat.div_one],
      fun _ hA hX _ => ⟨by rw [Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hA],
        by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hX]⟩⟩
  refine WP.loop (M := isa) (fun j u => ∃ i, i + j = k ∧ 0 < j ∧ MulHiI full s B Z len N z y x a m t k o i u) ?_ k s
    ⟨0, by omega_arith, hk, start⟩
  intro j u ⟨i, hij, hj, inv⟩
  refine WP.mono (mulModHiBody_ok hi hk' ho inv (by omega_arith)) fun u' ⟨iu, hc⟩ => ?_
  by_cases e : i + 1 = k
  · left
    refine ⟨by change u'.cf.map (!·) = some false; simp [hc, e], iu.ws, iu.keep, iu.rest, ?_, fun hZ hA hX hM => ?_⟩
    · rw [iu.count, e, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    · have v := (iu.value hZ hA hX hM).1
      rw [e] at v
      exact v
  · right
    exact ⟨by change u'.cf.map (!·) = some true; simp [hc, e], j - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, iu⟩

end MulHi

/-! ## The three product checks, in one loop -/

section Products
open VG.Impl.Rsa.X86.KeyCheckRt (stepUnit cnt33Hi qBitsHi operands choose productCheck products mulModHi)
open VG.Proof.Rsa.X86.KeyRt (RtWs MulIdx mulArrs)

theorem rot13 {a : Nat} (h : a < 2 ^ 13) :
    (BitVec.ofNat 32 a).rotateRight 13 = BitVec.ofNat 32 (8 * a * stepUnit) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, stepUnit]
  rw [Nat.mod_eq_of_lt (by omega_using [h] : a < 2 ^ 32), Nat.mod_eq_of_lt (by omega_using [h] : 8 * a * 65536 < 2 ^ 32)]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.div_eq_of_lt (by omega)]
  simp
  omega_using [h]

/-- What a check's step count leaves: `esi` up by `2^16 k`. -/
def Stepped (k : Nat) (u u' : State) : Prop :=
  Keeps [.eax, .esi] u u' ∧ u'.mem = u.mem ∧ u'.gpr .esi = u.gpr .esi + BitVec.ofNat 32 (k * stepUnit)

theorem cnt33Hi_ok (u : State) : WP isa (.block cnt33Hi) u (Stepped 33 u) :=
  wp_addS rfl fun _ T _ => WP.block_nil ⟨T.keeps.mono (by decide), T.mem, T.gpr⟩

theorem qBitsHi_ok {full : Bool} {u : State} {B : Addr} {Z a : Nat}
    (c : VG.Proof.Bignum.X86.CallArgument u B Z (qLenArg full) (BitVec.ofNat 32 a)) (ha : a < 2 ^ 13) :
    WP isa (.block (qBitsHi full)) u (Stepped (8 * a) u) := by
  unfold qBitsHi
  refine wp_movS c.readSrc fun t1 u1 _ => wp_ror ⟨by decide, by decide⟩ fun t2 u2 => wp_addS rfl fun t3 u3 _ =>
    WP.block_nil ⟨(u1.keeps.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans (u3.keeps.mono (by decide))),
      by rw [u3.mem, u2.mem, u1.mem], ?_⟩
  obtain e1 : t2.gpr .eax = BitVec.ofNat 32 (8 * a * stepUnit) := by rw [u2.gpr, u1.gpr, rot13 ha]
  obtain e2 : t2.gpr .esi = u.gpr .esi := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  rw [u3.gpr, e1, e2]

/-- `operands y x m cnt`: `[aY] := [y]`, `[aX] := [x]`, `[aVD] := [m]`, then `esi` up by `2^16 k`. -/
theorem Stg.operands_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x m k : Nat} {cnt : List Instr}
    (hy : y ∈ live) (hx : x ∈ live) (hm : m ∈ live)
    (hyY : y ≠ aY) (hxY : x ≠ aY) (hxX : x ≠ aX) (hmY : m ≠ aY) (hmX : m ≠ aX) (hmV : m ≠ aVD)
    (hcnt : ∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
      WP isa (.block cnt) u (Stepped k u)) :
    WP isa (operands g.full y x m cnt) s fun u =>
      Stg g s0 (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) (aVD :: aX :: aY :: live) c u ∧
      u.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (k * stepUnit) := by
  unfold operands
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.and (h.copy_ok (o := aY) (a := y) (by decide) hy hyY.symm)
    (VG.Proof.Rsa.X86.KeyRt.copy_ok h.ws (o := aY) (a := y) (by decide) (h.live_lt y hy) hyY.symm))
    fun t1 ⟨h1, _, _, _, r1, _⟩ => ?_
  obtain hx1 : x ∈ aY :: live := List.mem_cons_of_mem _ hx
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.and (h1.copy_ok (o := aX) (a := x) (by decide) hx1 hxX.symm)
    (VG.Proof.Rsa.X86.KeyRt.copy_ok h1.ws (o := aX) (a := x) (by decide) (h1.live_lt x hx1) hxX.symm))
    fun t2 ⟨h2, _, _, _, r2, _⟩ => ?_
  rw [upd_ne _ _ hxY] at h2
  obtain hm2 : m ∈ aX :: aY :: live := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.and (h2.copy_ok (o := aVD) (a := m) (by decide) hm2 hmV.symm)
    (VG.Proof.Rsa.X86.KeyRt.copy_ok h2.ws (o := aVD) (a := m) (by decide) (h2.live_lt m hm2) hmV.symm))
    fun t3 ⟨h3, _, _, _, r3, _⟩ => ?_
  rw [upd_ne _ _ hmX, upd_ne _ _ hmY] at h3
  refine WP.mono (hcnt t3 h3.ws h3.rest (VG.Proof.Rsa.X86.KeyRt.keep_outside h3.ws.ws h3.keep
    (fun j hj => List.mem_range.mp hj) (by decide))) fun u ⟨K, mem, e⟩ => ⟨h3.regs K mem (by decide), ?_⟩
  rw [e, r3.1 _ (by decide), r2.1 _ (by decide), r1.1 _ (by decide)]

/-- `mulModHi` from `Stg`, with `esi = 2^16 k + o`: `[aA] := ([aY] mod 2^k) [aX] mod [m]`. -/
theorem Stg.mulHi_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {m k o : Nat}
    (hm : m ∈ live) (hz : aZ ∈ live) (ha : aA ∈ live) (hA0 : A aZ = 0) (hAA : A aA = 0)
    (hmi : MulIdx nArr aZ aY aX aA m aT) (hfree : ∀ j ∈ live, j = aA ∨ j ∉ mulArrs aY aX aA aT)
    (hk : 0 < k) (hk' : k * stepUnit + o < 2 ^ 32) (ho : o < stepUnit)
    (e : s.gpr .esi = BitVec.ofNat 32 (k * stepUnit + o)) :
    WP isa (mulModHi g.full aZ aY aX aA m aT) s fun t => ∃ R,
      (num s.mem g.B g.w aX < A m → 2 * A m ≤ 2 ^ (32 * g.w) →
        R = num s.mem g.B g.w aY % 2 ^ k * num s.mem g.B g.w aX % A m) ∧
      Stg g s0 (upd A aA R) live c t ∧ t.gpr .esi = BitVec.ofNat 32 o := by
  refine WP.mono (mulModHi_ok h.ws hmi hk hk' ho e) fun t ⟨ht, k5, r5, e5, v5⟩ => ?_
  obtain gZ : num s.mem g.B g.w aZ = 0 := by rw [h.arrs.get hz, hA0]
  obtain gA : num s.mem g.B g.w aA = 0 := by rw [h.arrs.get ha, hAA]
  obtain gM : num s.mem g.B g.w m = A m := h.arrs.get hm
  refine ⟨num t.mem g.B g.w aA, fun hlt hM => ?_, ?_, e5⟩
  · rw [gZ, gA, gM] at v5
    rw [v5 rfl (by omega_using [hlt]) hlt hM, Nat.zero_add]
  · refine h.next ht k5 (by decide) (by decide) r5 allRegs_body ?_ h.live_lt
      (h.vd_keep k5 (by decide) (by decide)) (h.mask_keep k5 (by decide))
    intro j hj
    by_cases ej : j = aA
    · subst ej; rw [upd_self]
    · have n := (hfree j hj).resolve_left ej
      rw [upd_ne _ _ ej, k5.num (fun i hi ei => n (by subst ei; exact hi)) (by decide)
        (h.ws.ws.fit64 (h.live_lt j hj)), h.arrs.get hj]

theorem noEsi_ltA (full : Bool) :
    ∀ i ∈ instrs (seqs (ltA full aX aVD)), VG.X86.Taint.clobbers i .esi = false := by
  obtain h : (instrs (seqs (ltA full aX aVD))).all (fun i => !VG.X86.Taint.clobbers i .esi) = true := by
    rw [← Code.allInstrs_eq]; cases full <;> decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem noEsi_copy (full : Bool) :
    ∀ i ∈ instrs (VG.Impl.Rsa.X86.KeyRt.copy (lay full) aA aZ), VG.X86.Taint.clobbers i .esi = false := by
  obtain h : (instrs (VG.Impl.Rsa.X86.KeyRt.copy (lay full) aA aZ)).all (fun i => !VG.X86.Taint.clobbers i .esi) = true := by
    rw [← Code.allInstrs_eq]; cases full <;> decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem noEsi_eqA (full : Bool) :
    ∀ i ∈ instrs (seqs (eqA full aA aOne)), VG.X86.Taint.clobbers i .esi = false := by
  obtain h : (instrs (seqs (eqA full aA aOne))).all (fun i => !VG.X86.Taint.clobbers i .esi) = true := by
    rw [← Code.allInstrs_eq]; cases full <;> decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- What one check needs of the arrays it does not write. -/
structure Base (A : Nat → Nat) (live : List Nat) : Prop where
  zero : aZ ∈ live
  one : aOne ∈ live
  zeroV : A aZ = 0
  oneV : A aOne = 1
  free : ∀ j ∈ live, j ∉ [aY, aX, aA, aVD, aT, aT + 1, aT + 2, aT + 3, aW]

/-- A check's product: what it is when `[x] < [m]`. -/
def Prod (g : Geo) (A : Nat → Nat) (y x m k R : Nat) : Prop :=
  A x < A m → 2 * A m ≤ 2 ^ (32 * g.w) → R = A y % 2 ^ k * A x % A m

/-- A check after its operands: `[x] < [m]`, the product, `= 1`, and `esi` counted down. -/
theorem Stg.checkRest_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    {y x m k i : Nat}
    (h : Stg g s0 (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) (aVD :: aX :: aY :: live) c s)
    (b : Base A live) (hk : 0 < k) (hk' : k * stepUnit + i < 2 ^ 32) (hi : 1 ≤ i) (hi' : i < stepUnit)
    (e : s.gpr .esi = BitVec.ofNat 32 (k * stepUnit + i)) :
    WP isa (seqs (ltA g.full aX aVD ++ ([VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aA aZ,
      mulModHi g.full aZ aY aX aA aVD aT] : List (Prog isa)) ++ eqA g.full aA aOne ++
      ([.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]] : List (Prog isa)))) s fun t => ∃ R, Prod g A y x m k R ∧
      Stg g s0 A live ((c && decide (A x < A m)) && decide (R = 1)) t ∧
      t.gpr .esi = BitVec.ofNat 32 (i - 1) ∧ t.zf = some (decide (i - 1 = 0)) := by
  obtain nW : aW ∉ live := fun hw => b.free aW hw (by decide)
  obtain nV : aVD ∉ live := fun hw => b.free aVD hw (by decide)
  obtain nX : aX ∉ live := fun hw => b.free aX hw (by decide)
  obtain nY : aY ∉ live := fun hw => b.free aY hw (by decide)
  obtain nA : aA ∉ live := fun hw => b.free aA hw (by decide)
  obtain vX : upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) aX = A x := by
    rw [upd_ne _ _ (by decide), upd_self]
  obtain vV : upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) aVD = A m := upd_self _ _ _
  obtain keepA : ∀ j ∈ live, upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) j = A j := fun j hj => by
    rw [upd_ne _ _ (by rintro rfl; exact nV hj), upd_ne _ _ (by rintro rfl; exact nX hj),
      upd_ne _ _ (by rintro rfl; exact nY hj)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `[x] < [m]`.
  rw [wp_seqs_append (by simp [ltA]) (by simp)]
  refine WP.mono (WP.gpr (h.ltA_ok (a := aX) (b := aVD) (by simp) (by simp) (by simp [nW]; decide))
    (noEsi_ltA g.full)) fun t1 ⟨h1, e1⟩ => ?_
  rw [vX, vV] at h1
  -- `[aA] := 0`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.gpr (h1.copy_ok (o := aA) (a := aZ) (by decide) (by simp [b.zero]) (by decide))
    (noEsi_copy g.full)) fun t2 ⟨h2, e2⟩ => ?_
  obtain gY : num t2.mem g.B g.w aY = A y := by
    rw [h2.arrs.get (by simp), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
  obtain gX : num t2.mem g.B g.w aX = A x := by rw [h2.arrs.get (by simp), upd_ne _ _ (by decide), vX]
  obtain z0 : upd (upd (upd A aY (A y)) aX (A x)) aVD (A m) aZ = 0 := by
    rw [keepA _ b.zero, b.zeroV]
  rw [z0] at h2
  obtain h2' := h2.sub (live' := aA :: aVD :: live) fun j hj => by
    simp only [List.mem_cons] at hj ⊢
    rcases hj with hj | hj | hj <;> simp [hj]
  -- The product.
  rw [wp_seqs_cons (by simp [eqA])]
  refine WP.mono (h2'.mulHi_ok (m := aVD) (k := k) (o := i) (by simp) (by simp [b.zero]) (by simp)
    (by rw [upd_ne _ _ (by decide), z0]) (upd_self _ _ _) (by decide)
    (by
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · exact .inl rfl
      · exact .inr (by decide)
      · refine .inr fun hm => b.free j hj ?_
        simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    hk hk' hi' (by rw [e2, e1, e])) fun t3 ⟨R, hR, h3, e3⟩ => ?_
  rw [gY, gX, upd_ne _ _ (by decide), vV] at hR
  -- `= 1`.
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (WP.gpr (h3.eqA_ok (a := aA) (b := aOne) (by simp) (by simp [b.one]) (by simp [nW]; decide))
    (noEsi_eqA g.full)) fun t4 ⟨h4, e4⟩ => ?_
  obtain one4 : upd (upd (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) aA 0) aA R aOne = 1 := by
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), keepA _ b.one, b.oneV]
  rw [upd_self, one4] at h4
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok t4) fun t ⟨ct, zt, mt, kt⟩ => ?_
  obtain h5 := (h4.regs kt mt (by decide)).sub (live' := live) (fun j hj => by simp [hj])
  refine ⟨R, fun hlt hM => hR hlt hM, h5.congr' fun j hj => ?_, ?_, ?_⟩
  · rw [upd_ne _ _ (by rintro rfl; exact nA hj), upd_ne _ _ (by rintro rfl; exact nA hj), keepA j hj]
  · rw [ct, e4, e3]
    exact BitVec.ofNat_sub_ofNat_of_le (w := 32) i 1 (by decide) hi
  · rw [zt, e4, e3, show BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) from
      BitVec.ofNat_sub_ofNat_of_le (w := 32) i 1 (by decide) hi, ofNat_beq_zero (by unfold stepUnit at hi'; omega_using [hk'])]

/-- Check `i`'s multiplier, multiplicand, modulus and steps (3: `e dP`, 2: `e dQ`, 1: `q qInv`). -/
def opY (i : Nat) : Nat := if i = 1 then aQ else aE
def opX (i : Nat) : Nat := if i = 3 then aDP else if i = 2 then aDQ else aQI
def opM (i : Nat) : Nat := if i = 3 then aM1 else if i = 2 then aM2 else aP
def opK (qa i : Nat) : Nat := if i = 1 then 8 * qa else 33

/-- The arrays the checks read. -/
abbrev inputsLive : List Nat := [aE, aP, aQ, aDP, aDQ, aQI, aM1, aM2]

/-- `choose`: check `i`'s operands, and its steps in `esi`'s high half. -/
theorem Stg.choose_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (b : Base A live) (hlive : ∀ j ∈ inputsLive, j ∈ live) {qa i : Nat}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (e : s.gpr .esi = BitVec.ofNat 32 i)
    (qarg : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 qa)) (qa2 : qa < 2 ^ 13) :
    WP isa (choose g.full) s fun u =>
      Stg g s0 (upd (upd (upd A aY (A (opY i))) aX (A (opX i))) aVD (A (opM i))) (aVD :: aX :: aY :: live) c u ∧
      u.gpr .esi = BitVec.ofNat 32 (opK qa i * stepUnit + i) := by
  obtain nf : ∀ j ∈ inputsLive, j ∈ live ∧ j ≠ aY ∧ j ≠ aX ∧ j ≠ aVD := fun j hj =>
    ⟨hlive j hj, fun e => b.free j (hlive j hj) (by simp [e]), fun e => b.free j (hlive j hj) (by simp [e]),
      fun e => b.free j (hlive j hj) (by simp [e])⟩
  obtain ops : ∀ {u : State} {y x m k : Nat} {cnt : List Instr}, Stg g s0 A live c u →
      u.gpr .esi = BitVec.ofNat 32 i → y ∈ inputsLive → x ∈ inputsLive → m ∈ inputsLive →
      (∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
        WP isa (.block cnt) u (Stepped k u)) →
      WP isa (operands g.full y x m cnt) u fun u' =>
        Stg g s0 (upd (upd (upd A aY (A y)) aX (A x)) aVD (A m)) (aVD :: aX :: aY :: live) c u' ∧
        u'.gpr .esi = BitVec.ofNat 32 (k * stepUnit + i) := by
    intro u y x m k cnt hu eu hy hx hm hcnt
    obtain ⟨ly, yY, -, -⟩ := nf y hy
    obtain ⟨lx, xY, xX, -⟩ := nf x hx
    obtain ⟨lm, mY, mX, mV⟩ := nf m hm
    refine WP.mono (hu.operands_ok ly lx lm yY xY xX mY mX mV hcnt) fun u' ⟨h', e'⟩ => ⟨h', ?_⟩
    rw [e', eu, BitVec.ofNat_add_ofNat, Nat.add_comm]
  obtain c33 : ∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
      WP isa (.block cnt33Hi) u (Stepped 33 u) := fun u _ _ _ => cnt33Hi_ok u
  obtain cq : ∀ u : State, RtWs g.L u g.B g.Z g.len nArr → Keeps bodyRegs s0 u → Outside g.B 0 g.Z s0.mem u.mem →
      WP isa (.block (qBitsHi g.full)) u (Stepped (8 * qa) u) := fun _ _ K O => qBitsHi_ok (qarg.keep K (by decide) O) qa2
  unfold choose
  refine WP.seq (wp_cmpi fun u U _ z => WP.block_nil ?_)
  obtain hu := h.regs (U.keeps []) U.mem (by decide)
  obtain eu : u.gpr .esi = BitVec.ofNat 32 i := by rw [U.gpr]; exact e
  rw [e] at z
  rcases hi with rfl | rfl | rfl
  · refine WP.ite false (by change u.zf = _; rw [z]; decide) (fun f => absurd f (by decide)) fun _ => ?_
    refine WP.seq (wp_cmpi fun u₂ U₂ _ z₂ => WP.block_nil ?_)
    obtain hu₂ := hu.regs (U₂.keeps []) U₂.mem (by decide)
    obtain eu₂ : u₂.gpr .esi = BitVec.ofNat 32 1 := by rw [U₂.gpr]; exact eu
    rw [eu] at z₂
    refine WP.ite false (by change u₂.zf = _; rw [z₂]; decide) (fun f => absurd f (by decide)) fun _ => ?_
    exact ops hu₂ eu₂ (by decide) (by decide) (by decide) cq
  · refine WP.ite false (by change u.zf = _; rw [z]; decide) (fun f => absurd f (by decide)) fun _ => ?_
    refine WP.seq (wp_cmpi fun u₂ U₂ _ z₂ => WP.block_nil ?_)
    obtain hu₂ := hu.regs (U₂.keeps []) U₂.mem (by decide)
    obtain eu₂ : u₂.gpr .esi = BitVec.ofNat 32 2 := by rw [U₂.gpr]; exact eu
    rw [eu] at z₂
    refine WP.ite true (by change u₂.zf = _; rw [z₂]; decide) (fun _ => ?_) fun f => absurd f (by decide)
    exact ops hu₂ eu₂ (by decide) (by decide) (by decide) c33
  · refine WP.ite true (by change u.zf = _; rw [z]; decide) (fun _ => ?_) fun f => absurd f (by decide)
    exact ops hu eu (by decide) (by decide) (by decide) c33

/-- One check, from `esi = i`. -/
theorem Stg.product_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (b : Base A live) (hlive : ∀ j ∈ inputsLive, j ∈ live) {qa i : Nat}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (e : s.gpr .esi = BitVec.ofNat 32 i)
    (qarg : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 qa))
    (qa1 : 1 ≤ qa) (qa2 : qa < 2 ^ 13) :
    WP isa (productCheck g.full) s fun t => ∃ R, Prod g A (opY i) (opX i) (opM i) (opK qa i) R ∧
      Stg g s0 A live ((c && decide (A (opX i) < A (opM i))) && decide (R = 1)) t ∧
      t.gpr .esi = BitVec.ofNat 32 (i - 1) ∧ t.zf = some (decide (i - 1 = 0)) := by
  obtain hk : 0 < opK qa i := by unfold opK; split <;> omega_arith
  obtain hk' : opK qa i * stepUnit + i < 2 ^ 32 := by unfold opK stepUnit; split <;> omega_arith
  rw [show productCheck g.full = seqs (choose g.full :: (ltA g.full aX aVD ++
    ([VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aA aZ, mulModHi g.full aZ aY aX aA aVD aT] : List (Prog isa)) ++
    eqA g.full aA aOne ++ ([.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]] : List (Prog isa)))) from rfl, wp_seqs_cons (by simp [ltA])]
  refine WP.mono (h.choose_ok b hlive hi e qarg qa2) fun u ⟨hu, eu⟩ => ?_
  exact hu.checkRest_ok b hk hk' (by omega_using [hi]) (by unfold stepUnit; omega_using [hi]) eu

/-- The three checks: `dP`, `dQ`, then `qInv`. -/
theorem Stg.products_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (b : Base A live) (hlive : ∀ j ∈ inputsLive, j ∈ live) {qa : Nat}
    (qarg : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 qa))
    (qa1 : 1 ≤ qa) (qa2 : qa < 2 ^ 13) :
    WP isa (products g.full) s fun t => ∃ R₁ R₂ R₃, Prod g A aE aDP aM1 33 R₁ ∧ Prod g A aE aDQ aM2 33 R₂ ∧
      Prod g A aQ aQI aP (8 * qa) R₃ ∧
      Stg g s0 A live ((((((c && decide (A aDP < A aM1)) && decide (R₁ = 1)) && decide (A aDQ < A aM2)) &&
        decide (R₂ = 1)) && decide (A aQI < A aP)) && decide (R₃ = 1)) t := by
  unfold products
  refine WP.seq (wp_movi fun u U => WP.block_nil ?_)
  obtain hu := h.regs U.keeps U.mem (by decide)
  refine WP.loop (M := isa) (fun n u =>
      (n = 3 ∧ Stg g s0 A live c u ∧ u.gpr .esi = BitVec.ofNat 32 3) ∨
      (n = 2 ∧ ∃ R₁, Prod g A aE aDP aM1 33 R₁ ∧
        Stg g s0 A live ((c && decide (A aDP < A aM1)) && decide (R₁ = 1)) u ∧ u.gpr .esi = BitVec.ofNat 32 2) ∨
      (n = 1 ∧ ∃ R₁ R₂, Prod g A aE aDP aM1 33 R₁ ∧ Prod g A aE aDQ aM2 33 R₂ ∧
        Stg g s0 A live ((((c && decide (A aDP < A aM1)) && decide (R₁ = 1)) && decide (A aDQ < A aM2)) &&
          decide (R₂ = 1)) u ∧ u.gpr .esi = BitVec.ofNat 32 1)) ?_ 3 u (.inl ⟨rfl, hu, U.gpr⟩)
  rintro n v (⟨rfl, hv, ev⟩ | ⟨rfl, R₁, p₁, hv, ev⟩ | ⟨rfl, R₁, R₂, p₁, p₂, hv, ev⟩)
  · refine WP.mono (hv.product_ok b hlive (.inr (.inr rfl)) ev qarg qa1 qa2) fun t ⟨R, pR, ht, et, zt⟩ => ?_
    simp only [opY, opX, opM, opK] at pR ht
    exact .inr ⟨by change t.zf.map (!·) = _; rw [zt]; rfl, 2, by omega_using [], .inr (.inl ⟨rfl, R, pR, ht, et⟩)⟩
  · refine WP.mono (hv.product_ok b hlive (.inr (.inl rfl)) ev qarg qa1 qa2) fun t ⟨R, pR, ht, et, zt⟩ => ?_
    simp only [opY, opX, opM, opK] at pR ht
    exact .inr ⟨by change t.zf.map (!·) = _; rw [zt]; rfl, 1, by omega_using [], .inr (.inr ⟨rfl, R₁, R, p₁, pR, ht, et⟩)⟩
  · refine WP.mono (hv.product_ok b hlive (.inl rfl) ev qarg qa1 qa2) fun t ⟨R, pR, ht, _, zt⟩ => ?_
    simp only [opY, opX, opM, opK] at pR ht
    exact .inl ⟨by change t.zf.map (!·) = _; rw [zt]; rfl, R₁, R₂, R, p₁, p₂, pR, ht⟩

end Products

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcDiv`, which only this module used -/

section

/-! # Division stages for i686 key validation

The run-time width's division preserves the workspace base, tracked arrays,
and accumulated acceptance mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys

/-- The division from its set-up state. -/
theorem Stg.div_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVT]) :
    WP isa (division g.full) s fun t => ∃ Xq Xr,
      (0 < num s.mem g.B g.w aVD → Xr = num s.mem g.B g.w aVQ % num s.mem g.B g.w aVD ∧
        Xq = num s.mem g.B g.w aVQ / num s.mem g.B g.w aVD) ∧
      Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.div_ok h.ws (q := aVQ) (r := aVR) (d := aVD) (t := aVT) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.vdTop) fun t ⟨ht, k, r, v⟩ =>
      ⟨num t.mem g.B g.w aVQ, num t.mem g.B g.w aVR, fun pos => ⟨(v pos).2, (v pos).1⟩, ?_⟩
  have hw := h.ws.ws
  refine h.next ht k (by decide) (by decide) r (by decide) ?_ ?_
    (h.vd_keep k (by decide) (by decide)) (h.mask_keep k (by decide))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_self]
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_ne _ _ (by decide), upd_self]
    obtain hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.1, upd_ne _ _ hn.1, k.num (by simp; omega_using [hn]) (by decide) (hw.fit64 (h.live_lt j hj)),
      h.arrs.get hj]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    exact h.live_lt j hj

/-- `divSet a d`, then the division: `[a] / [d]` in `aVQ`, `[a] mod [d]` in `aVR`. -/
theorem Stg.divSet_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT]) :
    WP isa (seqs (divSet g.full a d)) s fun u => WP isa (division g.full) u fun t => ∃ Xq Xr, (0 < A d → Xr = A a % A d ∧ Xq = A a / A d) ∧
        Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  obtain aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  obtain aD : a ≠ aVD := fun e => hfree a ha (by simp [e])
  obtain dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  obtain dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  unfold divSet
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVQ) (a := a) (by decide) ha aQ.symm) fun t1 h1 => ?_
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) dD.symm)
    fun t2 h2 => ?_
  have h3 := h2
  obtain fq : num t2.mem g.B g.w aVQ = A a := by
    rw [h3.arrs.get (by simp), upd_ne (j := aVD) _ _ (by decide), upd_self]
  obtain fd : num t2.mem g.B g.w aVD = A d := by
    rw [h3.arrs.get (by simp), upd_self, upd_ne (j := aVQ) _ _ dQ]
  obtain h3' : Stg g s0 A live c t2 := (h3.sub (live' := live) fun j hj =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)).congr' fun j hj => by
    obtain hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.2.1, upd_ne _ _ hn.1]
  refine WP.mono (h3'.div_ok fun j hj => by
    obtain hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.2⟩) fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => ?_, ht⟩
  rw [fq, fd] at hv
  exact hv pos

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! # Key-check arithmetic agrees with the shared RSA validity predicates -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/KcBody.lean`, which only this module imported.
section

/-! # The checks of an RSA key on i686: `crtBody` and `keyBody`

`crtBody_ok`: from `BodyIn`, the mask is `crtBits` of what the code computes
(`CrtOut`); `keyBody_ok`: then and'ed with `d < n` and the remainders of `d`
modulo `p - 1` and `q - 1` equal to `dP` and `dQ` (`KeyOut`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys

/-- What the products are, where `p q = n` and their factors are below their moduli. -/
def ProdsOkP (g : Geo) (v : Vals) (R₁ R₂ R₃ : Nat) : Prop :=
  v.e < 2 ^ 33 → 2 * v.p ≤ 2 ^ (32 * g.w) → 2 * v.q ≤ 2 ^ (32 * g.w) → v.p * v.q = v.n →
    (v.dP < 2 * (v.p / 2) → R₁ = v.e * v.dP % (2 * (v.p / 2))) ∧
    (v.dQ < 2 * (v.q / 2) → R₂ = v.e * v.dQ % (2 * (v.q / 2))) ∧
    (v.qI < v.p → R₃ = v.q * v.qI % v.p)

/-- After `crtBody`. -/
def CrtOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ R₁ R₂ R₃,
  ProdsOkP g v R₁ R₂ R₃ ∧ ∃ A live, Stg g s0 A live (VG.Proof.Rsa.crtBitsP v.n v.p v.q v.dP v.dQ v.qI R₁ R₂ R₃) t

/-- The product checks bit by bit. -/
theorem Stg.productsP_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool}
    (h : Stg g s0 (aFin v) liveFin c s)
    (hq : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a)) :
    WP isa (products g.full) s fun t => ∃ R₁ R₂ R₃, ProdsOkP g v R₁ R₂ R₃ ∧
      Stg g s0 (aFin v) liveFin
        ((((((c && decide (v.dP < 2 * (v.p / 2))) && decide (R₁ = 1)) && decide (v.dQ < 2 * (v.q / 2))) &&
          decide (R₂ = 1)) && decide (v.qI < v.p)) && decide (R₃ = 1)) t := by
  obtain ⟨qa, qa1, qa2, qlt, qarg⟩ := hq
  refine WP.mono (h.products_ok ⟨by decide, by decide, rfl, rfl, by decide⟩ (by decide) qarg qa1 (by omega_using [qa2]))
    fun t ⟨R₁, R₂, R₃, p₁, p₂, p₃, ht⟩ => ⟨R₁, R₂, R₃, fun he hp hq' _ => ⟨fun hlt => ?_, fun hlt => ?_, fun hlt => ?_⟩, ht⟩
  · refine (p₁ hlt (by change 2 * (2 * (v.p / 2)) ≤ _; omega_using [hp])).trans ?_
    change v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2)) = _
    rw [Nat.mod_eq_of_lt he]
  · refine (p₂ hlt (by change 2 * (2 * (v.q / 2)) ≤ _; omega_using [hq'])).trans ?_
    change v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2)) = _
    rw [Nat.mod_eq_of_lt he]
  · refine (p₃ hlt hp).trans ?_
    change v.q % 2 ^ (8 * qa) * v.qI % v.p = _
    rw [Nat.mod_eq_of_lt qlt]

theorem seqs_one (p : Prog isa) : VG.Impl.Rsa.X86.Keys.seqs [p] = p := rfl

theorem crtBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa (crtBody g.full) s (CrtOut g s v) := by
  unfold crtBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (start_ok h) fun u hu => ?_
  rw [seqs_one]
  refine hu.crtChecks_ok h.pLen h.qLen (fun ap wo t ht => ?_) (fun t ht => ?_)
  · exact WP.mono (ht.wordProducts_ok wo) fun t' ⟨_, _, _, R₁, R₂, R₃, _, hR, ht'⟩ =>
      ⟨R₁, R₂, R₃, fun he _ _ hpq => hR he hpq, _, _, ht'⟩
  · exact WP.mono (ht.productsP_ok h.qLen) fun t' ⟨R₁, R₂, R₃, hR, ht'⟩ => ⟨R₁, R₂, R₃, hR, _, _, ht'⟩

/-! ## The checks of `d` -/

/-- The arrays the checks of `d` bit by bit use. -/
abbrev aDiv0 (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveD : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]


/-- After the division of `d` by `p - 1`. -/
def DivP (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Xq Y₁,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2)) ∧ Xq = v.d / (2 * (v.p / 2))) ∧
  Stg g s0 (upd (upd (aDiv0 v) aVQ Xq) aVR Y₁) (aVR :: aVQ :: liveD) (c && decide (v.d < v.n)) t

/-- After the division of `d` by `q - 1`. -/
def DivQ (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Y₁ Xq Y₂,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
  (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2)) ∧ Xq = v.d / (2 * (v.q / 2))) ∧
  Stg g s0 (upd (upd (aDiv0 v) aVQ Xq) aVR Y₂) (aVR :: aVQ :: liveD)
    (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t

theorem dChecks1_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aDiv0 v) liveD c s) :
    WP isa (dChecks1 g.full) s fun u => WP isa (division g.full) u (DivP g s0 v c) := by
  unfold dChecks1
  rw [wp_seqs_append (by simp [ltA]) (by simp [divSet])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  exact WP.mono (h1.divSet_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide))
    fun u wu => WP.mono wu fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => hv pos, ht⟩

theorem dChecks2_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivP g s0 v c s) :
    WP isa (dChecks2 g.full) s fun u => WP isa (division g.full) u (DivQ g s0 v c) := by
  obtain ⟨Xq, Y₁, hY, h⟩ := h
  unfold dChecks2
  rw [wp_seqs_append (by simp [eqA]) (by simp [divSet])]
  refine WP.mono (h.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  obtain h1' := (h1.sub (live' := liveD) (by decide)).congr (A' := aDiv0 v) rfl
  exact WP.mono (h1'.divSet_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide))
    fun u wu => WP.mono wu fun t ⟨Xq', Y₂, hv, ht⟩ =>
      ⟨Y₁, Xq', Y₂, fun pos => (hY pos).1, fun pos => hv pos, ht⟩

theorem dChecks3_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivQ g s0 v c s) :
    WP isa (dChecks3 g.full) s fun t => ∃ Y₁ Y₂, (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
      (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  obtain ⟨Y₁, Xq, Y₂, h1, h2, h⟩ := h
  exact WP.mono (h.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide) (by decide))
    fun t ht => ⟨Y₁, Y₂, h1, fun pos => (h2 pos).1, _, _, ht⟩

/-- The remainders of `d`, where `p q = n`. -/
def YsOk (v : Vals) (Y₁ Y₂ : Nat) : Prop :=
  v.p * v.q = v.n → 0 < 2 * (v.p / 2) → 0 < 2 * (v.q / 2) →
    Y₁ = v.d % (2 * (v.p / 2)) ∧ Y₂ = v.d % (2 * (v.q / 2))

/-- After `keyBody`. -/
def KeyOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ R₁ R₂ R₃ Y₁ Y₂,
  ProdsOkP g v R₁ R₂ R₃ ∧ YsOk v Y₁ Y₂ ∧
  ∃ A live, Stg g s0 A live (VG.Proof.Rsa.keyBitsP v.n v.d v.p v.q v.dP v.dQ v.qI R₁ R₂ R₃ Y₁ Y₂) t

/-- The checks of `d` bit by bit. -/
theorem dBits_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s) :
    WP isa (dBits g.full) s fun t => ∃ Y₁ Y₂, (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
      (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  obtain h0 : Stg g s0 (aDiv0 v) liveD c s := (h.sub (live' := liveD) (by decide)).congr rfl
  unfold dBits
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks1_ok h0) fun u1 w1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w1 fun t2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks2_ok h2) fun u2 w2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w2 fun t4 h4 => ?_
  rw [seqs_one]
  exact dChecks3_ok h4

theorem keyBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa (keyBody g.full) s (KeyOut g s v) := by
  unfold keyBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (start_ok h) fun u hu => ?_
  rw [seqs_one]
  refine hu.crtChecks_ok h.pLen h.qLen (fun ap wo t ht => ?_) (fun t ht => ?_)
  · rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (ht.wordProducts_ok wo) fun t1 ⟨M₁, M₂, M₃, R₁, R₂, R₃, eM, hR, h1⟩ => ?_
    rw [seqs_one]
    refine WP.mono (h1.dWords_ok wo.len wo.four (by have := wo.room; omega_using [this]) (by decide) (by decide))
      fun t2 ⟨Y₁, Y₂, eY₁, eY₂, A, live, h2⟩ =>
        ⟨R₁, R₂, R₃, Y₁, Y₂, fun he _ _ hpq => hR he hpq, fun hpq _ _ => ?_, A, live, h2⟩
    obtain ⟨m1, m2, -⟩ := eM hpq
    obtain ⟨-, tp1, tq1⟩ := wo.top hpq
    have a1 : aWord v M₁ M₂ M₃ aM1 = 2 * (v.p / 2) := m1
    have a2 : aWord v M₁ M₂ M₃ aM2 = 2 * (v.q / 2) := m2
    rw [a1] at eY₁; rw [a2] at eY₂
    exact ⟨eY₁ tp1, eY₂ tq1⟩
  · rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (ht.productsP_ok h.qLen) fun t1 ⟨R₁, R₂, R₃, hR, h1⟩ => ?_
    rw [seqs_one]
    exact WP.mono (dBits_ok h1) fun t2 ⟨Y₁, Y₂, eY₁, eY₂, A, live, h2⟩ =>
      ⟨R₁, R₂, R₃, Y₁, Y₂, hR, fun _ hp hq => ⟨eY₁ hp, eY₂ hq⟩, A, live, h2⟩

end VG.Proof.Rsa.X86.KeyCheck
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys

def validity (full : Bool) (k : Nat) (v : Vals) : Bool :=
  if full then Spec.Rsa.keyValid k v.n v.e v.d v.p v.q v.dP v.dQ v.qI
  else Spec.Rsa.crtKeyValid k v.n v.e v.p v.q v.dP v.dQ v.qI

structure Bounds (g : Geo) (k : Nat) (v : Vals) : Prop where
  pShort : v.p < 256 ^ (k - 1)
  qShort : v.q < 256 ^ (k - 1)
  pDouble : 2 * v.p ≤ 2 ^ (32 * g.w)
  qDouble : 2 * v.q ≤ 2 ^ (32 * g.w)

theorem checks_ok {g : Geo} {v : Vals} {s : State} {k : Nat} (h : BodyIn g v s)
    (b : Bounds g k v) (hm : Spec.Rsa.modulusValid v.n k = true)
    (he : Spec.Rsa.exponentValid v.e = true) :
    WP isa (if g.full then keyBody g.full else crtBody g.full) s fun t =>
      ∃ A live, Stg g s A live (validity g.full k v) t := by
  obtain eBound : v.e < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
    exact he.2
  obtain ⟨B, Z, len, full⟩ := g
  cases full
  · refine WP.mono (crtBody_ok h) fun t ⟨R₁, R₂, R₃, hR, A, live, ht⟩ => ?_
    obtain hR' := fun hpq => hR eBound b.pDouble b.qDouble hpq
    obtain eq := VG.Proof.Rsa.crtKeyValid_bitsP hm he b.pShort b.qShort
      (fun hpq => (hR' hpq).1) (fun hpq => (hR' hpq).2.1) (fun hpq => (hR' hpq).2.2)
    refine ⟨A, live, ?_⟩
    change Stg ⟨B, Z, len, false⟩ s A live (Spec.Rsa.crtKeyValid k v.n v.e v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
  · refine WP.mono (keyBody_ok h) fun t ⟨R₁, R₂, R₃, Y₁, Y₂, hR, hY, A, live, ht⟩ => ?_
    obtain hR' := fun hpq => hR eBound b.pDouble b.qDouble hpq
    obtain eq := VG.Proof.Rsa.keyValid_bitsP hm he b.pShort b.qShort
      (fun hpq => (hR' hpq).1) (fun hpq => (hR' hpq).2.1) (fun hpq => (hR' hpq).2.2) hY
    refine ⟨A, live, ?_⟩
    change Stg ⟨B, Z, len, true⟩ s A live (Spec.Rsa.keyValid k v.n v.e v.d v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
end VG.Proof.Rsa.X86.KeyCheck
