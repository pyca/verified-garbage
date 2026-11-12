module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Rsa.X86.KcChecks
public import VerifiedGarbage.Proof.Rsa.X86.KcWordChecks

public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Rsa.X86.KcDiv
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Spec.Rsa.Contract
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
  refine WP.mono (h.products_ok ⟨by decide, by decide, rfl, rfl, by decide⟩ (by decide) qarg qa1 (by omega))
    fun t ⟨R₁, R₂, R₃, p₁, p₂, p₃, ht⟩ => ⟨R₁, R₂, R₃, fun he hp hq' _ => ⟨fun hlt => ?_, fun hlt => ?_, fun hlt => ?_⟩, ht⟩
  · refine (p₁ hlt (by change 2 * (2 * (v.p / 2)) ≤ _; omega)).trans ?_
    change v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2)) = _
    rw [Nat.mod_eq_of_lt he]
  · refine (p₂ hlt (by change 2 * (2 * (v.q / 2)) ≤ _; omega)).trans ?_
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
  have h1' := (h1.sub (live' := liveD) (by decide)).congr (A' := aDiv0 v) rfl
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
  have h0 : Stg g s0 (aDiv0 v) liveD c s := (h.sub (live' := liveD) (by decide)).congr rfl
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
    refine WP.mono (h1.dWords_ok wo.len wo.four (by have := wo.room; omega) (by decide) (by decide))
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
  have eBound : v.e < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
    exact he.2
  obtain ⟨B, Z, len, full⟩ := g
  cases full
  · refine WP.mono (crtBody_ok h) fun t ⟨R₁, R₂, R₃, hR, A, live, ht⟩ => ?_
    have hR' := fun hpq => hR eBound b.pDouble b.qDouble hpq
    have eq := VG.Proof.Rsa.crtKeyValid_bitsP hm he b.pShort b.qShort
      (fun hpq => (hR' hpq).1) (fun hpq => (hR' hpq).2.1) (fun hpq => (hR' hpq).2.2)
    refine ⟨A, live, ?_⟩
    change Stg ⟨B, Z, len, false⟩ s A live (Spec.Rsa.crtKeyValid k v.n v.e v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
  · refine WP.mono (keyBody_ok h) fun t ⟨R₁, R₂, R₃, Y₁, Y₂, hR, hY, A, live, ht⟩ => ?_
    have hR' := fun hpq => hR eBound b.pDouble b.qDouble hpq
    have eq := VG.Proof.Rsa.keyValid_bitsP hm he b.pShort b.qShort
      (fun hpq => (hR' hpq).1) (fun hpq => (hR' hpq).2.1) (fun hpq => (hR' hpq).2.2) hY
    refine ⟨A, live, ?_⟩
    change Stg ⟨B, Z, len, true⟩ s A live (Spec.Rsa.keyValid k v.n v.e v.d v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
end VG.Proof.Rsa.X86.KeyCheck
