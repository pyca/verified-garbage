module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Rsa.X86.KcChecks

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

/-- What the products are, when their factors are below their moduli. -/
def ProdsOk (g : Geo) (v : Vals) (R₁ R₂ R₃ : Nat) : Prop :=
  (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
    R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
  (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
    R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
  (v.qI < v.p → 2 * v.p ≤ 2 ^ (32 * g.w) → R₃ = v.q * v.qI % v.p)

/-- After the division of `n` by `p`. -/
def DivN (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧
  Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t

/-- After `crtBody`. -/
def CrtOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂ R₁ R₂ R₃,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  Stg g s0 (aFin v) liveFin (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t

theorem crtChecks_ok' {g : Geo} {s0 s : State} {v : Vals} (h : DivN g s0 v s)
    (hq : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a)) :
    WP isa (crtChecks g.full) s (CrtOut g s0 v) := by
  obtain ⟨X₁, X₂, hX, h⟩ := h
  exact WP.mono (crtChecks_ok h hq) fun t ⟨R₁, R₂, R₃, h1, h2, h3, ht⟩ => ⟨X₁, X₂, R₁, R₂, R₃, hX, ⟨h1, h2, h3⟩, ht⟩

theorem start_ok' {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (start g.full) s fun u => WP isa (division g.full) u (DivN g s v) :=
  WP.mono (start_ok h) fun _ w => WP.mono w fun _ ⟨X₁, X₂, hX, ht⟩ => ⟨X₁, X₂, hX, ht⟩

theorem crtBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa (crtBody g.full) s (CrtOut g s v) := by
  unfold crtBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (start_ok' h) fun u hu => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t1 h1 => ?_
  rw [VG.Impl.Rsa.X86.Keys.seqs.eq_2]
  exact crtChecks_ok' h1 h.qLen

/-! ## The checks of `d` -/

/-- The mask before the checks of `d`. -/
abbrev cMask (v : Vals) (X₁ X₂ R₁ R₂ R₃ : Nat) : Bool :=
  VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃

/-- After the division of `d` by `p - 1`. -/
def DivP (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Xq Y₁,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2)) ∧ Xq = v.d / (2 * (v.p / 2))) ∧
  Stg g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₁) (aVR :: aVQ :: liveFin) (c && decide (v.d < v.n)) t

/-- After the division of `d` by `q - 1`. -/
def DivQ (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Y₁ Xq Y₂,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
  (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2)) ∧ Xq = v.d / (2 * (v.q / 2))) ∧
  Stg g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₂) (aVR :: aVQ :: liveFin)
    (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t

/-- After `keyBody`. -/
def KeyOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂ R₁ R₂ R₃ Y₁ Y₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
  ∃ A live, Stg g s0 A live
    (VG.Proof.Rsa.keyBits' v.n v.d v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃ Y₁ Y₂) t

theorem dChecks1_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s) :
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
  have h1' := (h1.sub (live' := liveFin) (by decide)).congr (A' := aFin v) rfl
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

theorem keyBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa (keyBody g.full) s (KeyOut g s v) := by
  unfold keyBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (crtBody_ok h) fun t1 ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks1_ok h1) fun u1 w1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w1 fun t2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks2_ok h2) fun u2 w2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w2 fun t4 h4 => ?_
  exact WP.mono (dChecks3_ok h4) fun t ⟨Y₁, Y₂, hY₁, hY₂, A, live, ht⟩ =>
    ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩

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

theorem ProdsOk.exact {g : Geo} {v : Vals} {k R₁ R₂ R₃ : Nat}
    (h : ProdsOk g v R₁ R₂ R₃) (b : Bounds g k v) (he : Spec.Rsa.exponentValid v.e = true) :
    (v.dP < 2 * (v.p / 2) → R₁ = v.e * v.dP % (2 * (v.p / 2))) ∧
    (v.dQ < 2 * (v.q / 2) → R₂ = v.e * v.dQ % (2 * (v.q / 2))) ∧
    (v.qI < v.p → R₃ = v.q * v.qI % v.p) := by
  have eBound : v.e < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
    exact he.2
  refine ⟨fun hp => ?_, fun hq => ?_, fun hq => ?_⟩
  · rw [h.1 hp (by have := b.pDouble; omega), Nat.mod_eq_of_lt eBound]
  · rw [h.2.1 hq (by have := b.qDouble; omega), Nat.mod_eq_of_lt eBound]
  · exact h.2.2 hq b.pDouble

theorem checks_ok {g : Geo} {v : Vals} {s : State} {k : Nat} (h : BodyIn g v s)
    (b : Bounds g k v) (hm : Spec.Rsa.modulusValid v.n k = true)
    (he : Spec.Rsa.exponentValid v.e = true) :
    WP isa (if g.full then keyBody g.full else crtBody g.full) s fun t =>
      ∃ A live, Stg g s A live (validity g.full k v) t := by
  obtain ⟨B, Z, len, full⟩ := g
  cases full
  · refine WP.mono (crtBody_ok h) fun t ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, ht⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := hR.exact b he
    have eq := VG.Proof.Rsa.crtKeyValid_bits hm he b.pShort b.qShort
      (fun pos => ⟨(hX pos).2, (hX pos).1⟩) h1 h2 h3
    refine ⟨aFin v, liveFin, ?_⟩
    change Stg ⟨B, Z, len, false⟩ s (aFin v) liveFin (Spec.Rsa.crtKeyValid k v.n v.e v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
  · refine WP.mono (keyBody_ok h) fun t ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := hR.exact b he
    have eq := VG.Proof.Rsa.keyValid_bits hm he b.pShort b.qShort
      (fun pos => ⟨(hX pos).2, (hX pos).1⟩) h1 h2 h3 hY₁ hY₂
    refine ⟨A, live, ?_⟩
    change Stg ⟨B, Z, len, true⟩ s A live (Spec.Rsa.keyValid k v.n v.e v.d v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
end VG.Proof.Rsa.X86.KeyCheck
