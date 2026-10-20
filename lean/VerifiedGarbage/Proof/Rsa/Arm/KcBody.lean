module

public import VerifiedGarbage.Proof.Rsa.Arm.KcChecks
import VerifiedGarbage.Proof.Rsa.Arm.KcOps
import VerifiedGarbage.Proof.Rsa.Arm.InvParts

/-! # The checks of an RSA key on ARMv7: `crtBody` and `keyBody`

`crtBody_ok`: from `BodyIn`, the mask is `crtBits` of what the code computes
(`CrtOut`); `keyBody_ok`: then and'ed with `d < n` and the remainders of `d`
modulo `p - 1` and `q - 1` equal to `dP` and `dQ` (`KeyOut`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What the products are, when their factors are below their moduli. -/
def ProdsOk (g : Geo) (v : Vals) (R₁ R₂ R₃ : Nat) : Prop :=
  (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
    R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
  (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
    R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
  (v.qI < v.p → 2 * v.p ≤ 2 ^ (32 * g.w) → R₃ = v.q % 2 ^ (32 * g.w) * v.qI % v.p)

/-- After the division of `n` by `p`. -/
def DivN (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧
  StgD g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t

/-- `ctxDiv` after it. -/
def DivN' (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧
  Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t

/-- After `crtBody`. -/
def CrtOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂ R₁ R₂ R₃,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  Stg g s0 (aFin v) liveFin (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t

theorem divN_ctx_ok {g : Geo} {s0 s : State} {v : Vals} (h : DivN g s0 v s) :
    WP isa (.block ctxDiv) s (DivN' g s0 v) := by
  obtain ⟨X₁, X₂, hX, h⟩ := h
  exact WP.mono h.ctx_ok fun t ht => ⟨X₁, X₂, hX, ht⟩

theorem crtChecks_ok' {g : Geo} {s0 s : State} {v : Vals} (h : DivN' g s0 v s) :
    WP isa crtChecks s (CrtOut g s0 v) := by
  obtain ⟨X₁, X₂, hX, h⟩ := h
  exact WP.mono (crtChecks_ok h) fun t ⟨R₁, R₂, R₃, h1, h2, h3, ht⟩ => ⟨X₁, X₂, R₁, R₂, R₃, hX, ⟨h1, h2, h3⟩, ht⟩

theorem start_ok' {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa start s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivN g s v) :=
  WP.mono (start_ok h) fun _ ⟨c, w⟩ => ⟨c, WP.mono w fun _ ⟨X₁, X₂, hX, ht⟩ => ⟨X₁, X₂, hX, ht⟩⟩

theorem crtBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa crtBody s (CrtOut g s v) := by
  unfold crtBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (start_ok' h) fun u ⟨_, hu⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  exact WP.mono (divN_ctx_ok h1) fun t2 h2 => crtChecks_ok' h2

/-! ## The checks of `d` -/

/-- The mask before the checks of `d`. -/
abbrev cMask (v : Vals) (X₁ X₂ R₁ R₂ R₃ : Nat) : Bool :=
  VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃

/-- After the division of `d` by `p - 1`. -/
def DivP (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Xq Y₁,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2)) ∧ Xq = v.d / (2 * (v.p / 2))) ∧
  StgD g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₁) (aVR :: aVQ :: liveFin) (c && decide (v.d < v.n)) t

def DivP' (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Xq Y₁,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2)) ∧ Xq = v.d / (2 * (v.p / 2))) ∧
  Stg g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₁) (aVR :: aVQ :: liveFin) (c && decide (v.d < v.n)) t

/-- After the division of `d` by `q - 1`. -/
def DivQ (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Y₁ Xq Y₂,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
  (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2)) ∧ Xq = v.d / (2 * (v.q / 2))) ∧
  StgD g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₂) (aVR :: aVQ :: liveFin)
    (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t

def DivQ' (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Y₁ Xq Y₂,
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
    WP isa dChecks1 s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivP g s0 v c) := by
  unfold dChecks1
  rw [wp_seqs_append (by simp [ltA]) (by simp [divSet])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  exact WP.mono (h1.divSet_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide))
    fun u ⟨cu, wu⟩ => ⟨cu, WP.mono wu fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => hv pos, ht⟩⟩

theorem divP_ctx_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivP g s0 v c s) :
    WP isa (.block ctxDiv) s (DivP' g s0 v c) := by
  obtain ⟨Xq, Y₁, hY, h⟩ := h
  exact WP.mono h.ctx_ok fun t ht => ⟨Xq, Y₁, hY, ht⟩

theorem dChecks2_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivP' g s0 v c s) :
    WP isa dChecks2 s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivQ g s0 v c) := by
  obtain ⟨Xq, Y₁, hY, h⟩ := h
  unfold dChecks2
  rw [wp_seqs_append (by simp [eqA]) (by simp [divSet])]
  refine WP.mono (h.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  have h1' := (h1.sub (live' := liveFin) (by decide)).congr (A' := aFin v) rfl
  exact WP.mono (h1'.divSet_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide))
    fun u ⟨cu, wu⟩ => ⟨cu, WP.mono wu fun t ⟨Xq', Y₂, hv, ht⟩ =>
      ⟨Y₁, Xq', Y₂, fun pos => (hY pos).1, fun pos => hv pos, ht⟩⟩

theorem divQ_ctx_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivQ g s0 v c s) :
    WP isa (.block ctxDiv) s (DivQ' g s0 v c) := by
  obtain ⟨Y₁, Xq, Y₂, h1, h2, h⟩ := h
  exact WP.mono h.ctx_ok fun t ht => ⟨Y₁, Xq, Y₂, h1, h2, ht⟩

theorem dChecks3_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivQ' g s0 v c s) :
    WP isa dChecks3 s fun t => ∃ Y₁ Y₂, (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
      (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  obtain ⟨Y₁, Xq, Y₂, h1, h2, h⟩ := h
  exact WP.mono (h.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide) (by decide))
    fun t ht => ⟨Y₁, Y₂, h1, fun pos => (h2 pos).1, _, _, ht⟩

theorem keyBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa keyBody s (KeyOut g s v) := by
  unfold keyBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (crtBody_ok h) fun t1 ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks1_ok h1) fun u1 ⟨_, w1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w1 fun t2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divP_ctx_ok h2) fun t3 h3 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks2_ok h3) fun u2 ⟨_, w2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w2 fun t4 h4 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divQ_ctx_ok h4) fun t5 h5 => ?_
  exact WP.mono (dChecks3_ok h5) fun t ⟨Y₁, Y₂, hY₁, hY₂, A, live, ht⟩ =>
    ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩

end VG.Proof.Rsa.Arm.KeyCheck
