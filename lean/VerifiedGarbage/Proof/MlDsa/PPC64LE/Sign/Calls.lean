module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Commit
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Commit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: calls of the primitives, as pieces

Once `sig` is in `r28` (`slay2`), each call of a polynomial primitive on
slots of `scratch` as a piece (`SPiece`), for any invariant `I` that implies
`SC2` and that the call keeps: its correctness from the call's contract, and
its constant time from the callee's (`callV_tr`), as the checks and the
signature use them.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW Regs2
  copyS zx and24_ok Callee)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt and24)
open VG.Impl.MlKem.PPC64LE (copy)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} {STK : Nat} (hS : S ≤ STK)
  {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)

/-- Slot `x` of `scratch`. -/
abbrev SL (p : Params) (STK : Nat) (σ : State) (x : Nat) : Addr := (slay2 p STK σ).A 0 (oP x)

theorem SL_pub {σ₁ σ₂ : State} (pub : sPub p σ₁ σ₂) (x : Nat) : SL p STK σ₁ x = SL p STK σ₂ x := by
  simp only [SL, slay2_pub pub]

include hP hS hI

theorem mulP_piece {x a b : Nat} (m : ∀ σ, KeyGen.MulOk (slay2 p STK σ) sWb2 (pS x) (pS a) (pS b))
    {F G : State → Poly} (hf : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ a) (F σ))
    (hg : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ b) (G σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS x) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK I (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ x) (multiplyNTT (F σ) (G σ)))
      (mulAt P (pS x) (pS a) (pS b)) := by
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.mul_tr hP.mul hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ a) ∧ Reduced x.mem (SL p STK σ b) ∧
      Reduced y.mem (SL p STK σ a) ∧ Reduced y.mem (SL p STK σ b)) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂), (hf _ _ h₁).1, (hg _ _ h₁).1,
      by rw [SL_pub pub]; exact (hf _ _ h₂).1, by rw [SL_pub pub]; exact (hg _ _ h₂).1⟩⟩
  unfold mulAt
  refine KeyGen.mul_ok hP.mul (hI _ _ h).site hS (m σ) (hf _ _ h).1 (hg _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS a)) = F σ := (hf _ _ h).2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS b)) = G σ := (hg _ _ h).2
  rw [e1, e2] at hq
  exact hq

omit hP in
theorem ipP_piece {name : String} {code : Prog isa} {t : Poly → Poly}
    (hc : Callee code (fun stk => inPlaceContract PPC64LE.abi t stk) S) {x : Nat}
    (m : ∀ σ, KeyGen.IpOk (slay2 p STK σ) sWb2 (pS x) (sc oPS)) {F : State → Poly}
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS x) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s' →
      I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ x) (F σ))
      (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ x) (t (F σ))) (callAt name code [(.r3, .ptr (pS x)), (.r4, .ptr (sc oPS))]) := by
  refine ⟨fun σ s _ ⟨h, hx⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.ip_tr (t := t) hc hS (m σ)
    (P := fun x' y => Two (slay2 p STK σ) sWb2 STK x' y ∧ Reduced x'.mem (SL p STK σ x) ∧ Reduced y.mem (SL p STK σ x))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, by
      rw [SL_pub pub]; exact h₂.2.1⟩⟩
  refine KeyGen.ip_ok (t := t) hc (hI _ _ h).site hS (m σ) hx.1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e : polyAt s.mem (lpa (slay2 p STK σ) (pS x)) = F σ := hx.2
  rw [e] at hq
  exact hq

theorem addP_piece {f g : Nat} (m : ∀ σ, KeyGen.AddOk (slay2 p STK σ) sWb2 (pS f) (pS g)) {F G : State → Poly}
    (hg : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ g) (G σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS f) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ))
      (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (add (F σ) (G σ))) (addAt P (pS f) (pS g)) := by
  refine ⟨fun σ s _ ⟨h, hf⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.add_tr hP.add hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ f) ∧ Reduced x.mem (SL p STK σ g) ∧
      Reduced y.mem (SL p STK σ f) ∧ Reduced y.mem (SL p STK σ g)) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, (hg _ _ h₁.1).1,
      by rw [SL_pub pub]; exact h₂.2.1, by rw [SL_pub pub]; exact (hg _ _ h₂.1).1⟩⟩
  unfold addAt
  refine KeyGen.add_ok hP.add (hI _ _ h).site hS (m σ) hf.1 (hg _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS f)) = F σ := hf.2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS g)) = G σ := (hg _ _ h).2
  rw [e1, e2] at hq
  exact hq

theorem subP_piece {f g : Nat} (m : ∀ σ, KeyGen.AddOk (slay2 p STK σ) sWb2 (pS f) (pS g)) {F G : State → Poly}
    (hg : ∀ σ s, I σ s → PolyIs s.mem (SL p STK σ g) (G σ))
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [tri (pS f) 1024, (1, 0, STK)]) s s' → I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ))
      (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (sub (F σ) (G σ))) (subAt P (pS f) (pS g)) := by
  refine ⟨fun σ s _ ⟨h, hf⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.sub_tr hP.sub hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ f) ∧ Reduced x.mem (SL p STK σ g) ∧
      Reduced y.mem (SL p STK σ f) ∧ Reduced y.mem (SL p STK σ g)) fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, (hg _ _ h₁.1).1,
      by rw [SL_pub pub]; exact h₂.2.1, by rw [SL_pub pub]; exact (hg _ _ h₂.1).1⟩⟩
  unfold subAt
  refine KeyGen.sub_ok hP.sub (hI _ _ h).site hS (m σ) hf.1 (hg _ _ h).1 fun s' k' hq => ⟨hk _ _ _ h k', ?_⟩
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (pS f)) = F σ := hf.2
  have e2 : polyAt s.mem (lpa (slay2 p STK σ) (pS g)) = G σ := (hg _ _ h).2
  rw [e1, e2] at hq
  exact hq

/-- The call of `vg_mldsa_norm_lt`, its result in `r3`. -/
theorem normP_piece {f B : Nat} (pf : ∀ σ, PtrIn (slay2 p STK σ) (pS f) 1024)
    (hfs : ∀ σ, sepAll (slay2 p STK σ).sizes (0, oP f, 1024) [(1, 0, STK)] = true) (hB : B < 2 ^ 31) {F : State → Poly}
    (hk : ∀ σ s s', I σ s → Kept ((slay2 p STK σ).RL [(1, 0, STK)]) s s' → I σ s') :
    SPiece p STK (fun σ s => I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ))
      (fun σ s => (I σ s ∧ PolyIs s.mem (SL p STK σ f) (F σ)) ∧
        (s.gpr .r3).setWidth 32 = (if normRq [F σ] < B then 1 else 0))
      (callAt "vg_mldsa_norm_lt" P.normLt (KeyGen.nlArgs (pS f) B)) := by
  refine ⟨fun σ s _ ⟨h, hf⟩ => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.nl_tr hP.normLt hS (pf σ) hB
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧ Reduced x.mem (SL p STK σ f) ∧ Reduced y.mem (SL p STK σ f))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁.1) (hI _ _ h₂.1), h₁.2.1, by
      rw [SL_pub pub]; exact h₂.2.1⟩⟩
  refine KeyGen.nl_ok hP.normLt (hI _ _ h).site hS (pf σ) hB hf.1 fun s' k' hq => ⟨⟨hk _ _ _ h k', ?_⟩, ?_⟩
  · exact polyIs_keepW (hI _ _ h).site.ok k'.frame (hfs σ) (by decide) rfl hf
  · have e : polyAt s.mem (lpa (slay2 p STK σ) (pS f)) = F σ := hf.2
    rw [e] at hq
    exact hq

end

/-! ## `r24 ← r24 ∧ r3` -/

/-- `1` if `a`, else `0`. -/
abbrev bit (a : Prop) [Decidable a] : BitVec 64 := if a then 1 else 0

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x : BitVec 64}
    (hx : x.setWidth 32 = if b then 1 else 0) : bit a &&& zx x = bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [bit, zx, hx, ha, hb, ite_true, ite_false, and_true,
    and_false] <;> decide

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : bit a = bit b := by
  by_cases ha : a
  · rw [show bit a = 1 from VG.Proof.MlDsa.KeyGen.ifp ha _ _, show bit b = 1 from VG.Proof.MlDsa.KeyGen.ifp (h.mp ha) _ _]
  · rw [show bit a = 0 from VG.Proof.MlDsa.KeyGen.ifn ha _ _,
      show bit b = 0 from VG.Proof.MlDsa.KeyGen.ifn (fun hb => ha (h.mpr hb)) _ _]

theorem forall_lt_succ {Q : Nat → Prop} {r : Nat} : ((∀ j < r, Q j) ∧ Q r) ↔ ∀ j < r + 1, Q j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega), h r (by omega)⟩⟩

section
variable {p : Params} {STK : Nat} {J J' : State → State → Prop} (hJ : ∀ σ s, J σ s → SC2 p STK σ s)
include hJ

/-- `and24`, from an invariant `J` that implies `SC2`. -/
theorem and24_piece
    (h : ∀ σ s s', J σ s → Regs2 s s' → s'.gpr .r24 = s.gpr .r24 &&& zx (s.gpr .r3) → J' σ s') :
    SPiece p STK J J' (.block and24) :=
  ⟨fun σ s _ hs => WP.mono (and24_ok s) fun s' ⟨_, e24, r⟩ => h σ s s' hs r e24,
    srel2 hJ and24_taint⟩

end

end VG.Proof.MlDsa.PPC64LE.Sign
