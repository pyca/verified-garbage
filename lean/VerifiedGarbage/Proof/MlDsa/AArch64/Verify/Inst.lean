import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.Decaps

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay`. -/
section

/-!
# ML-DSA verification on AArch64: parameters, buffers, and pieces

The facts about the parameter sets the proof uses (`VFacts`); the layout of
the buffers of verification (`pk`, `mu` and `sig` in `x25`, `x26` and `x27`,
read; `scratch` in `x28`, written: `vR p`, `vW p`), which the contract's
precondition gives from the prologue on (`vLay`), and the checks of pointers
into them, which `vlay` proves from the offsets by `omega`; what holds
throughout (`VC`: `Top`, and the inputs); and pieces of code, which take each
run from an invariant to the next and leak the same in two runs whose inputs
agree (`VPiece`), as in key generation.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params mlDsa44 mlDsa65 mlDsa87 q gamma2s ballParams simpleBitPackBounds bitlen)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  mem : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = p.ctildeLen + lenZ p * p.ℓ + p.ω + p.k
  ct : (p.ctildeLen, p.τ) ∈ ballParams ∧ 32 ≤ p.ctildeLen ∧ p.ctildeLen ≤ 64
  zl : lenZ p * p.ℓ ≤ 640 * 7 ∧ 576 ≤ lenZ p
  bp : BpOk (p.γ₁ - 1) p.γ₁ (lenZ p)
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s ∧ 0 < p.γ₁ - p.β ∧ p.γ₁ - p.β < 2 ^ 32
  hu : HuOk (p.ω + p.k) p.ω (256 * p.k)
  om : p.ω ≤ 80
  sbp : SbpOk (w1Max p) (w1Len p)
  w1 : p.k * w1Len p ≤ 1024
  g2 : p.γ₂ ∈ gamma2s ∧ w1Max p = (q - 1) / (2 * p.γ₂) - 1
  wl : w1Len p = 192 ∨ w1Len p = 128

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.AArch64.Verify.VFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by simp, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨by decide, by decide, by decide⟩, by decide, ⟨by decide, by decide, by decide, by decide⟩, by decide,
      ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

theorem VFacts.small {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) : scrLen p < 2 ^ 32 ∧ p.pkLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have := hF.zl; have := hF.ct; have := hF.om
  exact ⟨by rw [scr_eq]; omega, by rw [hF.pk]; omega, by rw [hF.sig]; omega⟩

/-! ## The contract -/

/-- The precondition of the shared contract. -/
abbrev vPre (p : Params) (S : Nat) (σ : State) : Prop := (Spec.MlDsa.verifyContract p AArch64.abi S).pre σ
/-- Its public data. -/
abbrev vPub (p : Params) (S : Nat) (σ₁ σ₂ : State) : Prop := (Spec.MlDsa.verifyContract p AArch64.abi S).pub σ₁ σ₂

/-- The inputs of a run from `σ`. -/
abbrev vPk (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) p.pkLen
abbrev vMu (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x1) 64
abbrev vSig (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x2) p.sigLen

theorem vPub_eq {p : Params} {S : Nat} {σ₁ σ₂ : State} (h : VG.Proof.MlDsa.AArch64.Verify.vPub p S σ₁ σ₂) :
    σ₁.sp = σ₂.sp ∧ VG.Proof.MlDsa.AArch64.Verify.vPk p σ₁ = VG.Proof.MlDsa.AArch64.Verify.vPk p σ₂ ∧ VG.Proof.MlDsa.AArch64.Verify.vMu σ₁ = VG.Proof.MlDsa.AArch64.Verify.vMu σ₂ ∧ VG.Proof.MlDsa.AArch64.Verify.vSig p σ₁ = VG.Proof.MlDsa.AArch64.Verify.vSig p σ₂ ∧
      σ₁.gpr .x0 = σ₂.gpr .x0 ∧ σ₁.gpr .x1 = σ₂.gpr .x1 ∧ σ₁.gpr .x2 = σ₂.gpr .x2 ∧ σ₁.gpr .x3 = σ₂.gpr .x3 := by
  unfold VG.Proof.MlDsa.AArch64.Verify.vPub at h
  sig_pub [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at h
  obtain ⟨hsp, hb, e0, e1, e2, e3⟩ := h
  have hb' := Proof.MlDsa.KeyGen.leakBytes_inj hb
  have l1 : (VG.Proof.MlDsa.AArch64.Verify.vPk p σ₁ ++ VG.Proof.MlDsa.AArch64.Verify.vMu σ₁).length = (VG.Proof.MlDsa.AArch64.Verify.vPk p σ₂ ++ VG.Proof.MlDsa.AArch64.Verify.vMu σ₂).length := by
    simp only [List.length_append, Proof.MlKem.bytesAt_length]
  obtain ⟨h12, h3⟩ := List.append_inj hb' l1
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp only [Proof.MlKem.bytesAt_length])
  exact ⟨hsp, h1, h2, h3, e0, e1, e2, e3⟩

/-! ## The layout -/

/-- `pk`, `mu` and `sig`. -/
abbrev vR (p : Params) : List (Reg × Nat) := [(.x25, p.pkLen), (.x26, 64), (.x27, p.sigLen)]
/-- `scratch`. -/
abbrev vW (p : Params) : List (Reg × Nat) := [(.x28, scrLen p)]

theorem vLay {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ) (h : Top σ s) :
    Lay S (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) s := by
  unfold VG.Proof.MlDsa.AArch64.Verify.vPre at hp
  sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at hp
  obtain ⟨hwf, hrd, hwr, d03, d13, d23, hres, n0, n1, n2, n3⟩ := hp
  obtain ⟨k0, k1, k2, k3⟩ := below_of_resv hres
  have hS : S ≤ σ.sp.toNat := le_of_wfP hwf
  have hsm := hF.small
  have e25 := h.x25; have e26 := h.x26; have e27 := h.x27; have e28 := h.x28
  have mrd : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr => by
    rw [h.rd, h.wr]; exact inR_self hr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [h.sp]; exact hS⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl)
    exacts [hsm.2.1, by decide, hsm.2.2, hsm.1]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    have w : ∀ r, VG.CallLay.isW (VG.Proof.MlDsa.AArch64.Verify.vW p) r = (r == .x28) := fun r => by cases r <;> rfl
    rintro b (rfl | rfl | rfl | rfl) b' (rfl | rfl | rfl | rfl) hne hw <;>
      simp only [w, e25, e26, e27, e28] at hne hw ⊢ <;> revert hne hw
    all_goals first
      | exact fun h => absurd rfl h
      | exact fun _ h => absurd h (by decide)
      | exact fun _ _ => d03 | exact fun _ _ => d13 | exact fun _ _ => d23 | exact fun _ _ => d03.symm
      | exact fun _ _ => d13.symm | exact fun _ _ => d23.symm
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28, h.sp]
    exacts [k0, k1, k2, k3]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    exacts [n0, n1, n2, n3]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    · exact mrd ⟨σ.gpr .x0, p.pkLen⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x1, 64⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x2, p.sigLen⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x3, scrLen p⟩ (by rw [hwr]; simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b rfl
    simp only [e28, h.wr]
    exact inR_self (r := ⟨σ.gpr .x3, scrLen p⟩) (by rw [hwr]; simp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp

theorem vOk (p : Params) : LayOk (VG.Proof.MlDsa.AArch64.Verify.vR p ++ VG.Proof.MlDsa.AArch64.Verify.vW p) := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp

/-! ## Checks of pointers, by `omega` -/

theorem vinB_x25 (p : Params) (o l : Nat) :
    VG.CallLay.inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: VG.Proof.MlDsa.AArch64.Verify.vW p) (.x25, o) l = decide (o + l ≤ p.pkLen) :=
  rfl
theorem vinB_x26 (p : Params) (o l : Nat) :
    VG.CallLay.inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: VG.Proof.MlDsa.AArch64.Verify.vW p) (.x26, o) l = decide (o + l ≤ 64) :=
  rfl
theorem vinB_x27 (p : Params) (o l : Nat) :
    VG.CallLay.inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: VG.Proof.MlDsa.AArch64.Verify.vW p) (.x27, o) l = decide (o + l ≤ p.sigLen) :=
  rfl
theorem vinB_x28 (p : Params) (o l : Nat) :
    VG.CallLay.inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: VG.Proof.MlDsa.AArch64.Verify.vW p) (.x28, o) l = decide (o + l ≤ scrLen p) :=
  rfl
theorem vinB_x28W (p : Params) (o l : Nat) : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Verify.vW p) (.x28, o) l = decide (o + l ≤ scrLen p) := rfl

theorem sepB_v {p : Params} {r r' : Reg} (h : r ≠ r') (hw : r = .x28 ∨ r' = .x28) (o l o' l' : Nat) :
    sepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (r, o) l (r', o') l' =
      (VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Verify.vR p ++ VG.Proof.MlDsa.AArch64.Verify.vW p) (r, o) l && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Verify.vR p ++ VG.Proof.MlDsa.AArch64.Verify.vW p) (r', o') l') := by
  refine sepB_ne h ?_ o l o' l'
  rcases hw with rfl | rfl <;> simp [VG.CallLay.isW, List.lookup]

/-- Unfolds the checks of pointers into the layout into arithmetic, then `omega`. -/
syntax "vlay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vlay) => `(tactic| vlay [])
  | `(tactic| vlay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlDsa.AArch64.keepB,
        VG.Proof.MlDsa.AArch64.sepB_same, VG.Proof.MlDsa.AArch64.Verify.sepB_v,
        VG.Proof.MlDsa.AArch64.Verify.vinB_x25, VG.Proof.MlDsa.AArch64.Verify.vinB_x26,
        VG.Proof.MlDsa.AArch64.Verify.vinB_x27, VG.Proof.MlDsa.AArch64.Verify.vinB_x28,
        VG.Proof.MlDsa.AArch64.Verify.vinB_x28W, List.all_cons, List.all_nil, List.cons_append, List.nil_append,
        List.all_append, Bool.and_self,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true,
        ↓reduceIte, Bool.false_eq_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.oSA,
        VG.Impl.MlDsa.AArch64.KeyGen.oSA4, VG.Impl.MlDsa.AArch64.KeyGen.oR4, VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.KeyGen.SV, VG.Impl.MlDsa.AArch64.Verify.oCT,
        VG.Impl.MlDsa.AArch64.Verify.oHint, or_true, true_or, and_true, true_and, $ls,*]
      and_intros <;> omega_arith))

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`: `Top`, and the inputs. -/
structure VC (p : Params) (σ s : State) : Prop where
  top : Top σ s
  pk : bytesAt s.mem (pa s (.x25, 0)) p.pkLen = VG.Proof.MlDsa.AArch64.Verify.vPk p σ
  mu : bytesAt s.mem (pa s (.x26, 0)) 64 = VG.Proof.MlDsa.AArch64.Verify.vMu σ
  sig : bytesAt s.mem (pa s (.x27, 0)) p.sigLen = VG.Proof.MlDsa.AArch64.Verify.vSig p σ

/-- A piece that writes `ws` keeps `VC`. -/
def vcChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws svP 48 && keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (.x25, 0) p.pkLen &&
    keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (.x26, 0) 64 && keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (.x27, 0) p.sigLen

section
variable {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ)
include hF hp

theorem VC.lay {s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VC p σ s) : Lay S (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) s := VG.Proof.MlDsa.AArch64.Verify.vLay hF hp h.top

theorem VC.step {s s' : State} (h : VG.Proof.MlDsa.AArch64.Verify.VC p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws)
    (hc : VG.Proof.MlDsa.AArch64.Verify.vcChk p ws = true) : VG.Proof.MlDsa.AArch64.Verify.VC p σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.Verify.vcChk, Bool.and_eq_true] at hc
  have L := h.lay hF hp
  exact ⟨h.top.step L hP hc.1.1.1, by rw [L.keepBytes hP hc.1.1.2]; exact h.pk,
    by rw [L.keepBytes hP hc.1.2]; exact h.mu, by rw [L.keepBytes hP hc.2]; exact h.sig⟩

end

/-! ## Two runs -/

/-- Two runs in the layout, with the same pointers and stack pointer. -/
structure VTwo (p : Params) (S : Nat) (x y : State) : Prop where
  lx : Lay S (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) x
  ly : Lay S (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) y
  same : SameB x y

theorem vc_two {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ₁ σ₂ x y : State} (p₁ : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₁) (p₂ : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₂)
    (pub : VG.Proof.MlDsa.AArch64.Verify.vPub p S σ₁ σ₂) (h₁ : VG.Proof.MlDsa.AArch64.Verify.VC p σ₁ x) (h₂ : VG.Proof.MlDsa.AArch64.Verify.VC p σ₂ y) : VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y := by
  obtain ⟨esp, _, _, _, e0, e1, e2, e3⟩ := VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub
  refine ⟨h₁.lay hF p₁, h₂.lay hF p₂, fun r hr => ?_, by rw [h₁.top.sp, h₂.top.sp, esp]⟩
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.top.x25, h₂.top.x25, e0]
  · rw [h₁.top.x26, h₂.top.x26, e1]
  · rw [h₁.top.x27, h₂.top.x27, e2]
  · rw [h₁.top.x28, h₂.top.x28, e3]

theorem VTwo.x28 {p : Params} {S : Nat} {x y : State} (h : VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ [Reg.x28], x.gpr r = y.gpr r := ⟨h.same.2, fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.same.1 .x28 (by decide)⟩

theorem VTwo.bases {p : Params} {S : Nat} {x y : State} (h : VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, x.gpr r = y.gpr r := ⟨h.same.2, h.same.1⟩

/-! ## Pieces -/

abbrev VR (p : Params) (S : Nat) (I : State → State → Prop) : State → State → Prop :=
  VG.Proof.MlDsa.AArch64.Rel2 (VG.Proof.MlDsa.AArch64.Verify.vPre p S) (VG.Proof.MlDsa.AArch64.Verify.vPub p S) I

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure VPiece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (VG.Proof.MlDsa.AArch64.Verify.VR p S I) c fun _ _ => True

section
variable {p : Params} {S : Nat} {I J K : State → State → Prop}

theorem VPiece.seq {c₁ c₂ : Prog isa} (h₁ : VG.Proof.MlDsa.AArch64.Verify.VPiece p S I J c₁) (h₂ : VG.Proof.MlDsa.AArch64.Verify.VPiece p S J K c₂) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem VPiece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : VG.Proof.MlDsa.AArch64.Verify.VPiece p S I J c)
    (hI : ∀ σ s, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ → I' σ s → I σ s) (hJ : ∀ σ s, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ → J σ s → J' σ s) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem VPiece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → VG.Proof.MlDsa.AArch64.Verify.VPiece p S (I k) (I (k + 1)) (f k)) →
      VG.Proof.MlDsa.AArch64.Verify.VPiece p S (I a) (I (a + n)) (VG.Impl.MlDsa.AArch64.Call.seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (Q := fun k => VG.Proof.MlDsa.AArch64.Verify.VR p S (I k)) n a fun k h₁ h₂ => relInv (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem vrel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₁ → VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₂ → VG.Proof.MlDsa.AArch64.Verify.vPub p S σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Verify.VR p S I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

/-- A branch, both ways: the condition agrees in both runs. -/
theorem relIte {P Q : State → State → Prop} {c : Cond} {th el : Prog isa}
    (hc : ∀ s₁ s₂, P s₁ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some true) th Q)
    (he : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some false) el Q) :
    RelCT isa P (.ite c th el) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hce := hc _ _ hp
  cases e₁ with
  | iteT c₁ b₁ =>
    cases e₂ with
    | iteT _ b₂ =>
      obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ ⟨hp, c₁⟩ b₁ b₂
      exact ⟨rfl, hq⟩
    | iteF c₂ _ => rw [c₁, c₂] at hce; cases hce
  | iteF c₁ b₁ =>
    cases e₂ with
    | iteT c₂ _ => rw [c₁, c₂] at hce; cases hce
    | iteF _ b₂ =>
      obtain ⟨rfl, hq⟩ := he _ _ _ _ _ _ ⟨hp, c₁⟩ b₁ b₂
      exact ⟨rfl, hq⟩

theorem eval24 (s : State) : isa.eval (.nonzero .x .x24) s = some (s.gpr .x24 != 0) := rfl

/-- `c` if `x24 ≠ 0`, where `x24` is whether `T σ` holds, which depends on public data only. -/
theorem VPiece.ifOk {c : Prog isa} {T : State → Prop} [DecidablePred T]
    (hx : ∀ σ s, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ₁ σ₂, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₁ → VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₂ → VG.Proof.MlDsa.AArch64.Verify.vPub p S σ₁ σ₂ → (T σ₁ ↔ T σ₂))
    (ht : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => I σ s ∧ T σ) J c) (he : ∀ σ s, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ → I σ s → ¬ T σ → J σ s) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S I J (VG.Impl.MlDsa.AArch64.KeyGen.ifOk c) := by
  have ev : ∀ σ s, VG.Proof.MlDsa.AArch64.Verify.vPre p S σ → I σ s → isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := fun σ s hp hs => by
    rw [VG.Proof.MlDsa.AArch64.Verify.eval24, hx σ s hp hs]; by_cases h : T σ <;> simp [h]
  refine ⟨fun σ s hp hs => WP.ite (decide (T σ)) (ev σ s hp hs) (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩)
    fun hb => WP.block_nil (he σ s hp hs (of_decide_eq_false hb)), VG.Proof.MlDsa.AArch64.Verify.relIte ?_ ?_ ?_⟩
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    rw [ev σ₁ x p₁ h₁, ev σ₂ y p₂ h₂, decide_eq_decide.mpr (hT σ₁ σ₂ p₁ p₂ pub)]
  · refine RelCT.mono ht.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hc⟩ => ?_) fun _ _ h => h
    rw [ev σ₁ x p₁ h₁] at hc
    have t₁ : T σ₁ := of_decide_eq_true (Option.some.inj hc)
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, t₁⟩, h₂, (hT σ₁ σ₂ p₁ p₂ pub).mp t₁⟩
  · exact RelCT.block_nil fun _ _ _ => trivial

end

end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Z`. -/
section

/-!
# ML-DSA verification on AArch64: the prologue, the hint and `z`

The prologue (`pro_vpiece`); the hint of the signature, with `x24` whether it
is well formed (`hint_vpiece`); then, if it is, `z[i]` (polynomial `k + i`
after `Â`) and `x24` whether each norm so far is small (`zOne_vpiece`). The
results in `x24` are functions of the signature, so they are the same in two
runs.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq polyAt coeffAt Reduced PolyIs HintIs normRq hintBitUnpack bitUnpack)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

/-! ## The inputs -/

/-- `h`, `z[i]`, and whether the norms of `z[0], …, z[j - 1]` are small, of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ)
abbrev zOf (p : Params) (σ : State) (i : Nat) : IPoly := Proof.MlDsa.Verify.vZ p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) i
abbrev normOk (p : Params) (σ : State) (j : Nat) : Prop := ∀ i < j, normRq [toRq (VG.Proof.MlDsa.AArch64.Verify.zOf p σ i)] < p.γ₁ - p.β

/-- The result in `x24`. -/
abbrev flag (P : Prop) [Decidable P] : BitVec 64 := if P then 1 else 0

theorem flag_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : VG.Proof.MlDsa.AArch64.Verify.flag P = VG.Proof.MlDsa.AArch64.Verify.flag Q := by
  by_cases hp : P
  · simp only [VG.Proof.MlDsa.AArch64.Verify.flag, hp, h.mp hp, ↓reduceIte]
  · simp only [VG.Proof.MlDsa.AArch64.Verify.flag, hp, mt h.mpr hp, ↓reduceIte]

/-- `and24` of a flag and a callee's result. -/
theorem and_flag {P Q : Prop} [Decidable P] [Decidable Q] (r : BitVec 64)
    (hr : r.setWidth 32 = if Q then 1 else 0) :
    ((VG.Proof.MlDsa.AArch64.Verify.flag P).setWidth 32 &&& r.setWidth 32).setWidth 64 = VG.Proof.MlDsa.AArch64.Verify.flag (P ∧ Q) := by
  rw [hr]
  by_cases hp : P <;> by_cases hq : Q <;> simp only [VG.Proof.MlDsa.AArch64.Verify.flag, hp, hq, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

theorem vpa0 (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

theorem VC.slice {p : Params} {σ s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VC p σ s) {o len : Nat} (hl : o + len ≤ p.sigLen) :
    bytesAt s.mem (pa s (.x27, o)) len = ((VG.Proof.MlDsa.AArch64.Verify.vSig p σ).drop o).take len := by
  rw [← h.sig, VG.Proof.MlDsa.AArch64.Verify.vpa0, Proof.MlKem.bytesAt_slice _ _ hl]

theorem VC.pkSlice {p : Params} {σ s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VC p σ s) {o len : Nat} (hl : o + len ≤ p.pkLen) :
    bytesAt s.mem (pa s (.x25, o)) len = ((VG.Proof.MlDsa.AArch64.Verify.vPk p σ).drop o).take len := by
  rw [← h.pk, VG.Proof.MlDsa.AArch64.Verify.vpa0, Proof.MlKem.bytesAt_slice _ _ hl]

theorem sc_ge {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) : 4096 + 1024 * (p.k * p.ℓ + p.k + p.ℓ + 6) ≤ scrLen p := by
  rw [scr_eq]; have := hF.k; have := hF.l; omega

/-- The block `and24`: only `x24`, and memory kept. -/
theorem and24_post {S : Nat} (s : State) :
    WP isa (.block and24) s fun s' => PPostB S s s' [] ∧ (∀ r, r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧ s'.mem = s.mem :=
  WP.mono (and24_ok s) fun _ ⟨o, e⟩ => ⟨postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _),
    fun r hr => o.get r (by simpa using hr), e, o.mem⟩

theorem and24_nomem : ∀ i ∈ and24, ∀ s, isa.addrs i s = [] := fun i hi _ => by
  simp only [and24, List.mem_singleton] at hi; subst hi; rfl

/-! ## The prologue -/

theorem pro_vpiece {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => s = σ) (fun σ s => VG.Proof.MlDsa.AArch64.Verify.VC p σ s ∧ s.gpr .x24 = 1) (.block VG.Impl.MlDsa.AArch64.KeyGen.pro) := by
  refine ⟨fun σ s hp hs => ?_, taintRel [.x0, .x1, .x2, .x3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · subst hs
    have hp' := hp
    unfold VG.Proof.MlDsa.AArch64.Verify.vPre at hp'
    sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at hp'
    obtain ⟨_, _, hwr, d03, d13, d23, _, _, _, _, _⟩ := hp'
    have hsc : 4096 + 1024 * (p.k * p.ℓ + p.k + p.ℓ + 6) ≤ Spec.MlDsa.scratchWords p * 8 := VG.Proof.MlDsa.AArch64.Verify.sc_ge hF
    have hsm := hF.small
    have hsv : SV + 48 ≤ Spec.MlDsa.scratchWords p * 8 := Nat.le_trans (by decide) (Nat.le_trans (Nat.le_add_right 4096 _) hsc)
    have hin : ∀ k < 6, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk =>
      ⟨⟨s.gpr .x3, Spec.MlDsa.scratchWords p * 8⟩, by rw [hwr]; simp,
        Offset.contains_base _ (by simp only [SV]; omega) (by simp only [SV]; omega)⟩
    refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.pro_ok hin) fun s' ⟨ht, h24, hf⟩ => ⟨⟨ht, ?_, ?_, ?_⟩, h24⟩
    · rw [VG.Proof.MlDsa.AArch64.Verify.vpa0, ht.x25]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d03.sub_right (Offset.sub_base _ hsv)) (Nat.le_of_lt (Nat.lt_trans hsm.2.1 (by decide)))
    · rw [VG.Proof.MlDsa.AArch64.Verify.vpa0, ht.x26]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d13.sub_right (Offset.sub_base _ hsv)) (by decide)
    · rw [VG.Proof.MlDsa.AArch64.Verify.vpa0, ht.x27]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d23.sub_right (Offset.sub_base _ hsv)) (Nat.le_of_lt (Nat.lt_trans hsm.2.2 (by decide)))
  · subst h₁ h₂
    obtain ⟨esp, _, _, _, e0, e1, e2, e3⟩ := VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub
    refine ⟨esp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The hint -/

/-- After the hint: `x24` whether it is well formed, and the hint. -/
def V1 (p : Params) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.VC p σ s ∧ s.gpr .x24 = VG.Proof.MlDsa.AArch64.Verify.flag ((VG.Proof.MlDsa.AArch64.Verify.hintOf p σ).isSome = true) ∧
    ∀ h, VG.Proof.MlDsa.AArch64.Verify.hintOf p σ = some h → HintIs s.mem (pa s (hP p 0)) p.k h

theorem hint_chk {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    rwChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (.x27, oHint p) (p.ω + p.k) (hP p 0) (256 * p.k * 4) = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.sig; have := hF.small
  unfold rwChk; vlay

theorem hint_eq (p : Params) (σ : State) :
    VG.Proof.MlDsa.AArch64.Verify.hintOf p σ = VG.Spec.MlDsa.hintBitUnpack p.ω p.k (((VG.Proof.MlDsa.AArch64.Verify.vSig p σ).drop (oHint p)).take (p.ω + p.k)) := rfl

theorem hint_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => VG.Proof.MlDsa.AArch64.Verify.VC p σ s ∧ s.gpr .x24 = 1) (VG.Proof.MlDsa.AArch64.Verify.V1 p) (hint P p) := by
  have hc := VG.Proof.MlDsa.AArch64.Verify.hint_chk hF
  refine ⟨fun σ s hp h => ?_, ?_⟩
  · have L := h.1.lay hF hp
    unfold hint
    refine WP.seq (WP.mono (huAt_ok hP.s64 hP.hintUnpack L hc hF.hu) fun s₁ ⟨hP₁, x₁, hq⟩ => ?_)
    have h₁ := h.1.step hF hp hP₁ (by
      have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.small
      unfold VG.Proof.MlDsa.AArch64.Verify.vcChk; vlay)
    refine WP.mono (VG.Proof.MlDsa.AArch64.Verify.and24_post (S := S) s₁) fun s₂ ⟨hP₂, g₂, x₂, hm⟩ => ?_
    have h₂ := h₁.step hF hp hP₂ (by
      have := hF.k; have := hF.l; have := scr_eq p; have := hF.small
      unfold VG.Proof.MlDsa.AArch64.Verify.vcChk; vlay)
    rw [h.1.slice (by rw [hF.sig, oHint]; omega), show p.ω + p.k - p.ω = p.k by omega, ← VG.Proof.MlDsa.AArch64.Verify.hint_eq] at hq
    refine ⟨h₂, ?_, fun hh e => ?_⟩
    · rw [x₂, x₁, h.2]
      revert hq; cases VG.Proof.MlDsa.AArch64.Verify.hintOf p σ with
      | some hh => intro ⟨hr, _⟩; rw [hr]; rfl
      | none => intro hr; rw [hr]; rfl
    · rw [e] at hq
      rw [hP₂.pa (show Reg.x28 ∈ keptRegs by decide), hm, hP₁.pa (show Reg.x28 ∈ keptRegs by decide)]
      exact hq.2
  · refine VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧ bytesAt x.mem (pa x (.x27, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (pa y (.x27, oHint p)) (p.ω + p.k)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
        ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1 h₂.1, by
          have hl : oHint p + (p.ω + p.k) ≤ p.sigLen := by rw [hF.sig, oHint]; omega
          rw [h₁.1.slice hl, h₂.1.slice hl, (VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub).2.2.2.1]⟩
    unfold hint
    exact RelCT.seq (huAt_tr hP.hintUnpack (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc hF.hu fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      (block_nomem_tr VG.Proof.MlDsa.AArch64.Verify.and24_nomem)

/-! ## `z` -/

/-- After `z[0], …, z[j - 1]`, with the hint well formed. -/
structure VZ (p : Params) (σ : State) (j : Nat) (s : State) : Prop where
  vc : VG.Proof.MlDsa.AArch64.Verify.VC p σ s
  hint : ∃ h, VG.Proof.MlDsa.AArch64.Verify.hintOf p σ = some h ∧ HintIs s.mem (pa s (hP p 0)) p.k h
  z : ∀ i < j, PolyIs s.mem (pa s (zP p i)) (toRq (VG.Proof.MlDsa.AArch64.Verify.zOf p σ i))

/-- A piece that writes `ws` keeps `VZ`. -/
structure VZChk (p : Params) (j : Nat) (ws : List (Ptr × Nat)) : Prop where
  vc : VG.Proof.MlDsa.AArch64.Verify.vcChk p ws = true
  hint : keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (hP p 0) (1024 * p.k) = true
  z : ∀ i < j, keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (zP p i) 1024 = true

theorem VZ.keep {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ) {j : Nat} {s s' : State}
    (h : VG.Proof.MlDsa.AArch64.Verify.VZ p σ j s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.Verify.VZChk p j ws) : VG.Proof.MlDsa.AArch64.Verify.VZ p σ j s' := by
  have L := h.vc.lay hF hp
  obtain ⟨hh, e, hH⟩ := h.hint
  exact ⟨h.vc.step hF hp hP hc.vc, ⟨hh, e, L.keepHint hP hc.hint hH⟩,
    fun i hi => L.keepPoly hP (hc.z i hi) (h.z i hi)⟩

theorem VFacts.scr {p : Params} (_ : VG.Proof.MlDsa.AArch64.Verify.VFacts p) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) :=
  scr_eq p

/-- Proves a `VZChk`. -/
syntax "vzchk " term:max : tactic
macro_rules
  | `(tactic| vzchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> vlay))

theorem zl_le {p : Params} {j : Nat} (hj : j < p.ℓ) : lenZ p * j + lenZ p ≤ lenZ p * p.ℓ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj

/-- `x24` whether the norms so far are small, and then `z[j]`, and whether its norm is. -/
abbrev Z0 (p : Params) (j : Nat) (σ s : State) : Prop := VG.Proof.MlDsa.AArch64.Verify.VZ p σ j s ∧ s.gpr .x24 = VG.Proof.MlDsa.AArch64.Verify.flag (VG.Proof.MlDsa.AArch64.Verify.normOk p σ j)
abbrev Z1 (p : Params) (j : Nat) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.Z0 p j σ s ∧ PolyIs s.mem (pa s (zP p j)) (toRq (VG.Proof.MlDsa.AArch64.Verify.zOf p σ j))
abbrev Z2 (p : Params) (j : Nat) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.Z1 p j σ s ∧ (s.gpr .x0).setWidth 32 = if normRq [toRq (VG.Proof.MlDsa.AArch64.Verify.zOf p σ j)] < p.γ₁ - p.β then 1 else 0

theorem zOf_eq (p : Params) (σ : State) (j : Nat) :
    VG.Proof.MlDsa.AArch64.Verify.zOf p σ j = VG.Spec.MlDsa.bitUnpack (((VG.Proof.MlDsa.AArch64.Verify.vSig p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p)) (p.γ₁ - 1) p.γ₁ := rfl

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {j : Nat} (hj : j < p.ℓ)
include hP hF hj

omit hP in
theorem bu_chk : rwChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (.x27, p.ctildeLen + lenZ p * j) (lenZ p) (zP p j) 1024 = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.sig; have := hF.small
  have := VG.Proof.MlDsa.AArch64.Verify.zl_le hj
  unfold rwChk; vlay

theorem bu_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.Z0 p j) (VG.Proof.MlDsa.AArch64.Verify.Z1 p j)
    (bitUnpackAt P (.x27, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (zP p j)) := by
  have hc := VG.Proof.MlDsa.AArch64.Verify.bu_chk hF hj
  refine ⟨fun σ s hp h => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := VG.Proof.MlDsa.AArch64.Verify.VTwo p S) (buAt_tr hP.bitUnpack (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc hF.bp
    fun x y h => ⟨h.lx, h.ly, h.same⟩) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1.vc h₂.1.vc⟩
  have L := h.1.vc.lay hF hp
  refine WP.mono (buAt_ok hP.s64 hP.bitUnpack L hc hF.bp) fun s' ⟨hP', x', hq⟩ => ?_
  have := VG.Proof.MlDsa.AArch64.Verify.zl_le hj
  refine ⟨⟨h.1.keep hF hp hP' (by vzchk hF), by rw [x', h.2]⟩, ?_⟩
  rw [h.1.vc.slice (by rw [hF.sig]; omega), ← VG.Proof.MlDsa.AArch64.Verify.zOf_eq] at hq
  rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
  exact hq

theorem norm_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.Z1 p j) (VG.Proof.MlDsa.AArch64.Verify.Z2 p j) (normLtAt P (zP p j) (p.γ₁ - p.β)) := by
  have hc : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Verify.vR p ++ VG.Proof.MlDsa.AArch64.Verify.vW p) (zP p j) 1024 = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlay
  refine ⟨fun σ s hp h => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧ Reduced x.mem (pa x (zP p j)) ∧
    Reduced y.mem (pa y (zP p j))) (normAt_tr hP.normLt (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2,
      h.1.same⟩) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1.1.vc h₂.1.1.vc, h₁.2.1, h₂.2.1⟩⟩
  have L := h.1.1.vc.lay hF hp
  refine WP.mono (normAt_ok hP.s64 hP.normLt L hc hF.g1.2.2 h.2.1) fun s' ⟨hP', x', hq⟩ => ?_
  have hz := L.keepPoly hP' (by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlay) h.2
  refine ⟨⟨⟨h.1.1.keep hF hp hP' (by vzchk hF), by rw [x', h.1.2]⟩, hz⟩, ?_⟩
  rw [hq, h.2.2]

omit hP in
theorem and_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.Z2 p j) (VG.Proof.MlDsa.AArch64.Verify.Z0 p (j + 1)) (.block and24) := by
  refine ⟨fun σ s hp h => ?_, block_nomem_tr VG.Proof.MlDsa.AArch64.Verify.and24_nomem⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Verify.and24_post (S := S) s) fun s' ⟨hP', _, x', _⟩ => ?_
  have L := h.1.1.1.vc.lay hF hp
  have hz := L.keepPoly hP' (by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlay) h.1.2
  obtain ⟨⟨⟨hv, hn⟩, _⟩, hr⟩ := h
  have hv' := hv.keep hF hp hP' (by vzchk hF)
  refine ⟨⟨hv'.vc, hv'.hint, fun i hi => ?_⟩, ?_⟩
  · rcases (by omega : i < j ∨ i = j) with hi | rfl
    · exact hv'.z i hi
    · exact hz
  · rw [x', hn, VG.Proof.MlDsa.AArch64.Verify.and_flag _ hr]
    exact VG.Proof.MlDsa.AArch64.Verify.flag_congr ⟨fun ⟨h1, h2⟩ i hi => by
      rcases (by omega : i < j ∨ i = j) with hi | rfl
      exacts [h1 i hi, h2], fun h1 => ⟨fun i hi => h1 i (by omega), h1 j (by omega)⟩⟩

theorem zOne_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.Z0 p j) (VG.Proof.MlDsa.AArch64.Verify.Z0 p (j + 1)) (zOne P p j) :=
  (VG.Proof.MlDsa.AArch64.Verify.bu_vpiece hP hF hj).seq ((VG.Proof.MlDsa.AArch64.Verify.norm_vpiece hP hF hj).seq (VG.Proof.MlDsa.AArch64.Verify.and_vpiece hF hj))

end

end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp`. -/
section

/-!
# ML-DSA verification on AArch64: the samplers

`ρ` to the seed (`copyRho_vpiece`); each entry `Â[r, s]` sampled from `ρ ‖ s ‖
r` (`expA_vpiece`), and `c` (`ball_vpiece`), each reduced, and `x24` 1 only if
every sampler succeeded, with their outputs (`VA`, `VB`). Each sampler's
output is masked with its result, without a branch; the seeds are functions of
the public key and the signature, the same in two runs.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq polyAt coeffAt Reduced PolyIs Bounds minBounds rejNTTPoly sampleInBall
  Outcome)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The seed of entry `e = rℓ + s` of `Â`. -/
abbrev seedOf (p : Params) (σ : State) (e : Nat) : List Byte :=
  Proof.MlDsa.Verify.aSeed (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (e / p.ℓ) (e % p.ℓ)
/-- `c̃`. -/
abbrev ctOf (p : Params) (σ : State) : List Byte := Proof.MlDsa.Verify.vCt p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ)

/-- After the first `e` entries of `Â`. -/
structure VA (p : Params) (σ : State) (e : Nat) (s : State) : Prop where
  vz : VG.Proof.MlDsa.AArch64.Verify.VZ p σ p.ℓ s
  nok : VG.Proof.MlDsa.AArch64.Verify.normOk p σ p.ℓ
  rho : bytesAt s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oSA)) 32 = (VG.Proof.MlDsa.AArch64.Verify.vPk p σ).take 32
  red : ∀ e' < e, Reduced s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e'))
  ok : ∃ q : Bool, s.gpr .x24 = VG.Proof.MlDsa.AArch64.Verify.flag (q = true) ∧
    (q = true → ∀ e' < e, ∃ b : Bounds, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.AArch64.Verify.seedOf p σ e') = some (polyAt s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e')))) ∧
    (q = false → ∃ e' < e, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.AArch64.Verify.seedOf p σ e') = none)

/-- A piece that writes `ws` keeps `VA`. -/
structure VAChk (p : Params) (e : Nat) (ws : List (Ptr × Nat)) : Prop where
  vz : VG.Proof.MlDsa.AArch64.Verify.VZChk p p.ℓ ws
  rho : keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (VG.Impl.MlDsa.AArch64.Call.sc oSA) 32 = true
  a : ∀ e' < e, keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (VG.Impl.MlDsa.AArch64.KeyGen.aP e') 1024 = true

/-- Proves a `VAChk`. -/
syntax "vachk " term:max : tactic
macro_rules
  | `(tactic| vachk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> intros <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> vlay))

theorem VA.keep {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ) {e : Nat} {s s' : State}
    (h : VG.Proof.MlDsa.AArch64.Verify.VA p σ e s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.Verify.VAChk p e ws)
    (h24 : s'.gpr .x24 = s.gpr .x24) : VG.Proof.MlDsa.AArch64.Verify.VA p σ e s' := by
  have L := h.vz.vc.lay hF hp
  obtain ⟨q, hq, h1, h0⟩ := h.ok
  refine ⟨h.vz.keep hF hp hP hc.vz, h.nok, by rw [L.keepBytes hP hc.rho]; exact h.rho,
    fun e' he' => L.keepRed hP (hc.a e' he') (h.red e' he'), q, by rw [h24]; exact hq, fun hq' e' he' => ?_, h0⟩
  obtain ⟨b, hb⟩ := h1 hq' e' he'
  exact ⟨b, by rw [hb, L.keepPolyAt hP (hc.a e' he')]⟩

/-! ## `ρ` -/

theorem copyRho_vpiece {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => VG.Proof.MlDsa.AArch64.Verify.Z0 p p.ℓ σ s ∧ VG.Proof.MlDsa.AArch64.Verify.normOk p σ p.ℓ) (VG.Proof.MlDsa.AArch64.Verify.VA p · 0) (.block (copy32 .x25 0 .x28 oSA)) := by
  have hc : copyPChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (VG.Impl.MlDsa.AArch64.Call.sc oSA) (.x25, 0) = true := by
    have := hF.k; have := hF.l; have := hF.scr; have := hF.pk; unfold copyPChk; vlay
  refine ⟨fun σ s hp h => ?_, taintRel [.x25, .x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · have L := h.1.1.vc.lay hF hp
    refine WP.mono (copyP_ok L hc) fun s' ⟨hP', k', hb⟩ => ?_
    refine ⟨h.1.1.keep hF hp hP' (by vzchk hF), h.2, ?_, fun _ h => absurd h (Nat.not_lt_zero _), true, ?_,
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (by decide)⟩
    · rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), hb, h.1.1.vc.pkSlice (by rw [hF.pk]; omega), List.drop_zero]
    · rw [k'.get .x24, h.1.2]; exact VG.Proof.MlDsa.AArch64.Verify.flag_congr (iff_of_true h.2 rfl)
  · have T := VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1.1.vc h₂.1.1.vc
    refine ⟨T.same.2, fun r hr => T.same.1 r ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

/-! ## An entry of `Â` -/

/-- The seed of `RejNTTPoly` set. -/
abbrev VA1 (p : Params) (e : Nat) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.VA p σ e s ∧ bytesAt s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oSA)) 34 = VG.Proof.MlDsa.AArch64.Verify.seedOf p σ e

/-- After `RejNTTPoly`. -/
abbrev VA2 (p : Params) (e : Nat) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.VA p σ e s ∧ ((s.gpr .x0).setWidth 32 = 1 → Reduced s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e))) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT (VG.Proof.MlDsa.AArch64.Verify.seedOf p σ e)) ((s.gpr .x0).setWidth 32) (polyAt s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e)))

theorem integerToBytes_one (x : Nat) : Spec.MlDsa.integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [Spec.MlDsa.integerToBytes]

theorem vsetTwo_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {o a b : Nat}
    (ho : o + 1 < 4096) (h1 : VG.CallLay.inB wbs (VG.Impl.MlDsa.AArch64.Call.sc o) 1 = true) (h2 : VG.CallLay.inB wbs (VG.Impl.MlDsa.AArch64.Call.sc (o + 1)) 1 = true) :
    WP isa (.block (setB (VG.Impl.MlDsa.AArch64.Call.sc o) a ++ setB (VG.Impl.MlDsa.AArch64.Call.sc (o + 1)) b)) s fun s' =>
      PPostB S s s' [(VG.Impl.MlDsa.AArch64.Call.sc o, 1), (VG.Impl.MlDsa.AArch64.Call.sc (o + 1), 1)] ∧ VG.Proof.MlKem.AArch64.Keep [.x9] s s' ∧
      bytesAt s'.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (p := VG.Impl.MlDsa.AArch64.Call.sc o) (v := a) (by simp only; omega) h1 (show Reg.x28 ∈ keptRegs by decide))
    fun s₁ ⟨hP₁, k₁, m₁⟩ => WP.mono (setB_ok (L.post hP₁) (p := VG.Impl.MlDsa.AArch64.Call.sc (o + 1)) (v := b) ho h2
      (show Reg.x28 ∈ keptRegs by decide))
      fun s₂ ⟨hP₂, k₂, m₂⟩ => ⟨PPostB.app hP₁ hP₂ (sc_bases _ (by simp)), (k₁.trans k₂).mono (by simp), ?_⟩
  have e : pa s₁ (VG.Impl.MlDsa.AArch64.Call.sc (o + 1)) = pa s (VG.Impl.MlDsa.AArch64.Call.sc o) + BitVec.ofNat 64 1 := by
    rw [hP₁.pa (show Reg.x28 ∈ keptRegs by decide), pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [m₂, m₁, e]
  exact bytesAt_two _ _ _ _

/-- The AND of a sampler's result and the mask of its output, from the registers `x28`. -/
theorem vtail_taint : ∀ j < 80, (taint.check (AArch64.Taint.ofRegs [.x28]) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.KeyGen.mask (VG.Impl.MlDsa.AArch64.Call.sc (oP j))))
    (VG.Taint.hintOf taint (AArch64.Taint.ofRegs [.x28]) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.KeyGen.mask (VG.Impl.MlDsa.AArch64.Call.sc 0))))).isSome = true := by
  decide +kernel

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {e : Nat} (he : e < p.k * p.ℓ)
include hP hF he

omit hP in
theorem seed_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA p · e) (VG.Proof.MlDsa.AArch64.Verify.VA1 p e)
    (.block (setB (VG.Impl.MlDsa.AArch64.Call.sc (oSA + 32)) (e % p.ℓ) ++ setB (VG.Impl.MlDsa.AArch64.Call.sc (oSA + 33)) (e / p.ℓ))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vz.vc h₂.vz.vc).x28) (setIJ_taint _ (by omega) _ (by omega))⟩
  have L := h.vz.vc.lay hF hp
  refine WP.mono (VG.Proof.MlDsa.AArch64.Verify.vsetTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by vlay) (by vlay))
    fun s' ⟨hP', k', hb⟩ => ⟨h.keep hF hp hP' (by vachk hF) (k'.get .x24), ?_⟩
  rw [bytes34, L.keepBytes hP' (by vlay), h.rho, sc_add, sc_pa hP', hb, VG.Proof.MlDsa.AArch64.Verify.seedOf, Proof.MlDsa.Verify.aSeed,
    VG.Proof.MlDsa.AArch64.Verify.integerToBytes_one, VG.Proof.MlDsa.AArch64.Verify.integerToBytes_one, List.append_assoc]
  rfl

omit hP in
theorem rej_chk : rejNttChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (VG.Impl.MlDsa.AArch64.Call.sc oSA) (VG.Impl.MlDsa.AArch64.KeyGen.aP e) (VG.Impl.MlDsa.AArch64.Call.sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  unfold rejNttChk; vlay

theorem rej_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA1 p e) (VG.Proof.MlDsa.AArch64.Verify.VA2 p e) (rejNttAt P (VG.Impl.MlDsa.AArch64.Call.sc oSS) (VG.Impl.MlDsa.AArch64.Call.sc oSA) (VG.Impl.MlDsa.AArch64.KeyGen.aP e)) := by
  have hc := VG.Proof.MlDsa.AArch64.Verify.rej_chk hF he
  refine ⟨fun σ s hp h => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    bytesAt x.mem (pa x (VG.Impl.MlDsa.AArch64.Call.sc oSA)) 34 = bytesAt y.mem (pa y (VG.Impl.MlDsa.AArch64.Call.sc oSA)) 34)
    (rejNttAt_tr hP.rejNtt (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc, by
      rw [h₁.2, h₂.2, VG.Proof.MlDsa.AArch64.Verify.seedOf, VG.Proof.MlDsa.AArch64.Verify.seedOf, (VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub).2.1]⟩⟩
  have L := h.1.vz.vc.lay hF hp
  refine WP.mono (rejNttAt_ok hP.s64 hP.rejNtt L hc) fun s' ⟨hP', x', hred, hout⟩ => ?_
  rw [h.2] at hout
  have e' : pa s' (VG.Impl.MlDsa.AArch64.KeyGen.aP e) = pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e) := sc_pa hP' _
  refine ⟨h.1.keep hF hp hP' (by vachk hF) x', fun h1 => by rw [e']; exact hred h1, by rw [e']; exact hout⟩

omit hP in
theorem tail_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA2 p e) (VG.Proof.MlDsa.AArch64.Verify.VA p · (e + 1)) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.KeyGen.mask (VG.Impl.MlDsa.AArch64.KeyGen.aP e))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (VG.Proof.MlDsa.AArch64.Verify.vtail_taint e (by omega))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := VG.Impl.MlDsa.AArch64.KeyGen.aP e) (by vlay) (by vlay) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (VG.Impl.MlDsa.AArch64.KeyGen.aP e) = pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  have hA : ∀ e' < e, polyAt s'.mem (pa s' (VG.Impl.MlDsa.AArch64.KeyGen.aP e')) = polyAt s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e')) := fun e' he' =>
    L.keepPolyAt hP' (by vlay)
  refine ⟨hvz, hv.nok, by rw [L.keepBytes hP' (by vlay)]; exact hv.rho, fun e'' he'' => ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' e'' he'' => ?_,
    fun hq' => ?_⟩
  · rcases (by omega : e'' < e ∨ e'' = e) with he'' | rfl
    · exact L.keepRed hP' (by vlay) (hv.red e'' he'')
    · rw [e']
      by_cases h1 : (s.gpr .x0).setWidth 32 = 1
      · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', VG.Proof.MlDsa.AArch64.Verify.and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact VG.Proof.MlDsa.AArch64.Verify.flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases (by omega : e'' < e ∨ e'' = e) with he'' | rfl
    · obtain ⟨b, hb⟩ := h1 hq'.1 e'' he''
      exact ⟨b, by rw [hb, hA e'' he'']⟩
    · rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
      · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
      · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · obtain ⟨e'', he'', hn⟩ := h0 hqq
      exact ⟨e'', by omega, hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1', _⟩ | ⟨_, hn⟩
      · exact absurd h1' hq'
      · exact ⟨e, by omega, hn⟩

theorem expA_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA p · e) (VG.Proof.MlDsa.AArch64.Verify.VA p · (e + 1)) (expA P p e) := by
  unfold expA sampled
  exact (VG.Proof.MlDsa.AArch64.Verify.seed_vpiece hF he).seq ((VG.Proof.MlDsa.AArch64.Verify.rej_vpiece hP hF he).seq (VG.Proof.MlDsa.AArch64.Verify.tail_vpiece hF he))

end

/-! ## `c` -/

/-- After the samplers. -/
structure VB (p : Params) (σ : State) (s : State) : Prop where
  vz : VG.Proof.MlDsa.AArch64.Verify.VZ p σ p.ℓ s
  nok : VG.Proof.MlDsa.AArch64.Verify.normOk p σ p.ℓ
  red : ∀ e < p.k * p.ℓ, Reduced s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e))
  redC : Reduced s.mem (pa s (cP p))
  ok : ∃ q : Bool, s.gpr .x24 = VG.Proof.MlDsa.AArch64.Verify.flag (q = true) ∧
    (q = true → (∀ e < p.k * p.ℓ, ∃ b : Bounds, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.AArch64.Verify.seedOf p σ e) = some (polyAt s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e)))) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (VG.Proof.MlDsa.AArch64.Verify.ctOf p σ)).map toRq = some (polyAt s.mem (pa s (cP p)))) ∧
    (q = false → (∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.AArch64.Verify.seedOf p σ e) = none) ∨
      (sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.AArch64.Verify.ctOf p σ)).map toRq = none)

/-- After `SampleInBall`. -/
abbrev VB1 (p : Params) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.VA p σ (p.k * p.ℓ) s ∧ ((s.gpr .x0).setWidth 32 = 1 → Reduced s.mem (pa s (cP p))) ∧
    Outcome (fun b => (sampleInBall p.τ b.ball (VG.Proof.MlDsa.AArch64.Verify.ctOf p σ)).map toRq) ((s.gpr .x0).setWidth 32)
      (polyAt s.mem (pa s (cP p)))

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p)
include hP hF

omit hP in
theorem ball_chk : ballChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (.x27, 0) p.ctildeLen (cP p) (VG.Impl.MlDsa.AArch64.Call.sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr; have := hF.ct; have := hF.sig
  unfold ballChk; vlay

omit hP in
theorem ctOf_eq {σ s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VC p σ s) : bytesAt s.mem (pa s (.x27, 0)) p.ctildeLen = VG.Proof.MlDsa.AArch64.Verify.ctOf p σ := by
  have := hF.sig
  rw [h.slice (by omega), List.drop_zero]; rfl

theorem ballCall_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA p · (p.k * p.ℓ)) (VG.Proof.MlDsa.AArch64.Verify.VB1 p)
    (ballAt P (VG.Impl.MlDsa.AArch64.Call.sc oSS) (.x27, 0) p.ctildeLen p.τ (cP p)) := by
  have hc := VG.Proof.MlDsa.AArch64.Verify.ball_chk hF
  refine ⟨fun σ s hp h => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    bytesAt x.mem (pa x (.x27, 0)) p.ctildeLen = bytesAt y.mem (pa y (.x27, 0)) p.ctildeLen)
    (ballAt_tr hP.ball (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc hF.ct.1 fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vz.vc h₂.vz.vc, by
      rw [VG.Proof.MlDsa.AArch64.Verify.ctOf_eq hF h₁.vz.vc, VG.Proof.MlDsa.AArch64.Verify.ctOf_eq hF h₂.vz.vc, VG.Proof.MlDsa.AArch64.Verify.ctOf, VG.Proof.MlDsa.AArch64.Verify.ctOf, (VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub).2.2.2.1]⟩⟩
  have L := h.vz.vc.lay hF hp
  refine WP.mono (ballAt_ok hP.s64 hP.ball L hc hF.ct.1) fun s' ⟨hP', x', hred, hout⟩ => ?_
  rw [VG.Proof.MlDsa.AArch64.Verify.ctOf_eq hF h.vz.vc] at hout
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  refine ⟨h.keep hF hp hP' (by vachk hF) x', fun h1 => by rw [e']; exact hred h1, by rw [e']; exact hout⟩

omit hP in
theorem ballTail_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VB1 p) (VG.Proof.MlDsa.AArch64.Verify.VB p) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.KeyGen.mask (cP p))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (VG.Proof.MlDsa.AArch64.Verify.vtail_taint _ (by omega))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := cP p) (by vlay) (by vlay) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  refine ⟨hvz, hv.nok, fun e he => L.keepRed hP' (by vlay) (hv.red e he), ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' => ⟨fun e he => ?_, ?_⟩,
    fun hq' => ?_⟩
  · rw [e']
    by_cases h1 : (s.gpr .x0).setWidth 32 = 1
    · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
    · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', VG.Proof.MlDsa.AArch64.Verify.and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact VG.Proof.MlDsa.AArch64.Verify.flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨b, hb⟩ := h1 hq'.1 e he
    exact ⟨b, by rw [hb, L.keepPolyAt hP' (by vlay)]⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
    · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
    · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · exact .inl (h0 hqq)
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1'', _⟩ | ⟨_, hn⟩
      · exact absurd h1'' hq'
      · exact .inr hn

end

/-! ## The samplers -/


end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4`. -/
section

/-! Four-way matrix expansion during verification: preserve decoded hints and z, and mask failed batches without a branch. -/

namespace VG.Proof.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Reduced polyAt coeffAt poly4 seed4 Bounds rejNTTPoly minBounds)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (masked_one masked_zero)

structure VS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  va : VG.Proof.MlDsa.AArch64.Verify.VA p σ e s
  done : ∀ k < j,bytesAt s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oSA4+34*k))) 34 = VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+k)

theorem vslot_ok {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ)
    {e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) {s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VS p σ e j s) :
    WP isa (seedSlot4 p e j) s (VG.Proof.MlDsa.AArch64.Verify.VS p σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (copySeed4_generic L (by vlay) (by vlay) (by vlay)) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.va.keep hF hp hP1 (by vachk hF) (hk1.get .x24)
  have L1 := h1.vz.vc.lay hF hp
  unfold setSR
  refine WP.mono (VG.Proof.MlDsa.AArch64.Verify.vsetTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%p.ℓ) (b := (e+j)/p.ℓ)
    (by dsimp only [oSA4]; omega) (by vlay) (by vlay)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by vachk hF) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [bytes34,L1.keepBytes hP2 (by vlay),sc_pa hP2,sc_pa hP1,hb1,h.va.rho,
      sc_add,← sc_pa hP1,hb2,VG.Proof.MlDsa.AArch64.Verify.seedOf,Proof.MlDsa.Verify.aSeed,VG.Proof.MlDsa.AArch64.Verify.integerToBytes_one,VG.Proof.MlDsa.AArch64.Verify.integerToBytes_one,List.append_assoc]
    rfl
  · rw [L1.keepBytes hP2 (by vlay),L.keepBytes hP1 (by vlay)]
    exact h.done k (by omega)

theorem vslot_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VS p · e j) (VG.Proof.MlDsa.AArch64.Verify.VS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.Verify.vslot_ok hF hp he hj h,
    VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := VG.Proof.MlDsa.AArch64.Verify.VTwo p S) (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (slot_taint p e hj))
      fun _ _ _ _ hp hp' hq h h' => VG.Proof.MlDsa.AArch64.Verify.vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc⟩

theorem vseed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oSA4)) k = VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+k) := by
  unfold seed4
  rw [show pa s (VG.Impl.MlDsa.AArch64.Call.sc oSA4)+BitVec.ofNat 64 (34*k) = pa s (VG.Impl.MlDsa.AArch64.Call.sc (oSA4+34*k)) from sc_add _ _ _]
  exact h.done k hk

theorem VS.seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VS p σ e 4 s) :
    bytesAt s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oSA4)) 136 = VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+0) ++ VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+1) ++ VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+2) ++ VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+3) := by
  have b : ∀ k < 4,bytesAt s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oSA4)+BitVec.ofNat 64 (34*k)) 34 = VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (e+k) :=
    fun k hk => VG.Proof.MlDsa.AArch64.Verify.vseed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34*0=0 from rfl,VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [bytes136,b0,b 1 (by decide),b 2 (by decide),b 3 (by decide)]

theorem vcall4_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p)
    {σ : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State} (h : VG.Proof.MlDsa.AArch64.Verify.VS p σ (4*g) 4 s) :
    WP isa (.seq (rej4At P (VG.Impl.MlDsa.AArch64.Call.sc (oR4 p)) (VG.Impl.MlDsa.AArch64.Call.sc oSA4) (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)))
      (.seq (.block and24) (mask4 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))))) s (VG.Proof.MlDsa.AArch64.Verify.VA p σ (4*g+4)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  refine WP.seq (WP.mono (rej4At_ok hP.s64 hP.rej4 L
    (seed := VG.Impl.MlDsa.AArch64.Call.sc oSA4) (a := VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) (ss := VG.Impl.MlDsa.AArch64.Call.sc (oR4 p)) (by unfold rej4Chk; vlay))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide) (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by rw [h20.get .x0]; exact hr01
  refine WP.mono (mask4_ok L20 (a := VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) (by vlay) (by vlay) hr20) fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) = pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) := sc_pa hP2 _
  have e20 : pa s20 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) = pa s2 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4,∀ i < 256,coeffAt s3.mem (poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g+k)) = poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) k := fun k => by rw [pa_poly4,sc_pa hP13]
  obtain ⟨q,hq,h1,h0⟩ := h.va.ok
  have hA : ∀ e' < 4*g,polyAt s3.mem (pa s3 (VG.Impl.MlDsa.AArch64.KeyGen.aP e')) = polyAt s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e')) := fun e' he' => L.keepPolyAt hP13 (by vlay)
  refine ⟨h.va.vz.keep hF hp hP13 (by vzchk hF),h.va.nok,by rw [L.keepBytes hP13 (by vlay)]; exact h.va.rho,
    fun e' he' => ?_,q && ((s2.gpr .x0).setWidth 32 == 1),?_,fun hq' e' he' => ?_,fun hq' => ?_⟩
  · by_cases hlt : e' < 4*g
    · exact L.keepRed hP13 (by vlay) (h.va.red e' hlt)
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
      rw [e3]
      by_cases hret : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one hret (hco4 k (by omega))).2 (hred hret k (by omega))
      · exact (masked_zero hret (hco4 k (by omega))).1
  · rw [k3.get .x24,e24,h24,hq,VG.Proof.MlDsa.AArch64.Verify.and_flag _ (Q := (s2.gpr .x0).setWidth 32 = 1)
      (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact VG.Proof.MlDsa.AArch64.Verify.flag_congr (by simp)
  · simp only [Bool.and_eq_true,beq_iff_eq] at hq'
    by_cases hlt : e' < 4*g
    · obtain ⟨b,hb⟩ := h1 hq'.1 e' hlt
      exact ⟨b,by rw [hb,hA e' hlt]⟩
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
      rcases hout with ⟨_,hb⟩ | ⟨hret,_⟩
      · obtain ⟨b,hb⟩ := hb k (by omega)
        exact ⟨b,by rw [e3,(masked_one hq'.2 (hco4 k (by omega))).1,← VG.Proof.MlDsa.AArch64.Verify.vseed4_eq h (by omega)]; exact hb⟩
      · rw [hq'.2] at hret; exact absurd hret (by decide)
  · cases hqq : q
    · obtain ⟨e',he',hn⟩ := h0 hqq; exact ⟨e',by omega,hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and,beq_eq_false_iff_ne,ne_eq] at hq'
      rcases hout with ⟨hret,_⟩ | ⟨_,k,hk,hn⟩
      · exact absurd hret hq'
      · exact ⟨4*g+k,by omega,by rw [← VG.Proof.MlDsa.AArch64.Verify.vseed4_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Verify

namespace VG.Proof.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem VTwo.step {p : Params} {S : Nat} {c : Prog isa} {Q : State → State → Prop}
    (hq : ∀ x y,Q x y → VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y) (htr : RelCT isa Q c fun _ _ => True)
    (hok : ∀ x y,Q x y → (WP isa c x fun x' => ∃ W,PostB S x x' W) ∧
      (WP isa c y fun y' => ∃ W,PostB S y y' W)) : RelCT isa Q c (VG.Proof.MlDsa.AArch64.Verify.VTwo p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W,PostB S x x' W) hok
    fun x y x' y' h ⟨_,hx⟩ ⟨_,hy⟩ => ⟨(hq x y h).lx.post hx,(hq x y h).ly.post hy,
      fun r hr => by rw [hx.bs r (bases_kept r hr),hy.bs r (bases_kept r hr)]; exact (hq x y h).same.1 r hr,
      by rw [hx.sp,hy.sp]; exact (hq x y h).same.2⟩

theorem vcall4_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VS p · (4*g) 4) (VG.Proof.MlDsa.AArch64.Verify.VA p · (4*g+4))
      (.seq (rej4At P (VG.Impl.MlDsa.AArch64.Call.sc (oR4 p)) (VG.Impl.MlDsa.AArch64.Call.sc oSA4) (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) (.seq (.block and24) (mask4 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.Verify.vcall4_ok hP hF hp hg h,
    VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧ bytesAt x.mem (pa x (VG.Impl.MlDsa.AArch64.Call.sc oSA4)) 136 = bytesAt y.mem (pa y (VG.Impl.MlDsa.AArch64.Call.sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [h.seeds,h'.seeds]; simp only [VG.Proof.MlDsa.AArch64.Verify.seedOf,(VG.Proof.MlDsa.AArch64.Verify.vPub_eq hq).2.1]⟩)⟩
  have hc : rej4Chk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (VG.Impl.MlDsa.AArch64.Call.sc oSA4) (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) (VG.Impl.MlDsa.AArch64.Call.sc (oR4 p)) = true := by unfold rej4Chk; vlay
  have ok := fun x (L : Lay S (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VG.Proof.MlDsa.AArch64.Verify.VTwo p S) (.seq (.block and24) (mask4 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)))) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (mask4_taint (4*g) (by omega)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail

end VG.Proof.MlDsa.AArch64.Verify

namespace VG.Proof.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem expA4_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA p · (4*g)) (VG.Proof.MlDsa.AArch64.Verify.VA p · (4*g+4)) (expA4 P p g) := by
  unfold expA4
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s => VG.Proof.MlDsa.AArch64.Verify.VS p σ (4*g) j s) 4 0 (fun j _ hj => VG.Proof.MlDsa.AArch64.Verify.vslot_piece hF hg (by omega)))
      (fun _ _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
      (fun _ _ _ h => by simpa using h)) (VG.Proof.MlDsa.AArch64.Verify.vcall4_piece hP hF hg)

theorem expAll_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA p · 0) (VG.Proof.MlDsa.AArch64.Verify.VA p · (p.k*p.ℓ)) (expAll P p) := by
  unfold expAll
  have hB : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VA p · 0) (VG.Proof.MlDsa.AArch64.Verify.VA p · (4*(p.k*p.ℓ/4))) (VG.Impl.MlDsa.AArch64.Call.seqR (expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (VPiece.seqR (I := fun g σ s => VG.Proof.MlDsa.AArch64.Verify.VA p σ (4*g) s) (p.k*p.ℓ/4) 0 (fun g _ hg => VG.Proof.MlDsa.AArch64.Verify.expA4_vpiece hP hF (by omega)))
  refine VPiece.mono (VPiece.seq hB
    (VPiece.seqR (I := fun e σ s => VG.Proof.MlDsa.AArch64.Verify.VA p σ e s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
      (fun e _ he => VG.Proof.MlDsa.AArch64.Verify.expA_vpiece hP hF (by omega)))) (fun _ _ _ h => h) (fun _ _ _ h => ?_)
  have he : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
  simpa only [he] using h

theorem samples_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => VG.Proof.MlDsa.AArch64.Verify.Z0 p p.ℓ σ s ∧ VG.Proof.MlDsa.AArch64.Verify.normOk p σ p.ℓ) (VG.Proof.MlDsa.AArch64.Verify.VB p) (samples P p) := by
  unfold samples sampled
  exact (VG.Proof.MlDsa.AArch64.Verify.copyRho_vpiece hF).seq ((VG.Proof.MlDsa.AArch64.Verify.expAll_vpiece hP hF).seq ((VG.Proof.MlDsa.AArch64.Verify.ballCall_vpiece hP hF).seq (VG.Proof.MlDsa.AArch64.Verify.ballTail_vpiece hF)))

end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute`. -/
section

/-!
# ML-DSA verification on AArch64: `w′₁`, row by row

With the entries `A'` of `Â` and `c = c0` as the samplers left them, and `x24`
their result `q` (`SC`): `ẑ[i] = NTT(z[i])` (`nttZ_vpiece`), `ĉ`
(`nttC_vpiece`), and each row `r` of `w′₁`, packed to `w1Encode(w′₁)`
(`row_vpiece`).
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs
  HintIs Bounds minBounds rejNTTPoly sampleInBall simpleBitPack d ofInt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (zHat dotAcc t1Hat wRow w1Row vT1 aSeed)

/-- Where row `r` of `w1Encode(w′₁)` goes. -/
abbrev rowP (p : Params) (r : Nat) : Ptr := VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k * p.ℓ + 0) + w1Len p * r)

/-- What the samplers gave: `q` whether they succeeded, `Â = A'` and `c = c0` if so. -/
def Gd (p : Params) (σ : State) (A' : Nat → Nat → VG.Spec.MlDsa.Poly) (c0 : VG.Spec.MlDsa.Poly) (q : Bool) : Prop :=
  (q = true → (∀ r < p.k, ∀ c < p.ℓ, ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r c) = some (A' r c)) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (VG.Proof.MlDsa.AArch64.Verify.ctOf p σ)).map toRq = some c0) ∧
    (q = false → (∃ r < p.k, ∃ c < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r c) = none) ∨
      (sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.AArch64.Verify.ctOf p σ)).map toRq = none)

/-- While computing: `ẑ[i]` for `i < j` (`z[i]` after), `ĉ` if `cn` (`c` if not),
and the rows of `w′₁` before `r` packed. -/
structure SC (p : Params) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly) (c0 : VG.Spec.MlDsa.Poly)
    (q : Bool) (j : Nat) (cn : Bool) (r : Nat) (s : State) : Prop where
  vc : VG.Proof.MlDsa.AArch64.Verify.VC p σ s
  hh : VG.Proof.MlDsa.AArch64.Verify.hintOf p σ = some h
  hint : HintIs s.mem (pa s (hP p 0)) p.k h
  nok : VG.Proof.MlDsa.AArch64.Verify.normOk p σ p.ℓ
  gd : VG.Proof.MlDsa.AArch64.Verify.Gd p σ A' c0 q
  a : ∀ r' < p.k, ∀ c < p.ℓ, PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r' + c))) (A' r' c)
  z : ∀ i < p.ℓ, PolyIs s.mem (pa s (zP p i))
    (if i < j then VG.Proof.MlDsa.Verify.zHat p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) i else toRq (VG.Proof.MlDsa.AArch64.Verify.zOf p σ i))
  c : PolyIs s.mem (pa s (cP p)) (if cn then VG.Spec.MlDsa.ntt c0 else c0)
  rows : ∀ r' < r, bytesAt s.mem (pa s (VG.Proof.MlDsa.AArch64.Verify.rowP p r')) (w1Len p) =
    VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' (VG.Spec.MlDsa.ntt c0) h r') (w1Max p)
  x24 : s.gpr .x24 = VG.Proof.MlDsa.AArch64.Verify.flag (q = true)

abbrev SCx (p : Params) (j : Nat) (cn : Bool) (r : Nat) (σ s : State) : Prop :=
  ∃ h A' c0 q, VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q j cn r s

/-- A piece that writes `ws` keeps `SC`. -/
structure SCChk (p : Params) (r : Nat) (ws : List (Ptr × Nat)) : Prop where
  vc : VG.Proof.MlDsa.AArch64.Verify.vcChk p ws = true
  hint : keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (hP p 0) (1024 * p.k) = true
  a : ∀ r' < p.k, ∀ c < p.ℓ, keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r' + c)) 1024 = true
  z : ∀ i < p.ℓ, keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (zP p i) 1024 = true
  c : keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (cP p) 1024 = true
  rows : ∀ r' < r, keepB (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) ws (VG.Proof.MlDsa.AArch64.Verify.rowP p r') (w1Len p) = true

theorem ar_lt {p : Params} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) : p.ℓ * r + c < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show r + 1 ≤ p.k by omega)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- Proves an `SCChk`. -/
syntax "scchk " term:max : tactic
macro_rules
  | `(tactic| scchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      rcases ($hF).wl with hw | hw <;> have hkw := ($hF).w1 <;> rw [hw] at hkw <;>
      refine ⟨?_, ?_, fun r' hr' c hc => ?_, ?_, ?_, ?_⟩ <;> intros <;>
      (try have := ar_lt hr' hc) <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> vlay [hw]))

theorem SC.keep {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ) {h : List (Vector Bool _)}
    {A' : Nat → Nat → VG.Spec.MlDsa.Poly} {c0 : VG.Spec.MlDsa.Poly} {q : Bool} {j : Nat} {cn : Bool} {r : Nat} {s s' : State}
    (hs : VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q j cn r s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.Verify.SCChk p r ws)
    (h24 : s'.gpr .x24 = s.gpr .x24) : VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q j cn r s' := by
  have L := hs.vc.lay hF hp
  exact ⟨hs.vc.step hF hp hP hc.vc, hs.hh, L.keepHint hP hc.hint hs.hint, hs.nok, hs.gd,
    fun r' hr' c hc' => L.keepPoly hP (hc.a r' hr' c hc') (hs.a r' hr' c hc'),
    fun i hi => L.keepPoly hP (hc.z i hi) (hs.z i hi), L.keepPoly hP hc.c hs.c,
    fun r' hr' => by rw [L.keepBytes hP (hc.rows r' hr')]; exact hs.rows r' hr', by rw [h24]; exact hs.x24⟩

theorem keepB_append {rbs wbs : List (Reg × Nat)} {ws₁ ws₂ : List (Ptr × Nat)} {q : Ptr} {l : Nat}
    (h₁ : keepB rbs wbs ws₁ q l = true) (h₂ : keepB rbs wbs ws₂ q l = true) :
    keepB rbs wbs (ws₁ ++ ws₂) q l = true := by
  simp only [keepB, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

theorem vcChk_append {p : Params} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : VG.Proof.MlDsa.AArch64.Verify.vcChk p ws₁ = true)
    (h₂ : VG.Proof.MlDsa.AArch64.Verify.vcChk p ws₂ = true) : VG.Proof.MlDsa.AArch64.Verify.vcChk p (ws₁ ++ ws₂) = true := by
  simp only [VG.Proof.MlDsa.AArch64.Verify.vcChk, Bool.and_eq_true] at *
  exact ⟨⟨⟨VG.Proof.MlDsa.AArch64.Verify.keepB_append h₁.1.1.1 h₂.1.1.1, VG.Proof.MlDsa.AArch64.Verify.keepB_append h₁.1.1.2 h₂.1.1.2⟩, VG.Proof.MlDsa.AArch64.Verify.keepB_append h₁.1.2 h₂.1.2⟩,
    VG.Proof.MlDsa.AArch64.Verify.keepB_append h₁.2 h₂.2⟩

/-- The checks of two pieces of writes, for both. -/
theorem SCChk.append {p : Params} {r : Nat} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : VG.Proof.MlDsa.AArch64.Verify.SCChk p r ws₁)
    (h₂ : VG.Proof.MlDsa.AArch64.Verify.SCChk p r ws₂) : VG.Proof.MlDsa.AArch64.Verify.SCChk p r (ws₁ ++ ws₂) :=
  ⟨VG.Proof.MlDsa.AArch64.Verify.vcChk_append h₁.vc h₂.vc, VG.Proof.MlDsa.AArch64.Verify.keepB_append h₁.hint h₂.hint,
    fun r' hr' c hc => VG.Proof.MlDsa.AArch64.Verify.keepB_append (h₁.a r' hr' c hc) (h₂.a r' hr' c hc), fun i hi => VG.Proof.MlDsa.AArch64.Verify.keepB_append (h₁.z i hi) (h₂.z i hi),
    VG.Proof.MlDsa.AArch64.Verify.keepB_append h₁.c h₂.c, fun r' hr' => VG.Proof.MlDsa.AArch64.Verify.keepB_append (h₁.rows r' hr') (h₂.rows r' hr')⟩

/-- No writes. -/
theorem SCChk.nil {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {r : Nat} (hr : r ≤ p.k) : VG.Proof.MlDsa.AArch64.Verify.SCChk p r [] := by
  scchk hF

/-- A write to `scratch` apart from what `SC` holds, proved once for any region (`scchk` on a literal list
of writes costs seconds). -/
theorem SCChk.x28 {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {r : Nat} (hr : r ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ SV ∨ SV + 48 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ) ≤ o)
    (h3 : o + n ≤ oP (p.k * p.ℓ) ∨ oP (p.k * p.ℓ) + w1Len p * r ≤ o)
    (h4 : o + n ≤ oP (p.k * p.ℓ + 1) ∨ oP (p.k * p.ℓ + (1 + p.k + p.ℓ + 1)) ≤ o) (h5 : o + n ≤ scrLen p) :
    VG.Proof.MlDsa.AArch64.Verify.SCChk p r [((.x28, o), n)] := by
  rw [scr_eq] at h5
  simp only [SV, oP] at h1 h2 h3 h4
  have : w1Len p * r ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega
  rcases hF.wl with hw | hw <;> rw [hw] at h3 this <;> scchk hF

theorem SCChk.cons_x28 {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {r : Nat} (hr : r ≤ p.k) {o n : Nat} {ws : List (Ptr × Nat)}
    (h1 : o + n ≤ SV ∨ SV + 48 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ) ≤ o)
    (h3 : o + n ≤ oP (p.k * p.ℓ) ∨ oP (p.k * p.ℓ) + w1Len p * r ≤ o ∨ oP (p.k * p.ℓ) + 1024 ≤ o)
    (h4 : o + n ≤ oP (p.k * p.ℓ + 1) ∨ oP (p.k * p.ℓ + (1 + p.k + p.ℓ + 1)) ≤ o) (h5 : o + n ≤ scrLen p)
    (h : VG.Proof.MlDsa.AArch64.Verify.SCChk p r ws) : VG.Proof.MlDsa.AArch64.Verify.SCChk p r (((.x28, o), n) :: ws) := by
  have : w1Len p * r ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega
  exact (SCChk.x28 hF hr h1 h2 (by omega) h4 h5).append (ws₁ := [_]) h

/-- Proves an `SCChk` of writes to `scratch` by `SCChk.cons_x28`, with `hr : r ≤ p.k`. -/
macro "scchks " hF:term:max hr:term:max : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact VG.Proof.MlDsa.AArch64.Verify.SCChk.nil $hF $hr
    | apply VG.Proof.MlDsa.AArch64.Verify.SCChk.cons_x28 $hF $hr)
  all_goals (
    have := ($hF).w1; have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).ct.2
    try rw [VG.Proof.MlDsa.AArch64.KeyGen.scr_eq]
    try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.SV,
      VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.Verify.oCT]
    omega_arith)))

/-! ## From the samplers -/

theorem seedOf_ar (p : Params) (σ : State) {r c : Nat} (hc : c < p.ℓ) :
    VG.Proof.MlDsa.AArch64.Verify.seedOf p σ (p.ℓ * r + c) = aSeed (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r c := by
  have hl : 0 < p.ℓ := by omega
  rw [VG.Proof.MlDsa.AArch64.Verify.seedOf, Nat.mul_add_div hl, Nat.div_eq_of_lt hc, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

theorem vb_sc {p : Params} {σ s : State} (hs : VG.Proof.MlDsa.AArch64.Verify.VB p σ s) : VG.Proof.MlDsa.AArch64.Verify.SCx p 0 false 0 σ s := by
  obtain ⟨h, hh, hH⟩ := hs.vz.hint
  obtain ⟨q, hq, h1, h0⟩ := hs.ok
  refine ⟨h, fun r c => polyAt s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r + c))), polyAt s.mem (pa s (cP p)), q,
    ⟨hs.vz.vc, hh, hH, hs.nok, ⟨fun hq' => ⟨fun r hr c hc => ?_, (h1 hq').2⟩, fun hq' => ?_⟩,
      fun r hr c hc => ⟨hs.red _ (VG.Proof.MlDsa.AArch64.Verify.ar_lt hr hc), rfl⟩, fun i hi => by rw [ifn (Nat.not_lt_zero _)]; exact hs.vz.z i hi,
      ⟨hs.redC, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _), hq⟩⟩
  · obtain ⟨b, hb⟩ := (h1 hq').1 _ (VG.Proof.MlDsa.AArch64.Verify.ar_lt hr hc)
    exact ⟨b, by rw [← VG.Proof.MlDsa.AArch64.Verify.seedOf_ar p σ hc]; exact hb⟩
  · rcases h0 hq' with ⟨e, he, hn⟩ | hn
    · have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
      refine .inl ⟨e / p.ℓ, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he), e % p.ℓ, Nat.mod_lt _ hl, ?_⟩
      rw [← VG.Proof.MlDsa.AArch64.Verify.seedOf_ar p σ (Nat.mod_lt _ hl), Nat.div_add_mod]; exact hn
    · exact .inr hn

/-! ## The NTTs -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p)
include hP hF

theorem nttZ_vpiece {i : Nat} (hi : i < p.ℓ) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCx p i false 0) (VG.Proof.MlDsa.AArch64.Verify.SCx p (i + 1) false 0) (nttAt P (VG.Impl.MlDsa.AArch64.Call.sc oSS) (zP p i)) := by
  have hc : ipChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (zP p i) (VG.Impl.MlDsa.AArch64.Call.sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    Reduced x.mem (pa x (zP p i)) ∧ Reduced y.mem (pa y (zP p i)))
    (by unfold nttAt; exact ipAt_tr hP.ntt (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vc h₂.vc,
      (h₁.z i hi).1, (h₂.z i hi).1⟩⟩
  have L := hs.vc.lay hF hp
  have hz := hs.z i hi
  rw [ifn (Nat.lt_irrefl _)] at hz
  unfold nttAt
  refine WP.mono (ipAt_ok hP.s64 hP.ntt L hc hz.1) fun s' ⟨hP', x', hq⟩ => ⟨h, A', c0, q, ?_⟩
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  refine ⟨hs.vc.step hF hp hP' (by unfold VG.Proof.MlDsa.AArch64.Verify.vcChk; vlay), hs.hh, L.keepHint hP' (by vlay) hs.hint, hs.nok, hs.gd,
    fun r' hr' c hc' => L.keepPoly hP' (by have := VG.Proof.MlDsa.AArch64.Verify.ar_lt hr' hc'; vlay) (hs.a r' hr' c hc'), fun i' hi' => ?_,
    L.keepPoly hP' (by vlay) hs.c, fun _ h => absurd h (Nat.not_lt_zero _), by rw [x']; exact hs.x24⟩
  rcases (by omega : i' < i ∨ i' = i ∨ i < i') with hlt | rfl | hgt
  · rw [ifp (by omega : i' < i + 1)]
    have := L.keepPoly hP' (by vlay) (hs.z i' hi')
    rwa [ifp hlt] at this
  · rw [ifp (Nat.lt_succ_self _), hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    rw [hz.2] at hq
    exact hq
  · rw [ifn (by omega : ¬ i' < i + 1)]
    have := L.keepPoly hP' (by vlay) (hs.z i' hi')
    rwa [ifn (by omega : ¬ i' < i)] at this

theorem nttC_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ false 0) (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true 0) (nttAt P (VG.Impl.MlDsa.AArch64.Call.sc oSS) (cP p)) := by
  have hc : ipChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (cP p) (VG.Impl.MlDsa.AArch64.Call.sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    Reduced x.mem (pa x (cP p)) ∧ Reduced y.mem (pa y (cP p)))
    (by unfold nttAt; exact ipAt_tr hP.ntt (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vc h₂.vc, h₁.c.1, h₂.c.1⟩⟩
  have L := hs.vc.lay hF hp
  have hcc := hs.c
  simp only [Bool.false_eq_true, ↓reduceIte] at hcc
  unfold nttAt
  refine WP.mono (ipAt_ok hP.s64 hP.ntt L hc hcc.1) fun s' ⟨hP', x', hq⟩ => ⟨h, A', c0, q, ?_⟩
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  refine ⟨hs.vc.step hF hp hP' (by unfold VG.Proof.MlDsa.AArch64.Verify.vcChk; vlay), hs.hh, L.keepHint hP' (by vlay) hs.hint, hs.nok, hs.gd,
    fun r' hr' c hc' => L.keepPoly hP' (by have := VG.Proof.MlDsa.AArch64.Verify.ar_lt hr' hc'; vlay) (hs.a r' hr' c hc'),
    fun i hi => L.keepPoly hP' (by vlay) (hs.z i hi), ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [x']; exact hs.x24⟩
  rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), ifp rfl]
  rw [hcc.2] at hq
  exact hq

end

/-! ## A row -/

/-- In row `r`, with `f` holding of the temporaries. -/
abbrev RowI (p : Params) (r : Nat)
    (f : State → List (Vector Bool Spec.MlDsa.n) → (Nat → Nat → VG.Spec.MlDsa.Poly) → VG.Spec.MlDsa.Poly → State → Prop) (σ s : State) : Prop :=
  ∃ h A' c0 q, VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q p.ℓ true r s ∧ f σ h A' c0 s

/-- `Σ_{s < j} Â[r, s] ẑ[s]` in `w′`. -/
abbrev wIs (p : Params) (σ : State) (r j : Nat) (A' : Nat → Nat → VG.Spec.MlDsa.Poly) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) (dotAcc p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' r j)

/-- `Σₛ Â[r, s] ẑ[s]`. -/
abbrev rDot (p : Params) (σ : State) (A' : Nat → Nat → VG.Spec.MlDsa.Poly) (r : Nat) : VG.Spec.MlDsa.Poly := dotAcc p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' r p.ℓ
/-- `t₁[r] · 2ᵈ`. -/
abbrev rU (p : Params) (σ : State) (r : Nat) : VG.Spec.MlDsa.Poly := (vT1 (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r).map fun c => ofInt (c * 2 ^ d : Nat)

theorem SC.zHat {p : Params} {σ : State} {h : List (Vector Bool _)} {A' : Nat → Nat → VG.Spec.MlDsa.Poly} {c0 : VG.Spec.MlDsa.Poly} {q : Bool}
    {r : Nat} {s : State} (hs : VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q p.ℓ true r s) {c : Nat} (hc : c < p.ℓ) :
    PolyIs s.mem (pa s (zP p c)) (VG.Proof.MlDsa.Verify.zHat p (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) c) := by
  have := hs.z c hc; rwa [ifp hc] at this

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

omit hP in
theorem mulW_chk {c : Nat} (hc : c < p.ℓ) : mulChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (wP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r + c)) (zP p c) = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := VG.Proof.MlDsa.AArch64.Verify.ar_lt hr hc
  unfold mulChk; vlay

end

theorem rowI_two {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {S r : Nat} {f : State → List (Vector Bool Spec.MlDsa.n) →
    (Nat → Nat → VG.Spec.MlDsa.Poly) → VG.Spec.MlDsa.Poly → State → Prop} {σ₁ σ₂ x y : State} (p₁ : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₁) (p₂ : VG.Proof.MlDsa.AArch64.Verify.vPre p S σ₂)
    (pub : VG.Proof.MlDsa.AArch64.Verify.vPub p S σ₁ σ₂) (h₁ : VG.Proof.MlDsa.AArch64.Verify.RowI p r f σ₁ x) (h₂ : VG.Proof.MlDsa.AArch64.Verify.RowI p r f σ₂ y) : VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y :=
  let ⟨_, _, _, _, a, _⟩ := h₁; let ⟨_, _, _, _, b, _⟩ := h₂; VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub a.vc b.vc

theorem hintRow_pa (p : Params) (s : State) (r : Nat) :
    pa s (hP p r) = pa s (hP p 0) + BitVec.ofNat 64 (1024 * r) := by
  have e : oP (p.k * p.ℓ + (1 + r)) = oP (p.k * p.ℓ + (1 + 0)) + 1024 * r := by simp only [oP]; omega
  rw [show pa s (hP p r) = s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + (1 + r))) from rfl,
    show pa s (hP p 0) = s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + (1 + 0))) from rfl, e, BitVec.ofNat_add,
    BitVec.add_assoc]

/-- The temporaries of a row, facts about them. -/
abbrev F1 (p : Params) (r j : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (_ : VG.Spec.MlDsa.Poly) (s : State) : Prop := VG.Proof.MlDsa.AArch64.Verify.wIs p σ r j A' s
abbrev F3 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (_ : VG.Spec.MlDsa.Poly) (s : State) : Prop := VG.Proof.MlDsa.AArch64.Verify.wIs p σ r p.ℓ A' s ∧ PolyIs s.mem (pa s (tmP p)) (VG.Proof.MlDsa.AArch64.Verify.rU p σ r)
abbrev F4 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (_ : VG.Spec.MlDsa.Poly) (s : State) : Prop := VG.Proof.MlDsa.AArch64.Verify.wIs p σ r p.ℓ A' s ∧ PolyIs s.mem (pa s (tmP p)) (VG.Spec.MlDsa.ntt (VG.Proof.MlDsa.AArch64.Verify.rU p σ r))
abbrev F5 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (c0 : VG.Spec.MlDsa.Poly) (s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.wIs p σ r p.ℓ A' s ∧ PolyIs s.mem (pa s (tm2P p)) (multiplyNTT (VG.Spec.MlDsa.ntt c0) (t1Hat (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r))
abbrev F6 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (c0 : VG.Spec.MlDsa.Poly) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) (Spec.MlDsa.sub (VG.Proof.MlDsa.AArch64.Verify.rDot p σ A' r) (multiplyNTT (VG.Spec.MlDsa.ntt c0) (t1Hat (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r)))
abbrev F7 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (c0 : VG.Spec.MlDsa.Poly) (s : State) : Prop := PolyIs s.mem (pa s (wP p)) (wRow p (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' (VG.Spec.MlDsa.ntt c0) r)
abbrev F8 (p : Params) (r : Nat) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly)
    (c0 : VG.Spec.MlDsa.Poly) (s : State) : Prop := NatPolyIs s.mem (pa s (w1P p)) (w1Row p (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' (VG.Spec.MlDsa.ntt c0) h r)

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

theorem dot0_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true r) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F1 p r 1)) (mulAt P (wP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r)) (zP p 0)) := by
  have hl := hF.l
  have hc := VG.Proof.MlDsa.AArch64.Verify.mulW_chk hF hr (c := 0) (by omega)
  rw [Nat.add_zero] at hc
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    (Reduced x.mem (pa x (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r))) ∧ Reduced x.mem (pa x (zP p 0))) ∧
    (Reduced y.mem (pa y (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r))) ∧ Reduced y.mem (pa y (zP p 0))))
    (mulAt_tr hP.mul (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vc h₂.vc, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    have hA := hs.a r hr 0 (by omega)
    rw [Nat.add_zero] at hA
    have hZ := hs.zHat (c := 0) (by omega)
    refine WP.mono (mulAt_ok hP.s64 hP.mul L hc hA.1 hZ.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', ?_⟩
    rw [hA.2, hZ.2] at hq
    show PolyIs _ _ _
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    simp only [dotAcc, Proof.MlDsa.Verify.add_zero_left]
    exact hq
  · have := h₁.a r hr 0 (by omega); rw [Nat.add_zero] at this; exact ⟨this.1, (h₁.zHat (c := 0) (by omega)).1⟩
  · have := h₂.a r hr 0 (by omega); rw [Nat.add_zero] at this; exact ⟨this.1, (h₂.zHat (c := 0) (by omega)).1⟩

theorem dotS_vpiece {j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F1 p r j)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F1 p r (j + 1)))
    (mulAddAt P (wP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r + j)) (zP p j)) := by
  have hc := VG.Proof.MlDsa.AArch64.Verify.mulW_chk hF hr hj
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    (Reduced x.mem (pa x (wP p)) ∧ Reduced x.mem (pa x (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r + j))) ∧ Reduced x.mem (pa x (zP p j))) ∧
    (Reduced y.mem (pa y (wP p)) ∧ Reduced y.mem (pa y (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * r + j))) ∧ Reduced y.mem (pa y (zP p j))))
    (mulAddAt_tr hP.mulAdd (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ⟨VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vc h₂.vc,
      ⟨w₁.1, (h₁.a r hr j hj).1, (h₁.zHat hj).1⟩, ⟨w₂.1, (h₂.a r hr j hj).1, (h₂.zHat hj).1⟩⟩⟩
  have L := hs.vc.lay hF hp
  have hA := hs.a r hr j hj
  have hZ := hs.zHat hj
  refine WP.mono (mulAddAt_ok hP.s64 hP.mulAdd L hc hw.1 hA.1 hZ.1) fun s' ⟨hP', x', hq⟩ =>
    ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', ?_⟩
  rw [hA.2, hZ.2, hw.2] at hq
  show PolyIs _ _ _
  rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
  exact hq

theorem dot_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true r) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F1 p r p.ℓ)) (dot P p r) := by
  have hl := hF.l
  unfold dot
  refine (VG.Proof.MlDsa.AArch64.Verify.dot0_vpiece hP hF hr).seq ?_
  refine VPiece.mono (VPiece.seqR (I := fun j => VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F1 p r j)) (p.ℓ - 1) 1
    fun j h1 h2 => VG.Proof.MlDsa.AArch64.Verify.dotS_vpiece hP hF hr (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

theorem t1_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F1 p r p.ℓ)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F3 p r)) (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) := by
  have hc : rwChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (.x25, 32 + 320 * r) 320 (tmP p) 1024 = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := hF.pk; unfold rwChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := VG.Proof.MlDsa.AArch64.Verify.VTwo p S)
    (t1At_tr hP.unpackT1 (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.lx, h.ly, h.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂⟩
  have L := hs.vc.lay hF hp
  refine WP.mono (t1At_ok hP.s64 hP.unpackT1 L hc) fun s' ⟨hP', x', hq⟩ =>
    ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', L.keepPoly hP' (by
      have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; vlay) hw, ?_⟩
  rw [hs.vc.pkSlice (by rw [hF.pk]; omega)] at hq
  rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
  exact hq

theorem nttT_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F3 p r)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F4 p r)) (nttAt P (VG.Impl.MlDsa.AArch64.Call.sc oSS) (tmP p)) := by
  have hc : ipChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (tmP p) (VG.Impl.MlDsa.AArch64.Call.sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw, ht⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    Reduced x.mem (pa x (tmP p)) ∧ Reduced y.mem (pa y (tmP p)))
    (by unfold nttAt; exact ipAt_tr hP.ntt (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    unfold nttAt
    refine WP.mono (ipAt_ok hP.s64 hP.ntt L hc ht.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', L.keepPoly hP' (by
        have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; vlay) hw, ?_⟩
    rw [ht.2] at hq
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, _, t⟩ := h₁; exact t.1
  · obtain ⟨_, _, _, _, _, _, t⟩ := h₂; exact t.1

theorem mulT_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F4 p r)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F5 p r)) (mulAt P (tm2P p) (cP p) (tmP p)) := by
  have hc : mulChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (tm2P p) (cP p) (tmP p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold mulChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw, ht⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    (Reduced x.mem (pa x (cP p)) ∧ Reduced x.mem (pa x (tmP p))) ∧
    (Reduced y.mem (pa y (cP p)) ∧ Reduced y.mem (pa y (tmP p))))
    (mulAt_tr hP.mul (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    have hC := hs.c
    rw [ifp rfl] at hC
    refine WP.mono (mulAt_ok hP.s64 hP.mul L hc hC.1 ht.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', L.keepPoly hP' (by
        have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; vlay) hw, ?_⟩
    rw [hC.2, ht.2] at hq
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    exact hq
  · obtain ⟨_, _, _, _, hs, _, t⟩ := h₁; exact ⟨hs.c.1, t.1⟩
  · obtain ⟨_, _, _, _, hs, _, t⟩ := h₂; exact ⟨hs.c.1, t.1⟩

theorem sub_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F5 p r)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F6 p r)) (subAt P (wP p) (tm2P p)) := by
  have hc : accChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (wP p) (tm2P p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold accChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw, ht⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    (Reduced x.mem (pa x (wP p)) ∧ Reduced x.mem (pa x (tm2P p))) ∧
    (Reduced y.mem (pa y (wP p)) ∧ Reduced y.mem (pa y (tm2P p))))
    (by unfold subAt; exact accAt_tr (op := Spec.MlDsa.sub) hP.sub (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    unfold subAt
    refine WP.mono (accAt_ok (op := Spec.MlDsa.sub) hP.s64 hP.sub L hc hw.1 ht.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', ?_⟩
    rw [hw.2, ht.2] at hq
    show PolyIs _ _ _
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, w, t⟩ := h₁; exact ⟨w.1, t.1⟩
  · obtain ⟨_, _, _, _, _, w, t⟩ := h₂; exact ⟨w.1, t.1⟩

theorem inv_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F6 p r)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F7 p r)) (invNttAt P (VG.Impl.MlDsa.AArch64.Call.sc oSS) (wP p)) := by
  have hc : ipChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (wP p) (VG.Impl.MlDsa.AArch64.Call.sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    Reduced x.mem (pa x (wP p)) ∧ Reduced y.mem (pa y (wP p)))
    (by unfold invNttAt; exact ipAt_tr hP.invNtt (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    unfold invNttAt
    refine WP.mono (ipAt_ok hP.s64 hP.invNtt L hc hw.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', ?_⟩
    rw [hw.2] at hq
    show PolyIs _ _ _
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, w⟩ := h₁; exact w.1
  · obtain ⟨_, _, _, _, _, w⟩ := h₂; exact w.1

theorem uh_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F7 p r)) (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F8 p r)) (useHintAt P (VG.Impl.MlDsa.AArch64.Verify.hP p r) (wP p) p.γ₂ (w1P p)) := by
  have hc : useHintChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (VG.Impl.MlDsa.AArch64.Verify.hP p r) (wP p) (w1P p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold useHintChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    Reduced x.mem (pa x (wP p)) ∧ Reduced y.mem (pa y (wP p)))
    (useHintAt_tr hP.useHint (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc hF.g2.1 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    refine WP.mono (useHintAt_ok hP.s64 hP.useHint L hc hF.g2.1 hw.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchks hF (Nat.le_of_lt hr)) x', ?_⟩
    rw [VG.Proof.MlDsa.AArch64.Verify.hintRow_pa p s r, Proof.MlDsa.Verify.hintAt_row hs.hint hr, hw.2] at hq
    show natPolyAt _ _ = _
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, w⟩ := h₁; exact w.1
  · obtain ⟨_, _, _, _, _, w⟩ := h₂; exact w.1

omit hP hr in
theorem w1_bound {m : Mem} {a : Addr} {σ : State} {h : List (Vector Bool Spec.MlDsa.n)} {A' : Nat → Nat → VG.Spec.MlDsa.Poly}
    {c0 : VG.Spec.MlDsa.Poly} {r : Nat} (hq : NatPolyIs m a (w1Row p (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' (VG.Spec.MlDsa.ntt c0) h r)) :
    ∀ i < 256, (coeffAt m a i).toNat ≤ w1Max p := fun i hi => by
  have := congrArg (·[i]'hi) hq
  simp only [natPolyAt, Vector.getElem_ofFn, w1Row, Vector.getElem_zipWith] at this
  rw [this, hF.g2.2]
  exact Proof.MlDsa.Verify.useHint_le hF.g2.1 _ _

theorem sbpR_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.RowI p r (VG.Proof.MlDsa.AArch64.Verify.F8 p r)) (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true (r + 1))
    (simpleBitPackAt P (w1P p) (w1Max p) (VG.Proof.MlDsa.AArch64.Verify.rowP p r) (w1Len p)) := by
  have hc : rwChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (w1P p) 1024 (VG.Proof.MlDsa.AArch64.Verify.rowP p r) (w1Len p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
    rcases hF.wl with hw | hw <;> have hkw := hF.w1 <;> rw [hw] at hkw <;> (unfold rwChk; vlay [hw])
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.Verify.VTwo p S x y ∧
    (∀ i < 256, (coeffAt x.mem (pa x (w1P p)) i).toNat ≤ w1Max p) ∧
    (∀ i < 256, (coeffAt y.mem (pa y (w1P p)) i).toNat ≤ w1Max p))
    (sbpAt_tr hP.simpleBitPack (VG.Proof.MlDsa.AArch64.Verify.vOk p) hc hF.sbp fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.Verify.rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    refine WP.mono (sbpAt_ok hP.s64 hP.simpleBitPack L hc hF.sbp (VG.Proof.MlDsa.AArch64.Verify.w1_bound hF hw)) fun s' ⟨hP', x', hq⟩ => ?_
    have hs' := hs.keep hF hp hP' (by
      have : w1Len p * r + w1Len p ≤ p.k * w1Len p := by
        rw [← Nat.mul_succ, Nat.mul_comm p.k]; exact Nat.mul_le_mul_left _ hr
      scchks hF (Nat.le_of_lt hr)) x'
    refine ⟨h, A', c0, q, ⟨hs'.vc, hs'.hh, hs'.hint, hs'.nok, hs'.gd, hs'.a, hs'.z, hs'.c, fun r' hr' => ?_,
      hs'.x24⟩⟩
    rcases (by omega : r' < r ∨ r' = r) with hlt | rfl
    · exact hs'.rows r' hlt
    · rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), hq, hw]
  · obtain ⟨_, _, _, _, _, w⟩ := h₁; exact VG.Proof.MlDsa.AArch64.Verify.w1_bound hF w
  · obtain ⟨_, _, _, _, _, w⟩ := h₂; exact VG.Proof.MlDsa.AArch64.Verify.w1_bound hF w

theorem row_vpiece : VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true r) (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true (r + 1))
    (VG.Impl.MlDsa.AArch64.Verify.row P p r) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.row
  exact (VG.Proof.MlDsa.AArch64.Verify.dot_vpiece hP hF hr).seq ((VG.Proof.MlDsa.AArch64.Verify.t1_vpiece hP hF hr).seq ((VG.Proof.MlDsa.AArch64.Verify.nttT_vpiece hP hF hr).seq
    ((VG.Proof.MlDsa.AArch64.Verify.mulT_vpiece hP hF hr).seq ((VG.Proof.MlDsa.AArch64.Verify.sub_vpiece hP hF hr).seq ((VG.Proof.MlDsa.AArch64.Verify.inv_vpiece hP hF hr).seq
      ((VG.Proof.MlDsa.AArch64.Verify.uh_vpiece hP hF hr).seq (VG.Proof.MlDsa.AArch64.Verify.sbpR_vpiece hP hF hr)))))))

end

end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp`. -/
section

/-!
# ML-DSA verification on AArch64: the comparison of `c̃′` with `c̃`

`cmpAnd a b n` ORs the XORs of the `n` bytes at `a` and `b` into `x10`, then
ANDs `(x10 - 1) >> 63`, 1 exactly when they are equal, into `x24`
(`cmpAnd_ok`), without a branch on the bytes: its addresses and branches
depend only on the pointers (`cmp_taint`, in `Final.lean`).
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only wp_ldrb wp_eor wp_orr wp_addImm wp_subImm wp_lsr wp_movz wp_nil count_loop
  ptr_add ptr_zero)
open VG.Proof.MlKem.AArch64.Decaps (xor_zero_iff bytesAt_succ')
open VG.Spec.Sha3 (bytesAt)

theorem shr_val (x : BitVec 64) (h : x.toNat < 256) : (x - 1) >>> 63 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have h1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (by
      show (1 : BitVec 64).toNat ≤ x.toNat; exact h1)]
    show (x.toNat - 1) >>> 63 = 0
    rw [Nat.shiftRight_eq_div_pow]
    omega

/-- After `k` of the `n` bytes at `A` and `B`. -/
structure CI (A B : Addr) (n : Nat) (s : State) (k : Nat) (u : State) : Prop where
  keep : VG.Proof.MlKem.AArch64.Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s u
  mem : u.mem = s.mem
  x0 : u.gpr .x0 = A + BitVec.ofNat 64 k
  x1 : u.gpr .x1 = B + BitVec.ofNat 64 k
  x2 : (u.gpr .x2).toNat = n - k
  x10 : (u.gpr .x10).toNat < 256
  eq : u.gpr .x10 = 0 ↔ bytesAt s.mem A k = bytesAt s.mem B k

theorem cstep {A B : Addr} {n : Nat} {s : State} (hn : n < 2 ^ 32)
    (ha : InRegions (s.rd ++ s.wr) A n) (hb : InRegions (s.rd ++ s.wr) B n) {k : Nat} (hk : k < n)
    {u : State} (h : VG.Proof.MlDsa.AArch64.Verify.CI A B n s k u) :
    WP isa (.block cmpBody) u fun u' => VG.Proof.MlDsa.AArch64.Verify.CI A B n s (k + 1) u' ∧ ((u'.gpr .x2).toNat ≠ 0 ↔ k + 1 ≠ n) := by
  have in₁ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 k) 1 := by
    rw [h.keep.rd, h.keep.wr]; exact VG.CallLay.inRegions_sub ha (by omega) (by omega)
  have in₂ : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 k) 1 := by
    rw [h.keep.rd, h.keep.wr]; exact VG.CallLay.inRegions_sub hb (by omega) (by omega)
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) (by decide) (by rw [h.x0, ptr_zero]) in₁ fun u₁ g₁ v₁ => ?_
  refine wp_ldrb (a := B + BitVec.ofNat 64 k) (by decide) (by rw [g₁.get .x1, h.x1, ptr_zero])
    (by rw [g₁.rd, g₁.wr]; exact in₂) fun u₂ g₂ v₂ => ?_
  refine wp_eor fun u₃ g₃ v₃ => wp_orr fun u₄ g₄ v₄ => wp_addImm (by decide) fun u₅ g₅ v₅ =>
    wp_addImm (by decide) fun u₆ g₆ v₆ => wp_subImm (by decide) fun u₇ g₇ v₇ => wp_nil ?_
  have o₇ : Only [.x0, .x1, .x2, .x9, .x10, .x11] u u₇ :=
    ((((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).trans g₆).trans g₇).mono
  have m₁ : u₁.mem = s.mem := by rw [g₁.mem, h.mem]
  have x9 : u₃.gpr .x9 = (s.mem (A + BitVec.ofNat 64 k)).setWidth 64 ^^^
      (s.mem (B + BitVec.ofNat 64 k)).setWidth 64 := by
    rw [v₃, g₂.get .x9, v₁, v₂, m₁, h.mem]
  have x10 : u₇.gpr .x10 = u.gpr .x10 ||| u₃.gpr .x9 := by
    rw [g₇.get .x10, g₆.get .x10, g₅.get .x10, v₄, g₃.get .x10, g₂.get .x10, g₁.get .x10]
  have x2 : u₇.gpr .x2 = u.gpr .x2 - BitVec.ofNat 64 1 := by
    rw [v₇, g₆.get .x2, g₅.get .x2, g₄.get .x2, g₃.get .x2, g₂.get .x2, g₁.get .x2]
  have hx2 : (u₇.gpr .x2).toNat = n - (k + 1) := by
    rw [x2, BitVec.toNat_sub_of_le (show (BitVec.ofNat 64 1).toNat ≤ (u.gpr .x2).toNat by
      rw [h.x2, BitVec.toNat_ofNat]; omega), h.x2, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨h.keep.trans o₇.keep |>.mono, by rw [o₇.mem, h.mem], ?_, ?_, hx2, ?_, ?_⟩, by rw [hx2]; omega⟩
  · rw [g₇.get .x0, g₆.get .x0, v₅, g₄.get .x0, g₃.get .x0, g₂.get .x0, g₁.get .x0, h.x0, ptr_add]
  · rw [g₇.get .x1, v₆, g₅.get .x1, g₄.get .x1, g₃.get .x1, g₂.get .x1, g₁.get .x1, h.x1, ptr_add]
  · rw [x10, BitVec.toNat_or, x9, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have a := (s.mem (A + BitVec.ofNat 64 k)).isLt
    have b := (s.mem (B + BitVec.ofNat 64 k)).isLt
    have c := h.x10
    exact Nat.or_lt_two_pow (n := 8) c (Nat.xor_lt_two_pow (by omega) (by omega))
  · have e1 : u.gpr .x10 ||| u₃.gpr .x9 = 0 ↔ u.gpr .x10 = 0 ∧ u₃.gpr .x9 = 0 := BitVec.or_eq_zero_iff
    rw [x10, e1, h.eq, x9, xor_zero_iff, bytesAt_succ', bytesAt_succ']
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro e
      obtain ⟨h1, h2⟩ := List.append_inj e (by rw [Proof.MlKem.bytesAt_length, Proof.MlKem.bytesAt_length])
      exact ⟨h1, List.head_eq_of_cons_eq h2⟩

theorem cmpAnd_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a b : Ptr} {n : Nat}
    (hn : 0 < n) (hn' : n < 65536) (ha : VG.CallLay.inB (rbs ++ wbs) a n = true) (hb : VG.CallLay.inB (rbs ++ wbs) b n = true) :
    WP isa (cmpAnd a b n) s fun s' => PPostB S s s' [] ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&&
        (if bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n then (1 : BitVec 64) else 0).setWidth 32).setWidth 64 := by
  have hA := L.inR ha
  have hB := L.inR hb
  have hok : ∀ x ∈ [(Reg.x0, Arg.ptr a), (.x1, .ptr b), (.x2, .imm n)], x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    exacts [⟨ptr_ok (L.ptrBs ha), .inl rfl⟩, ⟨ptr_ok (L.ptrBs hb), .inr (.inl rfl)⟩, ⟨trivial, .inr (.inr (.inl rfl))⟩]
  unfold cmpAnd
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s₁ h₁ => wp_movz fun s₂ h₂ e₂ => wp_nil ?_
  have a0 := Args.r0 h₁; have a1 := Args.r1 h₁; have a2 := Args.r2 h₁
  have k₂ : VG.Proof.MlKem.AArch64.Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s s₂ :=
    (h₁.2.trans h₂.keep).mono (by decide)
  have c₀ : VG.Proof.MlDsa.AArch64.Verify.CI (pa s a) (pa s b) n s 0 s₂ :=
    ⟨k₂, by rw [h₂.mem, h₁.1.2], by rw [h₂.get .x0, a0, ptr_zero]; rfl, by rw [h₂.get .x1, a1, ptr_zero]; rfl,
      by rw [h₂.get .x2, a2]; simp only [Arg.val, BitVec.toNat_ofNat]; omega, by rw [e₂]; decide,
      by rw [e₂]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (count_loop (cr := .x2) hn (VG.Proof.MlDsa.AArch64.Verify.CI (pa s a) (pa s b) n s)
    (fun k hk u h => VG.Proof.MlDsa.AArch64.Verify.cstep (by omega) hA hB hk h) c₀) fun s₃ h₃ => ?_)
  refine wp_subImm (by decide) fun s₄ h₄ e₄ => wp_lsr (by decide) fun s₅ h₅ e₅ =>
    wp_and32 fun s₆ h₆ e₆ => wp_nil ?_
  have o₆ : Only [.x10, .x24] s₃ s₆ := ((h₄.trans h₅).trans h₆).mono
  have k₆ : VG.Proof.MlKem.AArch64.Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x24] s s₆ :=
    (h₃.keep.trans o₆.keep).mono (by decide)
  refine ⟨postB_of_keep k₆ (by decide) (by rw [o₆.mem, h₃.mem]; exact Frame.refl _ _), ?_⟩
  have x24 : s₅.gpr .x24 = s.gpr .x24 := by
    rw [h₅.get .x24 (by decide), h₄.get .x24 (by decide), h₃.keep.gpr .x24 (by decide)]
  have x10 : s₅.gpr .x10 = (s₃.gpr .x10 - 1) >>> 63 := by rw [e₅, e₄]; rfl
  rw [e₆, x24, x10, VG.Proof.MlDsa.AArch64.Verify.shr_val _ h₃.x10]
  have he := h₃.eq
  by_cases e : bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n
  · rw [ite_eq_left (he.mpr e), ite_eq_left e]
  · rw [ite_eq_right (fun h => e (he.mp h)), ite_eq_right e]

end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final`. -/
section

/-!
# ML-DSA verification on AArch64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`c̃′ = H(μ ‖ w1Encode(w′₁))` (`hash_vpiece`) and its comparison with `c̃`
(`cmp_vpiece`); the function, piece by piece (`verify_vpiece`): a malformed
hint returns 0 at once, a `z` too large after the norms, and otherwise `x24`
holds the result of the samplers and then of the comparison. For primitives
`P` that meet their contracts (`PrimsOk`), `verify P p` meets `verifyContract
p` (`verify_verified`): it is correct, and leaks only its inputs, which the
contract makes public.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs HintIs Bounds minBounds rejNTTPoly sampleInBall
  simpleBitPack verifyMu normRq normR)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (w1Row aSeed)

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vMu σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ)

/-- At the end, before the epilogue: the result in `x24`. -/
def VFin (p : Params) (σ s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Verify.VC p σ s ∧ ((s.gpr .x24 = 1 ∧ ∃ b, VG.Proof.MlDsa.AArch64.Verify.vv p σ b = some true) ∨ (s.gpr .x24 = 0 ∧ VG.Proof.MlDsa.AArch64.Verify.vv p σ minBounds ≠ some true))

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : VG.Proof.MlDsa.AArch64.Verify.vv p σ b = some false) : VG.Proof.MlDsa.AArch64.Verify.vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := Proof.MlDsa.Verify.verifyMu_mono (Proof.MlDsa.Verify.bmax_left b minBounds).rejNTT
      (Proof.MlDsa.Verify.bmax_left b minBounds).ball h
    have e₂ := Proof.MlDsa.Verify.verifyMu_mono (Proof.MlDsa.Verify.bmax_right b minBounds).rejNTT
      (Proof.MlDsa.Verify.bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

/-! ## The hash -/

/-- `w1Encode(w′₁)`. -/
abbrev w1Enc (p : Params) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → VG.Spec.MlDsa.Poly) (c0 : VG.Spec.MlDsa.Poly) :
    List Byte :=
  (List.range p.k).flatMap fun r => VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) A' (VG.Spec.MlDsa.ntt c0) h r) (w1Max p)

/-- After the hash. -/
abbrev SCH (p : Params) (σ s : State) : Prop :=
  ∃ h A' c0 q, VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q p.ℓ true p.k s ∧
    bytesAt s.mem (pa s (sc oCT)) p.ctildeLen = Spec.MlDsa.H (VG.Proof.MlDsa.AArch64.Verify.vMu σ ++ VG.Proof.MlDsa.AArch64.Verify.w1Enc p σ h A' c0) p.ctildeLen

/-- The input pieces of the hash. -/
abbrev hIns (p : Params) : List Impl.MlKem.AArch64.Piece :=
  [⟨.x26, 0, 64⟩, ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩]

theorem hash_chk {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) : hashChk (VG.Proof.MlDsa.AArch64.Verify.vR p) (VG.Proof.MlDsa.AArch64.Verify.vW p) (VG.Proof.MlDsa.AArch64.Verify.hIns p) ⟨.x28, oCT, p.ctildeLen⟩ = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := hF.ct.2; have := hF.w1
  unfold hashChk pieceChk; vlay

theorem hash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, x.gpr r = y.gpr r) →
      RelCT isa P ((shake256With keccak.callee) (VG.Proof.MlDsa.AArch64.Verify.hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaVerifyHashTaint p hp
  exact VectorTaint.relRegs VG.Proof.MlDsa.AArch64.KeyGen.bases hr hh

theorem cmp_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, x.gpr r = y.gpr r) →
      RelCT isa P (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) fun _ _ => True := by
  intro P hr
  rcases hp with rfl | rfl | rfl
  · exact taintRel VG.Proof.MlDsa.AArch64.KeyGen.bases hr (by taint_decide)
  · exact taintRel VG.Proof.MlDsa.AArch64.KeyGen.bases hr (by taint_decide)
  · exact taintRel VG.Proof.MlDsa.AArch64.KeyGen.bases hr (by taint_decide)

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.AArch64.Verify.flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem rows_bytes {p : Params} {σ : State} {h : List (Vector Bool Spec.MlDsa.n)} {A' : Nat → Nat → VG.Spec.MlDsa.Poly} {c0 : VG.Spec.MlDsa.Poly}
    {q : Bool} {s : State} (hs : VG.Proof.MlDsa.AArch64.Verify.SC p σ h A' c0 q p.ℓ true p.k s) :
    Proof.MlKem.AArch64.pbytes s ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩ = VG.Proof.MlDsa.AArch64.Verify.w1Enc p σ h A' c0 := by
  show bytesAt s.mem (s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + 0))) (p.k * w1Len p) = _
  rw [show p.k * w1Len p = w1Len p * p.k from Nat.mul_comm _ _, Proof.MlDsa.KeyGen.bytesAt_pieces]
  exact VG.Proof.MlDsa.AArch64.Verify.flatMap_congr' fun r hr => hs.rows r (List.mem_range.mp hr)

theorem hash_vpiece {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true p.k) (VG.Proof.MlDsa.AArch64.Verify.SCH p) ((shake256With keccak.callee) (VG.Proof.MlDsa.AArch64.Verify.hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := VG.Proof.MlDsa.AArch64.Verify.VTwo p S) (VG.Proof.MlDsa.AArch64.Verify.hash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  refine WP.mono (shake_ok h16 hSl L (by simp) (VG.Proof.MlDsa.AArch64.Verify.hash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨h, A', c0, q, ?_, ?_⟩
  · exact hs.keep hF hp hP' (by scchks hF (Nat.le_refl _)) x'
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), ho, VG.Proof.MlDsa.AArch64.Verify.rows_bytes hs]
    refine congrArg (Spec.MlDsa.H · p.ctildeLen) (congrArg (· ++ _) ?_)
    show bytesAt s.mem (s.gpr .x26 + BitVec.ofNat 64 0) 64 = _
    exact hs.vc.mu

/-! ## The comparison -/

theorem cmp_vpiece {S : Nat} {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.SCH p) (VG.Proof.MlDsa.AArch64.Verify.VFin p) (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hH⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := VG.Proof.MlDsa.AArch64.Verify.VTwo p S) (VG.Proof.MlDsa.AArch64.Verify.cmp_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  have := hF.ct.2; have := hF.sig; have := hF.scr; have := hF.k; have := hF.l; have := hF.kl
  refine WP.mono (VG.Proof.MlDsa.AArch64.Verify.cmpAnd_ok L (by omega) (by omega) (by vlay) (by vlay)) fun s' ⟨hP', x'⟩ => ⟨?_, ?_⟩
  · exact hs.vc.step hF hp hP' (by unfold VG.Proof.MlDsa.AArch64.Verify.vcChk; vlay)
  · rw [hH, VG.Proof.MlDsa.AArch64.Verify.ctOf_eq hF hs.vc, hs.x24] at x'
    have e : s'.gpr .x24 = VG.Proof.MlDsa.AArch64.Verify.flag (q = true ∧ Spec.MlDsa.H (VG.Proof.MlDsa.AArch64.Verify.vMu σ ++ VG.Proof.MlDsa.AArch64.Verify.w1Enc p σ h A' c0) p.ctildeLen = VG.Proof.MlDsa.AArch64.Verify.ctOf p σ) := by
      rw [x', VG.Proof.MlDsa.AArch64.Verify.and_flag (P := q = true)
        (Q := Spec.MlDsa.H (VG.Proof.MlDsa.AArch64.Verify.vMu σ ++ VG.Proof.MlDsa.AArch64.Verify.w1Enc p σ h A' c0) p.ctildeLen = VG.Proof.MlDsa.AArch64.Verify.ctOf p σ) _ (by split <;> rfl)]
    obtain ⟨hA1, hA0⟩ := hs.gd
    cases q with
    | false =>
      refine .inr ⟨by rw [e]; exact ifn (fun h => Bool.false_ne_true h.1) _ _, ?_⟩
      rcases hA0 rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ hs.hh hr hc hn']; nofun
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_ball_none minBounds _ _ hs.hh (Option.map_eq_none_iff.mp hn')]; nofun
    | true =>
      obtain ⟨hA, hB⟩ := hA1 rfl
      obtain ⟨nA, hnA⟩ := Proof.MlDsa.Verify.common_bound (P := fun r n => ∀ c < p.ℓ,
          rejNTTPoly n (aSeed (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r c) = some (A' r c))
        (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
          Proof.MlDsa.Verify.common_bound (P := fun c n => rejNTTPoly n (aSeed (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) r c) = some (A' r c))
            (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc =>
              let ⟨b, hb⟩ := hA r hr c hc; ⟨b.rejNTT, hb⟩
      obtain ⟨bB, hbB⟩ := hB
      obtain ⟨cc, hcc, hcc'⟩ := Option.map_eq_some_iff.mp hbB
      have hl : h.length = p.k := hs.hint.1
      have ev := Proof.MlDsa.Verify.verifyMu_rows p ⟨0, 0, nA, bB.ball⟩ (VG.Proof.MlDsa.AArch64.Verify.vPk p σ) (VG.Proof.MlDsa.AArch64.Verify.vMu σ) (VG.Proof.MlDsa.AArch64.Verify.vSig p σ) hs.hh hl hnA
        hcc
      rw [decide_eq_true ((Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1 _).mpr hs.nok), hcc', Bool.true_and,
        ← hF.g2.2] at ev
      by_cases hE : Spec.MlDsa.H (VG.Proof.MlDsa.AArch64.Verify.vMu σ ++ VG.Proof.MlDsa.AArch64.Verify.w1Enc p σ h A' c0) p.ctildeLen = VG.Proof.MlDsa.AArch64.Verify.ctOf p σ
      · exact .inl ⟨by rw [e]; exact ifp (show true = true ∧ _ from ⟨rfl, hE⟩) _ _, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
      · exact .inr ⟨by rw [e]; exact ifn (fun h : true = true ∧ _ => hE h.2) _ _,
          VG.Proof.MlDsa.AArch64.Verify.false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

/-! ## The function -/

theorem compute_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VB p) (VG.Proof.MlDsa.AArch64.Verify.VFin p) ((computeWith keccak.callee) P p) := by
  unfold computeWith
  refine VPiece.seq (J := VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ false 0) ?_ ((VG.Proof.MlDsa.AArch64.Verify.nttC_vpiece hP hF).seq (VPiece.seq (J := VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true p.k) ?_
    ((VG.Proof.MlDsa.AArch64.Verify.hash_vpiece hP.s16 hP.s64 hF).seq (VG.Proof.MlDsa.AArch64.Verify.cmp_vpiece hF))))
  · refine VPiece.mono (VPiece.seqR (I := fun i => VG.Proof.MlDsa.AArch64.Verify.SCx p i false 0) p.ℓ 0 fun i _ hi => VG.Proof.MlDsa.AArch64.Verify.nttZ_vpiece hP hF (by omega))
      (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Verify.vb_sc h) fun _ _ _ h => ?_
    simpa using h
  · refine VPiece.mono (VPiece.seqR (I := fun r => VG.Proof.MlDsa.AArch64.Verify.SCx p p.ℓ true r) p.k 0 fun r _ hr => VG.Proof.MlDsa.AArch64.Verify.row_vpiece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem normOk_zero (p : Params) (σ : State) : VG.Proof.MlDsa.AArch64.Verify.normOk p σ 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem body_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => VG.Proof.MlDsa.AArch64.Verify.VC p σ s ∧ s.gpr .x24 = 1) (VG.Proof.MlDsa.AArch64.Verify.VFin p) ((bodyWith keccak.callee) P p) := by
  unfold bodyWith
  refine (VG.Proof.MlDsa.AArch64.Verify.hint_vpiece hP hF).seq (VPiece.ifOk (T := fun σ => (VG.Proof.MlDsa.AArch64.Verify.hintOf p σ).isSome = true)
    (fun _ _ _ h => h.2.1) (fun _ _ _ _ pub => by rw [VG.Proof.MlDsa.AArch64.Verify.hintOf, VG.Proof.MlDsa.AArch64.Verify.hintOf, (VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine VPiece.seq (J := VG.Proof.MlDsa.AArch64.Verify.Z0 p p.ℓ) ?_ (VPiece.ifOk (T := fun σ => VG.Proof.MlDsa.AArch64.Verify.normOk p σ p.ℓ) (fun _ _ _ h => h.2)
      (fun _ _ _ _ pub => by simp only [VG.Proof.MlDsa.AArch64.Verify.normOk, VG.Proof.MlDsa.AArch64.Verify.zOf, (VG.Proof.MlDsa.AArch64.Verify.vPub_eq pub).2.2.2.1]) ((VG.Proof.MlDsa.AArch64.Verify.samples_vpiece hP hF).seq
        (VG.Proof.MlDsa.AArch64.Verify.compute_vpiece hP hF)) fun σ s _ h hn => ⟨h.1.vc, .inr ⟨by rw [h.2]; exact ifn hn _ _, ?_⟩⟩)
    · refine VPiece.mono (VPiece.seqR (I := fun j => VG.Proof.MlDsa.AArch64.Verify.Z0 p j) p.ℓ 0 fun j _ hj => VG.Proof.MlDsa.AArch64.Verify.zOne_vpiece hP hF (by omega))
        (fun σ s _ ⟨⟨hv, hx, hH⟩, ht⟩ => ⟨⟨hv, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩, ?_⟩) fun _ _ _ h => ?_
      · obtain ⟨hh, e⟩ := Option.isSome_iff_exists.mp ht
        exact ⟨hh, e, hH hh e⟩
      · rw [hx]; exact VG.Proof.MlDsa.AArch64.Verify.flag_congr (iff_of_true ht (VG.Proof.MlDsa.AArch64.Verify.normOk_zero p σ))
      · simpa using h
    · obtain ⟨hh, e, _⟩ := h.1.hint
      show verifyMu p minBounds _ _ _ ≠ some true
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1]; exact hn)
  · intro σ s _ h hn
    refine ⟨h.1, .inr ⟨by rw [h.2.1]; exact ifn hn _ _, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

theorem epi_vpiece {S : Nat} {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (VG.Proof.MlDsa.AArch64.Verify.VFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p AArch64.abi S).post σ s)
      (.block VG.Impl.MlDsa.AArch64.KeyGen.epi) := by
  refine ⟨fun σ s hp ⟨hv, hr⟩ => ?_, VG.Proof.MlDsa.AArch64.Verify.vrel_of (Q := VG.Proof.MlDsa.AArch64.Verify.VTwo p S) (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.AArch64.Verify.vc_two hF p₁ p₂ pub h₁.1 h₂.1⟩
  have L := hv.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := hF.scr; have := hF.k; vlay)
    rwa [pa, hv.top.x28] at this
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.epi_ok hv.top hin) fun s' ⟨ha, hx, _⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  rcases hr with ⟨e, hb⟩ | ⟨e, hb⟩
  · exact .inl ⟨by rw [hx, e]; rfl, hb⟩
  · exact .inr ⟨by rw [hx, e]; rfl, hb⟩

theorem verify_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.Verify.VFacts p) :
    VG.Proof.MlDsa.AArch64.Verify.VPiece p S (fun σ s => s = σ)
      (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p AArch64.abi S).post σ s) ((verifyWith keccak.callee) P p) :=
  (VG.Proof.MlDsa.AArch64.Verify.pro_vpiece hF).seq ((VG.Proof.MlDsa.AArch64.Verify.body_vpiece hP hF).seq (VG.Proof.MlDsa.AArch64.Verify.epi_vpiece hF))

/-- `vg_mldsa*_verify` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls that use at most `S`
bytes of stack, if the contract is satisfiable. -/
theorem verify_verified {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : ∃ s, (Spec.MlDsa.verifyContract p AArch64.abi S).pre s) :
    Verified AArch64.target ((verifyWith keccak.callee) P p) (Spec.MlDsa.verifyContract p AArch64.abi S) :=
  ⟨fun σ hσ => (VG.Proof.MlDsa.AArch64.Verify.verify_vpiece hP (VG.Proof.MlDsa.AArch64.Verify.vfacts hp)).ok σ σ hσ rfl,
    relStart (Q := fun _ _ => True) (VG.Proof.MlDsa.AArch64.Verify.verify_vpiece hP (VG.Proof.MlDsa.AArch64.Verify.vfacts hp)).tr, hsat⟩

end VG.Proof.MlDsa.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst`. -/
section

/-!
# ML-DSA verification on AArch64, with this library's primitives

Verification with the AArch64 implementations of the primitives (`prims_ok`)
is verified with 16 bytes of stack (`verify44_verified`, …).
-/

namespace VG.Proof.MlDsa.AArch64.Verify

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen (prims_okWith scrLen)

/-- A state satisfying `verifyContract`'s precondition. -/
def vSat (p : Spec.MlDsa.Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x20000 | .x3 => 0x100000 | _ => 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x10000, 64⟩, ⟨0x20000, p.sigLen⟩]
  wr := [⟨0x100000, scrLen p⟩]

theorem verify_sat (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∃ s, (Spec.MlDsa.verifyContract p AArch64.abi 16).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨VG.Proof.MlDsa.AArch64.Verify.vSat Spec.MlDsa.mlDsa44, ?_⟩
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨VG.Proof.MlDsa.AArch64.Verify.vSat Spec.MlDsa.mlDsa65, ?_⟩
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨VG.Proof.MlDsa.AArch64.Verify.vSat Spec.MlDsa.mlDsa87, ?_⟩
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]

theorem verify44_verifiedWith :
    Verified AArch64.target (verify44With keccak.callee) (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Verify.verify_verified (keccak := keccak) (prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa44 (.inl rfl) (VG.Proof.MlDsa.AArch64.Verify.verify_sat _ (.inl rfl))

theorem verify65_verifiedWith :
    Verified AArch64.target (verify65With keccak.callee) (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Verify.verify_verified (keccak := keccak) (prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa65 (.inr (.inl rfl)) (VG.Proof.MlDsa.AArch64.Verify.verify_sat _ (.inr (.inl rfl)))

theorem verify87_verifiedWith :
    Verified AArch64.target (verify87With keccak.callee) (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Verify.verify_verified (keccak := keccak) (prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa87 (.inr (.inr rfl)) (VG.Proof.MlDsa.AArch64.Verify.verify_sat _ (.inr (.inr rfl)))

theorem verify44_verified :
    Verified AArch64.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Verify.verify44_verifiedWith (keccak := .scalar)

theorem verify65_verified :
    Verified AArch64.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Verify.verify65_verifiedWith (keccak := .scalar)

theorem verify87_verified :
    Verified AArch64.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Verify.verify87_verifiedWith (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.Verify

end
