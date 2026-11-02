module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPartCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # What the stage's timing may depend on

Its arguments, the stack pointer, p, q and the h tape determine the
generator search's plan, and so everything the stage's timing depends on. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorPlan GeneratorSearchPlan ValidatePublic PackPublic)

variable {pLen : Nat}

/-- The plan, and the separation of the domain check's workspace. -/
structure StagePublic where
  plan : GeneratorSearchPlan
  checkFrame : (⟨plan.core.F, frameBytes⟩ : Region).Disjoint ⟨off plan.core.B domainCheck, Impl.Dsa.Layout.usedBytes⟩
  checkHash : (⟨plan.core.S, oRsa⟩ : Region).Disjoint ⟨off plan.core.B domainCheck, Impl.Dsa.Layout.usedBytes⟩

theorem StagePublic.ext {a b : StagePublic} (h : a.plan = b.plan) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

def publicOf (hb : Supported pLen) {s : State} (A : StageABI pLen s) : StagePublic :=
  ⟨plan hb A, A.framePart hb (StageABI.domainCheck_room hb),
    A.parts hb (used_small hb (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide))
      (StageABI.domainCheck_room hb) (Or.inl (by decide))⟩

/-- The status the search leaves. -/
abbrev StagePublic.status (P : StagePublic) : BitVec 64 := statusOf P.plan

def StagePublic.pack (P : StagePublic) : PackPublic := ⟨P.plan.core.B, P.plan.core.F, P.plan.core.S⟩

/-- The domain check, with the domain the search finds. -/
def StagePublic.validate (hb : Supported pLen) (P : StagePublic) : ValidatePublic where
  input := ⟨off P.plan.core.B domainCheck, pLen, qLen pLen,
    Spec.Dsa.encodeParams pLen (qLen pLen) ⟨Spec.Dsa.decodeBE P.plan.core.pb, P.plan.q, gOf P.plan⟩, hb.lengths,
    VG.Proof.Dsa.Generation.encodeParams_length _ _ _⟩
  B := P.plan.core.B
  F := P.plan.core.F
  S := P.plan.core.S
  base := rfl
  frame := P.checkFrame
  hash := P.checkHash

theorem GeneratorPlan.ext' {a b : GeneratorPlan} (hB : a.B = b.B) (hA : a.A = b.A) (hF : a.F = b.F)
    (hS : a.S = b.S) (hp : a.hp = b.hp) (hZ : a.Z = b.Z) (hl : a.len = b.len) (hpb : a.pb = b.pb)
    (hhb : a.hb = b.hb) (heb : a.eb = b.eb) : a = b := by
  cases a; cases b
  simp only at hB hA hF hS hp hZ hl hpb hhb heb
  subst hB hA hF hS hp hZ hl hpb hhb heb
  rfl

theorem GeneratorSearchPlan.ext' {a b : GeneratorSearchPlan} (hc : a.core = b.core) (hs : a.saved = b.saved)
    (ht : a.tape = b.tape) (hp : a.tapePtr = b.tapePtr) (hq : a.q = b.q) : a = b := by
  cases a; cases b
  simp only at hc hs ht hp hq
  subst hc hs ht hp hq
  rfl

/-- What the contract makes public. -/
structure View where
  x0 : Addr
  x1 : Addr
  x2 : Addr
  x3 : Addr
  sp : Addr
  p : Nat
  q : Nat
  tape : List Byte

def view (pLen : Nat) (s : State) : View :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.sp, pOf pLen s.mem (s.gpr .x0), qOf pLen s.mem (s.gpr .x0), tape s⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem view_of_pub {s₁ s₂ : State} (h : (contract pLen).pub s₁ s₂) : view pLen s₁ = view pLen s₂ := by
  sig_pub [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
  obtain ⟨hp, hl⟩ := List.cons.inj hl
  obtain ⟨hq, hr⟩ := List.cons.inj hl
  have hr' := map_toNat_inj hr
  simp only [view, View.mk.injEq]
  exact ⟨h0, h1, h2, h3, hsp, hp, hq, hr'⟩

/-- p's bytes, from its value. -/
theorem pBytes_eq {s : State} : pBytes pLen s = Spec.Dsa.encodeBE pLen (pOf pLen s.mem (s.gpr .x0)) := by
  have := VG.Proof.Dsa.encodeBE_decodeBE (pBytes pLen s)
  rw [bytesAt_length] at this
  exact this.symm

theorem publicOf_eq (hb : Supported pLen) {s₁ s₂ : State} (A₁ : StageABI pLen s₁) (A₂ : StageABI pLen s₂)
    (hv : view pLen s₁ = view pLen s₂) : publicOf hb A₁ = publicOf hb A₂ := by
  simp only [view, View.mk.injEq] at hv
  obtain ⟨h0, -, h2, h3, hsp, hp, hq, ht⟩ := hv
  have he : ∀ {s : State} (A : StageABI pLen s), eBytes pLen s =
      Spec.Dsa.encodeBE pLen ((pOf pLen s.mem (s.gpr .x0) - 1) / qOf pLen s.mem (s.gpr .x0)) := fun A => A.exponent
  apply StagePublic.ext
  apply GeneratorSearchPlan.ext'
  · apply GeneratorPlan.ext'
    all_goals simp only [publicOf, plan, Arena.generatorPlan, arena]
    all_goals first
      | rw [h0]
      | rw [pBytes_eq, pBytes_eq, hp]
      | rw [he A₁, he A₂, hp, hq]
      | simp only [frameBase, hsp]
  · simp only [publicOf, plan, h0, h2, h3]
  · simp only [publicOf, plan]; exact ht
  · simp only [publicOf, plan, h2]
  · simp only [publicOf, plan, hq]

end VG.Proof.Dsa.AArch64.Generator
