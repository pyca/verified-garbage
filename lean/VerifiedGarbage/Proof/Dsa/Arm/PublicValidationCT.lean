module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationABI
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PublicValidationContract

/-! # The validator's constant-time ABI contract -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Impl.Dsa.Layout
open VG.Proof.Dsa.PublicValidation (component)

def values (s : State) (pLen qLen : Nat) : Pointer → Nat
  | .input .p => component s.mem (key s) 0 pLen
  | .input .q => component s.mem (key s) pLen qLen
  | .input .g => component s.mem (key s) (pLen + qLen) pLen
  | .input .y => component s.mem (key s) (2 * pLen + qLen) pLen
  | _ => 0

theorem keyInputs {s : State} {pLen qLen : Nat} (H : (armContract pLen qLen).pre s) :
    ∀ i ∈ inputs pLen qLen, Input s (ws s) (size s) i.1 i.2 (values s pLen qLen i.1) := by
  obtain ⟨_, hk, pp, pq, pg, py, _⟩ := H.2.2.2.2.2
  change 3 * pLen + qLen ≤ keyLen s at hk
  intro i hi
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact keyInput (offset := 0) H (by decide) (by omega) (by simpa only [layout, BitVec.add_zero] using pp)
  · exact keyInput H (by decide) (by omega) pq
  · exact keyInput H (by decide) (by omega) pg
  · exact keyInput H (by decide) (by omega) py

theorem domain {s : State} {pLen qLen : Nat} (H : (armContract pLen qLen).pre s) :
    DomainOk (values s pLen qLen (.input .p)) (values s pLen qLen (.input .q)) :=
  let D := H.2.2.2.2.2.2.2.2.2.2.2
  ⟨D.1, D.2.1, D.2.2.1, D.2.2.2⟩

theorem ct {pLen qLen nP nQ : Nat} (wp : Width pLen nP) (wq : Width qLen nQ)
    (qp : qLen ≤ pLen) (q32 : qLen ≤ 32) :
    ConstantTime isa (armContract pLen qLen).pre (armContract pLen qLen).pub (body pLen qLen) := by
  apply SameTrace.constantTime
  intro s₁ s₂ H₁ H₂ Pub
  have B : ws s₂ = ws s₁ := congrArg State.addr Pub.2.1.symm
  have K : key s₁ = key s₂ := congrArg State.addr Pub.2.2.2.1
  have E₂ : Pow.Entry s₂ (ws s₁) (size s₂) := B ▸ entry H₂
  have I₂ : ∀ i ∈ inputs pLen qLen, Input s₂ (ws s₁) (size s₂) i.1 i.2 (values s₂ pLen qLen i.1) := B ▸ keyInputs H₂
  refine body_trace (entry H₁) E₂ (by have H := H₁.2.2.2.2.2.1; change 15713 ≤ size s₁ at H; omega)
    (by have H := H₂.2.2.2.2.2.1; change 15713 ≤ size s₂ at H; omega)
    wp wq qp q32 (keyInputs H₁) I₂ ?_ (domain H₁) (domain H₂)
  intro i hi
  obtain ⟨_, _, pp₁, pq₁, pg₁, py₁, _⟩ := H₁.2.2.2.2.2
  obtain ⟨_, _, pp₂, pq₂, pg₂, py₂, _⟩ := H₂.2.2.2.2.2
  rw [B, ← K] at pp₂ pq₂ pg₂ py₂
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> unfold PtrEq pointerValue <;>
    apply BitVec.eq_of_toNat_eq
  · exact pp₁.trans pp₂.symm
  · exact pq₁.trans pq₂.symm
  · exact pg₁.trans pg₂.symm
  · exact py₁.trans py₂.symm

end VG.Proof.Dsa.Arm.PublicValidation
