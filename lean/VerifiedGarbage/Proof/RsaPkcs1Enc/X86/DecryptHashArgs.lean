module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPlan

/-! # Complete argument preparation for SHA-256 and HMAC updates -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def shaInitPlan (_ : Nat) : CallArg := .scratch sSt

def shaUpdatePlan : Nat → CallArg
  | 0 => .scratch sSt | 1 | 2 => .value 0 | 3 => .scratch sD | 4 => .input 4 | _ => .scratch sHash

def shaFinalizePlan : Nat → CallArg
  | 0 => .scratch sSt | 1 => .input 4 | 2 => .value 0 | 3 => .scratch sDH | _ => .scratch sHash

def macInitPlan (key : Nat) : Nat → CallArg
  | 0 => .scratch sSt | 1 => .scratch sOuter | 2 => .scratch key | 3 => .value 32 | _ => .scratch sHash

def kdkUpdatePlan : Nat → CallArg
  | 0 => .scratch sSt | 1 => .value 64 | 2 => .value 0 | 3 => .input 9 | 4 => .input 4 | _ => .scratch sHash

def prfUpdatePlan (len : Nat) : Nat → CallArg
  | 0 => .scratch sSt | 1 => .value 64 | 2 => .value 0 | 3 => .scratch sMsg | 4 => .value len | _ => .scratch sHash

def Prepared (g : Geometry) (bs : Fin 9 → List Byte) (plan : Nat → CallArg) (n : Nat)
    (s t : State) : Prop := Context g bs t ∧ Arguments g (fun j => (plan j).valueAt g) n t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t

theorem shaInitArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block shaInitArgs) s (Prepared g bs shaInitPlan 1 s) := by
  have code : shaInitArgs = (List.range 1).flatMap fun j => (shaInitPlan j).code j := rfl
  rw [code]
  exact plan_ok h _ 1 (by decide) (by intro j hj; trivial)

theorem shaUpdArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block shaUpdArgs) s (Prepared g bs shaUpdatePlan 6 s) := by
  have code : shaUpdArgs = (List.range 6).flatMap fun j => (shaUpdatePlan j).code j := rfl
  rw [code]
  apply plan_ok h _ 6 (by decide)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [shaUpdatePlan, CallArg.valid]

theorem shaFinArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block shaFinArgs) s (Prepared g bs shaFinalizePlan 5 s) := by
  have code : shaFinArgs = (List.range 5).flatMap fun j => (shaFinalizePlan j).code j := rfl
  rw [code]
  apply plan_ok h _ 5 (by decide)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with
    rfl | rfl | rfl | rfl | rfl <;> simp [shaFinalizePlan, CallArg.valid]

theorem macInitArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (key : Nat) :
    WP isa (.block (macInitArgs key)) s (Prepared g bs (macInitPlan key) 5 s) := by
  have code : macInitArgs key = (List.range 5).flatMap fun j => (macInitPlan key j).code j := rfl
  rw [code]
  apply plan_ok h _ 5 (by decide)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with
    rfl | rfl | rfl | rfl | rfl <;> trivial

theorem kdkUpdArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block kdkUpdArgs) s (Prepared g bs kdkUpdatePlan 6 s) := by
  have code : kdkUpdArgs = (List.range 6).flatMap fun j => (kdkUpdatePlan j).code j := rfl
  rw [code]
  apply plan_ok h _ 6 (by decide)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kdkUpdatePlan, CallArg.valid]

theorem prfUpdArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (len : Nat) :
    WP isa (.block (prfUpdArgs len)) s (Prepared g bs (prfUpdatePlan len) 6 s) := by
  have code : prfUpdArgs len = (List.range 6).flatMap fun j => (prfUpdatePlan len j).code j := rfl
  rw [code]
  apply plan_ok h _ 6 (by decide)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

def kdkFinalizePlan : Nat → CallArg
  | 0 => .scratch sSt | 1 => .scratch sOuter | 2 => .inputAdd 4 64
  | 3 => .value 0 | 4 => .scratch sKDK | _ => .scratch sHash

theorem kdkFinArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block kdkFinArgs) s (Prepared g bs kdkFinalizePlan 6 s) := by
  have code : kdkFinArgs = (List.range 6).flatMap fun j => (kdkFinalizePlan j).code j := rfl
  rw [code]
  apply plan_ok h _ 6 (by decide)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kdkFinalizePlan, CallArg.valid]

end VG.Proof.RsaPkcs1Enc.X86.Dec
