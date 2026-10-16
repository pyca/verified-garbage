module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnInput
public import VerifiedGarbage.Proof.Rsa.Arm.PrivBodyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Allocation adds no secret-dependent trace around the private body -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

theorem PrivFnInput.pushAlloc {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivFnInput g bs s) : isa.push (.alloc frameBytes) (pcPushed s) = some (entered s) := by
  have stackFit : 56 ≤ s.sp.toNat := by have := h.stackFit; simp only [stackBytes] at this; omega
  have allocation : frameBytes ≤ (pcPushed s).sp.toNat := by
    change frameBytes ≤ (s.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' stackFit]
    have := h.stackFit
    simp only [stackBytes, frameBytes] at *
    omega
  have hn : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 frameBytes) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, allocation, and_self, ite_true]
  rfl

theorem allocation_ct {bytes : Nat} {body : Prog isa} {P : State → State → Prop}
    (inside : RelCT isa (fun a b => ∃ s t, P s t ∧ isa.push (.alloc bytes) s = some a ∧
      isa.push (.alloc bytes) t = some b) body (fun _ _ => True)) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | frame p1 b1 q1 =>
    cases e2 with
    | frame p2 b2 q2 =>
      have trace := (inside _ _ _ _ _ _ ⟨s, t, h, p1, p2⟩ b1 b2).1
      exact ⟨by simp only [addrs, trace], trivial⟩

theorem privateAlloc_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivFnInput g bs1 s) (ht : PrivFnInput g bs2 t) (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun a b => a = pcPushed s ∧ b = pcPushed t)
      (.frame (.alloc frameBytes) (body v.name v.code v.pcName v.pc v.pdName v.pd) (.free frameBytes))
      (fun _ _ => True) := by
  apply allocation_ct
  intro a b tr1 tr2 u v' h e1 e2
  obtain ⟨_, _, ⟨rfl, rfl⟩, pa, pb⟩ := h
  have ea : entered s = a := Option.some.inj (hs.pushAlloc.symm.trans pa)
  have eb' : entered t = b := Option.some.inj (ht.pushAlloc.symm.trans pb)
  subst a; subst b
  exact privateBody_ct v nb eb _ _ _ _ _ _
    ⟨⟨hs.context, hs.output, hs.modulus, hs.count⟩, ⟨ht.context, ht.output, ht.modulus, ht.count⟩,
      hs.context.sp.trans ht.context.sp.symm⟩ e1 e2
end VG.Proof.Rsa.Arm
