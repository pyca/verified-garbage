module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Mont.X86.Words
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.X86.PublicDispatchTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.KcDispatch
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # Width dispatch branches only on the common public modulus length -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem dispatch_relCT (full : Bool) (widths : List Nat) (n : Nat) (P : State → State → Prop)
    (member : n ∈ widths) (bound : ∀ w ∈ widths, w < 2 ^ 32)
    (width : ∀ s t, P s t → s.gpr .eax = BitVec.ofNat 32 n ∧ t.gpr .eax = BitVec.ofNat 32 n)
    (keep : ∀ s t u v, P s t → Keeps [] s u → Keeps [] t v → u.mem = s.mem → v.mem = t.mem → P u v)
    (body : RelCT isa P (sized full n) (fun _ _ => True)) :
    RelCT isa P (dispatch full widths) (fun _ _ => True) := by
  induction widths with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    have hn := bound n member
    have hw := bound w List.mem_cons_self
    have Compare : RelCT isa P (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 w))])
        (fun s t => P s t ∧ s.zf = some (decide (n = w)) ∧ t.zf = some (decide (n = w))) := by
      intro s t tr ur sf tf H E F
      obtain ⟨Ks, Ms, Zs⟩ := wp_result (compareWidth_ok hn hw (width s t H).1) E
      obtain ⟨Kt, Mt, Zt⟩ := wp_result (compareWidth_ok hn hw (width s t H).2) F
      have CT : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 w))])
          (fun _ _ => True) := by
        apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
        rfl
      exact ⟨(CT _ _ _ _ _ _ trivial E F).1, keep s t sf tf H Ks Kt Ms Mt, Zs, Zt⟩
    unfold dispatch
    refine VG.RelCT.seq Compare (VG.RelCT.ite (M := isa) (c := .e) ?_ ?_ ?_)
    · intro s t H
      exact H.2.1.trans H.2.2.symm
    · intro s t tr ur sf tf ⟨H, Z⟩ E F
      have eq : n = w := by
        change s.zf = some true at Z
        rw [H.2.1] at Z
        exact of_decide_eq_true (Option.some.inj Z)
      subst w
      exact body _ _ _ _ _ _ H.1 E F
    · intro s t tr ur sf tf ⟨H, Z⟩ E F
      have ne : n ≠ w := by
        change s.zf = some false at Z
        rw [H.2.1] at Z
        exact of_decide_eq_false (Option.some.inj Z)
      exact ih (by simpa only [List.mem_cons, ne, false_or] using member)
        (fun v hv => bound v (List.mem_cons_of_mem w hv)) _ _ _ _ _ _ H.1 E F

end VG.Proof.Rsa.X86.KeyCheck
