module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The callable private wrapper leaks only public layout and key bytes -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

theorem privateFn_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivFnInput g bs1 s ∧ PrivFnInput g bs2 t ∧ s.sp = t.sp)
      (privCode v) (fun _ _ => True) := by
  unfold privCode code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u w hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (s := s0)
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (by decide) (by change 56 ≤ s0.sp.toNat; have := hs.stackFit; simp only [stackBytes] at this; omega)
  have pt' := push_pushed (s := t0)
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (by decide) (by change 56 ≤ t0.sp.toNat; have := ht.stackFit; simp only [stackBytes] at this; omega)
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  have alloc := relCT_keep_sp (privateAlloc_ct v hs ht nb eb) (by
    intro a b h
    rw [h.1, h.2]
    simp only [pcPushed, pushed_sp, sp])
  have restore : RelCT isa (fun s t => s.sp = t.sp) (.block Impl.Bignum.Arm.PcFn.restore)
      (fun s t => s.sp = t.sp) := stackLoads_ct pcCalleeSaved
  have trace := (alloc.seq restore) _ _ _ _ _ _ ⟨rfl, rfl⟩ e1 e2
  exact ⟨trace.1, trivial⟩
end VG.Proof.Rsa.Arm
