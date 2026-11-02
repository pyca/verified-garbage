module

import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
public import VerifiedGarbage.Proof.Mont.X86.Rt.Verified
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The precondition of a call of `vg_rsa_mont_mul_at` from public RSA

From the frame of its arguments (`mulArgs_ok`) below the caller's `esp`,
apart from the working space (`CallRoom`): the callee's state, with its
permissions narrowed to its arguments and the working space, meets its
precondition (`callee_abi`, `callee_pre`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.MontMul (Apart scratchBytes)

/-- The callee's precondition from its facts and the 56 bytes of stack below
its `esp`, apart from the working space and the arguments. -/
theorem rtPre_of {s : State} (A : RtABI s) (stackLo : 56 ≤ (s.gpr .esp).toNat)
    (stkScratch : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩)
    (stkArgs : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩) :
    (Proof.Rsa.MontMul.mulContract abi 56).pre s := by
  cases A
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals with_reducible assumption

/-- The callee's state: the call's, with the permissions of the arguments and the working space. -/
abbrev calleeOf (g : State) (base : Addr) (bytes : Nat) : State :=
  g.callEntry.withRegions [⟨argAddr g.callEntry 0, 36⟩] [⟨base, bytes⟩]

/-- An address of the stack, as a number. -/
theorem setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem callee_abi {s g : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbytes : bytes = (args 9).toNat * 8)
    (R : CallRoom (s.gpr .esp) base bytes) {o a b : Nat} (ho : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4)
    (ho0 : o ≠ 0) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36)
    (hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem)
    (hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        mulArg len o a b (s.gpr .edi) (args 9) i)
    (hinv : (val32 s.mem base numOff (nw len) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (numAt len b) (nw len) < val32 s.mem base numOff (nw len)) :
    RtABI (calleeOf g base bytes) := by
  have low := R.low
  have hsp := (s.gpr .esp).isLt
  have nwr := h.scratch.nowrap
  have hw := wb_le h.upper
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have wbe := wb_eq len
  have gEsp : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [hesp, sub_toNat (by omega_arith)]
  have argc : ∀ i < 9, arg (calleeOf g base bytes) i = mulArg len o a b (s.gpr .edi) (args 9) i := by
    intro i hi
    show arg g.callEntry i = _
    rw [arg_callEntry (by omega_arith) (by omega_arith)]
    have e := addr_eq (x := g.gpr .esp) (k := 4 * i) (by omega_arith)
    simp only [addr] at e
    rw [e, hread i hi]
  have v8 : ∀ j ≤ 8, numAt len j < 2 ^ 32 := fun j hj => by
    have := Nat.mul_le_mul hj hw; simp only [numAt, numOff]; omega_arith
  have v0 : (arg (calleeOf g base bytes) 0).toNat = base.toNat := by rw [argc 0 (by decide)]; exact h.edi
  have v1 : (arg (calleeOf g base bytes) 1).toNat * 8 = bytes := by rw [argc 1 (by decide)]; exact hbytes.symm
  have vn : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 32 v).toNat = v := fun hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have v2 : (arg (calleeOf g base bytes) 2).toNat = Spec.Rsa.modulusWords len := by
    rw [argc 2 (by decide)]; exact vn (by simp only [Spec.Rsa.modulusWords]; omega_arith)
  have v3 : (arg (calleeOf g base bytes) 3).toNat = numOff := by rw [argc 3 (by decide)]; exact vn (by decide)
  have v4 : (arg (calleeOf g base bytes) 4).toNat = invOff := by rw [argc 4 (by decide)]; exact vn (by decide)
  have v5 : (arg (calleeOf g base bytes) 5).toNat = numAt len 5 := by
    rw [argc 5 (by decide)]; exact vn (v8 5 (by decide))
  have v6 : (arg (calleeOf g base bytes) 6).toNat = numAt len o := by
    rw [argc 6 (by decide)]; exact vn (v8 o (by omega_arith))
  have v7 : (arg (calleeOf g base bytes) 7).toNat = numAt len a := by
    rw [argc 7 (by decide)]; exact vn (v8 a (by omega_arith))
  have v8' : (arg (calleeOf g base bytes) 8).toNat = numAt len b := by
    rw [argc 8 (by decide)]; exact vn (v8 b (by omega_arith))
  have ws : wsOf (calleeOf g base bytes) = base := by
    show (arg (calleeOf g base bytes) 0).setWidth 64 = base
    rw [argc 0 (by decide)]; exact h.scratch.edi
  have ln : lenOf (calleeOf g base bytes) = bytes := v1
  -- The memory of the working space is the caller's.
  have Fc : Frame [below (s.gpr .esp) 40] s.mem (calleeOf g base bytes).mem := by
    have F₁ : Frame [below (g.gpr .esp) 4] g.mem g.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_top (Nat.le_refl 4) (by omega_arith) (by decide))
    refine (hFg.sub fun r hr => ?_).trans (F₁.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, below_sub (by decide) (by omega_arith)⟩
    · rw [List.mem_singleton.mp hr, hesp]
      exact ⟨_, List.mem_singleton_self _, below_inner (by decide) (by omega_arith)⟩
  have numc : ∀ d k, d + k ≤ bytes → Proof.Rsa.MontMul.numAt (calleeOf g base bytes).mem base d k =
      Proof.Rsa.MontMul.numAt s.mem base d k := fun d k hdk => by
    unfold Proof.Rsa.MontMul.numAt
    rw [Fc.read (r := ⟨base, bytes⟩) (Offset.contains_base _ hdk (by omega_arith))
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact R.apart40.symm) (by omega_arith)]
  have argAddr0 : argAddr (calleeOf g base bytes) 0 = (g.gpr .esp).setWidth 64 := by
    show argAddr g.callEntry 0 = _
    rw [argAddr_callEntry]; simp
  have retBase : ((calleeOf g base bytes).gpr .esp).setWidth 64 = (g.gpr .esp - 4).setWidth 64 := by
    simp [calleeOf]
  have W2 : 2 * Spec.Rsa.modulusWords len = nw len := rfl
  have e04 : numAt len 4 + wb len ≤ numAt len 5 := by simp only [numAt]; omega_arith
  have so : ∀ j ≤ 4, numAt len j + wb len ≤ numAt len 5 := fun j hj => by
    have := Nat.mul_le_mul_right (wb len) hj; simp only [numAt] at *; omega_arith
  have fo := (h.fits (j := o) (by omega_arith)).1
  have fa := (h.fits (j := a) (by omega_arith)).1
  have fb := (h.fits (j := b) (by omega_arith)).1
  have f0 := (h.fits (j := 0) (by decide)).1
  have ewb : wb len = 8 * Spec.Rsa.modulusWords len := rfl
  have n0 : numAt len 0 = numOff := by simp [numAt]
  have no : numOff + wb len ≤ numAt len o := by
    have := Nat.mul_le_mul_right (wb len) (Nat.one_le_iff_ne_zero.mpr ho0); simp only [numAt] at *; omega_arith
  refine ⟨?_, rfl, by rw [ws, ln]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · show (g.gpr .esp - 4).toNat + 4 + 36 ≤ 2 ^ 32
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat (by omega_arith)]; omega_arith
  · rw [ws, ln, argAddr0, hesp]; exact (R.apart.sub_left (below_sub (by decide) low)).symm
  · rw [retBase, ws, ln, hesp]; exact R.apart.sub_left (below_inner (a := 4) (k := 36) (b := 96) (by decide) low)
  · rw [retBase, argAddr0]
    refine Region.disjoint_of_le (.inl ?_) ?_ ?_ <;> simp only [setWidth_toNat] <;>
      (try rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat (by omega_arith)]) <;> omega_arith
  · rw [v0, ln]; exact nwr
  · rw [v2]; exact dims.1
  · rw [v3, v2]; simp only [numOff] at f0 n0 ⊢; omega_arith
  · rw [v4]; simp only [numOff, invOff] at f0 n0 ⊢; omega_arith
  · rw [v5, v2]; simp only [scratchBytes]; omega_arith
  · rw [v6, v2]; omega_arith
  · rw [v7, v2]; omega_arith
  · rw [v8', v2]; omega_arith
  · rw [v3, v5, v2]; unfold Apart; have := so 0 (by decide); simp only [scratchBytes]; rw [n0] at this; omega_arith
  · rw [v4, v5, v2]; unfold Apart; have := so 0 (by decide); simp only [scratchBytes, invOff]; rw [n0] at this
    simp only [numOff] at this; omega_arith
  · rw [v6, v5, v2]; unfold Apart; have := so o ho; omega_arith
  · rw [v7, v5, v2]; unfold Apart; have := so a ha; omega_arith
  · rw [v8', v5, v2]; unfold Apart; have := so b hb; omega_arith
  · rw [v6, v3, v2]; unfold Apart; omega_arith
  · rw [v6, v4, v2]; unfold Apart; simp only [numOff, invOff] at no ⊢; omega_arith
  · rw [ws, v3, v2, v4, numc _ _ (by rw [← n0]; omega_arith), numc _ _ (by simp only [invOff, numOff] at n0 ⊢; omega_arith),
      numAt_val32, numAt_w32]
    exact hinv
  · rw [ws, v8', v3, v2, numc _ _ (by omega_arith), numc _ _ (by rw [← n0]; omega_arith), numAt_val32, numAt_val32]
    exact hB

/-- The callee's precondition, at a call 36 bytes below `esp`: its 56 bytes
of stack are among the 96 of the call's room. -/
theorem callee_pre {s g : State} {base : Addr} {bytes : Nat} (A : RtABI (calleeOf g base bytes))
    (R : CallRoom (s.gpr .esp) base bytes) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36) :
    (Proof.Rsa.MontMul.mulContract abi 56).pre (calleeOf g base bytes) := by
  have low := R.low
  have hsp := (s.gpr .esp).isLt
  have eW : (⟨wsOf (calleeOf g base bytes), lenOf (calleeOf g base bytes)⟩ : Region) = ⟨base, bytes⟩ := by
    have h := A.wr
    simp only [calleeOf, State.withRegions_wr, List.cons.injEq, and_true] at h
    exact h.symm
  have e : (calleeOf g base bytes).gpr .esp = s.gpr .esp - BitVec.ofNat 32 40 := by
    show g.callEntry.gpr .esp = _
    rw [State.callEntry_esp, hesp, BitVec.sub_sub]; rfl
  have e40 : (s.gpr .esp - BitVec.ofNat 32 40).toNat = (s.gpr .esp).toNat - 40 := sub_toNat (by omega)
  have e56 : ((calleeOf g base bytes).gpr .esp).setWidth 64 - 56#64 =
      (s.gpr .esp - BitVec.ofNat 32 40 - BitVec.ofNat 32 56).setWidth 64 := by
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have sub : Region.Sub ⟨((calleeOf g base bytes).gpr .esp).setWidth 64 - 56#64, 56⟩ (below (s.gpr .esp) 96) := by
    rw [e56]; exact below_inner (a := 56) (k := 40) (b := 96) (by decide) low
  refine rtPre_of A (by rw [e, e40]; omega) (by rw [eW]; exact R.apart.sub_left sub) ?_
  have argA : argAddr (calleeOf g base bytes) 0 = (g.gpr .esp).setWidth 64 := by
    show argAddr g.callEntry 0 = _
    rw [argAddr_callEntry]; simp
  have e96 : (s.gpr .esp - BitVec.ofNat 32 40 - BitVec.ofNat 32 56).toNat = (s.gpr .esp).toNat - 96 := by
    rw [sub_toNat (by rw [e40]; omega), e40]; omega
  have e36 : (s.gpr .esp - BitVec.ofNat 32 36).toNat = (s.gpr .esp).toNat - 36 := sub_toNat (by omega)
  rw [argA, e56, hesp]
  refine Region.disjoint_of_le (.inl ?_) ?_ ?_ <;> simp only [setWidth_toNat, e96, e36] <;> omega

end VG.Proof.Bignum.X86.PublicRt
