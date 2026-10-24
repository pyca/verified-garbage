module

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top5
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top3
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Rsa.Arm.RvBase
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Body
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top4
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1

/-! # DSA's probable-prime test on ARMv7: constant time (`prime_ct`)

Two calls with the same public parameters `mkP` leak the same: the
allocation and `pre`'s addresses are on the stack, the push's and the pop's
too, the body's are the stage's (`body_vp`), and the restore's on the stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat}

/-- `pre`'s addresses are `r12`'s offsets, which it keeps. -/
theorem pre_ct (bits : Nat) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (Impl.Dsa.Arm.ProbablePrime.pre bits)) (fun s t => s.sp = t.sp) := by
  unfold Impl.Dsa.Arm.ProbablePrime.pre
  apply VG.Proof.Rsa.Arm.setupBlock_ct
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro i hi s t h
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [addrs, h2]

theorem alloc_push {s : State} (h : 32 ≤ s.sp.toNat) : isa.push (.alloc 32) s = some (allocated 32 s) := by
  simp only [isa, push, show (0 : Nat) < 32 ∧ 32 < 4096 ∧ 32 % 8 = 0 ∧ encodable (BitVec.ofNat 32 32) = true from
    by decide, h, and_self, ite_true]
  rfl

/-- The states after `pre`, for two calls. -/
def AfterPre (bits : Nat) (a b : State) : Prop :=
  ∃ s t, (CIn bits s ∧ CIn bits t ∧ s.sp = t.sp ∧ mkP bits s = mkP bits t) ∧ PreOut bits s a ∧ PreOut bits t b

theorem pre_out {s u : State} {tr : List Leak} (enc : PreEnc bits) (h : CIn bits s)
    (e : Exec isa (.block (Impl.Dsa.Arm.ProbablePrime.pre bits)) (allocated 32 s) tr u) : PreOut bits s u := by
  have hA : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
    ⟨cA s, List.mem_append_left _ (by rw [h.rd]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      Region.contains_self _ _⟩
  obtain ⟨tr', u', e', rest, fr, vals, r1, r2⟩ := pre_ok enc h.spLo h.spHi hA
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨rest, fr, vals, r1, r2⟩

/-- The frame's body, for two calls. -/
theorem inner_ct (v : RoundImpl) (hb : Bits bits) :
    RelCT isa (fun a' b' => ∃ a b, AfterPre bits a b ∧
        isa.push (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) a = some a' ∧
        isa.push (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) b = some b')
      (.seq (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (.block VG.Impl.Bignum.Arm.PcFn.restore)) (fun _ _ => True) := by
  intro a' b' tr1 tr2 u w hp e1 e2
  obtain ⟨a, b, ⟨s, t, ⟨hs, ht, sp, hP⟩, o1, o2⟩, pa, pb⟩ := hp
  have f1 : 56 ≤ a.sp.toNat := by rw [o1.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
                                  rw [sub_toNat' (by have := hs.spLo; omega)]; have := hs.spLo; omega
  have f2 : 56 ≤ b.sp.toNat := by rw [o2.rest.sp]; show 56 ≤ (t.sp - BitVec.ofNat 32 32).toNat
                                  rw [sub_toNat' (by have := ht.spLo; omega)]; have := ht.spLo; omega
  have ea : pcPushed a = a' := Option.some.inj ((push_pushed (by decide) (by simpa using f1)).symm.trans pa)
  have eb : pcPushed b = b' := Option.some.inj ((push_pushed (by decide) (by simpa using f2)).symm.trans pb)
  subst a'; subst b'
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨n1, w1, en1, run1, ⟨-, bk1, -⟩⟩ := body_wide v hb hs o1
      obtain ⟨n2, w2, en2, run2, ⟨-, bk2, -⟩⟩ := body_wide v hb ht o2
      obtain ⟨rfl, rfl⟩ := Exec.det body1 run1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 run2
      have pre1 := in_c hb hs o1
      have pre2 := in_c hb ht o2
      have bx1 : Bk (mkP bits s) (sx bits s a) (sx bits s a) := ⟨pre1, rfl, rfl, rfl, Frame.refl _ _⟩
      have bx2 : Bk (mkP bits t) (sx bits t b) (sx bits t b) := ⟨pre2, rfl, rfl, rfl, Frame.refl _ _⟩
      have sp1 := bk1.sp.trans pre1.sp
      have sp2 := bk2.sp.trans pre2.sp
      rw [← hP] at pre2 bx2 sp2
      have trB := ((body_vp v (P := mkP bits s) (E := In (mkP bits s)) fun _ e => e).ct _ _ _ _ _ _
        ⟨_, _, ⟨pre1, bx1⟩, ⟨pre2, bx2⟩⟩ en1 en2).1
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by show w1.sp = w2.sp; rw [sp1, sp2]) rest1 rest2).1
      exact ⟨by rw [trB, trR], trivial⟩

/-- Two calls with the same public parameters. -/
theorem prime_ct (v : RoundImpl) (hb : Bits bits) (enc : PreEnc bits) :
    RelCT isa (fun s t => CIn bits s ∧ CIn bits t ∧ s.sp = t.sp ∧ mkP bits s = mkP bits t)
      (Impl.Dsa.Arm.ProbablePrime.code bits v.name v.code) (fun _ _ => True) := by
  unfold Impl.Dsa.Arm.ProbablePrime.code
  apply VG.Proof.Rsa.Arm.allocation_ct
  intro a b tr1 tr2 u w hp e1 e2
  obtain ⟨s, t, ⟨hs, ht, sp, hP⟩, pa, pb⟩ := hp
  have ea : allocated 32 s = a := Option.some.inj ((alloc_push (by have := hs.spLo; omega)).symm.trans pa)
  have eb : allocated 32 t = b := Option.some.inj ((alloc_push (by have := ht.spLo; omega)).symm.trans pb)
  subst a; subst b
  cases e1 with
  | seq pre1 fr1 =>
    cases e2 with
    | seq pre2 fr2 =>
      have trP := (pre_ct bits _ _ _ _ _ _ (show (allocated 32 s).sp = (allocated 32 t).sp by
        show s.sp - _ = t.sp - _; rw [sp]) pre1 pre2).1
      have o1 := pre_out enc hs pre1
      have o2 := pre_out enc ht pre2
      have trF := (RelCT.frame (P := AfterPre bits) (fun x y ⟨s, t, ⟨_, _, sp, _⟩, o1, o2⟩ => by
          rw [o1.rest.sp, o2.rest.sp]; show s.sp - _ = t.sp - _; rw [sp])
        (fun a' b' tr1 tr2 u w ⟨x, y, hxy, px, py⟩ e1 e2 => inner_ct v hb a' b' tr1 tr2 u w ⟨x, y, hxy, px, py⟩ e1 e2)
        _ _ _ _ u w ⟨s, t, ⟨hs, ht, sp, hP⟩, o1, o2⟩ fr1 fr2).1
      exact ⟨by rw [trP, trF], trivial⟩

end

end VG.Proof.Dsa.Arm.Prime
