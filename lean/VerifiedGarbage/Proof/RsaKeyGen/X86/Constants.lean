module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsFrame
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsOne
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
/-! # Complete one-time preparation of Montgomery one and minus one -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ConstantsSubtract.lean`, which only this module imported.
section

/-! # A native subtraction prepares Montgomery minus one while preserving one -/

section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2
open VG.Impl.Bignum.X86.PublicContext

theorem subtract_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity one : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (oneVal : val32 s.mem g.W (g.array 9) g.words = one) (oneLt : one < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.Constants.subtract g.w) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 9) g.words = one ∧
      val32 t.mem g.W (g.array 10) g.words = c - one ∧
      Outside g.W (g.array 10) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Constants.subtract
  rw [Prepared.slot_eq, Prepared.slot_eq, Prepared.slot_eq]
  refine WP.mono (chainSubW_ok S.scratch (by have := v.minWidth; omega)
    (v.arrayFit (by decide)) (v.arrayFit (by decide)) (v.arrayFit (by decide))
    (Or.inr (g.arrayBefore (by decide))) (Or.inr (g.arrayBefore (by decide))))
    fun t ⟨O, ⟨borrow, _, equation⟩, K⟩ => ?_
  change val32 t.mem g.W (g.array 10) g.words + val32 s.mem g.W (g.array 9) g.words =
    val32 s.mem g.W (g.array 0) g.words + 2 ^ (32 * g.words) * borrow.toNat at equation
  rw [S.modulus.candidate, oneVal] at equation
  have value : val32 t.mem g.W (g.array 10) g.words = c - one := by
    have bound := val32_lt t.mem g.W (g.array 10) g.words
    change val32 t.mem g.W (g.array 10) g.words + one = c + 2 ^ (32 * g.words) * borrow.toNat at equation
    cases borrow <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at equation <;> omega
  have W := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs S.scratch.nowrap W
  have fit := v.arrayFit (j := 10) (by decide)
  refine ⟨⟨Prepared.keepRanges v S.context K (by decide) W (fun r mem => by
      obtain rfl := List.mem_singleton.mp mem; exact v.arrayHeader _),
    S.modulus.keep v F (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 10; omega))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide))),
    S.caller.keepOuts K (by decide) W (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit),
    S.scratch.of_keeps K (by decide)⟩, ?_, value, O, K⟩
  rw [O.val32 (Or.inl (g.arrayBefore (by decide))) (by have := S.scratch.nowrap; have := v.arrayFit (j := 9) (by decide); omega)]
  exact oneVal

end VG.Proof.RsaKeyGen.X86.Constants
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (odd : c % 2 = 1) (positive : 0 < c)
    (r2 : val32 s.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c) :
    WP isa (VG.Impl.RsaKeyGen.X86.Constants.code g.w name mont) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Constants.code
  rw [Prepared.slot_eq]
  refine WP.seq (WP.mono (plainOne_ok v S) fun a ⟨A, one, r2Same, Oa, Ka⟩ => ?_)
  have r2A := r2Same.trans r2
  refine WP.seq (WP.mono (mulY_ok verified noSp stack v A.context length A.modulus
    (by unfold Proof.Rsa.Mont.Operand; decide) odd (by rw [r2A]; exact Nat.mod_lt _ positive)
    A.caller.readLen (by rw [A.caller.sp]; exact A.caller.low) (by rw [A.caller.sp]; exact A.caller.stackFar))
    fun b ⟨Vb, Ob, Kb, Cb, Mb, Fb⟩ => ?_)
  rw [A.caller.sp] at Fb
  have B : Ready g c capacity p b := ⟨Cb, Mb, A.caller.keepFrame Kb (by decide) Fb,
    A.scratch.of_keeps Kb (by decide)⟩
  rw [one, r2A, one_r2 odd] at Vb
  refine WP.seq (WP.mono (Prepared.copy_ready v B 9 6 (by decide) (by decide) (by decide))
    fun d ⟨D, Vd, Od, Kd⟩ => ?_)
  have oneD := Vd.trans Vb
  refine WP.mono (subtract_ok v D oneD (Nat.mod_lt _ positive)) fun t ⟨T, oneT, minusT, Ot, Kt⟩ => ?_
  have Wa : WorkspaceFrame g (ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.scratch.nowrap (Outs.of_outside
      (Oa.mono (Nat.le_refl _) (by unfold Geometry.words; omega))
      (show (g.array 6, 8 * (g.w + 2)) ∈ ranges g from by simp [ranges, montWrites]))
  have Wb := Ob.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ montWrites g 6, r ∈ ranges g)
  have Wd : WorkspaceFrame g (ranges g) b.mem d.mem :=
    WorkspaceFrame.of_outs B.scratch.nowrap (Outs.of_outside Od
      (by simp [ranges]))
  have Wt : WorkspaceFrame g (ranges g) d.mem t.mem :=
    WorkspaceFrame.of_outs D.scratch.nowrap (Outs.of_outside Ot
      (by simp [ranges]))
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fd : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) b.mem d.mem :=
    (workspaceGlobalFrame (Outs.of_outside Od (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) d.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ot (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨T, oneT, minusT, ((Wa.trans Wb).trans Wd).trans Wt, ((Fa.trans Fb).trans Fd).trans Ft, ?_⟩
  have Ksa : Keeps clob s a := Ka.mono (by unfold clob; decide)
  exact ((Ksa.widen Kb).widen Kd).widen Kt

end VG.Proof.RsaKeyGen.X86.Constants
