module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.Mont.RangeCover
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # A native subtraction prepares Montgomery minus one while preserving one -/

@[expose] public section
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
