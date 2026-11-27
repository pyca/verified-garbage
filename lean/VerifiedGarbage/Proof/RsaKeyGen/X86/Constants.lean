module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Mont.X86.Power
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! ### `RsaKeyGen.X86.ConstantsMath`, which this module and modules that import it used -/

section

/-! # Multiplying a plain one by R² produces the Montgomery representation of one -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.Proof.MillerRabin

theorem one_r2 {c w : Nat} (odd : c % 2 = 1) :
    Word32.mm c w 1 (2 ^ (64 * w) * 2 ^ (64 * w) % c) = 2 ^ (64 * w) % c := by
  unfold Word32.mm
  rw [Nat.one_mul, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Word32.R_rinv odd,
    ← Nat.mul_mod, Nat.mul_one]

end VG.Proof.RsaKeyGen.X86.Constants

end

end

/-! ### `RsaKeyGen.X86.ConstantsOne`, which this module and modules that import it used -/

section

/-! # Plain one enters the prepared multiplier without rebuilding its modulus -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

theorem plainOne_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) :
    WP isa (VG.Impl.Mont.X86.Dynamic.one g.w (g.array 6)) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 1 ∧
      val32 t.mem g.W (g.array 4) g.words = val32 s.mem g.W (g.array 4) g.words ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t := by
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.one_ok S.scratch (by have := v.minWidth; omega_using [this])
    (show g.array 6 + 8 * g.w ≤ g.L from by have := v.arrayFit (j := 6) (by decide); unfold Geometry.words at this; omega_using [this]))
    fun t ⟨O, V, K⟩ => ?_
  rw [show 8 * g.w = 4 * g.words by unfold Geometry.words; omega_using []] at O
  have W := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs S.scratch.nowrap W
  refine ⟨⟨S.context.keepOutside K (by decide) O (v.arrayHeader _),
    S.modulus.keep v F (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 6; omega))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide))),
    S.caller.keepOuts K (by decide) W (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide)),
    S.scratch.of_keeps K (by decide)⟩, ?_, ?_, O, K⟩
  · unfold Geometry.words
    rw [← wordsVal_eq_val32]
    exact V
  · exact O.val32 (Or.inl (g.arrayBefore (by decide))) (by have := S.scratch.nowrap; have := v.arrayFit (j := 4) (by decide); omega_arith)

end VG.Proof.RsaKeyGen.X86.Constants

end

end

/-! ### `RsaKeyGen.X86.ConstantsFrame`, which this module and modules that import it used -/

section

/-! # Preparing one and minus one preserves R², c-1 and the exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def ranges (g : Geometry) : List (Nat × Nat) := montWrites g 6 ++ [(g.array 9, 4 * g.words), (g.array 10, 4 * g.words)]

theorem preserve {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 5 ∨ j = 27) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply F.val32 (v.arrayFit (by omega_using [index]))
  intro r mem
  simp only [ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases index with rfl | rfl | rfl <;>
    rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using []

end VG.Proof.RsaKeyGen.X86.Constants

end

end

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
      (Oa.mono (Nat.le_refl _) (by unfold Geometry.words; omega_using []))
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
