module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionStore
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Divide
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Omega

/-! # Quotient and remainder share the runtime RSA division kernel

Division uses four arrays of the shared temporary bank. Its frame also
includes the two saved division bits.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.Rsa.X86.KeyRt (sCy sQb)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs DivisionOutputs inverseRanges
  inverse_frame inverse_frame_clear)

def divisionRanges (d q r : Nat) : List (Nat × Nat) :=
  [(hdr, 4 * (4 * (d + 2))), (sCy, 4), (sQb, 4), (q, 4 * d), (r, 4 * d)]

theorem divisionFrom_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    {src divisor quotient remainder : Loc} (h : Ws s B Z n N) (bound : 4 ≤ N)
    (hw : w ≠ .correction)
    (input : DivisionInputs Z (w.words n) (src.offset n) (divisor.offset n))
    (output : DivisionOutputs Z (w.words n) (quotient.offset n) (remainder.offset n))
    (positive : 0 < val32 s.mem B (divisor.offset n) (w.words n)) :
    WP isa (divisionFrom w src divisor quotient remainder) s fun t =>
      Ws t B Z n N ∧ Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
        s.mem t.mem ∧
      val32 t.mem B (quotient.offset n) (w.words n) =
        val32 s.mem B (src.offset n) (w.words n) / val32 s.mem B (divisor.offset n) (w.words n) ∧
      val32 t.mem B (remainder.offset n) (w.words n) =
        val32 s.mem B (src.offset n) (w.words n) % val32 s.mem B (divisor.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold divisionFrom
  refine WP.seq (WP.mono (divisionLoad_ok h bound hw input)
    fun u ⟨hu, Ou, numerator, modulus, top, Ku⟩ => ?_)
  refine WP.seq (WP.mono (divide_ok hu bound hw top) fun v ⟨hv, Ov, Kv, computed⟩ => ?_)
  have result := computed (by rw [modulus]; exact positive)
  rw [numerator, modulus] at result
  refine WP.mono (divisionStore_ok hv bound hw output) fun t ⟨ht, Ot, Q, R, Kt⟩ => ?_
  refine ⟨ht, ?_, Q.trans result.1, R.trans result.2,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  have first : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      s.mem u.mem := Outs.of_outside Ou (List.mem_cons_self ..)
  have middle : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      u.mem v.mem := Ov.cover (by
    intro region member
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map] at member
    rcases member with ⟨j, hj, rfl⟩ | ⟨slot, hs, rfl⟩
    · refine ⟨(hdr, 4 * (4 * (w.words n + 2))), List.mem_cons_self .., Nat.le_add_right .., ?_⟩
      have small : j < 4 := by
        have bounds := (by decide : ∀ j ∈ ([0, 1, 3] : List Nat), j < 4) j hj
        exact bounds
      have last := VG.Proof.Rsa.X86.Keys.arr_end (w := w.words n) small
      simpa only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
        Nat.mul_assoc, Nat.mul_left_comm] using last
    · refine ⟨(slot, 4), ?_, Nat.le_refl _, Nat.le_refl _⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [divisionRanges])
  have last : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      v.mem t.mem := Ot.mono (by
    intro region member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.KeyRuntime
