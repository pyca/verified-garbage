module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomeryConstants
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! Subtract Montgomery one from the modulus using the existing word loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem parent_difference {s : State} {base : Addr} {size n m r out input : Nat}
    (C : Context n m base size s) (hn : 0 < n)
    (ho : out < 9) (hi : input < 9) (ho0 : out ≠ 0) (hoi : out ≠ input)
    (one : val32 s.mem base (slot n input) (2 * n) = r) (reduced : r < m) :
    WP isa (parentDifference n out input) s fun t =>
      Context n m base size t ∧ val32 t.mem base (slot n out) (2 * n) = m - r ∧
      Outside base (slot n out) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b6 := slot_bound (n := n) (i := input) hi
  have b7 := slot_bound (n := n) (i := out) ho
  have s07 := slot_le (n := n) (i := 0) (j := out) (by omega)
  have s67 := slot_sep (n := n) (i := out) (j := input) hoi
  have hz := C.size_le
  unfold stride at b0 b6 b7 s07 s67
  refine WP.mono (chainSubW_ok C.scr (k := 2 * n) (o := slot n out) (a := slot n 0)
    (b := slot n input) (by omega) (by omega) (by omega) (by omega)
    (.inr (by omega)) (by omega)) fun t ⟨F, ⟨carry, _, value⟩, K⟩ => ?_
  have modulus : val32 s.mem base (slot n 0) (2 * n) = m := by
    rw [← wordsVal_eq_val32]; exact C.modulus.val
  rw [one, modulus] at value
  have bound := val32_lt t.mem base (slot n out) (2 * n)
  have result : val32 t.mem base (slot n out) (2 * n) = m - r := by
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero,
      Nat.mul_one] at value <;> omega
  have F' : Outside base (slot n out) (8 * n) s.mem t.mem := by
    simpa only [show 4 * (2 * n) = 8 * n by omega] using F
  exact ⟨C.outside_keep K (by decide) (by decide) F' (.inl (by omega))
    (by have := slot_header n out; omega), result, F', K⟩

theorem montgomery_minus_one {s : State} {base : Addr} {size n m r : Nat}
    (C : Context n m base size s) (hn : 0 < n)
    (one : val32 s.mem base (slot n 6) (2 * n) = r) (reduced : r < m) :
    WP isa (montgomeryMinusOne n) s fun t =>
      Context n m base size t ∧ val32 t.mem base (slot n 7) (2 * n) = m - r ∧
      Outside base (slot n 7) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t :=
  parent_difference C hn (by decide : 7 < 9) (by decide : 6 < 9) (by decide) (by decide) one reduced

end VG.Proof.Dsa.X86.Generation
