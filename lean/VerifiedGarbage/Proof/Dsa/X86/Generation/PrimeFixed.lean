module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame

/-! # Prepared exponent metadata and input pointers survive every witness round -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def primeFixedHeader (d : Nat) : Prop :=
  d = 0 ∨ d = primeTwos ∨ d = primeTape ∨ d = primeTapeLen ∨ d = primeWitness

theorem PrimeFrame.header {base witness : Addr} {n len size d : Nat} {s t : Mem}
    (O : PrimeFrame base n witness len s t) (width : n ≤ 48)
    (sizeBound : size ≤ 2 ^ 64) (room : primeExponent + 8 * n ≤ size)
    (apart : Region.Disjoint ⟨base, size⟩ ⟨witness, len⟩) (hd : primeFixedHeader d) :
    t.readW (off base d) 32 = s.readW (off base d) 32 := by
  have bound : d + 4 ≤ size := by
    rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      simp only [primeTwos, primeTape, primeTapeLen, primeWitness, primeExponent] at * <;> omega
  apply O.readW (Region.contains_self _ 4) ?_ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    have flagRoom : primeIsUniform + 4 ≤ size := by unfold primeIsUniform primeExponent at *; omega
    apply Offset.disjoint base ?_ (by omega) (Nat.le_trans (primeWrites_bound width flagRoom item hi) sizeBound)
    simp only [primeWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot, stride, roundCount, roundStatus, primeUniform, primeUsed, primeStatus, primeIsUniform,
        primeTwos, primeTape, primeTapeLen, primeWitness] <;> omega
  · obtain rfl := List.mem_singleton.mp hr
    exact apart.sub_left (Offset.sub_base _ bound)

theorem PrimeFrame.context {base witness : Addr} {n len size m : Nat} {s t : State} {rs : List Reg}
    (O : PrimeFrame base n witness len s.mem t.mem) (C : Context n m base size s)
    (width : n ≤ 48) (room : primeExponent + 8 * n ≤ size)
    (apart : Region.Disjoint ⟨base, size⟩ ⟨witness, len⟩)
    (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) : Context n m base size t := by
  have sizeBound : size ≤ 2 ^ 64 := by have := C.scr.nowrap; omega
  have flagRoom : primeIsUniform + 4 ≤ size := by unfold primeIsUniform primeExponent at *; omega
  have modulus := O.constants width sizeBound flagRoom apart (j := 0) (.inl rfl)
  refine ⟨C.scr.of_keeps K di sp, C.size_le,
    ⟨C.modulus.n0, C.modulus.mo, C.modulus.tmp, C.modulus.sep, modulus.trans C.modulus.val⟩, C.gt_one, ?_⟩
  have inv := O.header width sizeBound room apart (d := 0) (.inl rfl)
  simpa only [w32, inv] using C.inverse
end VG.Proof.Dsa.X86.Generation
