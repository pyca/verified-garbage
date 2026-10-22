module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundTail
public import VerifiedGarbage.Impl.Dsa.X86.Generation.WitnessTape
import VerifiedGarbage.Proof.Framework.Offset

/-! Read the updated policy counts and the retained tape cursor. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont

theorem policy_counters {m m' : Mem} {base : Addr} {i uniform checks : Nat} {passed u : Bool}
    (index : m.readW (off base roundIndex) 32 = BitVec.ofNat 32 i)
    (count : m.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform)
    (memory : m' = (if passed then countMemory m base i uniform u else m).writeW
      (off base primeStatus) (BitVec.ofNat 32 (nextStatus passed i uniform checks u))) :
    m'.readW (off base roundIndex) 32 = BitVec.ofNat 32 (if passed then i + 1 else i) ∧
      m'.readW (off base uniformCount) 32 = BitVec.ofNat 32 (if passed then uniform + u.toNat else uniform) := by
  have first := Offset.sep base (n := 4) (k := 4) (.inl (by decide : roundIndex + 4 ≤ primeStatus)) (by decide) (by decide)
  have second := Offset.sep base (n := 4) (k := 4) (.inl (by decide : uniformCount + 4 ≤ primeStatus)) (by decide) (by decide)
  cases passed
  · simp only [Bool.false_eq_true, ite_false] at memory ⊢
    constructor
    · rw [memory, Mem.readW_writeW_sep first (by decide), index]
    · rw [memory, Mem.readW_writeW_sep second (by decide), count]
  · simp only [ite_true] at memory ⊢
    constructor
    · rw [memory, Mem.readW_writeW_sep first (by decide)]
      unfold countMemory
      rw [Mem.readW_writeW_sep (Offset.sep base (.inl (by decide : roundIndex + 4 ≤ uniformCount))
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
    · rw [memory, Mem.readW_writeW_sep second (by decide)]
      unfold countMemory
      rw [Mem.readW_writeW_self32]

theorem policy_tape_control {s t : State} {base : Addr} {d : Nat}
    (F : PolicyFrame base s t) (lo : witnessCursor ≤ d) (hi : d + 4 ≤ Layout.control + 128) :
    t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    apply Offset.disjoint base (.inr ?_) (by unfold Layout.control at hi; omega) (by decide) <;>
    simp only [roundIndex, uniformCount, primeStatus, witnessCursor] at lo ⊢ <;> omega

end VG.Proof.Dsa.X86.Generation
