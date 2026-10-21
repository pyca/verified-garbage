module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! A phase draws exactly the next prefix of its public entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

private theorem sourceAddress {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    State.addr (p.tape + BitVec.ofNat 32 offset) = off (State.addr p.tape) offset :=
  VG.Arm.addr_add (by have := h.tapeFits; have := h.bitsPositive; omega)

theorem WitnessState.source_fits {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    (p.tape + BitVec.ofNat 32 offset).toNat + (p.bits + 7) / 8 ≤ 2 ^ 32 := by
  have start : p.tape.toNat + offset < 2 ^ 32 := by have := h.tapeFits; have := h.bitsPositive; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 32), Nat.mod_eq_of_lt start]
  have := h.tapeFits
  omega

theorem WitnessState.source_read {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    InRegions (s.rd ++ s.wr) (State.addr (p.tape + BitVec.ofNat 32 offset)) ((p.bits + 7) / 8) := by
  rw [sourceAddress h enough]
  exact VG.CallLay.inRegions_sub h.tapeRead enough (by have := h.tapeCount; omega)

theorem WitnessState.source_separate {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    (⟨State.addr (p.tape + BitVec.ofNat 32 offset), (p.bits + 7) / 8⟩ : Region).Disjoint
      ⟨State.addr p.base, 8 * p.capacity⟩ := by
  rw [sourceAddress h enough]
  exact h.tapeScratch.sub_left (Offset.sub_base _ enough)

theorem WitnessState.source_bytes {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    Spec.Rsa.bytesAt s.mem (State.addr (p.tape + BitVec.ofNat 32 offset)) ((p.bits + 7) / 8) =
      (p.bytes.drop offset).take ((p.bits + 7) / 8) := by
  rw [sourceAddress h enough, ← VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.tape) enough, h.tapeBytes]

end VG.Proof.Ffdh.Arm.ParameterCandidate
