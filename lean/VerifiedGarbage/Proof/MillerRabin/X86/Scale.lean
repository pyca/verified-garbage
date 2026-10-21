module

public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.MillerRabin.Index32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Scaling a public prepared array stride by its five-bit constant index -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont.X86
open VG.Proof.MillerRabin

def scaleBit (r tmp : Reg) (j bit : Nat) : List Instr :=
  [.alu .add r (.reg r)] ++ if j / 2 ^ bit % 2 = 1 then [.alu .add r (.reg tmp)] else []

theorem scaleBit_ok (s : State) (r tmp : Reg) (distinct : tmp ≠ r) (j bit c : Nat)
    (value : s.gpr r = BitVec.ofNat 32 c * s.gpr tmp) :
    WP isa (.block (scaleBit r tmp j bit)) s fun t =>
      t.gpr r = BitVec.ofNat 32 (indexStep j c bit) * s.gpr tmp ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  unfold scaleBit indexStep
  by_cases digit : j / 2 ^ bit % 2 = 1
  · simp only [digit, ite_true, List.singleton_append]
    refine wp_addS rfl fun a A _ => wp_addS rfl fun t T _ => WP.block_nil ?_
    refine ⟨?_, T.mem.trans A.mem, A.keeps.trans T.keeps⟩
    rw [T.gpr, A.gpr, A.other tmp distinct, value]
    calc
      BitVec.ofNat 32 c * s.gpr tmp + BitVec.ofNat 32 c * s.gpr tmp + s.gpr tmp =
          (BitVec.ofNat 32 c + BitVec.ofNat 32 c + 1#32) * s.gpr tmp := by
        rw [BitVec.add_mul, BitVec.add_mul, BitVec.one_mul]
      _ = _ := by
        rw [show (1#32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
        congr 2 <;> omega
  · simp only [digit, ite_false, List.append_nil, Nat.add_zero]
    refine wp_addS rfl fun t T _ => WP.block_nil ⟨?_, T.mem, T.keeps⟩
    rw [T.gpr, value, ← BitVec.add_mul, ← BitVec.ofNat_add]
    congr 2 <;> omega

theorem scaleBits_ok (bits : List Nat) (s : State) (r tmp : Reg) (distinct : tmp ≠ r) (j c : Nat)
    (value : s.gpr r = BitVec.ofNat 32 c * s.gpr tmp) :
    WP isa (.block (bits.flatMap (scaleBit r tmp j))) s fun t =>
      t.gpr r = BitVec.ofNat 32 (indexFold j bits c) * s.gpr tmp ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  induction bits generalizing s c with
  | nil => exact WP.block_nil ⟨value, rfl, Keeps.refl _ _⟩
  | cons bit bits ih =>
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (scaleBit_ok s r tmp distinct j bit c value) fun a ⟨R, M, K⟩ => ?_)
    have valueA : a.gpr r = BitVec.ofNat 32 (indexStep j c bit) * a.gpr tmp := by
      rw [K.1 tmp (by simpa using distinct)]; exact R
    refine WP.mono (ih a (indexStep j c bit) valueA) ?_
    rintro t ⟨Rt, Mt, Kt⟩
    refine ⟨?_, Mt.trans M, K.trans Kt⟩
    rw [Rt, K.1 tmp (by simpa using distinct)]
    rfl

theorem scaleIndex_ok (s : State) (r tmp : Reg) (distinct : tmp ≠ r) (j : Nat) (bound : j < 32)
    (zero : s.gpr r = 0) :
    WP isa (.block (scaleIndex r tmp j)) s fun t =>
      t.gpr r = BitVec.ofNat 32 j * s.gpr tmp ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  refine WP.mono (scaleBits_ok [4, 3, 2, 1, 0] s r tmp distinct j 0 ?_) ?_
  · rw [BitVec.zero_mul]
    exact zero.trans (show (0 : BitVec 32) = 0#32 from rfl)
  · rintro t ⟨R, M, K⟩
    exact ⟨by rw [R, index5_eq bound], M, K⟩

end VG.Proof.MillerRabin.X86
