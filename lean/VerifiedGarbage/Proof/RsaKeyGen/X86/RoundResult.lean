module

public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic

/-! # The reviewed round returns its test result and preserves prepared operands -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem reviewed_frame {g : Geometry} {capacity : Nat} {m m' : Mem}
    (length : g.L = 8 * capacity)
    (K : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact g.W capacity g.w m m') :
    WorkspaceFrame g (roundWrites g) m m' := by
  intro i index apart
  apply K i (by omega_arith)
  · intro k mem
    change k ∈ [23, 26, 29, 30, 1] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact apart (184, 8) (by simp [roundWrites])
    · exact apart (208, 8) (by simp [roundWrites])
    · exact apart (232, 8) (by simp [roundWrites])
    · exact apart (240, 8) (by simp [roundWrites])
    · exact apart (8, 8) (by simp [roundWrites])
  · intro j mem
    change j ∈ [2, 3, 5, 6, 8] at mem
    have a := apart (g.array 2, 16 * (g.w + 2)) (by simp [roundWrites])
    have b := apart (g.array 5, 16 * (g.w + 2)) (by simp [roundWrites])
    have c := apart (g.array 8, 8 * (g.w + 2)) (by simp [roundWrites])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at a b c ⊢ <;> omega_arith
  · have h := apart (g.array 11, 128 * (g.w + 2)) (by simp [roundWrites])
    change i < g.array 11 ∨ g.array 27 ≤ i
    have endOffset : g.array 11 + 128 * (g.w + 2) = g.array 27 := by
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
      omega_arith
    change i < g.array 11 ∨ g.array 11 + 128 * (g.w + 2) ≤ i at h
    rw [endOffset] at h
    exact h


theorem roundPost {g : Geometry} {s t : State} {capacity c b : Nat}
    (ptrBound : g.W.toNat < 2 ^ 32) (capBound : capacity < 2 ^ 32)
    (a0 : arg s 0 = BitVec.ofNat 32 g.W.toNat) (a1 : arg s 1 = BitVec.ofNat 32 capacity)
    (M : Modulus g c s.mem)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (post : (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).post s t) :
    (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact g.W capacity g.w s.mem t.mem := by
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  sig_post [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes] at post
  simp only [a0, a1, ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capBound, M.width] at post
  obtain ⟨result, keeps⟩ := post
  refine ⟨?_, keeps⟩
  have candidate : Proof.Rsa.Mont.numAt s.mem g.W g.w 0 = c := by
    rw [VG.Proof.Mont.X86.Compact.numAt_val32]
    exact M.candidate
  rw [candidate] at result
  have value := result b (by rw [VG.Proof.Mont.X86.Compact.numAt_val32]; exact witness)
  rw [BitVec.setWidth_append_eq_right] at value
  exact value

end VG.Proof.RsaKeyGen.X86.RoundCall
