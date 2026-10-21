module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic

/-! # Candidate preparation satisfies the reviewed callable round's representation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Data.layout {g : Geometry} (v : g.Valid) {s : VG.X86.State} {c capacity : Nat} {p : BitVec 32}
    (S : Data g c capacity p s) (length : g.L = 8 * capacity) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem g.W capacity := by
  unfold Spec.MillerRabin.Layout
  rw [S.ready.modulus.width]
  refine ⟨Or.inr rfl, ?_, v.minWidth, v.maxWidth, ?_, ?_⟩
  · have M := S.ready.modulus.layout v (by rw [length]; omega)
    simpa only [length, Nat.mul_div_cancel_left capacity (by decide : 0 < 8)] using M
  · change Spec.Rsa.Mont.arrAt g.w 28 ≤ 8 * capacity
    rw [← length]
    exact v.arraysFit
  · exact S.stride

theorem prepared_of {g : Geometry} {m : Mem} {c : Nat}
    (M : Modulus g c m) (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 m g.W (g.array 5) g.words < c)
    (one : val32 m g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c)
    (minusOne : val32 m g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c)
    (exponent : val32 m g.W (g.array 27) g.words = Spec.MillerRabin.exponent c)
    (marker : word m g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)) :
    Spec.MillerRabin.Prepared Spec.MillerRabin.compact m g.W := by
  unfold Spec.MillerRabin.Prepared
  rw [M.width]
  dsimp only
  rw [VG.Proof.Mont.X86.Compact.numAt_val32]
  simp only [show val32 m g.W (Spec.Rsa.Mont.arrAt g.w 0) (2 * g.w) = c from M.candidate]
  change 3 ≤ c ∧ _
  refine ⟨large, odd, M.inverse, ?_, ?_, ?_, ?_, marker⟩
  all_goals rw [VG.Proof.Mont.X86.Compact.numAt_val32]
  · exact witness
  · exact one
  · exact minusOne
  · exact exponent

theorem Data.prepared {g : Geometry} {s : VG.X86.State} {c capacity b : Nat} {p : BitVec 32}
    (S : Data g c capacity p s) (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c) :
    Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem g.W :=
  prepared_of S.ready.modulus odd large (by rw [witness]; exact Nat.mod_lt _ (by omega))
    S.one S.minusOne S.exponent S.marker

end VG.Proof.RsaKeyGen.X86.Prepare
