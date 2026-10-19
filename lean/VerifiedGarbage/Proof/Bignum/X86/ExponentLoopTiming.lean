module

public import VerifiedGarbage.Proof.Bignum.X86.ExponentScanState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A public byte sequence fixes the complete exponent-scan trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem exponentLoop_relCT (ep : BitVec 32) (eb : List Byte)
    (fit : ep.toNat + eb.length ≤ 2 ^ 32) (countFit : eb.length < 2 ^ 32)
    (k : Nat) :
    RelCT isa (fun s t => ∃ j, j + k = eb.length ∧ 0 < k ∧
      ExponentState ep eb j k s ∧ ExponentState ep eb j k t)
      (.loop exponentByte .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa)
    (fun k s t => ∃ j, j + k = eb.length ∧ 0 < k ∧
      ExponentState ep eb j k s ∧ ExponentState ep eb j k t) ?_ k
  intro n s t tr ur sf tf ⟨j, Eq, Pos, S, T⟩ E F
  have hj : j < eb.length := by omega
  have hn : n < 2 ^ 32 := by omega
  obtain ⟨S', Zs⟩ := wp_result (S.step fit hj Pos hn) E
  obtain ⟨T', Zt⟩ := wp_result (T.step fit hj Pos hn) F
  refine ⟨exponentByte_trace S T fit hj E F, ?_, fun _ => trivial, ?_⟩
  · change sf.zf.map not = tf.zf.map not
    rw [Zs, Zt]
  · intro Continue
    have ne : n ≠ 1 := by
      intro h
      change sf.zf.map not = some true at Continue
      simp only [Zs, h, decide_true, Option.map_some, Bool.not_true] at Continue
      cases Continue
    exact ⟨n - 1, by omega, j + 1, by omega, by omega, S', T'⟩

end VG.Proof.Bignum.X86
