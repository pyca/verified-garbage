module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySeed
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySquares
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset

/-! Fast R-squared setup reuses verified initialization, doubling and squaring. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem montgomery_setup {s : State} {base : Addr} {n m bits : Nat}
    (scr : Scr s base montgomeryBytes) (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (hn : 0 < n) (hn' : n ≤ 48) (modulus : wordsVal s.mem base (slot n 0) n = m)
    (gt : 1 < m) (odd : m % 2 = 1)
    (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n) (top : 2 ^ (bits - 1) ≤ m) :
    WP isa (montgomerySetup n bits) s fun t =>
      Context n m base montgomeryBytes t ∧
      wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % m ∧
      Frame [⟨base, contextBytes n⟩,
        ⟨off base montgomeryScratch, Spec.Rsa.MontMul.scratchBytes n⟩,
        below (s.gpr .esp) 40] s.mem t.mem ∧ Keeps powerClob s t := by
  have fits : contextBytes n ≤ montgomeryBytes := by
    simp only [contextBytes, slot, stride, montgomeryBytes]; omega
  unfold montgomerySetup
  refine WP.seq (WP.mono (contextStart_ok scr hn fits modulus gt odd)
    fun u ⟨Cu, oneU, Ou, Ku⟩ => ?_)
  refine WP.seq (WP.mono (montgomery_seed Cu hn hn' bitsLow bitsHigh top odd)
    fun v ⟨Cv, valueV, oneV, Ov, Kv⟩ => ?_)
  have K := Ku.trans Kv
  have roomV : CallRoom (v.gpr .esp) base montgomeryBytes := by
    rw [K.1 .esp (by decide)]; exact room
  have value : val32 v.mem base (slot n 4) (2 * n) = 2 ^ n * 2 ^ (64 * n) % m := by
    rw [← wordsVal_eq_val32]; exact valueV
  refine WP.mono (montgomery_squares (E := n) 6 Cv roomV hn hn'
    (VG.Proof.Bignum.coprime_pow2 odd _) (by rw [value]; exact Nat.mod_lt _ (by omega))
    (by rw [value, Nat.mod_mod])) fun t ⟨Ct, bound, residue, F, cs, rd, wr⟩ => ?_
  have O := montgomery_offsets (a := 4) (b := 4) hn hn' (show 4 < 9 by decide) (by decide) (by decide) (by decide)
  have b3 := slot_bound (n := n) (i := 3) (by decide)
  have s34 := slot_le (n := n) (i := 3) (j := 4) (by decide)
  have sameOne := montgomery_frame_read Cv.scr roomV F (k := 2 * n) (d := slot n 3)
    (by unfold stride at b3; omega) O.o_le O.s_le
    (.inl (by unfold stride at s34; omega))
    (.inl (by simp only [slot, stride, montgomeryScratch]; omega))
  have frameUV := (Ou.trans Ov).frame (size := contextBytes n) (by
    intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [contextBytes, slot, stride] <;> omega)
  have finalK : Keeps powerClob v t := ⟨fun r hr => cs r (by
    cases r <;> simp_all [powerClob, calleeSaved]), rd, wr⟩
  refine ⟨Ct, ?_, ?_, ?_, K.trans finalK⟩
  · rw [wordsVal_eq_val32, sameOne, ← wordsVal_eq_val32, oneV, oneU]
  · rw [wordsVal_eq_val32, ← Nat.mod_eq_of_lt bound, residue]
  · rw [K.1 .esp (by decide)] at F
    apply Frame.trans (frameUV.sub (fun r hr => ?_)) (F.sub (fun r hr => ?_))
    · rw [List.mem_singleton.mp hr]
      exact ⟨⟨base, contextBytes n⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨base, contextBytes n⟩, by simp,
          Offset.sub_base base (by simp only [contextBytes, slot, stride]; omega)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.Dsa.X86.Generation
