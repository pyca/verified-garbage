module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderLayout
import VerifiedGarbage.Proof.RsaKeyGen.X86.MontInverse
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.Mont.RangeCover

/-! # A fresh candidate reaches the existing prepared Montgomery contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareHeader
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2

def ranges : List (Nat × Nat) := Header.ranges ++ [(56, 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1) :
    WP isa (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.PrepareHeader.code
  rw [Prepared.slot_eq]
  refine WP.seq (WP.mono (Header.context_ok v scratch) fun a ⟨Ca, Oa, Ka, Ma⟩ => ?_)
  have Sa := scratch.of_keeps Ka (by decide)
  have candidateA : val32 a.mem g.W (g.array 0) g.words = c := by
    rw [Oa.val32 (fun r mem => by
      simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have h := v.arrayHeader 0
      rcases mem with rfl | rfl | rfl <;> right <;> omega)
      (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega)]
    exact candidate
  have oddLow : w32 a.mem g.W (g.array 0) % 2 = 1 := by
    rw [← LowWord.parity _ _ _ g.words (by have := v.minWidth; unfold Geometry.words; omega), candidateA]
    exact odd
  have callerA := caller.keepOuts Ka (by decide) Oa (fun r mem => by
    simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    have := v.headerFit
    rcases mem with rfl | rfl | rfl <;> omega)
  have widthA : Spec.Rsa.Mont.wOf a.mem g.W = g.w := by
    rw [Ma]
    exact Header.width_eq (by have := v.maxWidth; omega)
  have layoutA : Spec.Rsa.Mont.Layout a.mem g.W capacity := by
    rw [Ma]
    apply Header.layout scratch.edi (by have := v.minWidth; omega) (by have := v.maxWidth; omega)
    · rw [← length]
      have fit := v.arraysFit
      unfold Spec.Rsa.Mont.arrAt Spec.Rsa.Mont.hdrBytes at *
      omega
    · rw [← length]
      exact scratch.nowrap
  refine WP.mono (MontInverse.code_ok Sa
    (by have := v.arrayFit (j := 0) (by decide); have := v.minWidth; unfold Geometry.words at *; omega)
    (by have := v.headerFit; omega) (Or.inl (by have := v.arrayHeader 0; omega)) oddLow)
    fun t ⟨inverse, Ot, Kt⟩ => ?_
  have St := Sa.of_keeps Kt (by decide)
  have Ct : Context g t := by
    refine ⟨Ca.ws.of_keeps Kt, ?_, ?_, ?_, ?_⟩
    · rw [PtrAt, Kt.1 .edi (by decide)]; exact Ca.base
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.width
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.stride
    · intro j hj
      rw [Ot.w32 (by omega) (by omega)]; exact Ca.pointers j hj
  have Mt : Modulus g c t.mem := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (word t.mem g.W 48).toNat = g.w
      rw [Ot.word (by decide) (by decide)]
      exact widthA
    · intro j hj
      change word t.mem g.W (8 * Spec.Rsa.Mont.arrWord j) = _
      rw [Ot.word (Or.inr (by unfold Spec.Rsa.Mont.arrWord; omega)) (by unfold Spec.Rsa.Mont.arrWord; omega)]
      simpa only [widthA, Geometry.array, VG.Proof.Mont.word, VG.Proof.Mont.off, Spec.Rsa.Mont.wordAt] using layoutA.2.2.2 j hj
    · rw [Ot.val32 (Or.inr (by have := v.arrayHeader 0; omega))
        (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega)]
      exact candidateA
    · exact inverse
  refine ⟨⟨Ct, Mt, callerA.keepOuts Kt (by decide) (Outs.of_outside Ot (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; omega), St⟩, ?_, ?_⟩
  · exact (Oa.mono (fun r mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact (Ka.mono (by unfold clob; decide)).trans Kt

end VG.Proof.RsaKeyGen.X86.PrepareHeader
