module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFirst
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentMarker
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentShiftPasses
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFinish
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words32
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Complete native exponent and alignment-marker preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def ranges (w src out : Nat) : List (Nat × Nat) := [(markerOffset, 8), (src + 8 * w, 4), (out, 8 * w + 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w minusOne src out c : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (minusFit : minusOne + 8 * w ≤ size) (srcFit : src + 8 * w + 4 ≤ size)
    (outFit : out + 8 * w + 8 ≤ size) (lo : markerOffset + 8 ≤ src) (sep : src + 8 * w + 4 ≤ out)
    (candidate : val32 s.mem base src (2 * w) = c)
    (minusValue : val32 s.mem base minusOne (2 * w) = c - 1) (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (code w minusOne src out) s fun t =>
      val32 t.mem base out (2 * w) = Spec.MillerRabin.exponent c ∧
      word t.mem base (out + 8 * w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs base (ranges w src out) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.seq (WP.mono (ExponentMarker.code_ok scratch minusFit minusValue (by omega))
    fun a ⟨marker, Ma, Ka⟩ => ?_)
  have Sa := scratch.of_keeps Ka (by decide)
  have markerFit : markerOffset + 8 ≤ size := by omega
  refine WP.seq (WP.mono (Header.storePair_ok Sa markerFit) fun b ⟨Mb, Ob, Kb⟩ => ?_)
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  have Sb := scratch.of_keeps Ksb (by unfold clob; decide)
  have candidateB : val32 b.mem base src (2 * w) = c := by
    rw [Ob.val32 (Or.inr lo) (by have := scratch.nowrap; omega), Ma]
    exact candidate
  have markerB : word b.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [VG.Proof.Mont.word, Mb, Mem.readW_writeW_self64, marker]
  refine WP.seq (WP.mono (firstPass_ok Sb (by omega) (by omega) (by omega) (by omega))
    fun d ⟨valueD, topD, Od, Kd⟩ => ?_)
  have Ksd : Keeps clob s d := Ksb.widen Kd
  have Sd := scratch.of_keeps Ksd (by unfold clob; decide)
  have markerD : word d.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [Od.word (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> left <;> omega) (by have := scratch.nowrap; omega)]
    exact markerB
  have C : ExponentShift.Context base size (2 * w) markerOffset out
      ((Spec.Rsa.splitTwos (c - 1)).1 % 64) d :=
    ⟨Sd, by omega, by omega, markerFit, by omega, Nat.mod_lt _ (by decide), markerD, topD⟩
  have valueD' : val32 d.mem base out (2 * w) = c / 2 := by rw [valueD, candidateB]
  refine WP.seq (WP.mono (ExponentShift.passes_exponent C odd valueD') fun e ⟨Ce, Oe, Ve, Ke⟩ => ?_)
  refine WP.mono (finish_ok Ce.scratch markerFit (by omega)) fun t ⟨markerT, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (Ksd.widen Ke).widen Kt⟩
  · rw [Ot.val32 (Or.inl (by omega)) (by have := scratch.nowrap; omega)]
    exact Ve
  · have : out + 4 * (2 * w) = out + 8 * w := by omega
    rw [this] at markerT
    exact markerT.trans Ce.value
  · have Fsb : Outs base (ranges w src out) s.mem b.mem := by
      rw [← Ma]
      exact Outs.of_outside Ob (List.mem_cons_self ..)
    have Fd : Outs base (ranges w src out) b.mem d.mem := Od.cover (by
      intro r mem
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact ⟨(src + 8 * w, 4), by simp [ranges], by omega, by omega⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega, by omega⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega, by omega⟩)
    have Fe : Outs base (ranges w src out) d.mem e.mem :=
      Outs.of_outside (Oe.mono (by omega) (by omega)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have Ft : Outs base (ranges w src out) e.mem t.mem :=
      Outs.of_outside (Ot.mono (by omega) (by omega)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    exact ((Fsb.trans Fd).trans Fe).trans Ft

end VG.Proof.RsaKeyGen.X86.Exponent
