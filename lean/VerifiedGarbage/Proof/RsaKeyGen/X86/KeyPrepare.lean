module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelect

/-! # The native factor, LCM, and private-inverse stages compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def prepareArrays : List Nat := [aPa, aQa, aPm, aQm, aPhi, aHalf, aU, aV, aDen, aL, aD]

theorem prepareLoaded_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa (prepareLoaded n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n prepareArrays) s.mem t.mem ∧
      KeyReady B n (val32 s.mem B kEv 2) (num s.mem B n aPa) (num s.mem B n aQa) t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have small : k ≤ n := by omega
  have wide : 2 ≤ n := by omega
  have pBound : max (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  have qBound : min (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  unfold prepareLoaded seqs
  refine WP.seq (WP.mono (primes_ok h width positive even boundP boundQ zero one)
    fun u ⟨hu, Ou, P, Q, Pm, Qm, product, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  have frameU : Outs B (stageRanges n prepareArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  refine WP.seq (WP.mono (lcmPart_ok hu width positive
    (by rw [Pm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound) product oneU)
    fun v ⟨hv, Ov, L, Kv⟩ => ?_)
  rw [Pm, Qm] at L
  have narrowFrame := lcm_stage_frame small Ov
  have Pv : num v.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) narrowFrame).trans P
  have Qv : num v.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) narrowFrame).trans Q
  have Pmv : num v.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) narrowFrame).trans Pm
  have Qmv : num v.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) narrowFrame).trans Qm
  have frameV : Outs B (stageRanges n prepareArrays) u.mem v.mem := stage_mono (by decide) narrowFrame
  have prefixFrame := frameU.trans frameV
  have E : val32 v.mem B kEv 2 = val32 s.mem B kEv 2 := stage_preserves_e prefixFrame
  have loadedV : num v.mem B n aE = val32 v.mem B kEv 2 :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) prefixFrame).trans (loaded.trans E.symm)
  have oneV : num v.mem B n aOne = 1 :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) prefixFrame).trans one
  refine WP.mono (dSelect_ok hv wide loadedV oneV) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  rw [E, L] at inverse
  have frameT : Outs B (stageRanges n prepareArrays) v.mem t.mem :=
    stage_mono (js := exponentArrays) (by decide) Ot
  have frame := prefixFrame.trans frameT
  refine ⟨ht, frame, ⟨?_, ?_, ?_, ?_, ?_, stage_preserves_e frame, ?_, ?_, inverse, bit⟩,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · exact (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ot).trans Pv
  · exact (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ot).trans Qv
  · exact (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ot).trans Pmv
  · exact (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ot).trans Qmv
  · exact (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ot).trans L
  · exact (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) frame).trans loaded
  · exact (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) frame).trans one

end VG.Proof.RsaKeyGen.X86.Key
