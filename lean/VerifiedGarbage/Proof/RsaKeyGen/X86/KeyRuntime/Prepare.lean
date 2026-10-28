module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Primes
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DSelect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad

/-! # The native factor, LCM, and private-inverse stages compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aPm aQm aE aOne kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady prepareArrays stageRanges stage_keep stage_preserves_num
  stage_mono stage_preserves_e exponentArrays exponent_preserves_num)

theorem prepareLoaded_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa prepareLoaded s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n prepareArrays) s.mem t.mem ∧
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
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), spU]
  have narrowFrame := OutsS.lift (fun _ _ => lcm_stage_frame small) Ov
  have Pv : num v.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans P
  have Qv : num v.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Q
  have Pmv : num v.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pm
  have Qmv : num v.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qm
  have frameV : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => stage_mono (by decide)) narrowFrame
  have prefixFrame := (OutsS.of_outs frameU).trans frameV
  have E : val32 v.mem B kEv 2 = val32 s.mem B kEv 2 := h.read_val32 (by decide) prefixFrame stage_preserves_e
  have loadedV : num v.mem B n aE = val32 v.mem B kEv 2 :=
    (h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans (loaded.trans E.symm)
  have oneV : num v.mem B n aOne = 1 :=
    (h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one
  refine WP.mono (dSelect_ok hv wide loadedV oneV) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  rw [E, L] at inverse
  have frameT : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) v.mem t.mem := by
    rw [← spV]
    exact OutsS.lift (fun _ _ => stage_mono (js := exponentArrays) (by decide)) Ot
  have frame := prefixFrame.trans frameT
  refine ⟨ht, frame, ⟨?_, ?_, ?_, ?_, ?_, h.read_val32 (by decide) frame stage_preserves_e, ?_, ?_, inverse, bit⟩,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pmv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qmv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans L
  · exact (h.read_num (by decide) frame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans loaded
  · exact (h.read_num (by decide) frame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one

end VG.Proof.RsaKeyGen.X86.KeyRuntime
