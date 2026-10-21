module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHalveStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyTwosLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Preparing and running the complete native common-halving schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem twos_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (twos n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n halveArrays [kFlag] s.mem t.mem ∧
      triple t.mem B n = VG.Proof.RsaKeyGen.halveIter (32 * n)
        (num s.mem B n aPm, num s.mem B n aQm, num s.mem B n aPhi) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fu := h.fit64 (j := aU) (by decide)
  have fq := h.fit64 (j := aQm) (by decide)
  have ff := h.fit64 (j := aPhi) (by decide)
  unfold twos VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide)) fun u ⟨hu, Ou, copiedU, Ku, _⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide)) fun v ⟨hv, Ov, copiedV, Kv, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun w W _ => WP.block_nil ?_)
  have hw := hv.rest W.keeps (by decide) (by decide)
  refine WP.mono (twos_loop hw W.gpr) fun t H => ?_
  have valueW : triple w.mem B n =
      (num s.mem B n aPm, num s.mem B n aQm, num s.mem B n aPhi) := by
    unfold triple
    rw [W.mem, Ov.num (j := aU) (by decide) (by simp) fu, copiedU, copiedV,
      Ou.num (j := aQm) (by decide) (by simp) fq,
      Ov.num (j := aPhi) (by decide) (by simp) ff,
      Ou.num (j := aPhi) (by decide) (by simp) ff]
  have frame : Keep B n halveArrays [kFlag] v.mem t.mem := by
    have F := H.frame
    rw [W.mem] at F
    exact F
  refine ⟨H.workspace, ?_, ?_, ?_⟩
  · exact ((Ou.join Ov (js := halveArrays) (ds := [kFlag])
      (by simp [halveArrays]) (by simp) (by simp [halveArrays]) (by simp))).trans frame
  · rw [H.value, valueW]
  · exact (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans
      ((W.keeps.mono (by decide)).trans H.rest))

end VG.Proof.RsaKeyGen.X86.Key
