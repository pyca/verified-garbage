module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterState
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputCopy
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputZero

/-! # Publish a successful domain or a fully cleared failure result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem finishOutput_ok {P : SearchContextPlan} {initial s : State} {expected : Option Spec.Dsa.Params}
    (F : ParameterFinished P expected initial s)
    (length : P.saved 7 = BitVec.ofNat 32 (2 * P.geometry.pLen + P.geometry.qLen))
    (room : (P.saved 6).toNat + (2 * P.geometry.pLen + P.geometry.qLen) ≤ 2 ^ 32)
    (apart : (P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)).Disjoint
      ⟨(P.saved 6).setWidth 64, 2 * P.geometry.pLen + P.geometry.qLen⟩)
    (write : ∀ i, i < 2 * P.geometry.pLen + P.geometry.qLen →
      InRegions s.wr (off ((P.saved 6).setWidth 64) i) 1) :
    WP isa finishOutput s fun t =>
      t.gpr .eax = (if expected.isSome then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem ((P.saved 6).setWidth 64) (2 * P.geometry.pLen + P.geometry.qLen) =
        (expected.map (Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen)).getD
          (List.replicate (2 * P.geometry.pLen + P.geometry.qLen) 0) ∧
      Frame [⟨(P.saved 6).setWidth 64, 2 * P.geometry.pLen + P.geometry.qLen⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  obtain ⟨W, R, outcome, _, _, _⟩ := F
  have out := R.fixed 6 (by decide) (by decide)
  have len := (R.fixed 7 (by decide) (by decide)).trans length
  have pw := P.geometry.width
  have qw := P.geometry.qWidth
  have positive : 0 < 2 * P.geometry.pLen + P.geometry.qLen := by omega
  have small : 2 * P.geometry.pLen + P.geometry.qLen < 2 ^ 32 := by omega
  unfold finishOutput
  refine WP.seq (WP.mono (frameSuccess_ok R.arena.frame R.representation) fun a ⟨zf, mem, K⟩ => ?_)
  have Ra := R.congr mem K (by decide)
  rcases outcome with ⟨bad, rfl⟩ | ⟨params, good, rfl, encoded⟩
  · have no : W 19 ≠ 1 := by rcases bad with h | h <;> rw [h] <;> decide
    refine WP.ite false (by change a.zf = some false; rw [zf]; congr 1; exact decide_eq_false no)
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.mono (outputZero_ok Ra.arena.frame Ra.representation positive small len
      (by rw [out]; exact room) (by intro i hi; rw [out, K.2.2]; exact write i hi)) fun t ⟨ax, O, bytes, Kt⟩ => ?_
    rw [out, mem] at O
    rw [out] at bytes
    exact ⟨ax, bytes, O, (K.mono (by decide)).trans (Kt.mono (by decide))⟩
  · refine WP.ite true (by change a.zf = some true; rw [zf, good]; rfl)
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (outputCopy_ok Ra positive small len
      (by unfold packed usedBytes domainCheck; omega)
      (by rw [out]; exact room) (by rw [out]; exact apart)
      (by intro i hi; rw [out, K.2.2]; exact write i hi)) fun t ⟨ax, bytes, O, Kt⟩ => ?_
    rw [out, mem] at O bytes
    exact ⟨ax, bytes.trans encoded, O, (K.mono (by decide)).trans Kt⟩
end VG.Proof.Dsa.X86.Generation
