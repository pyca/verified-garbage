module
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateCompute
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateLoad

/-! # One native reduction constructs both p and its exact generator exponent -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem candidateCompute_ok {s : State} {base : Addr} {size plen qlen n q : Nat}
    (S : Scr s base size) (width : n ≤ 48) (room : 3072 ≤ size) (positive : 0 < n)
    (p4 : 4 ≤ plen) (pWidth : plen ≤ 8 * n) (pWords : plen % 4 = 0)
    (q4 : 4 ≤ qlen) (qWidth : qlen ≤ 8 * n) (qWords : qlen % 4 = 0)
    (xfit : (s.gpr .esi).toNat + plen ≤ 2 ^ 32) (qfit : (s.gpr .ecx).toNat + qlen ≤ 2 ^ 32)
    (xread : ∀ d, d + 4 ≤ plen → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (qread : ∀ d, d + 4 ≤ qlen → InRegions (s.rd ++ s.wr) ((s.gpr .ecx).setWidth 64 + BitVec.ofNat 64 d) 4)
    (xapart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, plen⟩ ⟨base, size⟩)
    (qapart : Region.Disjoint ⟨(s.gpr .ecx).setWidth 64, qlen⟩ ⟨base, size⟩)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .ecx).setWidth 64) qlen) = q)
    (qpos : 0 < q) (qbound : 2 * q < 2 ^ (32 * (2 * n))) :
    WP isa (candidateCompute plen qlen n) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) plen)
      val32 t.mem base candidateP (2 * n) = x + 1 - x % (2 * q) ∧
      val32 t.mem base candidateQuotient (2 * n) = (x + 1 - x % (2 * q) - 1) / q ∧
      Outs base ((candidateQuotient, 8 * n) ::
        ((candidateDivisor, 4 * (2 * n + 1)) :: (candidateTemporary, 4 * (2 * n + 1)) :: candidateWrites (2 * n))) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  unfold candidateCompute loadCandidate
  refine WP.seq (WP.mono (loadComponent_ok S (by unfold candidateQuotient; omega) xfit p4 pWidth pWords xread
    (xapart.sub_right (Offset.sub_base _ (by unfold candidateQuotient; omega)))) fun a ⟨xval, Ka, Oa⟩ => ?_)
  refine WP.seq (wp_movS rfl fun b ab _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s b := (Ka.mono (by decide)).trans (ab.keeps.mono (by decide))
  have qb : b.gpr .esi = s.gpr .ecx := ab.gpr.trans (Ka.1 _ (by decide))
  have qbytes : Spec.Rsa.bytesAt b.mem ((b.gpr .esi).setWidth 64) qlen =
      Spec.Rsa.bytesAt s.mem ((s.gpr .ecx).setWidth 64) qlen := by
    rw [qb, ab.mem]
    apply drawFrame_bytes (copyOutside_frame Oa) ?_ (by omega)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact qapart.sub_right (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        (Offset.sub_base base (d := 0) (n := 8 * n) (k := size) (by omega)))
  refine WP.seq (WP.mono (loadDivisor_ok (S.of_keeps K (by decide)) width (by omega)
    (by rw [qb]; exact qfit) q4 qWidth qWords
    (by intro d hd; rw [qb, K.2.1, K.2.2]; exact qread d hd)
    (by rw [qb]; exact qapart.sub_right (Offset.sub_base _ (by unfold candidateDivisor; omega)))) fun c ⟨divisor, Oc, Kc⟩ => ?_)
  rw [qbytes, qval] at divisor
  have xvalue : val32 c.mem base candidateQuotient (2 * n) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) plen) := by
    rw [Oc.val32 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [candidateQuotient, candidateDivisor, candidateTemporary] <;> omega)
      (by unfold candidateQuotient; omega), ab.mem, ← wordsVal_eq_val32, xval]
  have Ksc := K.trans (Kc.mono (by decide))
  refine WP.mono (candidateReduction_ok (S.of_keeps Ksc (by decide)) (by omega) (by omega) room qpos qbound xvalue divisor)
    fun t ⟨pv, ev, Ot, Kt⟩ => ?_
  refine ⟨pv, ev, ?_, Ksc.trans (Kt.mono (by decide))⟩
  have Oab : Outside base candidateQuotient (8 * n) s.mem b.mem := by rw [ab.mem]; exact Oa
  exact ((Outs.of_outside Oab (by simp)).trans (Oc.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp))).trans
    (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
end VG.Proof.Dsa.X86.Generation
