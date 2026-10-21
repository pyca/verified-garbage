module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLower
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessOdd
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The native uniform mask is exactly the reviewed witness interval [2,c-1) -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessUniform
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86 VG.Impl.RsaKeyGen.X86.WitnessUniform

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w src modulus : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (srcFit : src + 8 * w ≤ size) (modFit : modulus + 8 * w ≤ size)
    (apart : src + 8 * w ≤ modulus ∨ modulus + 8 * w ≤ src)
    (odd : val32 s.mem base modulus (2 * w) % 2 = 1) :
    WP isa (code w src modulus) s fun t =>
      t.gpr .eax = cmask (decide (2 ≤ val32 s.mem base src (2 * w) ∧
        val32 s.mem base src (2 * w) < val32 s.mem base modulus (2 * w) - 1)) ∧
      val32 t.mem base src (2 * w) = val32 s.mem base src (2 * w) ∧
      Outside base src 4 s.mem t.mem ∧ Keeps clob s t := by
  refine WP.seq (WP.mono (WitnessLower.code_ok scratch (by omega) (by omega)) fun a ⟨lower, Ma, Ka⟩ => ?_)
  refine WP.seq (WP.mono (WitnessOdd.mark_ok (n := 2 * w) (scratch.of_keeps Ka (by decide)) (by omega) (by omega))
    fun b ⟨valueB, saved, Ob, Kb⟩ => ?_)
  rw [Ma] at valueB saved Ob
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.lessThan_ok w (scratch.of_keeps Ksb (by unfold clob; decide))
    positive srcFit modFit) fun c ⟨compared, Kc, Mc⟩ => ?_)
  rw [wordsVal_eq_val32, wordsVal_eq_val32, valueB,
    Ob.val32 (by omega) (by have := scratch.nowrap; omega)] at compared
  have Ksc : Keeps clob s c := Ksb.widen Kc
  have Oc : Outside base src 4 s.mem c.mem := Mc ▸ Ob
  have savedC : c.gpr .esi = s.mem.readW (off base src) 32 := (Kc.1 .esi (by decide)).trans saved
  refine WP.seq (WP.mono (WitnessOdd.restore_ok (n := 2 * w) (scratch.of_keeps Ksc (by unfold clob; decide))
    (by omega) (by omega) Oc savedC) fun d ⟨valueD, Od, Kd⟩ => ?_)
  refine wp_and fun t T => WP.block_nil ?_
  have lowerD : d.gpr .ebx = mask32 (2 ≤ val32 s.mem base src (2 * w)) := by
    rw [Kd.1 .ebx (by decide), Kc.1 .ebx (by decide), Kb.1 .ebx (by decide), lower]
    simp only [cmask, mask32, decide_eq_true_eq]
  have comparedD : d.gpr .eax = mask32 (val32 s.mem base src (2 * w) +
      (1 - val32 s.mem base src (2 * w) % 2) < val32 s.mem base modulus (2 * w)) :=
    (Kd.1 .eax (by decide)).trans compared
  refine ⟨?_, ?_, ?_, ((Ksc.widen Kd).widen T.keeps)⟩
  · rw [T.gpr, comparedD, lowerD, mask32_and]
    have compare : (val32 s.mem base src (2 * w) + (1 - val32 s.mem base src (2 * w) % 2) <
        val32 s.mem base modulus (2 * w) ∧ 2 ≤ val32 s.mem base src (2 * w)) ↔
        (2 ≤ val32 s.mem base src (2 * w) ∧ val32 s.mem base src (2 * w) < val32 s.mem base modulus (2 * w) - 1) := by omega
    simp only [mask32, cmask, decide_eq_true_eq, compare]
  · rw [T.mem]; exact valueD
  · rw [T.mem]; exact Od

end VG.Proof.RsaKeyGen.X86.WitnessUniform
