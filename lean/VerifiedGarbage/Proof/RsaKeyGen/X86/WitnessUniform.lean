module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.RsaKeyGen.X86.OrScan
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessOdd
import VerifiedGarbage.Proof.Mont.LowUpdate32
import Init.Prelude
/-! # The native uniform mask is exactly the reviewed witness interval [2,c-1) -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/OrScan.lean`, which only this module imported.
section

/-! # The native OR scan detects exactly a zero integer without writing memory -/

section
namespace VG.Proof.RsaKeyGen.X86.OrScan
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.OrScan

theorem code_ok {s : State} {base : Addr} {size n src : Nat}
    (scratch : Scr s base size) (positive : 0 < n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      (t.gpr .ebx = 0#32 ↔ val32 s.mem base src n = 0) ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edx] s t := by
  let Inv := fun j t => t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edx] s t ∧
    (t.gpr .ebx = 0#32 ↔ val32 s.mem base src j = 0)
  have stable : LoopStable Inv := by
    rintro j u t ⟨M, K, Z⟩ ⟨Mt, Rd, Wr, R⟩
    refine ⟨Mt.trans M, ⟨?_, Rd.trans K.2.1, Wr.trans K.2.2⟩, ?_⟩
    · intro r mem
      exact (R r (by intro eq; subst r; simp at mem) (by intro eq; subst r; simp at mem)).trans (K.1 r mem)
    · rw [R .ebx (by decide) (by decide)]
      exact Z
  unfold code
  refine WP.seq (wp_movS rfl fun a A _ => WP.block_nil ?_)
  refine wordLoop_ok Inv positive (by have := scratch.size_lt; omega) stable
    ⟨A.mem, A.keeps.mono (by decide), by rw [A.gpr]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩ ?_ ?_
  · intro j index t ⟨M, K, Z⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine wp_orS (readSrc_at' St pointer (d := src) (by omega)) fun u U => WP.block_nil ?_
    refine ⟨⟨U.mem.trans M, K.widen U.keeps, ?_⟩, U.other .ebp (by decide), U.other .edi (by decide)⟩
    rw [U.gpr, BitVec.or_eq_zero_iff, Z, M]
    have wordZero : s.mem.readW (off base (src + 4 * j)) 32 = 0#32 ↔ w32 s.mem base (src + 4 * j) = 0 :=
      ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
    rw [wordZero, val32_succ]
    have power : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    constructor
    · rintro ⟨left, right⟩
      rw [left, right, Nat.mul_zero]
    · intro sum
      have product : 2 ^ (32 * j) * w32 s.mem base (src + 4 * j) = 0 := by omega
      exact ⟨by omega, (Nat.mul_eq_zero.mp product).resolve_left (Nat.ne_of_gt power)⟩
  · intro t ⟨M, K, Z⟩
    exact ⟨Z, M, K⟩

end VG.Proof.RsaKeyGen.X86.OrScan
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessLowerFinish.lean`, which only this module imported.
section

/-! # Finish the witness lower-bound scan as an all-zero or all-one mask -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem finish_ok {s : State} {base : Addr} {size src upper : Nat} (scratch : Scr s base size)
    (fit : src + 4 ≤ size) (zero : s.gpr .ebx = 0#32 ↔ upper = 0) :
    WP isa (.block (finish src)) s fun t =>
      t.gpr .ebx = cmask (decide (¬(upper = 0 ∧ w32 s.mem base src < 2))) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch fit) fun a A _ => wp_orS rfl fun b B =>
    wp_logicS (.inr rfl) rfl fun c C => wp_orS rfl fun d D => ?_
  have low : c.gpr .eax = (s.mem.readW (off base src) 32 ||| 1#32) ^^^ 1#32 := by
    rw [C.gpr, B.gpr, A.gpr]
    rfl
  have combined : d.gpr .ebx = s.gpr .ebx ||| ((s.mem.readW (off base src) 32 ||| 1#32) ^^^ 1#32) := by
    rw [D.gpr, low, C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide)]
  have combinedZero : (d.gpr .ebx).toNat = 0 ↔ upper = 0 ∧ w32 s.mem base src < 2 := by
    rw [show (d.gpr .ebx).toNat = 0 ↔ d.gpr .ebx = 0#32 from @BitVec.toNat_inj 32 (d.gpr .ebx) (0#32),
      combined, BitVec.or_eq_zero_iff, zero, clear_low_zero]
  refine wp_cmpi fun e E cf _ => wp_sbb_self cf fun f F => wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ((((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).trans (E.keeps _)).widen F.keeps).widen T.keeps⟩
  · rw [T.gpr, F.gpr]
    change cmask (decide ((d.gpr .ebx).toNat < 1)) ^^^ BitVec.allOnes 32 = _
    rw [SigMask.flip_mask]
    exact congrArg cmask (decide_eq_decide.mpr (not_congr combinedZero))
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.WitnessLower
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessLower.lean`, which only this module imported.
section

/-! # The complete native witness scan detects exactly the lower bound two -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem code_ok {s : State} {base : Addr} {size n src : Nat} (scratch : Scr s base size)
    (positive : 2 ≤ n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      t.gpr .ebx = cmask (decide (2 ≤ val32 s.mem base src n)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ebp, .edx] s t := by
  refine WP.seq (WP.mono (OrScan.code_ok scratch (by omega_arith) (by omega_arith)) fun a ⟨Z, M, K⟩ => ?_)
  refine WP.mono (finish_ok (scratch.of_keeps K (by decide)) (by omega_arith) Z) fun t ⟨V, Mt, Kt⟩ => ?_
  rw [M] at V
  have compare : (¬(val32 s.mem base (src + 4) (n - 1) = 0 ∧ w32 s.mem base src < 2)) ↔
      2 ≤ val32 s.mem base src n := by
    rw [← below_two _ _ _ _ (by omega_arith)]
    omega_arith
  rw [decide_eq_decide.mpr compare] at V
  exact ⟨V, Mt.trans M, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessLower
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessOdd.lean`, which only this module imported.
section

/-! # The native range comparison sees x with bit zero set and then restores x -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessOdd
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessOdd

theorem mark_ok {s : State} {base : Addr} {size src n : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : src + 4 * n ≤ size) :
    WP isa (.block (mark src)) s fun t =>
      val32 t.mem base src n = val32 s.mem base src n + (1 - val32 s.mem base src n % 2) ∧
      t.gpr .esi = s.mem.readW (off base src) 32 ∧ Outside base src 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  unfold mark
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => wp_movS rfl fun b B _ => wp_orS rfl fun c C => ?_
  have K : Keeps [.eax, .esi] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have Sc := scratch.of_keeps K (by decide)
  refine wp_storeS (Sc.ea (by omega)) (Sc.write (by omega)) fun t T => WP.block_nil ?_
  have O : Outside base src 4 s.mem t.mem := by
    rw [T.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have low : w32 t.mem base src = w32 s.mem base src ||| 1 := by
    rw [T.mem, w32_write_self, C.gpr, B.gpr, A.gpr, BitVec.toNat_or]
    rfl
  refine ⟨val32_low_or_one positive (by have := scratch.nowrap; omega) O low, ?_, O, K.widen (T.keeps [])⟩
  rw [(T.keeps []).1 .esi (by decide), C.other .esi (by decide), B.other .esi (by decide), A.gpr]

theorem restore_ok {s original : State} {base : Addr} {size src n : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : src + 4 * n ≤ size) (O : Outside base src 4 original.mem s.mem)
    (saved : s.gpr .esi = original.mem.readW (off base src) 32) :
    WP isa (.block (restore src)) s fun t =>
      val32 t.mem base src n = val32 original.mem base src n ∧
      Outside base src 4 original.mem t.mem ∧ Keeps [] s t := by
  unfold restore
  refine wp_storeS (scratch.ea (by omega)) (scratch.write (by omega)) fun t T => WP.block_nil ?_
  have Ot : Outside base src 4 s.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have low : w32 t.mem base src = w32 original.mem base src := by rw [T.mem, w32_write_self, saved]
  exact ⟨val32_restore_low positive (by have := scratch.nowrap; omega) (O.trans Ot) low, O.trans Ot, T.keeps []⟩

end VG.Proof.RsaKeyGen.X86.WitnessOdd
end

end

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
