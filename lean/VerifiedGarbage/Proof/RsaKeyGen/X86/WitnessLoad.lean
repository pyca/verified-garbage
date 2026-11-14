module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
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
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallbackWord
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32
import VerifiedGarbage.Proof.RsaKeyGen.WitnessSample
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessZeros
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData

/-! ### `RsaKeyGen.X86.WitnessSample`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.WitnessUniform`, which only this module used -/

section

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
  refine WP.seq (WP.mono (WitnessLower.code_ok scratch (by omega_using [positive]) (by omega_using [srcFit])) fun a ⟨lower, Ma, Ka⟩ => ?_)
  refine WP.seq (WP.mono (WitnessOdd.mark_ok (n := 2 * w) (scratch.of_keeps Ka (by decide)) (by omega_using [positive]) (by omega_using [srcFit]))
    fun b ⟨valueB, saved, Ob, Kb⟩ => ?_)
  rw [Ma] at valueB saved Ob
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.lessThan_ok w (scratch.of_keeps Ksb (by unfold clob; decide))
    positive srcFit modFit) fun c ⟨compared, Kc, Mc⟩ => ?_)
  rw [wordsVal_eq_val32, wordsVal_eq_val32, valueB,
    Ob.val32 (by omega_using [positive, apart]) (by have := scratch.nowrap; omega_using [modFit, this])] at compared
  have Ksc : Keeps clob s c := Ksb.widen Kc
  have Oc : Outside base src 4 s.mem c.mem := Mc ▸ Ob
  have savedC : c.gpr .esi = s.mem.readW (off base src) 32 := (Kc.1 .esi (by decide)).trans saved
  refine WP.seq (WP.mono (WitnessOdd.restore_ok (n := 2 * w) (scratch.of_keeps Ksc (by unfold clob; decide))
    (by omega_using [positive]) (by omega_using [srcFit]) Oc savedC) fun d ⟨valueD, Od, Kd⟩ => ?_)
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
        (2 ≤ val32 s.mem base src (2 * w) ∧ val32 s.mem base src (2 * w) < val32 s.mem base modulus (2 * w) - 1) := by omega_using [odd]
    simp only [mask32, cmask, decide_eq_true_eq, compare]
  · rw [T.mem]; exact valueD
  · rw [T.mem]; exact Od

end VG.Proof.RsaKeyGen.X86.WitnessUniform

end

end

/-! ### `RsaKeyGen.X86.WitnessFallback`, which only this module used -/

section

/-! # Native fallback produces exactly the reviewed forced witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem codeAt_ok {s : State} {base : Addr} {size k src : Nat} (scratch : Scr s base size)
    (positive : 2 ≤ k) (fit : src + 4 * k ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (codeAt k src)) s fun t =>
      val32 t.mem base src k =
        (if uniform then val32 s.mem base src k else (val32 s.mem base src k ||| 2) % 2 ^ (32 * k - 1)) ∧
      Outside base src (4 * k) s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold codeAt
  refine WP.block_append (WP.mono (low_ok (uniform := uniform) scratch (by omega_using [positive, fit]) mask) fun a ⟨low, Oa, Ka⟩ => ?_)
  refine WP.mono (high_ok (uniform := uniform) (scratch.of_keeps Ka (by decide)) (by omega_using [positive, fit])
    (by rw [Ka.1 .eax (by decide)]; exact mask)) fun t ⟨top, Ot, Kt⟩ => ?_
  have lowSame : w32 t.mem base src = w32 a.mem base src := Ot.w32 (by omega_using [positive]) (by have := scratch.nowrap; omega_using [fit, this])
  have topSame : w32 a.mem base (src + 4 * k - 4) = w32 s.mem base (src + 4 * k - 4) :=
    Oa.w32 (by omega_using [positive]) (by have := scratch.nowrap; omega_using [fit, this])
  refine ⟨?_, (Oa.mono (by omega_using []) (by omega_using [positive])).trans (Ot.mono (by omega_using [positive]) (by omega_using [positive])), Ka.trans Kt⟩
  cases uniform
  · simp at low top
    change val32 t.mem base src k = (val32 s.mem base src k ||| 2) % 2 ^ (32 * k - 1)
    apply VG.Proof.RsaKeyGen.val32_witness_fallback (by omega_using [positive])
    · rw [lowSame, low]
    · rw [show src + 4 * (k - 1) = src + 4 * k - 4 by omega_using [positive], top, topSame]
    · intro j first last
      exact (Ot.w32 (by omega_using [last]) (by have := scratch.nowrap; omega_using [fit, last, this])).trans
        (Oa.w32 (by omega_using [first]) (by have := scratch.nowrap; omega_using [fit, last, this]))
  · simp at low top
    change val32 t.mem base src k = val32 s.mem base src k
    apply val32_congr
    intro j hj
    by_cases first : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using lowSame.trans low
    · by_cases last : j = k - 1
      · subst j
        rw [show src + 4 * (k - 1) = src + 4 * k - 4 by omega_using [positive]]
        exact top.trans topSame
      · exact (Ot.w32 (by omega_using [last]) (by have := scratch.nowrap; omega_using [fit, hj, this])).trans
          (Oa.w32 (by omega_using [first]) (by have := scratch.nowrap; omega_using [fit, hj, this]))

end VG.Proof.RsaKeyGen.X86.WitnessFallback

end

end


/-! # Native witness sampling computes the exact reviewed value and uniform flag -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessSample
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessSample

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem codeAt_ok {s : State} {base : Addr} {size w k src modulus c x : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (two : 2 ≤ k) (narrow : k ≤ 2 * w) (srcFit : src + 8 * w ≤ size) (modFit : modulus + 8 * w ≤ size)
    (apart : src + 8 * w ≤ modulus ∨ modulus + 8 * w ≤ src)
    (candidate : val32 s.mem base modulus (2 * w) = c) (witness : val32 s.mem base src (2 * w) = x)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) (bound : x < 2 ^ (32 * k)) :
    WP isa (codeAt k w src modulus) s fun t =>
      val32 t.mem base src (2 * w) = (Spec.RsaKeyGen.witness (c - 1) x).1 ∧
      t.gpr .eax = cmask (Spec.RsaKeyGen.witness (c - 1) x).2 ∧
      Outside base src (8 * w) s.mem t.mem ∧ Keeps clob s t := by
  have sample := VG.Proof.RsaKeyGen.witness_sampleAt shape bound
  -- The words above the `k` low ones are zero.
  have split (m : Mem) : val32 m base src (2 * w) = val32 m base src k + 2 ^ (32 * k) * val32 m base (src + 4 * k) (2 * w - k) := by
    rw [← VG.Proof.Mont.val32_append, Nat.add_sub_cancel' narrow]
  have parts {lo hi v : Nat} (h : v = lo + 2 ^ (32 * k) * hi) (hv : v < 2 ^ (32 * k)) : lo = v ∧ hi = 0 := by
    rcases Nat.eq_zero_or_pos hi with e | e
    · subst e; rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨h.symm, rfl⟩
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) e; omega_using [h, hv, this]
  have lowX : val32 s.mem base src k = x ∧ val32 s.mem base (src + 4 * k) (2 * w - k) = 0 :=
    parts (by rw [← witness]; exact split s.mem) bound
  unfold codeAt
  refine WP.seq (WP.mono (WitnessUniform.code_ok scratch positive srcFit modFit apart
    (by rw [candidate]; exact odd)) fun a ⟨uniform, Va, Oa, Ka⟩ => ?_)
  rw [candidate, witness] at uniform
  have lowA : val32 a.mem base src k = x ∧ val32 a.mem base (src + 4 * k) (2 * w - k) = 0 :=
    parts (by rw [← (Va.trans witness)]; exact split a.mem) bound
  refine WP.mono (WitnessFallback.codeAt_ok (uniform := decide (2 ≤ x ∧ x < c - 1))
    (scratch.of_keeps Ka (by unfold WitnessUniform.clob; decide)) two (by omega_using [narrow, srcFit]) uniform)
    fun t ⟨V, Ot, Kt⟩ => ?_
  have high : val32 t.mem base (src + 4 * k) (2 * w - k) = 0 := by
    rw [← lowA.2]
    apply val32_congr
    intro j hj
    exact Ot.w32 (by omega_using []) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
  refine ⟨?_, ?_, (Oa.mono (by omega_using []) (by omega_using [positive])).trans (Ot.mono (by omega_using []) (by omega_using [narrow])), ?_⟩
  · rw [split t.mem, high, Nat.mul_zero, Nat.add_zero, V, lowA.1, sample]
  · rw [Kt.1 .eax (by decide), uniform, sample]
  · exact (Ka.mono (by unfold clob WitnessUniform.clob; decide)).widen Kt

end VG.Proof.RsaKeyGen.X86.WitnessSample

end

end


/-! # Entropy import and interval sampling retain all reusable candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem codeAt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) {D k : Nat} (width : 4 * input.count = D) (two : 2 ≤ k)
    (narrow : k ≤ input.count) (wide : input.count ≤ g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt D k g.w) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) D))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  rw [Prepared.slot_eq, Prepared.slot_eq, ← width, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  have arrayFit : g.array 6 + 4 * g.words ≤ g.L := v.arrayFit (by decide)
  have hw : g.words = 2 * g.w := rfl
  have dstAddr : input.dst.setWidth 64 = off g.W (g.array 6) := by
    rw [← destination]
    have fit : g.array 6 < g.L := by
      have := v.minWidth
      unfold Geometry.words at arrayFit
      omega_using [arrayFit, this]
    exact S.ready.scratch.ea fit
  have region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr]
  have load := Import.load_ok C source destination
  change WP isa (VG.Impl.RsaKeyGen.X86.Import.load input.count (g.array 6)) s _ at load
  refine WP.seq (WP.mono load fun a ⟨value, F, K⟩ => ?_)
  have Va : val32 a.mem g.W (g.array 6) input.count =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * input.count)) := by
    rw [dstAddr] at value
    rw [← VG.Proof.Bignum.read_eq_val32]
    exact value
  rw [region] at F
  have Oa := frame_outside F (by have := S.ready.scratch.nowrap; omega_using [wide, arrayFit, this])
  have A := WitnessMont.data_outside v S (Oa.mono (by omega_using []) (by omega_using [wide])) K (by decide) (by decide)
  refine WP.seq (WP.mono (WitnessLoad.zeros_ok A.ready.scratch (g.array 6 + 4 * k) (2 * g.w - k)
    (by omega_using [narrow, wide, arrayFit, hw])) fun b ⟨Zb, Ob, Kb⟩ => ?_)
  have B := WitnessMont.data_outside v A
    (Ob.mono (by have := g.arrayBefore (i := 5) (j := 6) (by decide); omega_using [])
      (by omega_using [narrow, wide, hw])) Kb (by decide) (by decide)
  -- The witness: the draw's low `32 k` bits, zeros above.
  have lowB : val32 b.mem g.W (g.array 6) k =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * input.count)) % 2 ^ (32 * k) := by
    rw [← Va, show input.count = k + (input.count - k) by omega_using [narrow], VG.Proof.Mont.val32_append,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
    exact Ob.val32 (by omega_using []) (by have := S.ready.scratch.nowrap; omega_using [narrow, wide, arrayFit, this])
  have wordsB : val32 b.mem g.W (g.array 6) (2 * g.w) = val32 b.mem g.W (g.array 6) k := by
    rw [show 2 * g.w = k + (2 * g.w - k) by omega_using [narrow, wide, hw], VG.Proof.Mont.val32_append, Zb,
      Nat.mul_zero, Nat.add_zero]
  refine WP.mono (WitnessSample.codeAt_ok B.ready.scratch (by have := v.minWidth; omega_using [this]) two
    (by omega_using [narrow, wide, hw])
    (by omega_using [arrayFit, hw])
    (by have := v.arrayFit (j := 0) (by decide); unfold Geometry.words at this; omega_using [this])
    (Or.inr (by have := g.arrayBefore (i := 0) (j := 6) (by decide); unfold Geometry.words at this; omega_using [this]))
    B.ready.modulus.candidate (wordsB.trans lowB) odd shape (Nat.mod_lt _ (Nat.two_pow_pos _)))
    fun t ⟨Vt, mask, Ot, Kt⟩ => ?_
  rw [VG.Proof.RsaKeyGen.witness_mod shape] at Vt mask
  have Ot' : Outside g.W (g.array 6) (4 * g.words) b.mem t.mem := by
    rw [show 4 * g.words = 8 * g.w by unfold Geometry.words; omega_using []]
    exact Ot
  exact ⟨WitnessMont.data_outside v B Ot' Kt (by unfold WitnessSample.clob; decide)
    (by unfold WitnessSample.clob; decide), Vt, mask,
    ((Oa.mono (by omega_using []) (by omega_using [wide])).trans
      (Ob.mono (by omega_using []) (by omega_using [narrow, wide, hw]))).trans Ot',
    ((K.mono (by unfold clob; decide)).widen Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessLoad
