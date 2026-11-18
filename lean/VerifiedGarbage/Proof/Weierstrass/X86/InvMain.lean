module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Divstep.Word32Bits
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Weierstrass.MontContract
import VerifiedGarbage.Proof.Divstep.Tc32
import VerifiedGarbage.Proof.Divstep.Iter
import Mathlib.Data.Nat.Prime.Basic
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.Divstep.Alg32
import VerifiedGarbage.Proof.Divstep.Batch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
public import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Framework.X86.Wp
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Divstep.Word32
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Basic
import VerifiedGarbage.Proof.Weierstrass.X86.InvMatrix

/-! ### `Weierstrass.X86.InvBatch`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86.InvCount`, which this module and modules that import it used -/

section

/-! ## `InvStart` -/

@[expose] public section

section

/-! # Initializing the word matrix for a divstep batch -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) :
    WP isa (.block P.batchStart) s fun u =>
      wordState u.mem base P.sW =
        ⟨s.mem.readW (off base P.sW) 32, s.mem.readW (off base P.sF) 32,
          s.mem.readW (off base P.sG) 32, 1, 0, 0, 1⟩ ∧
      Keeps [.eax] s u ∧ Outside base (P.sW + 4) 24 s.mem u.mem := by
  have hn := hs.nowrap
  have eW : P.sW = P.tbl + 288 := rfl
  have eF : P.sF = P.tbl := rfl
  have eG : P.sG = P.tbl + 36 := rfl
  unfold InvCfg.batchStart
  refine WP.block_append (WP.block_append (WP.mono
    (copy_ok 1 hs (o := P.sW + 4) (a := P.sF) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_))
  simp only [val32, Nat.mul_zero, Nat.add_zero] at F₁
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copy_ok 1 hs₁ (o := P.sW + 8) (a := P.sG) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  simp only [val32, Nat.mul_zero, Nat.add_zero] at G₂
  rw [O₁.w32 (by omega_arith) (by omega_arith)] at G₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (setMatrix_ok hs₂ (dst := P.sW + 12) (by omega_arith))
    fun u ⟨U, V, Q, R, K₃, O₃⟩ => ⟨?_, (K₁.trans K₂).trans K₃, ?_⟩
  · have D : w32 u.mem base P.sW = w32 s.mem base P.sW := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), O₂.w32 (by omega_arith) (by omega_arith), O₁.w32 (by omega_arith) (by omega_arith)]
    have F : w32 u.mem base (P.sW + 4) = w32 s.mem base P.sF := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), O₂.w32 (by omega_arith) (by omega_arith), F₁]
    have G : w32 u.mem base (P.sW + 8) = w32 s.mem base P.sG := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), G₂]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₃ x (by omega_arith), O₂ x (by omega_arith), O₁ x (by omega_arith)]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvWords` -/

section

/-! # A thirty-step batch computes the full signed transition matrix -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem low_cong32 {m : Mem} {base : Addr} {d : Nat} {x : Int}
    (h : (val32 m base d 9 : Int) % 2 ^ 288 = x % 2 ^ 288) :
    ((m.readW (off base d) 32).toNat : Int) % 2 ^ 32 = x % 2 ^ 32 := by
  have D : (2 : Int) ^ 32 ∣ 2 ^ 288 := pow_dvd_pow 2 (by decide)
  have E : (w32 m base d : Int) % 2 ^ 32 = (val32 m base d 9 : Int) % 2 ^ 32 := by
    rw [val32, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.add_mul_emod_self_left]
  rw [E, ← Int.emod_emod_of_dvd _ D, h, Int.emod_emod_of_dvd _ D]

theorem words_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} {I : Divstep.W32.IState}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hI : StateAt P base I s)
    (hd : |I.d| + 64 < 2 ^ 30) (hf : I.f % 2 = 1) :
    WP isa (.seq (.block P.batchStart) (VG.Impl.Weierstrass.X86.Inv.wordSteps P.sW 30)) s fun z =>
      MatrixAt P base (Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)) z ∧
      Keeps wordClob s z ∧ Outside base P.sW 28 s.mem z.mem := by
  have eW : P.sW = P.tbl + 288 := rfl
  refine WP.seq (WP.mono (batchStart_ok hs ht) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)
  have rel : (wordState s₁.mem base P.sW).rel (Divstep.MSt.init I.d I.f I.g) 32 := by
    rw [V₁]
    refine ⟨hI.d, rfl, rfl, rfl, rfl, low_cong32 hI.f, low_cong32 hI.g⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hd hf 30 (by decide)
  refine WP.mono (wordSteps_ok (hs.of_keeps K₁ (by decide)) (by omega_arith) (by decide) (by decide))
    fun z ⟨V₂, K₂, O₂⟩ => ⟨?_, (K₁.mono (by decide)).trans K₂, ?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D, U, V, Q, R, _, _⟩ := matrix
    exact ⟨D, U, V, Q, R⟩
  · intro x hx
    rw [O₂ x hx, O₁ x (by omega_arith)]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvCount` -/

section

/-! # The public counter for the outer inversion loop -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem batchEnd_ok {P : InvCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hj : 1 ≤ j) (hj32 : j < 2 ^ 32)
    (hc : w32 s.mem base P.sCount = j) :
    WP isa (.block P.batchEnd) s fun z =>
      w32 z.mem base P.sCount = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps [.esi] s z ∧ Outside base P.sCount 4 s.mem z.mem := by
  have hn := hs.nowrap
  have ec : P.sCount = P.tbl + 316 := rfl
  unfold InvCfg.batchEnd
  refine wp_movS (readSrc_sc hs (by omega_arith)) fun s₁ U₁ _ => ?_
  have J : s₁.gpr .esi = BitVec.ofNat 32 j := by
    rw [U₁.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32]
    exact hc
  refine wp_decCounter hj J fun s₂ J₂ K₂ M₂ => ?_
  have K := U₁.keeps.trans K₂
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega_arith)) (hs₂.write (by omega_arith)) fun s₃ U₃ => ?_
  have J₃ : s₃.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [U₃.gpr, J₂]
  refine wp_testCounter (by omega_arith) J₃ fun z F hz => WP.block_nil ⟨?_, hz, ?_, ?_⟩
  · rw [F.mem, U₃.mem, w32_write_self, J₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · exact (K.trans (U₃.keeps _)).trans (F.keeps _)
  · rw [F.mem, U₃.mem, M₂, U₁.mem]
    exact writeW32_outside _ _ _ (by omega_arith)

end VG.Proof.Weierstrass.X86.Inv

end

end

end

/-! ### `Weierstrass.X86.InvLayout`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86.InvRedSum`, which this module and modules that import it used -/

section

/-! # The signed numerator of a divstep coefficient reduction -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem redSum_ok {s : State} {base : Addr} {size acc modulus tmp n : Nat} (minv : BitVec 32)
    (hs : Scr s base size) (ha : acc + 4 * (n + 2) ≤ size) (hm : modulus + 4 * n ≤ size)
    (ht : tmp + 4 ≤ size)
    (sta : tmp + 4 ≤ acc ∨ acc + 4 * (n + 2) ≤ tmp)
    (sam : acc + 4 * (n + 2) ≤ modulus ∨ modulus + 4 * n ≤ acc)
    (stm : tmp + 4 ≤ modulus ∨ modulus + 4 * n ≤ tmp) :
    WP isa (.block (redSum acc modulus tmp n minv)) s fun z =>
      Unch base [(acc, 4 * (n + 2)), (tmp, 4)] s.mem z.mem ∧ Keeps wordClob s z ∧
      val32 z.mem base acc (n + 2) =
        (val32 s.mem base acc (n + 1) +
          (w32 s.mem base acc * minv.toNat % 2 ^ 32) * val32 s.mem base modulus n +
          2 ^ (32 * (n + 1)) *
            (if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then 2 ^ 32 - 1 else 0)) %
          2 ^ (32 * (n + 2)) := by
  have hn := hs.nowrap
  unfold redSum
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono (maskOf_ok hs (by omega_using [ha])) fun s₁ ⟨C₁, K₁, M₁⟩ => ?_)))))
  refine wp_movS rfl fun s₂ U₂ _ => WP.block_nil ?_
  have K₂ : Keeps wordClob s s₂ := (K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have M₂ : s₂.mem = s.mem := U₂.mem.trans M₁
  have hs₂ := hs.of_keeps K₂ (by decide)
  refine WP.mono (zeros_ok hs₂ (acc := acc + 4 * (n + 1)) (k := 1) (by omega_using [ha]))
    fun s₃ ⟨O₃, V₃, K₃⟩ => ?_
  have V₃' : val32 s₃.mem base acc (n + 2) = val32 s.mem base acc (n + 1) := by
    simp only [val32, Nat.mul_zero, Nat.add_zero] at V₃
    rw [val32_succ, O₃.val32 (by omega_using []) (by omega_using [ha, hn]), V₃, M₂, Nat.mul_zero, Nat.add_zero]
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (quotientWord_ok minv hs₃ (by omega_using [ha]) ht) fun s₄ ⟨Q₄, K₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  rw [O₃.w32 (by omega_using []) (by omega_using [ha, hn]), M₂] at Q₄
  have V₄ : val32 s₄.mem base acc (n + 2) = val32 s.mem base acc (n + 1) := by
    rw [O₄.val32 (by omega_using [sta]) (by omega_using [ha, hn]), V₃']
  have P₄ : val32 s₄.mem base modulus n = val32 s.mem base modulus n := by
    rw [O₄.val32 (by omega_using [stm]) (by omega_using [hm, hn]), O₃.val32 (by omega_using [sam]) (by omega_using [hm, hn]), M₂]
  refine WP.mono (rowAdd_ok hs₄ ht ha hm (by omega_using [sam])
    (row_bound (by rw [V₄]; exact val32_lt _ _ _ _))) fun s₅ ⟨O₅, V₅, K₅⟩ => ?_
  rw [V₄, Q₄, P₄] at V₅
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  refine WP.mono (addSignWord_ok hs₅ (dst := acc + 4 * (n + 1)) (by omega_using [ha]))
    fun z ⟨V₆, K₆, O₆⟩ => ⟨?_, ?_, ?_⟩
  · intro x hx
    have hacc := hx (acc, 4 * (n + 2)) (by simp)
    have htmp := hx (tmp, 4) (by simp)
    rw [O₆ x (by omega_using [hacc]), O₅ x hacc, O₄ x htmp, O₃ x (by omega_using [hacc]), M₂]
  · exact (((K₂.trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans (K₆.mono (by decide))
  · have S : (s₅.gpr .esi).toNat =
        if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then 2 ^ 32 - 1 else 0 := by
      rw [K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), U₂.gpr, C₁]
      split <;> rfl
    rw [val32_succ, O₆.val32 (by omega_using []) (by omega_using [ha, hn]), V₆, S]
    have E := add_top_mod (top := w32 s₅.mem base (acc + 4 * (n + 1)))
      (sign := if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then 2 ^ 32 - 1 else 0)
      (Nat.two_pow_pos (32 * (n + 1))) (val32_lt s₅.mem base acc (n + 1))
    rw [E, ← val32_succ, Nat.mul_comm (2 ^ (32 * (n + 1))) (2 ^ 32), ← pow32_succ, V₅]

end VG.Proof.Weierstrass.X86.Inv

end

end

/-! ### `Divstep.Red32`, which this module and modules that import it used -/

section

/-! ### `Divstep.Tc32Red`, which this module and modules that import it used -/

section

/-! # Signed Montgomery reduction on multiword values -/

@[expose] public section

namespace VG.Proof.Divstep.W32

/-- `-p < mredRaw t < 2p` for `|t| ≤ 2^31 p`. -/
theorem mredRaw_range {p m t : Int} (hp : 0 < p) (hm : (p * m + 1) % 2 ^ 32 = 0) (ht : |t| ≤ 2 ^ 31 * p) :
    -p < mredRaw p m t ∧ mredRaw p m t < 2 * p := by
  have hraw := mredRaw_spec (t := t) hm
  have hk0 : 0 ≤ (t * m) % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have hk1 : (t * m) % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  rw [abs_le] at ht
  constructor
  · by_contra h; push Not at h
    have : 2 ^ 32 * mredRaw p m t ≤ 2 ^ 32 * (-p) := by nlinarith
    nlinarith
  · by_contra h; push Not at h
    have : 2 ^ 32 * (2 * p) ≤ 2 ^ 32 * mredRaw p m t := by nlinarith
    nlinarith

/-- `mred` as the code computes it, on words of `n + 1` (`A = 2^(32 n)`, `p < A`):
`W` holds `t`; `E` the sum `W + A 2^32 S + k p` modulo `A 2^64`, for `W`'s sign
word `S` and `k ≡ W m`; `R` its words above the lowest; `R₁ = R + p` if
negative; `R₂ = R₁ - p`; `R₃ = R₂ + p` if negative. -/
theorem mred_first_words {A B H p m t W k E R R₁ : Int} (hB : B = 2 ^ 32) (hH : H = 2 ^ 31) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hW0 : 0 ≤ W) (hW1 : W < A * B) (hWt : W % (A * B) = t % (A * B))
    (hk0 : 0 ≤ k) (hk1 : k < B) (hk : k % B = (W * m) % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    : R₁ = mredRaw p m t + if mredRaw p m t < 0 then p else 0 := by
  subst hB hH
  have hH : 0 < A * 2 ^ 31 := by positivity
  have hQ : A * 2 ^ 32 = 2 * (A * 2 ^ 31) := by ring
  have hpH : 2 * p < A * 2 ^ 31 := by omega_arith
  rw [abs_le] at ht
  have htH : -(A * 2 ^ 31) ≤ t ∧ t < A * 2 ^ 31 := by
    constructor <;> omega_arith
  -- `W` holds `t`.
  have eW := tc_eq hH htH.1 htH.2 hW0 (by rw [← hQ]; exact hW1) (by rw [← hQ]; exact hWt)
  have sW := tc_neg htH.1 htH.2 eW
  -- `k = t m mod 2^32`.
  have hk' : k = (t * m) % 2 ^ 32 := by
    have h32 : (2 : Int) ^ 32 ∣ A * 2 ^ 32 := dvd_mul_left _ _
    have hWt' : W % 2 ^ 32 = t % 2 ^ 32 := by
      rw [← Int.emod_emod_of_dvd W h32, ← Int.emod_emod_of_dvd t h32, hWt]
    rw [← Int.emod_eq_of_lt hk0 hk1, hk, Int.mul_emod, hWt', ← Int.mul_emod]
  -- The sum is `t + k p = 2^32 r`, in two's complement.
  set r := mredRaw p m t with hr
  have hraw : 2 ^ 32 * r = t + (t * m) % 2 ^ 32 * p := mredRaw_spec hm
  rw [← hk'] at hraw
  obtain ⟨rlo, rhi⟩ := mredRaw_range hp hm (abs_le.mpr ⟨by omega_arith, ht.2⟩)
  rw [← hr] at rlo rhi
  have hE' : E = 2 ^ 32 * (r + if r < 0 then A * 2 ^ 32 else 0) := by
    have hX : W + A * 2 ^ 32 * (if A * 2 ^ 31 ≤ W then 2 ^ 32 - 1 else 0) + k * p =
        2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) + A * 2 ^ 32 * 2 ^ 32 *
          ((if t < 0 then 1 else 0) - (if r < 0 then 1 else 0)) := by
      have hS : (if A * 2 ^ 31 ≤ W then (2 : Int) ^ 32 - 1 else 0) = if t < 0 then 2 ^ 32 - 1 else 0 := by
        simp only [sW]
      have hkp : k * p = 2 ^ 32 * r - t := by omega_arith
      rw [hS, eW, hkp]
      by_cases h1 : t < 0 <;> by_cases h2 : r < 0 <;> simp only [h1, h2, ↓reduceIte] <;> ring
    rw [hE, hX, Int.add_mul_emod_self_left]
    have h0 : 0 ≤ 2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) := by
      split <;> omega_arith
    have h1 : 2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) < A * 2 ^ 32 * 2 ^ 32 := by
      split <;> omega_arith
    rw [Int.emod_eq_of_lt h0 h1]
    split <;> ring
  have eR : R = r + if r < 0 then 2 * (A * 2 ^ 31) else 0 := by
    rw [hR, hE', Int.mul_ediv_cancel_left _ (by norm_num), hQ]
  have rH : -(A * 2 ^ 31) ≤ r ∧ r < A * 2 ^ 31 := ⟨by omega_arith, by omega_arith⟩
  have sR := tc_neg rH.1 rH.2 eR
  -- `R₁ = r + p` if negative, else `r`.
  have eR₁ : R₁ = r + if r < 0 then p else 0 := by
    have hc : (if A * 2 ^ 31 ≤ R then p else 0) = if r < 0 then p else 0 := by simp only [sR]
    rw [hR₁, hc, eR, hQ]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]
      rw [show r + 2 * (A * 2 ^ 31) + p = r + p + 2 * (A * 2 ^ 31) * 1 by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega_arith) (by omega_arith)]
    · simp only [h, ↓reduceIte, Int.add_zero]
      rw [Int.emod_eq_of_lt (by omega_arith) (by omega_arith)]
  exact eR₁

end VG.Proof.Divstep.W32

end

end

/-! # Finishing a 32-bit divstep reduction with one conditional subtraction -/

@[expose] public section

namespace VG.Proof.Divstep.W32

theorem norm_first_mod {p r : Int} (_hp : 0 < p) (hr : -p < r ∧ r < 2 * p) :
    (r + if r < 0 then p else 0) % p = norm p r := by
  unfold norm
  by_cases h : r < 0
  · simp only [h, ↓reduceIte]
    exact Int.emod_eq_of_lt (by omega_using [hr]) (by omega_using [h])
  · simp only [h, ↓reduceIte, Int.add_zero]
    by_cases h' : p ≤ r
    · simp only [h', ↓reduceIte]
      calc
        r % p = ((r - p) + p) % p := by rw [Int.sub_add_cancel]
        _ = (r - p) % p := Int.add_emod_right _ _
        _ = r - p := Int.emod_eq_of_lt (by omega_using [h']) (by omega_using [hr])
    · simp only [h', ↓reduceIte]
      exact Int.emod_eq_of_lt (by omega_using [h]) (by omega_using [h'])

theorem mred_first_nat {A B H p m W k E R R₁ : Nat} {t : Int}
    (hB : B = 2 ^ 32) (hH : H = 2 ^ 31) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hW1 : W < A * B) (hWt : (W : Int) % ((A * B : Nat) : Int) = t % ((A * B : Nat) : Int))
    (hk : k = W % B * m % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B)) :
    R₁ < 2 * p ∧ ((R₁ % p : Nat) : Int) = mred p m t := by
  have hB1 : 1 ≤ B := by rw [hB]; exact Nat.one_le_two_pow
  have hk1 : k < B := by rw [hk]; exact Nat.mod_lt _ (by omega_using [hB])
  have F : (R₁ : Int) = mredRaw p m t + if mredRaw p m t < 0 then (p : Int) else 0 := by
    refine mred_first_words (A := A) (B := B) (H := H) (p := p) (m := m) (t := t)
      (W := W) (k := k) (E := E) (R := R) (R₁ := R₁)
      (by rw [hB]; norm_num) (by rw [hH]; norm_num) (by exact_mod_cast hA)
      (by exact_mod_cast hp) (by exact_mod_cast hpA) (by exact_mod_cast hm) ht
      (by omega_using []) (by exact_mod_cast hW1) (by exact_mod_cast hWt)
      (by omega_using []) (by exact_mod_cast hk1) ?_ ?_ ?_ ?_
    · rw [hk]
      have h1 : W % B * m % B = W * m % B := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [h1]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    · rw [hE, ← Nat.cast_mul A H, ite_natCast_le]; push_cast [Nat.cast_sub hB1]; rfl
    · rw [hR]; push_cast; rfl
    · rw [hR₁, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl
  have hm' : ((p : Int) * m + 1) % 2 ^ 32 = 0 := by rw [hB] at hm; exact_mod_cast hm
  have hp' : (0 : Int) < p := by omega_using [hp]
  have bounds := mredRaw_range hp' hm' ht
  constructor
  · split at F <;> omega_arith
  · rw [Int.natCast_emod, F]
    exact norm_first_mod hp' bounds

end VG.Proof.Divstep.W32

end

end

/-! ### `Weierstrass.X86.InvRed`, which only this module used -/

section

/-! # Reduction of a signed divstep coefficient row -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass VG.Impl.Mont

structure RedLay (M : Mod) (size acc tmp out n : Nat) : Prop where
  width : words M = n
  positive : 0 < n
  acc_bound : acc + 4 * (n + 2) ≤ size
  tmp_bound : tmp + 4 * (n + 1) ≤ size
  out_bound : out + 4 * n ≤ size
  mod_bound : M.mo + 4 * n ≤ size
  sub_bound : M.tmp + 4 * n ≤ size
  ta : tmp + 4 * (n + 1) ≤ acc ∨ acc + 4 * (n + 2) ≤ tmp
  am : acc + 4 * (n + 2) ≤ M.mo ∨ M.mo + 4 * n ≤ acc
  tm : tmp + 4 * (n + 1) ≤ M.mo ∨ M.mo + 4 * n ≤ tmp
  sa : M.tmp + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ M.tmp
  sm : M.tmp + 4 * n ≤ M.mo ∨ M.mo + 4 * n ≤ M.tmp
  oa : out + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ out
  os : out + 4 * n ≤ M.tmp ∨ M.tmp + 4 * n ≤ out

theorem reduce_ok {s : State} {base : Addr} {size acc tmp out n p : Nat} {M : Mod} {t : Int}
    (hs : Scr s base size) (L : RedLay M size acc tmp out n)
    (hp : 0 < p) (hm : val32 s.mem base M.mo n = p)
    (hinv : (p * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (ht : |t| ≤ 2 ^ 31 * p)
    (hval : (val32 s.mem base acc (n + 1) : Int) % 2 ^ (32 * (n + 1)) = t % 2 ^ (32 * (n + 1))) :
    WP isa (.block (reduce M acc tmp out)) s fun z =>
      Unch base [(acc, 4 * (n + 2)), (tmp, 4 * (n + 1)), (M.tmp, 4 * n), (out, 4 * n)] s.mem z.mem ∧
      Keeps wordClob s z ∧ (val32 z.mem base out n : Int) = Divstep.W32.mred p (minv32 M).toNat t := by
  have hn := hs.nowrap
  have ha := L.acc_bound; have htmp := L.tmp_bound; have hout := L.out_bound
  have hmod := L.mod_bound; have hsub := L.sub_bound
  have hta := L.ta; have ham := L.am; have htm := L.tm
  have hsa := L.sa; have hoa := L.oa
  unfold reduce
  rw [L.width]
  refine WP.block_append (WP.block_append (WP.mono
    (redSum_ok (minv32 M) hs ha hmod (by omega_arith) (by omega_arith) ham (by omega_arith))
    fun s₁ ⟨O₁, K₁, V₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have M₁ : val32 s₁.mem base M.mo n = p := by
    rw [Outs.val32 O₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith), hm]
  refine WP.mono (addIfNeg_ok hs₁ (acc := acc + 4) (modulus := M.mo) (tmp := tmp) (n := n)
    (by omega_arith) hmod htmp (by omega_arith) htm) fun s₂ ⟨O₂, K₂, V₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have M₂ : val32 s₂.mem base M.mo n = p := by
    rw [Outs.val32 O₂ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith), M₁]
  have P : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
    rw [pow32_succ, Nat.mul_comm]
  have E : val32 s₁.mem base acc (n + 2) =
      (val32 s.mem base acc (n + 1) + 2 ^ (32 * n) * 2 ^ 32 *
        (if 2 ^ (32 * n) * 2 ^ 31 ≤ val32 s.mem base acc (n + 1) then 2 ^ 32 - 1 else 0) +
        (w32 s.mem base acc * (minv32 M).toNat % 2 ^ 32) * p) %
        (2 ^ (32 * n) * 2 ^ 32 * 2 ^ 32) := by
    rw [V₁, hm]
    simp only [sign32]
    have P' : 2 ^ (32 * (n + 2)) = (2 ^ (32 * n) * 2 ^ 32) * 2 ^ 32 := by
      rw [show n + 2 = (n + 1) + 1 by omega_arith, pow32_succ, pow32_succ]
      ring
    rw [P', P]
    rw [Nat.add_right_comm]
  have F : val32 s₂.mem base (acc + 4) (n + 1) =
      (val32 s₁.mem base (acc + 4) (n + 1) +
        if 2 ^ (32 * n) * 2 ^ 31 ≤ val32 s₁.mem base (acc + 4) (n + 1) then p else 0) %
        (2 ^ (32 * n) * 2 ^ 32) := by
    rw [V₂, M₁]
    simp only [sign32, P]
  have H := Divstep.W32.mred_first_nat
    (A := 2 ^ (32 * n)) (B := 2 ^ 32) (H := 2 ^ 31) (p := p) (m := (minv32 M).toNat)
    (W := val32 s.mem base acc (n + 1))
    (k := w32 s.mem base acc * (minv32 M).toNat % 2 ^ 32)
    (E := val32 s₁.mem base acc (n + 2)) (R := val32 s₁.mem base (acc + 4) (n + 1))
    (R₁ := val32 s₂.mem base (acc + 4) (n + 1)) (t := t)
    rfl rfl (Nat.two_pow_pos _) hp (by rw [← hm]; exact val32_lt _ _ _ _) hinv ht
    (by rw [← P]; exact val32_lt _ _ _ _)
    (by simpa only [← P, Nat.cast_pow, Nat.cast_ofNat] using hval)
    (by rw [← low32]) E (high32 _ _ _ _) F
  rcases H with ⟨bound, result⟩
  refine WP.mono (csub_ok hs₂ L.width L.positive (by omega_arith) hout hsub hmod
    (by omega_arith) L.sm (by omega_arith) L.os M₂ bound) fun z ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · intro x hx
    have hac := hx (acc, 4 * (n + 2)) (by simp)
    have htc := hx (tmp, 4 * (n + 1)) (by simp)
    rw [O₃ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact hx _ (by simp)),
      O₂ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega_arith),
      O₁ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega_arith)]
  · exact (K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  · rw [V₃]
    exact result

end VG.Proof.Weierstrass.X86.Inv

end

end


/-! ## `InvCoeff` -/

@[expose] public section

section

/-! # Updating an inverse coefficient from one divstep matrix row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass VG.Impl.Mont

theorem abHalf_ok {s : State} {base : Addr} {size u v acc a b tmp out k p : Nat}
    {M : Mod} {cu cv x y : Int} (hs : Scr s base size)
    (L : LinearLay size u v acc a b tmp (k + 1) k) (R : RedLay M size acc tmp out (k + 1))
    (hp : 0 < p) (hm : val32 s.mem base M.mo (k + 1) = p)
    (hinv : (p * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hu : s.mem.readW (off base u) 32 = BitVec.ofInt 32 cu)
    (hv : s.mem.readW (off base v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hx : (val32 s.mem base a (k + 1) : Int) = x) (hy : (val32 s.mem base b (k + 1) : Int) = y)
    (hxb : |x| ≤ p) (hyb : |y| ≤ p) :
    WP isa (.block (linear u v acc a b tmp (k + 1) k ++ reduce M acc tmp out)) s fun z =>
      (val32 z.mem base out (k + 1) : Int) = Divstep.W32.mred p (minv32 M).toNat (cu * x + cv * y) ∧
      Keeps wordClob s z ∧
      Unch base [(acc, 4 * (k + 1 + 2)), (tmp, 4 * (k + 1 + 1)),
        (M.tmp, 4 * (k + 1)), (out, 4 * (k + 1))] s.mem z.mem := by
  have hn := hs.nowrap
  have hmod := R.mod_bound; have ham := R.am; have htm := R.tm
  refine WP.block_append (WP.mono (linear_ok hs L) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), hx, hy] at V₁
  have hm₁ : val32 s₁.mem base M.mo (k + 1) = p := by
    rw [Outs.val32 O₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hn, hmod]), hm]
  have bound : |cu * x + cv * y| ≤ 2 ^ 31 * p := by
    have H := Divstep.W32.comb_le huv hxb hyb
    have hp' : (0 : Int) ≤ p := Int.natCast_nonneg _
    omega_using [H]
  refine WP.mono (reduce_ok (hs.of_keeps K₁ (by decide)) R hp hm₁ hinv bound V₁)
    fun z ⟨O₂, K₂, V₂⟩ => ⟨V₂, (K₁.mono (by decide)).trans K₂, ?_⟩
  intro q hq
  rw [O₂ q hq]
  apply O₁ q
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hq (acc, 4 * (k + 1 + 2)) (by simp)
  · have := hq (tmp, 4 * (k + 1 + 1)) (by simp)
    simp only
    omega_using [this]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvLayout` -/

section

/-! # Arithmetic layouts for the two rows of a 256-bit divstep batch -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Weierstrass


theorem fgLayout {P : InvCfg} {size row : Nat} (ht : P.tbl + 320 ≤ size) (hr : row ≤ 1) :
    LinearLay size (P.sW + 12 + 8 * row) (P.sW + 16 + 8 * row)
      P.sT P.sF P.sG P.sU 9 7 := by
  constructor <;> (try dsimp only [InvCfg.sW, InvCfg.sT, InvCfg.sF, InvCfg.sG, InvCfg.sU]) <;> omega_arith

theorem abLayout {P : InvCfg} {size row : Nat} (ht : P.tbl + 320 ≤ size) (hr : row ≤ 1) :
    LinearLay size (P.sW + 12 + 8 * row) (P.sW + 16 + 8 * row)
      P.sT P.sA P.sB P.sU 8 7 := by
  constructor <;> (try dsimp only [InvCfg.sW, InvCfg.sT, InvCfg.sA, InvCfg.sB, InvCfg.sU]) <;> omega_arith

theorem redLayout {P : InvCfg} {size out : Nat} (L : WorkLay P size) (ho : out = P.sNF ∨ out = P.sB) :
    RedLay P.M size P.sT P.sU out 8 := by
  have ht := L.tbl_bound; have hm := L.mod_bound; have htmp := L.tmp_bound
  have htm := L.tbl_mod; have htt := L.tbl_tmp; have hmt := L.mod_tmp
  constructor
  · simp only [VG.Impl.Mont.X86.words, L.n4]
  · decide
  all_goals rcases ho with rfl | rfl <;>
    (try dsimp only [InvCfg.sT, InvCfg.sU, InvCfg.sNF, InvCfg.sB]) <;> omega_arith

end VG.Proof.Weierstrass.X86.Inv

end

end

end

/-! ### `Weierstrass.X86.InvFg`, which only this module used -/

section

/-! # Applying both matrix rows to the signed divstep values -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                     InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT, InvCfg.sU, InvCfg.sW]) <;> omega_arith))

theorem fgUpdate_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat} {T : Divstep.MSt} {f g : Int}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hT : MatrixAt P base T s)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hf : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = f % 2 ^ 288)
    (hg : (val32 s.mem base P.sG 9 : Int) % 2 ^ 288 = g % 2 ^ 288)
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ 256)
    (hdivF : 2 ^ 30 ∣ T.u * f + T.v * g) (hdivG : 2 ^ 30 ∣ T.q * f + T.r * g) :
    WP isa (.block P.fgUpdate) s fun z =>
      (val32 z.mem base P.sF 9 : Int) % 2 ^ 288 = ((T.u * f + T.v * g) / 2 ^ 30) % 2 ^ 288 ∧
      (val32 z.mem base P.sG 9 : Int) % 2 ^ 288 = ((T.q * f + T.r * g) / 2 ^ 30) % 2 ^ 288 ∧
      Keeps clob s z ∧ Outside base P.tbl 288 s.mem z.mem ∧
      val32 z.mem base P.sA 8 = val32 s.mem base P.sA 8 ∧
      val32 z.mem base P.sB 8 = val32 s.mem base P.sB 8 := by
  have hn := hs.nowrap
  obtain L₁ : LinearLay size (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using fgLayout ht (row := 0) (by decide)
  obtain L₂ : LinearLay size (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 := by
    simpa only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using fgLayout ht (row := 1) (by decide)
  unfold InvCfg.fgUpdate
  rw [show VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++
      VG.Impl.Weierstrass.X86.Inv.shr30 P.sNF P.sT 9 ++
      VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++
      VG.Impl.Weierstrass.X86.Inv.shr30 P.sNG P.sT 9 =
      (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++
       VG.Impl.Weierstrass.X86.Inv.shr30 P.sNF P.sT 9) ++
      (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++
       VG.Impl.Weierstrass.X86.Inv.shr30 P.sNG P.sT 9) by simp only [List.append_assoc]]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (fHalf_ok hs L₁ (dst := P.sNF) (by apart) (by apart) hT.u hT.v huv hf hg hfb hgb hp hdivF)
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_)))
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain q₁ : s₁.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q := by
    rw [read32_unch O₁ (by apart) (by apart), hT.q]
  obtain r₁ : s₁.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r := by
    rw [read32_unch O₁ (by apart) (by apart), hT.r]
  refine WP.mono (fHalf_ok hs₁ L₂ (dst := P.sNG) (by apart) (by apart) q₁ r₁ hqr
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hf)
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hg) hfb hgb hp hdivG)
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (copy_ok 9 hs₂ (o := P.sF) (a := P.sNF) (by apart) (by apart) (by apart))
    fun s₃ ⟨F₃, K₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (copy_ok 9 hs₃ (o := P.sG) (a := P.sNG) (by apart) (by apart) (by apart))
    fun z ⟨G₄, K₄, O₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₄.val32 (by apart) (by apart), F₃, Outs.val32 O₂ (by apart) (by apart)]
    exact F₁
  · rw [G₄, O₃.val32 (by apart) (by apart)]
    exact G₂
  · exact ((K₁.trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · have H₁ : Outside base P.tbl 288 s.mem s₁.mem := O₁.outside (by apart)
    obtain H₂ : Outside base P.tbl 288 s₁.mem s₂.mem := O₂.outside (by apart)
    exact ((H₁.trans H₂).trans (O₃.mono (by apart) (by apart))).trans (O₄.mono (by apart) (by apart))

  · rw [O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
      Outs.val32 O₂ (by apart) (by apart), Outs.val32 O₁ (by apart) (by apart)]
  · rw [O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
      Outs.val32 O₂ (by apart) (by apart), Outs.val32 O₁ (by apart) (by apart)]

end VG.Proof.Weierstrass.X86.Inv

end

end

/-! ### `Weierstrass.X86.InvAb`, which only this module used -/

section

/-! # Applying both matrix rows to the reduced inverse coefficients -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                     InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sT, InvCfg.sU, InvCfg.sW]) <;> omega_arith))

theorem abUpdate_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat} {T : Divstep.MSt} {a b : Int}
    (hs : Scr s base size) (L : WorkLay P size) (hT : MatrixAt P base T s)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hp : 0 < p) (hm : val32 s.mem base P.M.mo 8 = p)
    (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (ha : (val32 s.mem base P.sA 8 : Int) = a) (hb : (val32 s.mem base P.sB 8 : Int) = b)
    (hab : |a| ≤ p) (hbb : |b| ≤ p) :
    WP isa (.block P.abUpdate) s fun z =>
      (val32 z.mem base P.sA 8 : Int) = Divstep.W32.mred p (minv32 P.M).toNat (T.u * a + T.v * b) ∧
      (val32 z.mem base P.sB 8 : Int) = Divstep.W32.mred p (minv32 P.M).toNat (T.q * a + T.r * b) ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 288), (P.M.tmp, 32)] s.mem z.mem ∧
      val32 z.mem base P.sF 9 = val32 s.mem base P.sF 9 ∧
      val32 z.mem base P.sG 9 = val32 s.mem base P.sG 9 := by
  have hn := hs.nowrap
  obtain ht := L.tbl_bound; have hmod := L.mod_bound; have htmp := L.tmp_bound
  obtain htm := L.tbl_mod; have htt := L.tbl_tmp; have hmt := L.mod_tmp
  obtain L₁ : LinearLay size (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using abLayout ht (row := 0) (by decide)
  obtain L₂ : LinearLay size (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7 := by
    simpa only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using abLayout ht (row := 1) (by decide)
  unfold InvCfg.abUpdate
  rw [List.append_assoc
    (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 ++
      VG.Impl.Weierstrass.X86.Inv.reduce P.M P.sT P.sU P.sNF)
    (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7)]
  refine WP.block_append (WP.block_append (WP.mono
    (abHalf_ok hs L₁ (redLayout L (.inl rfl)) hp hm hinv hT.u hT.v huv ha hb hab hbb)
    fun s₁ ⟨A₁, K₁, O₁⟩ => ?_))
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain q₁ : s₁.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q := by
    rw [read32_unch O₁ (by apart) (by apart), hT.q]
  obtain r₁ : s₁.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r := by
    rw [read32_unch O₁ (by apart) (by apart), hT.r]
  refine WP.mono (abHalf_ok hs₁ L₂ (redLayout L (.inr rfl)) hp
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hm) hinv q₁ r₁ hqr
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact ha)
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hb) hab hbb)
    fun s₂ ⟨B₂, K₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (copy_ok 8 hs₂ (o := P.sA) (a := P.sNF) (by apart) (by apart) (by apart))
    fun z ⟨A₃, K₃, O₃⟩ => ⟨?_, ?_, (K₁.trans K₂).trans (K₃.mono (by decide)), ?_, ?_, ?_⟩
  · rw [A₃, Outs.val32 O₂ (by apart) (by apart)]
    exact A₁
  · rw [O₃.val32 (by apart) (by apart)]
    exact B₂
  · intro x hx
    obtain ht' := hx (P.tbl, 288) (by simp)
    obtain hm' := hx (P.M.tmp, 32) (by simp)
    rw [O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

  · rw [O₃.val32 (by apart) (by apart), Outs.val32 O₂ (by apart) (by apart),
      Outs.val32 O₁ (by apart) (by apart)]
  · rw [O₃.val32 (by apart) (by apart), Outs.val32 O₂ (by apart) (by apart),
      Outs.val32 O₁ (by apart) (by apart)]

end VG.Proof.Weierstrass.X86.Inv

end

end


/-! # A complete thirty-step inversion batch -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                     InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sW, InvCfg.sCount]) <;> omega_arith))

theorem batch_ok {P : InvCfg} {s : State} {base : Addr} {size p j : Nat} {I : Divstep.W32.IState}
    (hs : Scr s base size) (L : WorkLay P size) (hI : StateAt P base I s)
    (hd : |I.d| + 64 < 2 ^ 30) (hf : I.f % 2 = 1)
    (hfb : |I.f| ≤ p) (hgb : |I.g| ≤ p) (hab : |I.a| ≤ p) (hbb : |I.b| ≤ p)
    (hp : 0 < p) (hp256 : p < 2 ^ 256) (hm : val32 s.mem base P.M.mo 8 = p)
    (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (hj : 1 ≤ j) (hj32 : j < 2 ^ 32) (hc : w32 s.mem base P.sCount = j)
    (hbound : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
      |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30)
    (hdiv : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
      2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g) :
    WP isa P.batch s fun z =>
      StateAt P base (Divstep.W32.batch 30 p (minv32 P.M).toNat I) z ∧
      w32 z.mem base P.sCount = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem z.mem := by
  have hn := hs.nowrap
  obtain ht := L.tbl_bound; have hmod := L.mod_bound; have htmp := L.tmp_bound
  obtain htm := L.tbl_mod; have htt := L.tbl_tmp
  let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
  change |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30 at hbound
  change 2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g at hdiv
  unfold InvCfg.batch
  refine WP.seq (WP.mono (words_ok hs ht hI hd hf) fun s₁ ⟨Mat₁, K₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.block_append (WP.block_append (WP.mono
    (fgUpdate_ok hs₁ ht Mat₁ hbound.1 hbound.2
      (by rw [O₁.val32 (by apart) (by apart)]; exact hI.f)
      (by rw [O₁.val32 (by apart) (by apart)]; exact hI.g) hfb hgb hp256 hdiv.1 hdiv.2)
    fun s₂ ⟨F₂, G₂, K₂, O₂, A₂, B₂⟩ => ?_))
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  obtain Mat₂ : MatrixAt P base T s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.d
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.u
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.v
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.q
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.r
  refine WP.mono (abUpdate_ok hs₂ L Mat₂ hbound.1 hbound.2 hp
    (by rw [O₂.val32 (by apart) (by apart), O₁.val32 (by apart) (by apart), hm]) hinv
    (by rw [A₂, O₁.val32 (by apart) (by apart)]; exact hI.a)
    (by rw [B₂, O₁.val32 (by apart) (by apart)]; exact hI.b) hab hbb)
    fun s₃ ⟨A₃, B₃, K₃, O₃, F₃, G₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  obtain Count : w32 s₃.mem base P.sCount = j := by
    rw [word_unch O₃ (by apart) (by apart), O₂.w32 (by apart) (by apart),
      O₁.w32 (by apart) (by apart), hc]
  refine WP.mono (batchEnd_ok hs₃ ht hj hj32 Count) fun z ⟨C₄, Z₄, K₄, O₄⟩ =>
    ⟨?_, C₄, Z₄, ((K₁.trans (K₂.mono (by decide))).trans K₃).trans (K₄.mono (by decide)), ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [read32_unch O₄.unch (by apart) (by apart), read32_unch O₃ (by apart) (by apart)]
      rw [Divstep.W32.batch_d]
      exact Mat₂.d
    · rw [O₄.val32 (by apart) (by apart), F₃]
      exact F₂
    · rw [O₄.val32 (by apart) (by apart), G₃]
      exact G₂
    · rw [O₄.val32 (by apart) (by apart)]
      rw [Divstep.W32.batch_a]
      exact A₃
    · rw [O₄.val32 (by apart) (by apart)]
      rw [Divstep.W32.batch_b]
      exact B₃
  · intro x hx
    obtain ht' := hx (P.tbl, 320) (by simp)
    obtain hm' := hx (P.M.tmp, 32) (by simp)
    rw [O₄ x (by apart), O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv

end

end

/-! ### `Weierstrass.X86.InvInit`, which this module and modules that import it used -/

section

/-! # Initial state of the 256-bit divstep inversion -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sW, InvCfg.sCount]) <;> omega))

theorem init_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat}
    (hs : Scr s base size) (L : InvLay P size) (hm : val32 s.mem base P.M.mo 8 = p) :
    WP isa (.block P.init) s fun z =>
      StateAt P base ⟨1, p, val32 s.mem base P.base 8, 0, 1⟩ z ∧
      w32 z.mem base P.sCount = 20 ∧ Keeps [.eax] s z ∧ Outside base P.tbl 320 s.mem z.mem := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hmod := L.mod_bound; have hbase := L.base_bound
  have htm := L.tbl_mod; have hbt := L.base_tbl
  unfold InvCfg.init
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.mono
    (copyPad_ok hs (dst := P.sF) (src := P.M.mo) (by apart) hmod (by apart))
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_)))))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copyPad_ok hs₁ (dst := P.sG) (src := P.base) (by apart) hbase (by apart))
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (zeros_ok hs₂ (acc := P.sA) (k := 8) (by apart)) fun s₃ ⟨O₃, A₃, K₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (one8_ok hs₃ (dst := P.sB) (by apart)) fun s₄ ⟨B₄, K₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.mono (setWord_ok 1 hs₄ (dst := P.sW) (by apart)) fun s₅ ⟨D₅, K₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  refine WP.mono (setWord_ok 20 hs₅ (dst := P.sCount) (by apart)) fun z ⟨C₆, K₆, O₆⟩ =>
    ⟨?_, C₆, ((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 z.mem base P.sW = 1
      rw [O₆.w32 (by apart) (by apart), D₅]
      rfl
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart),
        O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
        O₂.val32 (by apart) (by apart), F₁, hm]
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart),
        O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart), G₂,
        O₁.val32 (by apart) (by apart)]
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart),
        O₄.val32 (by apart) (by apart), A₃]
      rfl
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart), B₄]
      rfl
  · intro x hx
    rw [O₆ x (by apart), O₅ x (by apart), O₄ x (by apart), O₃ x (by apart),
      O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv

end

end

/-! ### `Weierstrass.X86.InvRun`, which only this module used -/

section

/-! # The fixed twenty-batch inversion loop -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem run_ok {P : InvCfg} {s : State} {base : Addr} {size p x : Nat}
    (hs : Scr s base size) (L : WorkLay P size) (hp : 0 < p) (hp256 : p < 2 ^ 256)
    (hm : val32 s.mem base P.M.mo 8 = p) (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (hI : StateAt P base (Divstep.W32.invRun 30 p (minv32 P.M).toNat x 0) s)
    (hc : w32 s.mem base P.sCount = 20)
    (facts : ∀ k < 20, BatchFacts (Divstep.W32.invRun 30 p (minv32 P.M).toNat x k) p) :
    WP isa (.loop P.batch .ne) s fun z =>
      StateAt P base (Divstep.W32.invRun 30 p (minv32 P.M).toNat x 20) z ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem z.mem := by
  have hn := hs.nowrap
  have hmod := L.mod_bound; have htm := L.tbl_mod; have hmt := L.mod_tmp
  let J := fun j u => Scr u base size ∧
    StateAt P base (Divstep.W32.invRun 30 p (minv32 P.M).toNat x (20 - j)) u ∧
    w32 u.mem base P.sCount = j ∧ Keeps wordClob s u ∧
    Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem u.mem
  refine countLoop_ok (Inv := J) (n := 20) ?_ ?_ (by decide) ?_
  · intro j u hj hj20 hJ
    obtain ⟨hu, Iu, Cu, Ku, Ou⟩ := hJ
    have F := facts (20 - j) (by omega_using [hj])
    have Mu : val32 u.mem base P.M.mo 8 = p := by
      rw [Outs.val32 Ou (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        constructor <;> omega_arith) (by omega_using [hn, hmod]), hm]
    refine WP.mono (batch_ok hu L Iu F.delta F.odd F.f F.g F.a F.b hp hp256 Mu hinv hj
      (by omega_using [hj20]) Cu F.matrix F.division) fun z ⟨Iz, Cz, Zz, Kz, Oz⟩ => ⟨?_, Zz⟩
    refine ⟨hu.of_keeps Kz (by decide), ?_, Cz, Ku.trans Kz, ?_⟩
    · rw [show 20 - (j - 1) = (20 - j) + 1 by omega_using [hj, hj20], Divstep.W32.invRun]
      exact Iz
    · exact (Ou.trans Oz).mono (by
        intro w hw
        simpa only [List.mem_append, or_self] using hw)
  · intro u hJ
    obtain ⟨_, Iu, _, Ku, Ou⟩ := hJ
    exact ⟨Iu, Ku, Ou⟩
  · exact ⟨hs, hI, hc, Keeps.refl _ _, Unch.refl _ _ _⟩

end VG.Proof.Weierstrass.X86.Inv

end

end


/-! # Soundness of the 256-bit divstep inversion -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem runFacts {p x : Nat} {m : Int} (hp : (p : Int) % 2 = 1) (hp1 : 1 < p)
    (hm : ((p : Int) * m + 1) % 2 ^ 32 = 0) (hx : x < p) {k : Nat} (hk : k < 20) :
    BatchFacts (Divstep.W32.invRun 30 p m x k) p := by
  obtain ⟨hd, hf, hfb, hgb, ha0, ha1, hb0, hb1⟩ :=
    Divstep.W32.invRun_bounds (N := 30) (by decide) hp (by omega_using [hp1]) hm (Int.natCast_nonneg x) (by omega_using [hx]) k
  refine ⟨?_, hf, hfb, hgb, ?_, ?_, ?_, ?_⟩
  · push_cast at hd
    omega_using [hk, hd]
  · rw [abs_of_nonneg ha0]
    omega_using [ha1]
  · rw [abs_of_nonneg hb0]
    omega_using [hb1]
  · exact Divstep.msteps_bnd _ _ _ 30
  · have H := Divstep.msteps_mat (d := (Divstep.W32.invRun 30 p m x k).d)
      (g := (Divstep.W32.invRun 30 p m x k).g) hf 30
    exact ⟨⟨_, H.1.symm⟩, ⟨_, H.2.symm⟩⟩

theorem finish_sign {P : InvCfg} {base : Addr} {s : State} {f : Int}
    (hf : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = f % 2 ^ 288) :
    (f = 1 → (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) = P.C) ∧
    (f = -1 → (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) = P.Cn) := by
  have E := low_cong32 hf
  have hb := (s.mem.readW (off base P.sF) 32).isLt
  have E' : (w32 s.mem base P.sF : Int) = f % 2 ^ 32 := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hb)] at E
    exact E
  constructor
  · intro h
    rw [h, Int.emod_eq_of_lt (by decide) (by decide)] at E'
    rw [ite_eq_right (by omega_using [E'])]
  · intro h
    rw [h, show (-1 : Int) % 2 ^ 32 = 2 ^ 32 - 1 by decide] at E'
    rw [ite_eq_left (by omega_using [E'])]

theorem invPow_ok {P : InvCfg} {base : Addr} {size p : Nat} [NeZero p]
    (hpr : p.Prime) (hT : InvToM p) (L : InvLay P size) (hp2 : 2 < p)
    (hR : UnitMod p (2 ^ 256)) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size p s.mem base) (hX : val32 s.mem base P.base 8 < p) (hC : InvOk P p) :
    WP isa P.inv s fun z => Keeps invClob s z ∧ Unch base (invW P) s.mem z.mem ∧
      val32 z.mem base P.out 8 < p ∧
      toM p (2 ^ 256) (val32 z.mem base P.out 8) =
        toM p (2 ^ 256) (val32 s.mem base P.base 8) ^ (p - 2) := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hmod := L.mod_bound
  have htm := L.tbl_mod; have hmt := L.mod_tmp
  have hm : val32 s.mem base P.M.mo 8 = p := by
    simpa only [L.n4, wordsVal_eq_val32] using hM.val
  have hp256 : p < 2 ^ 256 := by rw [← hm]; exact val32_lt _ _ _ _
  have oddNat : p % 2 = 1 := by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega_using [hk]⟩) (by omega_using [hp2])
    · omega_using [hk]
  have odd : (p : Int) % 2 = 1 := by exact_mod_cast oddNat
  have hinv := minv32_inv hM.inv
  have hinvI : ((p : Int) * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0 := by exact_mod_cast hinv
  have hCm : P.C < p := by rw [hC.C]; exact Nat.mod_lt _ (by omega_using [hp2])
  have hCnm : P.Cn < p := by rw [hC.Cn]; have := hC.Cpos; omega_using [hp2, this]
  have modU : ∀ {mem' : Mem}, Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem mem' →
      ModOkW P.M size p mem' base := by
    intro mem' U
    refine ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩
    rw [L.n4, wordsVal_eq_val32, Outs.val32 U (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      constructor <;> omega_arith) (by omega_using [hn, hmod]), hm]
  unfold InvCfg.inv
  refine WP.seq (WP.mono (init_ok hs L hm) fun s₁ ⟨I₁, C₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have U₁ : Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem s₁.mem :=
    fun q hq => O₁ q (hq (P.tbl, 320) (by simp))
  have hm₁ : val32 s₁.mem base P.M.mo 8 = p := by
    simpa only [L.n4, wordsVal_eq_val32] using (modU U₁).val
  refine WP.seq (WP.mono (run_ok hs₁ L.toWorkLay (by omega_using [hp2]) hp256 hm₁ hinv I₁ C₁
    (fun _ hk => runFacts odd (by omega_using [hp2]) hinvI hX hk)) fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have U : Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem s₂.mem :=
    fun q hq => (U₂ q hq).trans (U₁ q hq)
  refine WP.mono (finish_ok hs₂ L hC hp256 hCm hCnm)
    fun z ⟨V₃, E₃, K₃, U₃⟩ => ⟨?_, ?_, V₃, ?_⟩
  · exact ((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))
  · intro q hq
    rw [U₃ q hq, U q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hq (P.tbl, 320) (by simp [invW]), hq (P.M.tmp, 32) (by simp [invW])⟩)]
  let X := val32 s.mem base P.base 8
  let I := Divstep.W32.invRun 30 p (minv32 P.M).toNat X 20
  have ha : (val32 s₂.mem base P.sA 8 : Int) = I.a := I₂.a
  have done : (Divstep.divsteps (30 * 20) (1, p, (X : Int))).2.2 = 0 ∧
      (Divstep.divsteps (30 * 20) (1, p, (X : Int))).2.1.natAbs = Int.gcd p X :=
    Divstep.divsteps_words (n := 4) odd (Int.natCast_nonneg _) (by exact_mod_cast hX.le)
      (by exact_mod_cast hp256) (.inl ⟨by decide, by decide⟩)
  have spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧
      (X : Int) * (I.f * I.a) * 2 ^ 40 ≡ 1 [ZMOD p] := by
    intro hX0
    exact Divstep.W32.invRun_spec (N := 30) (B := 20) (by decide) odd (by omega_using [hp2]) hinvI done (by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime (by omega_using [hX0]) hX hpr)
  have signs := finish_sign I₂.f
  refine hT (K := 2 ^ 40) (f := I.f) hp2 hR hX ?_ ?_ ?_ E₃
  · intro hX0
    have Z := (Divstep.W32.invRun_zero (N := 30) (p := p) (m := (minv32 P.M).toNat) (by omega_using [hp2]) 20).2
    have ia : I.a = 0 := by
      change (Divstep.W32.invRun 30 p (minv32 P.M).toNat X 20).a = 0
      change X = 0 at hX0
      rw [hX0, Nat.cast_zero]
      exact Z
    have : (val32 s₂.mem base P.sA 8 : Int) = 0 := ha.trans ia
    exact_mod_cast this
  · intro hX0
    have H := (spec hX0).2
    rw [← ha] at H
    exact_mod_cast H
  · intro hX0
    rcases (spec hX0).1 with H | H
    · rw [signs.1 H, hC.C, H]
      push_cast
      rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    · rw [signs.2 H, hC.Cn, H, Nat.cast_sub hCm.le]
      have C : (P.C : Int) ≡ ((2 ^ 40 * (2 ^ 256) ^ 3 : Nat) : Int) [ZMOD p] := by
        rw [hC.C]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
      have P0 : (p : Int) ≡ 0 [ZMOD p] := Int.emod_self.trans (Int.zero_emod _).symm
      have H := P0.sub C
      push_cast at H ⊢
      simpa only [Int.ModEq, Int.neg_one_mul, Int.zero_sub] using H

theorem invSound_of_toM {p : Nat} [NeZero p] (hp : p.Prime) (hT : InvToM p) : InvSound p :=
  fun L hp2 hR _ hs hM hX hC => invPow_ok hp hT L hp2 hR hs hM hX hC

end VG.Proof.Weierstrass.X86.Inv
