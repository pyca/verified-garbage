module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Prepare
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyQinv
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.GcdIsOne
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Widen
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.RsaKeyGen.TopWord32
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyMaskFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimeProduct
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCrtCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartOutcome
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime

/-! ### `RsaKeyGen.X86.KeyRuntime.KeyPart`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.Qinv`, which only this module used -/

section

/-! # The CRT coefficient uses a prime-width native inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aDen aQi kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (safePrime qinvArrays stageRanges stage_keep stage_inverse stage_outside
  inverse_workspace inverse_array_layout inverse_end_le InverseLayout)

theorem qinvPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa qinvPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n qinvArrays) s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) = 1 then 1 else 0) ∧
      num t.mem B n aQi < safePrime (num s.mem B n aPa) ∧
      (safePrime (num s.mem B n aPa) : Int) ∣
        (num t.mem B n aQi : Int) * num s.mem B n aQa -
          Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := num s.mem B n aPa
  let Q := num s.mem B n aQa
  let M := safePrime P
  have small : k ≤ n := by omega_using [width]
  have half : n / 2 = k := by omega_using [width]
  have mo : M % 2 = 1 := by
    unfold M safePrime
    split
    · next H => exact H.1
    · decide
  have ml : 1 < M := by unfold M safePrime; split <;> omega_arith
  have threeBound : 3 < 2 ^ (32 * k) := by
    have H := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 32 ≤ 32 * k by omega_using [positive])
    omega_using [H]
  have mb : M < 2 ^ (32 * k) := by
    unfold M safePrime
    split
    · exact boundP
    · exact threeBound
  unfold qinvPart seqs
  refine WP.seq (WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, _, modulus, Ku⟩ => ?_)
  change num u.mem B n aDen = M at modulus
  have Qu : num u.mem B n aQa = Q := Ou.num (by decide) (by decide) (h.fit64 (by decide))
  have maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  have lowQ : val32 u.mem B (arr n aQa) k = Q :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq small (by change num u.mem B n aQa < _; rw [Qu]; exact boundQ)).trans Qu
  have lowM : val32 u.mem B (arr n aDen) k = M :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq small (by change num u.mem B n aDen < _; rw [modulus]; exact mb)).trans modulus
  have hk := inverse_workspace hu.old positive small
  have layout := inverse_array_layout hu.old small (a := aQa) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  have layout' : InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQa).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] using layout
  refine WP.seq (WP.mono (inverseFrom_ok hu (by decide) (by decide) layout' 
    (by change val32 u.mem B (arr n aDen) (n / 2) % 2 = 1; rw [half, lowM]; exact mo)
    (by change 1 < val32 u.mem B (arr n aDen) (n / 2); rw [half, lowM]; exact ml))
    fun v ⟨hv, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  simp only [Width.words, half, VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array] at Ov gcd congruence boundX
  have hvSmall := inverse_workspace hv.old positive small
  change num v.mem B k 1 = Nat.gcd (val32 u.mem B (arr n aQa) k) (val32 u.mem B (arr n aDen) k) at gcd
  change (val32 u.mem B (arr n aDen) k : Int) ∣ (num v.mem B k 3 : Int) * val32 u.mem B (arr n aQa) k - num v.mem B k 1 at congruence
  change num v.mem B k 3 < val32 u.mem B (arr n aDen) k at boundX
  rw [lowQ, lowM] at gcd congruence
  rw [lowM] at boundX
  rw [gcd] at congruence
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (hu.inverse_slot (by decide) Ov).trans maskU
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .prime) hv (by decide) (by decide))
    fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  simp only [Width.words, half] at Ow
  change slot w.mem B kFlag = (if num v.mem B (n / 2) 1 = 1 then 1 else 0) at flag
  rw [half, gcd] at flag
  have Xw : num w.mem B k 3 = num v.mem B k 3 :=
    Ow.num (by decide) (by decide) (hvSmall.fit64 (by decide))
  have maskW : slot w.mem B kOk = slot s.mem B kOk :=
    (Ow.slot (by decide) (by decide)).trans maskV
  refine WP.seq (WP.mono (andS_ok hw (by decide) (by decide) (by decide)
    (by rw [maskW]; exact bit) (by rw [flag]; split <;> omega_using []))
    fun a ⟨ha, Oa, maskA, Ka⟩ => ?_)
  rw [maskW, flag] at maskA
  have Xa : num a.mem B k 3 = num v.mem B k 3 := by
    have F := hvSmall.fit64 (j := 3) (by decide)
    have same : val32 a.mem B (arr k 3) k = val32 w.mem B (arr k 3) k := by
      apply Oa.val32 _ (by unfold S at F; omega_using [F])
      intro r hr
      change r ∈ [] ++ [(kOk, 4)] at hr
      have E : r = (kOk, 4) := by simpa only [List.nil_append, List.mem_singleton] using hr
      subst r
      exact Or.inr (Nat.le_trans (by decide : kOk + 4 ≤ hdr) (Nat.le_add_right ..))
    exact same.trans Xw
  have sourceBound : arr k 3 + 4 * k ≤ Z := by
    have F := hk.arr_fit (j := 3) (by decide)
    unfold S at F
    omega_using [F]
  have before : arr k 3 + 4 * k ≤ arr n aQi := by
    have F := arr_end (w := k) (show 3 < 15 by decide)
    have E := inverse_end_le small (j := aQi) (by decide)
    unfold S at F
    omega_using [F, E]
  have widening := widen_ok ha .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQi)
    (.array .prime 3) (by change n / 2 ≤ n; omega_using []) (ha.arr_fit (by decide))
    (by simpa only [offset_array, Width.words, half] using sourceBound)
    (Or.inl (by simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] using before))
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] at widening
  refine WP.mono widening
    fun t ⟨ht, Ot, _, coefficient, Kt⟩ => ?_
  have X : num t.mem B n aQi = num v.mem B k 3 := coefficient.trans Xa
  have maskT : slot t.mem B kOk = slot a.mem B kOk :=
    Ot.w32 (Nat.le_trans (by decide : kOk + 4 ≤ hdr) (Nat.le_add_right ..) |> Or.inl) (by decide)
  have frameU : Outs B (stageRanges n qinvArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have frameV : OutsS B (s.gpr .esp) (stageRanges n qinvArrays) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => stage_inverse small) Ov
  have frameW : Outs B (stageRanges n qinvArrays) v.mem w.mem :=
    stage_keep small (by
      intro j hj
      left
      have H : ∀ j ∈ [aT2, aT1], j < 15 := by decide
      exact H j hj) (by decide) Ow
  have frameA : Outs B (stageRanges n qinvArrays) w.mem a.mem :=
    stage_keep (Nat.le_refl n) (by simp) (by decide) Oa
  refine ⟨ht, ((((OutsS.of_outs frameU).trans frameV).trans (OutsS.of_outs frameW)).trans
      (OutsS.of_outs frameA)).trans (OutsS.of_outs (stage_outside (by decide) Ot)),
    ?_, ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · rw [maskT, maskA]
    change (if slot s.mem B kOk = 1 ∧ (if Nat.gcd Q M = 1 then 1 else 0) = 1 then 1 else 0) =
      (if slot s.mem B kOk = 1 ∧ Nat.gcd Q M = 1 then 1 else 0)
    by_cases G : Nat.gcd Q M = 1 <;> simp [G]
  · rw [X]
    exact boundX
  · rw [X]
    exact congruence

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.FinalMask`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.TopBit`, which only this module used -/

section

/-! # Read the high modulus word through its public runtime address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Impl.RsaKeyGen.X86.Key (aN kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem topBit_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block topBit) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if 2 ^ (32 * n - 1) ≤ num s.mem B n aN then 1 else 0) ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have fits := h.arr_fit (j := aN) (by decide)
  have positive := h.wpos
  have nowrap := h.old.workspace.nowrap
  unfold topBit
  refine h.ptr_ok (arr aN) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fits; omega_using [fits, nowrap])
    fun u Ku mu Pu => ?_
  have hu := h.keep Ku (by rw [mu]; exact Outside.refl _ _ _ _)
  refine hu.bytes_ok .modulus .edx fun v Kv mv count => ?_
  change (v.gpr .edx).toNat = 4 * n at count
  refine wp_addS rfl fun w W _ => wp_subS rfl fun x X _ => ?_
  have Kx : Keeps [.ebp, .edx] s x := (Ku.trans (Kv.mono (by decide))).trans
    ((W.keeps.mono (by decide)).trans (X.keeps.mono (by decide)))
  have mx : x.mem = s.mem := X.mem.trans (W.mem.trans (mv.trans mu))
  have hx := h.keep Kx (by rw [mx]; exact Outside.refl _ _ _ _)
  have Px : PtrAt x B .ebp (VG.Proof.Rsa.X86.Keys.arr n aN + 4 * (n - 1)) := by
    rw [PtrAt, X.gpr, W.gpr, BitVec.toNat_sub, BitVec.toNat_add,
      Kv.1 _ (by decide), Pu, count]
    simp only [arr, offset_array, Width.words] at *
    simp only [show (4 : BitVec 32).toNat = 4 by rfl]
    unfold VG.Proof.Rsa.X86.Keys.S at fits
    omega_using [positive]
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr hx.full.rt Px (d := 0)
    (by unfold VG.Proof.Rsa.X86.Keys.S at fits; omega_using [fits])) fun y Y _ => ?_
  refine wp_shr (by decide) fun z Zf _ => ?_
  have K : Keeps [.eax, .edx, .ebp] s z := (Kx.mono (by decide)).trans
    ((Y.keeps.mono (by decide)).trans (Zf.keeps.mono (by decide)))
  have memory : z.mem = s.mem := Zf.mem.trans (Y.mem.trans mx)
  have hz := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  refine WP.mono (store_slot hz (d := kFlag) (by decide) .eax) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, Zf.gpr, Y.gpr, mx, Nat.add_zero,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change w32 s.mem B (VG.Proof.Rsa.X86.Keys.arr n aN + 4 * (n - 1)) / 2 ^ 31 = _
  rw [← VG.Proof.RsaKeyGen.WordBounds32.top_div positive]
  change num s.mem B n aN / 2 ^ (32 * n - 1) = _
  have bound := val32_lt s.mem B (VG.Proof.Rsa.X86.Keys.arr n aN) n
  change num s.mem B n aN < 2 ^ (32 * n) at bound
  have factor : 2 ^ (32 * n) = 2 ^ (32 * n - 1) * 2 := by
    calc
      2 ^ (32 * n) = 2 ^ ((32 * n - 1) + 1) := congrArg (2 ^ ·) (by omega_using [positive])
      _ = _ := Nat.pow_succ ..
  rw [factor] at bound
  split
  · next H => exact Nat.div_eq_of_lt_le (by simpa only [Nat.one_mul] using H) (by omega_using [bound])
  · next H => exact Nat.div_eq_of_lt (by omega_using [H])

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The final native mask is exactly the RSA key shape check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/MaskFlag.lean`, which only this module imported.
section

/-! # Combine a checked bit with the persistent RSA validity mask -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem withFlag_ok {s : State} {B : Addr} {Z n value : Nat} {c : Prog isa} {rs : List Reg}
    (bit : slot s.mem B kOk ≤ 1) (valueBit : value ≤ 1)
    (correct : WP isa c s fun u => Ws u B Z n 32 ∧ Keep B n [] [kFlag] s.mem u.mem ∧
      slot u.mem B kFlag = value ∧ Keeps rs s u) (eax : .eax ∈ rs := by decide) :
    WP isa (withFlag c) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧ value = 1 then 1 else 0) ∧ Keeps rs s t := by
  unfold withFlag
  refine WP.seq (WP.mono correct fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  refine WP.mono (andS_ok hu (by decide) (by decide) (by decide)
    (by rw [maskU]; exact bit) (by rw [flag]; exact valueBit)) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  exact ⟨ht, Ou.join Ot (js := []) (ds := [kFlag, kOk]), by rw [mask, maskU, flag], Ku.trans (Kt.mono (by simpa using eax))⟩


end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FinalExponent.lean`, which only this module imported.
section

/-! # The lower bound on the runtime public exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aE kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem exponentAtLeastThree_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa exponentAtLeastThree s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 3 ≤ num s.mem B n aE ∧ slot s.mem B kOk = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold exponentAtLeastThree seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (3 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 3 at constant
  have E : num u.mem B n aE = num s.mem B n aE := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [E, constant] at subtract
  have iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (Ov.slot (by decide) (by simp)).trans (Ou.slot (by decide) (by simp))
  refine WP.seq (WP.mono (saveSlot_ok hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  rw [maskV] at flag
  have borrowW : (w.gpr .ebx).toNat = (v.gpr .ebx).toNat := congrArg BitVec.toNat (Kw.1 .ebx (by decide))
  refine WP.mono (borrowMask_ok hw (by rw [borrowW]; exact borrow)
    (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  refine ⟨ht, ((Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ow
    (js := [aT1, aT2]) (ds := [kFlag])).join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  simpa only [borrowW, iffBorrow, flag] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aN aE kOk kFlag kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (mask_bit mask_ite_one maskFlag_preserves_e)

theorem finalMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa finalMask s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        2 ^ (32 * n - 1) ≤ num s.mem B n aN ∧
        num s.mem B n aPa % 2 = 1 ∧ num s.mem B n aQa % 2 = 1 ∧
        Spec.Rsa.exponentValid (val32 s.mem B kEv 2) = true then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold finalMask seqs
  refine WP.seq (WP.mono (withFlag_ok bit (by split <;> omega_arith) (topBit_ok h))
    fun u ⟨hu, Ou, Mu, Ku⟩ => ?_)
  have Pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mu]; exact mask_bit _)
    (show num u.mem B n aPa % 2 ≤ 1 by omega_arith) (bitOf_ok hu (by decide) (by decide)))
    fun v ⟨hv, Ov, Mv, Kv⟩ => ?_)
  rw [Pu, Mu] at Mv
  have Fv := Ou.trans Ov
  have Qv : num v.mem B n aQa = num s.mem B n aQa := Fv.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mv]; exact mask_bit _)
    (show num v.mem B n aQa % 2 ≤ 1 by omega_arith) (bitOf_ok hv (by decide) (by decide)))
    fun w ⟨hw, Ow, Mw, Kw⟩ => ?_)
  rw [Qv, Mv] at Mw
  have Fw := Fv.trans Ow
  have Ew : num w.mem B n aE = val32 s.mem B kEv 2 :=
    (Fw.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mw]; exact mask_bit _)
    (show num w.mem B n aE % 2 ≤ 1 by omega_arith) (bitOf_ok hw (by decide) (by decide)))
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Ew, Mw] at Ma
  have Fa := Fw.trans Oa
  have Ea : val32 a.mem B kEv 2 = val32 s.mem B kEv 2 := maskFlag_preserves_e Fa
  refine WP.seq (WP.mono (withFlag_ok (by rw [Ma]; exact mask_bit _)
    (by split <;> omega_arith) (exponentUpper_ok ha)) fun b ⟨hb, Ob, Mb, Kb⟩ => ?_)
  rw [Ea, Ma] at Mb
  have Fb := Fa.trans Ob
  have Eb : num b.mem B n aE = val32 s.mem B kEv 2 :=
    (Fb.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.mono (exponentAtLeastThree_ok hb (by rw [Mb]; exact mask_bit _))
    fun t ⟨ht, Ot, Mt, Kt⟩ => ?_
  rw [Eb, Mb] at Mt
  refine ⟨ht, Fb.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt))))⟩
  exact Mt.trans (Key.finalMask_cond _ _ _ _ _ _)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Complete native arithmetic after the small-private-exponent check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Divisor.lean`, which only this module imported.
section

/-! # A safe CRT divisor, including zero factor predecessors -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem divisorOf_ok {s : State} {B : Addr} {Z n input : Nat} (h : Ws s B Z n 32)
    (hi : input < 32) (ip : 16 ≤ input) (one : num s.mem B n aOne = 1) :
    WP isa (divisorOf input) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, aDen] [sT, kFlag] s.mem t.mem ∧
      num t.mem B n aDen = (if num s.mem B n input = 0 then 1 else num s.mem B n input) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fi := h.fit64 hi
  have fo := h.fit64 (j := aOne) (by decide)
  unfold divisorOf seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (0 : BitVec 32))
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change num u.mem B n aT1 = 0 at zero
  have Iu : num u.mem B n input = num s.mem B n input :=
    Ou.num (by simp only [List.mem_singleton]; unfold aT1; omega) (by simp) fi
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by simp) fo).trans one
  refine WP.seq (WP.mono (eq_ok hu (by decide) hi (by decide)
    (by unfold aT2; omega) (by decide) (by decide)) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [Iu, zero] at flag
  have Iv : num v.mem B n input = num s.mem B n input :=
    (Ov.num (by simp only [List.mem_singleton]; unfold aT2; omega) (by decide) fi).trans Iu
  have oneV : num v.mem B n aOne = 1 :=
    (Ov.num (by decide) (by decide) fo).trans oneU
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (sel_ok hv (by decide) hi (by decide) (by decide) bit (by right; decide))
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aT1, aT2, aDen]) (ds := [sT, kFlag])).join Ot
    (js := [aT1, aT2, aDen]) (ds := [sT, kFlag]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  rw [selected, flag, Iv, oneV]
  by_cases I : num s.mem B n input = 0 <;> simp [I]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Crt.lean`, which only this module imported.
section

/-! # Compute both CRT exponents with safe fixed-schedule division -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aD aQm aPm aOne aDp aDq aDen kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (stageRanges stage_keep stage_preserves_num crtArrays crtDivisor)

theorem crtPart_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa crtPart s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n crtArrays) s.mem t.mem ∧
      num t.mem B n aDp = num s.mem B n aD % crtDivisor (num s.mem B n aPm) ∧
      num t.mem B n aDq = num s.mem B n aD % crtDivisor (num s.mem B n aQm) ∧
      slot t.mem B kOk = slot s.mem B kOk ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fd := h.fit64 (j := aD) (by decide)
  have fq := h.fit64 (j := aQm) (by decide)
  have fo := h.fit64 (j := aOne) (by decide)
  have fp := h.fit64 (j := aDp) (by decide)
  unfold crtPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (divisorOf_ok h (by decide) (by decide) one)
    fun u ⟨hu, Ou, divisorP, Ku⟩ => ?_)
  have frameU : Outs B (stageRanges n crtArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  have Du : num u.mem B n aD = num s.mem B n aD :=
    Ou.num (by decide) (by decide) fd
  have divP : 0 < num u.mem B n aDen := by rw [divisorP]; split <;> omega
  refine WP.seq (WP.mono (arrayDivision_ok hu (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) divP)
    fun v ⟨hv, Ov, _, P, Kv⟩ => ?_)
  rw [Du, divisorP] at P
  have frameV : Outs B (stageRanges n crtArrays) u.mem v.mem := stage_division (by decide) (by decide) Ov
  have prefixFrame := frameU.trans frameV
  have Qv : num v.mem B n aQm = num s.mem B n aQm :=
    stage_preserves_num (by decide) (by decide) fq prefixFrame
  have Dv : num v.mem B n aD = num s.mem B n aD :=
    stage_preserves_num (by decide) (by decide) fd prefixFrame
  have oneV : num v.mem B n aOne = 1 :=
    (stage_preserves_num (by decide) (by decide) fo prefixFrame).trans one
  refine WP.seq (WP.mono (divisorOf_ok hv (by decide) (by decide) oneV)
    fun w ⟨hw, Ow, divisorQ, Kw⟩ => ?_)
  rw [Qv] at divisorQ
  have frameW : Outs B (stageRanges n crtArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  have Dw : num w.mem B n aD = num s.mem B n aD :=
    (Ow.num (by decide) (by decide) fd).trans Dv
  have Pw : num w.mem B n aDp = num v.mem B n aDp := Ow.num (by decide) (by decide) fp
  have divQ : 0 < num w.mem B n aDen := by rw [divisorQ]; split <;> omega
  refine WP.mono (arrayDivision_ok hw (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) divQ)
    fun t ⟨ht, Ot, _, Q, Kt⟩ => ?_
  rw [Dw, divisorQ] at Q
  have frameT : Outs B (stageRanges n crtArrays) w.mem t.mem := stage_division (by decide) (by decide) Ot
  exact ⟨ht, (prefixFrame.trans frameW).trans frameT,
    ((arrayDivision_preserves_num (by decide) (by decide) (by decide) fp Ot).trans Pw).trans P,
    Q, (arrayDivision_preserves_slot (by decide) Ot).trans ((Ow.slot (by decide) (by decide)).trans
      ((arrayDivision_preserves_slot (by decide) Ov).trans (Ou.slot (by decide) (by decide)))),
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans Kt))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aPm aQm aOne aQi aN aE kEv kOk kFlag kStatus)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyPartResult keyPartArrays stageRanges stage_preserves_num
  stage_preserves_e stage_mono stage_keep safePrime mask_bit mask_ite_one)

theorem keyPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2)
    (one : num s.mem B n aOne = 1) :
    WP isa keyPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n keyPartArrays) s.mem t.mem ∧
      KeyPartResult B n s.mem t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold keyPart seqs
  refine WP.seq (WP.mono (qinvPart_ok h width positive boundP boundQ bit)
    fun u ⟨hu, Ou, Mu, boundQi, congruence, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one
  have Du : num u.mem B n aD = num s.mem B n aD :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Pmu : num u.mem B n aPm = num s.mem B n aPm :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Qmu : num u.mem B n aQm = num s.mem B n aQm :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have frameU : OutsS B (s.gpr .esp) (stageRanges n keyPartArrays) s.mem u.mem :=
    OutsS.lift (fun _ _ => stage_mono (by decide)) Ou
  refine WP.seq (WP.mono (crtPart_ok hu oneU) fun v ⟨hv, Ov, Dp, Dq, Mv, Kv⟩ => ?_)
  rw [Du, Pmu] at Dp
  rw [Du, Qmu] at Dq
  rw [Mu] at Mv
  have qiV : num v.mem B n aQi = num u.mem B n aQi :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov
  have frameV : Outs B (stageRanges n keyPartArrays) u.mem v.mem := stage_mono (by decide) Ov
  have prefixFrame := frameU.trans (OutsS.of_outs frameV)
  have Pv : num v.mem B n aPa = num s.mem B n aPa :=
    h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Qv : num v.mem B n aQa = num s.mem B n aQa :=
    h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  refine WP.seq (WP.mono (primeProduct_ok hv width positive even (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Pv]; exact boundP) (by rw [Qv]; exact boundQ))
    fun w ⟨hw, Ow, N, Kw⟩ => ?_)
  rw [Pv, Qv] at N
  have frameW : Outs B (stageRanges n keyPartArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  have fullPrefix := prefixFrame.trans (OutsS.of_outs frameW)
  have Pw : num w.mem B n aPa = num s.mem B n aPa :=
    h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Qw : num w.mem B n aQa = num s.mem B n aQa :=
    h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Ew : val32 w.mem B kEv 2 = val32 s.mem B kEv 2 := h.read_val32 (by decide) fullPrefix stage_preserves_e
  have loadedW : num w.mem B n aE = val32 w.mem B kEv 2 :=
    (h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans (loaded.trans Ew.symm)
  have Mw : slot w.mem B kOk = (if slot s.mem B kOk = 1 ∧
      Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) = 1 then 1 else 0) :=
    (Ow.slot (by decide) (by decide)).trans Mv
  refine WP.seq (WP.mono (finalMask_ok hw (by rw [Mw]; exact mask_bit _) loadedW)
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Mw, N, Pw, Qw, Ew] at Ma
  simp only [mask_ite_one, and_assoc] at Ma
  refine WP.mono (saveSlot_ok ha (by decide) (by decide)) fun t ⟨ht, Ot, status, Kt⟩ => ?_
  have last : Keep B n [aT1, aT2] [kFlag, kOk, kStatus] w.mem t.mem :=
    Oa.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk, kStatus])
  have tail : Keep B n [aN, aT1, aT2] (productScalars ++ [kFlag, kOk, kStatus]) v.mem t.mem :=
    Ow.join last (js := [aN, aT1, aT2]) (ds := (productScalars ++ [kFlag, kOk, kStatus]))
      (by decide) (by decide) (by decide) (by decide)
  have qiT : num t.mem B n aQi = num u.mem B n aQi :=
    (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans qiV
  have frameA : Outs B (stageRanges n keyPartArrays) w.mem a.mem :=
    stage_keep (Nat.le_refl n) (by
      intro j hj
      left
      have H : ∀ j ∈ [aT1, aT2], j < 15 := by decide
      exact H j hj) (by decide) Oa
  have frameT : Outs B (stageRanges n keyPartArrays) a.mem t.mem :=
    stage_keep (Nat.le_refl n) (by simp) (by decide) Ot
  have maskT : slot t.mem B kOk = slot a.mem B kOk := Ot.slot (by decide) (by decide)
  refine ⟨ht, (fullPrefix.trans (OutsS.of_outs frameA)).trans (OutsS.of_outs frameT), ⟨?_, ?_, ?_, ?_, ?_, maskT.trans Ma, ?_⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans ((Ka.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · exact (last.num (by decide) (by decide) (h.fit64 (by decide))).trans N
  · exact (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans Dp
  · exact (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans Dq
  · rw [qiT]
    exact boundQi
  · rw [qiT]
    exact congruence
  · exact status.trans maskT.symm

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end


/-! # Complete native numeric RSA derivation, including all failure cases -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE aOne kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady CoreOutcome deriveArrays stageRanges stage_keep stage_mono
  stage_preserves_num stage_preserves_e)

theorem deriveLoaded_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa deriveLoaded s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n deriveArrays) s.mem t.mem ∧
      CoreOutcome B n (val32 s.mem B kEv 2) (num s.mem B n aPa) (num s.mem B n aQa) t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have boundP' : num s.mem B n aPa < 2 ^ (16 * n) := by rw [show 16 * n = 32 * k by omega_using [width]]; exact boundP
  have boundQ' : num s.mem B n aQa < 2 ^ (16 * n) := by rw [show 16 * n = 32 * k by omega_using [width]]; exact boundQ
  unfold deriveLoaded
  refine WP.seq (WP.mono (prepareLoaded_ok h width positive even boundP boundQ zero one loaded)
    fun u ⟨hu, Ou, R, Ku⟩ => ?_)
  have frameU : OutsS B (s.gpr .esp) (stageRanges n deriveArrays) s.mem u.mem :=
    OutsS.lift (fun _ _ => stage_mono (by decide)) Ou
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  refine WP.seq (WP.mono (smallMask_ok hu R.bit) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  have ready := KeyReady.small hu.old R Ov
  have maskV : slot v.mem B kOk = slot u.mem B kOk := Ov.slot (by decide) (by simp)
  have DV : num v.mem B n aD = num u.mem B n aD := Ov.num (by decide) (by simp) (h.fit64 (by decide))
  have frameV : Outs B (stageRanges n deriveArrays) u.mem v.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by simp) Ov
  have branch : isa.eval .ne v = some (decide (slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n))) := by
    change v.zf.map Bool.not = _
    change v.zf = some (decide (¬(slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n)))) at flag
    rw [flag]
    by_cases small : slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n) <;> simp [small]
  refine WP.ite _ branch (fun retryBit => ?_) (fun normalBit => ?_)
  · have small := of_decide_eq_true retryBit
    refine WP.mono (retry_ok hv) fun t ⟨ht, Ot, mask, status, Kt⟩ => ?_
    have frameT : Outs B (stageRanges n deriveArrays) v.mem t.mem :=
      stage_keep (Nat.le_refl n) (by simp) (by decide) Ot
    exact ⟨ht, (frameU.trans (OutsS.of_outs frameV)).trans (OutsS.of_outs frameT), R.retry small.1 small.2 mask status,
      Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  · have notSmall : ¬(slot v.mem B kOk = 1 ∧ num v.mem B n aD ≤ 2 ^ (16 * n)) := by
      rw [maskV, DV]
      exact of_decide_eq_false normalBit
    have pBound : num v.mem B n aPa < 2 ^ (32 * k) := by
      rw [ready.pValue]
      exact Nat.max_lt.mpr ⟨boundP, boundQ⟩
    have qBound : num v.mem B n aQa < 2 ^ (32 * k) := by
      rw [ready.qValue]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
    refine WP.mono (keyPart_ok hv width positive even pBound qBound ready.bit
      (ready.loaded.trans ready.exponent.symm) ready.one) fun t ⟨ht, Ot, result, Kt⟩ => ?_
    have spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), spU]
    have frameT : OutsS B (s.gpr .esp) (stageRanges n deriveArrays) v.mem t.mem := by
      rw [← spV]
      exact OutsS.lift (fun _ _ => stage_mono (by decide)) Ot
    exact ⟨ht, (frameU.trans (OutsS.of_outs frameV)).trans frameT,
      KeyReady.part_of lower upper boundP' boundQ' ready notSmall
        (hv.read_num (by decide) Ot (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide))))
        (hv.read_num (by decide) Ot (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide))))
        (hv.read_num (by decide) Ot (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide))))
        (hv.read_val32 (by decide) Ot stage_preserves_e) result,
      Ku.trans ((Kv.mono (by decide)).trans Kt)⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
