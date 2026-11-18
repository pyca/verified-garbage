module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Primes
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.X86.DivLoop
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddSecond
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop

/-! ### `RsaKeyGen.X86.KeyRuntime.InverseKeeps`, which this module and modules that import it used -/

section

/-! # What a call of `vg_rsa_keygen_inverse` leaves in the workspace

The numbers and header words the inverse keeps (`Ws.inverse_num`, `Ws.inverse_slot`), for
the frame of a call (`OutsS`): the stack it writes is beyond the workspace. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.RsaKeyGen.X86.Key (inverseRanges)

/-- A number in the workspace keeps its value. -/
theorem OutsS.val32_eq {B : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} {Z : Nat}
    (h : OutsS B sp rs m m') (D : VG.Proof.RsaKeyGen.X86.KeyArgs.DeepStk sp B Z)
    (nowrap : B.toNat + Z ≤ 2 ^ 32) {d k : Nat} (hd : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 4 * k ≤ Z) : val32 m' B d k = val32 m B d k := by
  apply (h.outs D nowrap).val32 _ (by omega_using [nowrap, hs])
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact Or.inl hs

/-- The memory with the stack below `sp` as in `m₁`, the rest as in `m₂`: what `OutsS` changes as
`Outs` would. -/
def hyb (sp : BitVec 32) (m₁ m₂ : Mem) : Mem := fun x => if (below sp 52).Contains x 1 then m₁ x else m₂ x

theorem OutsS.outs_hyb {B : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m₁ m₂ : Mem}
    (h : OutsS B sp rs m₁ m₂) : Outs B rs m₁ (hyb sp m₁ m₂) := by
  intro x hx
  unfold hyb
  by_cases hz : (below sp 52).Contains x 1
  · simp only [hz, ↓reduceIte]
  · simp only [hz, ↓reduceIte]
    exact h x hx hz

/-- A number in the workspace changes as `Outs` lets it. -/
theorem OutsS.read {B : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m₁ m₂ : Mem} {Z : Nat}
    (h : OutsS B sp rs m₁ m₂) (D : VG.Proof.RsaKeyGen.X86.KeyArgs.DeepStk sp B Z)
    (nowrap : B.toNat + Z ≤ 2 ^ 32) {d k : Nat} (fit : d + 4 * k ≤ Z)
    (old : Outs B rs m₁ (hyb sp m₁ m₂) → val32 (hyb sp m₁ m₂) B d k = val32 m₁ B d k) :
    val32 m₂ B d k = val32 m₁ B d k := by
  rw [← old h.outs_hyb]
  have far := stack_far D nowrap
  have size : (stackRange B sp).2 = 52 := rfl
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => ?_)
  unfold hyb
  have notStack : ¬ (below sp 52).Contains (off B (d + 4 * j) + BitVec.ofNat 64 i) 1 := by
    intro c
    have H := (stack_contains D nowrap _).mp c
    rw [ofs_off B (by omega_using [nowrap, fit, hj, hi])] at H
    omega_using [fit, far, hj, hi, H]
  simp only [notStack, ↓reduceIte]

theorem Ws.read_num {s : State} {B : Addr} {Z n N j : Nat} (W : Ws s B Z n N) (hj : j < N)
    {rs : List (Nat × Nat)} {m₁ m₂ : Mem} (h : OutsS B (s.gpr .esp) rs m₁ m₂)
    (old : Outs B rs m₁ (hyb (s.gpr .esp) m₁ m₂) → num (hyb (s.gpr .esp) m₁ m₂) B n j = num m₁ B n j) :
    num m₂ B n j = num m₁ B n j :=
  h.read W.deep W.old.workspace.nowrap (by have := W.arr_fit hj; unfold S at this; omega_using [this]) old

theorem Ws.read_val32 {s : State} {B : Addr} {Z n N d k : Nat} (W : Ws s B Z n N) (fit : d + 4 * k ≤ hdr)
    {rs : List (Nat × Nat)} {m₁ m₂ : Mem} (h : OutsS B (s.gpr .esp) rs m₁ m₂)
    (old : Outs B rs m₁ (hyb (s.gpr .esp) m₁ m₂) → val32 (hyb (s.gpr .esp) m₁ m₂) B d k = val32 m₁ B d k) :
    val32 m₂ B d k = val32 m₁ B d k :=
  h.read W.deep W.old.workspace.nowrap (Nat.le_trans fit W.hdr_le) old

theorem Ws.inverse_num {s : State} {B : Addr} {Z n N k j : Nat} {m m' : Mem} (h : Ws s B Z n N)
    (width : k ≤ n) (persistent : 15 ≤ j) (hj : j < N)
    (changed : OutsS B (s.gpr .esp) (inverseRanges k invSlots) m m') : num m' B n j = num m B n j := by
  have fit := h.arr_fit hj
  apply changed.val32_eq h.deep h.old.workspace.nowrap _ (by unfold S at fit; omega_using [fit])
  intro r hr
  simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have endBound := VG.Proof.RsaKeyGen.X86.Key.inverse_end_le width persistent
    have endEq : arr k 15 = hdr + 4 * (15 * (k + 2)) := by unfold arr S; omega_using []
    rw [endEq] at endBound
    exact Or.inr endBound
  all_goals have lower : hdr ≤ arr n j := Nat.le_add_right ..
  all_goals simp only [sOdd, sB, sC, hdr] at lower ⊢
  all_goals omega_using [lower]

theorem Ws.inverse_slot {s : State} {B : Addr} {Z n N k d : Nat} {m m' : Mem} (h : Ws s B Z n N)
    (bound : d + 4 ≤ 100) (changed : OutsS B (s.gpr .esp) (inverseRanges k invSlots) m m') :
    slot m' B d = slot m B d := by
  have header := h.hdr_le
  have value : val32 m' B d 1 = val32 m B d 1 := by
    apply changed.val32_eq h.deep h.old.workspace.nowrap _ (by unfold hdr at header; omega_using [bound, header])
    intro r hr
    simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals simp only [sOdd, sB, sC, hdr]
    all_goals omega_using [bound]
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.Widen`, which this module and modules that import it used -/

section

/-! # Widening between banks reuses the shared clear and copy operations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem widenTo_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (target w : Width) (out src : Loc) (width : w.words n ≤ target.words n)
    (fit : out.offset n + 4 * (target.words n + 2) ≤ Z) (sourceBound : src.offset n + 4 * w.words n ≤ Z)
    (separate : src.offset n + 4 * w.words n ≤ out.offset n ∨
      out.offset n + 4 * (target.words n + 2) ≤ src.offset n) :
    WP isa (widenTo target w out src) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * (target.words n + 2)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (target.words n + 2) = val32 s.mem B (src.offset n) (w.words n) ∧
      val32 t.mem B (out.offset n) (target.words n) = val32 s.mem B (src.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold widenTo
  refine WP.seq (WP.mono (zero_ok h target out fit) fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change Outside B (out.offset n) (4 * (target.words n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (out.offset n) (target.words n + 2) = 0 at zero
  have source : val32 u.mem B (src.offset n) (w.words n) =
      val32 s.mem B (src.offset n) (w.words n) := Ou.val32 separate (by omega_using [sourceBound, nowrap])
  have high : val32 u.mem B (out.offset n + 4 * w.words n) (target.words n + 2 - w.words n) = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (by change _ ≤ target.words n + 2; omega_using [width])
  refine WP.mono (copy_loc_ok hu w out src (by omega_using [width, fit]) sourceBound (by omega_using [width, separate]))
    fun t ⟨ht, Ot, copied, Kt⟩ => ?_
  have highT : val32 t.mem B (out.offset n + 4 * w.words n) (target.words n + 2 - w.words n) = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by omega_using [width, fit, nowrap]), high]
  have full : val32 t.mem B (out.offset n) (target.words n + 2) = val32 s.mem B (src.offset n) (w.words n) := by
    have append := val32_append t.mem B (out.offset n) (w.words n) (target.words n + 2 - w.words n)
    rw [show w.words n + (target.words n + 2 - w.words n) = target.words n + 2 by omega_using [width],
      highT, Nat.mul_zero, Nat.add_zero, copied, source] at append
    exact append
  have bound : val32 t.mem B (out.offset n) (target.words n + 2) < 2 ^ (32 * target.words n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (val32_lt s.mem B (src.offset n) (w.words n))
      (Nat.pow_le_pow_right (by decide) (by omega_using [width]))
  exact ⟨ht, Ou.trans (Ot.mono (Nat.le_refl _) (by omega_using [width])), full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [] : target.words n ≤ target.words n + 2) bound).trans full,
    (Ku.mono (by decide)).trans Kt⟩


theorem widen_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (w : Width) (out src : Loc) (width : w.words n ≤ n)
    (fit : out.offset n + 4 * (n + 2) ≤ Z) (sourceBound : src.offset n + 4 * w.words n ≤ Z)
    (separate : src.offset n + 4 * w.words n ≤ out.offset n ∨
      out.offset n + 4 * (n + 2) ≤ src.offset n) :
    WP isa (widen w out src) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * (n + 2)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (n + 2) = val32 s.mem B (src.offset n) (w.words n) ∧
      val32 t.mem B (out.offset n) n = val32 s.mem B (src.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
  widenTo_ok h .modulus w out src width fit sourceBound separate

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.CorrectionGeometry`, which only this module used -/

section

/-! # The fixed 128-bit correction bank fits every native RSA workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def correctionScratch : List (Nat × Nat) := [(kProduct, 28), (hdr, 96)]

theorem correction_preserves_exponent {m m' : Mem} {B : Addr} (O : Outs B correctionScratch m m') :
    val32 m' B kEv 2 = val32 m B kEv 2 := by
  apply O.val32 _ (by decide)
  intro r hr
  simp only [correctionScratch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

theorem correction_scratch_arr {m m' : Mem} {B : Addr} {j : Nat} (hj : j < 4)
    (O : Outside B (arr 4 j) (S 4) m m') : Outs B correctionScratch m m' := by
  intro x hx
  apply O x
  have H := hx (hdr, 96) (by simp [correctionScratch])
  simp only [arr, S, hdr] at H ⊢
  omega_using [hj, H]

theorem correction_scratch_outside {m m' : Mem} {B : Addr} {out len : Nat}
    (low : hdr ≤ out) (high : out + len ≤ hdr + 96) (O : Outside B out len m m') :
    Outs B correctionScratch m m' := by
  intro x hx
  apply O x
  have H := hx (hdr, 96) (by simp [correctionScratch])
  simp only at H
  omega_using [low, high, H]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.GcdIsOne`, which this module and modules that import it used -/

section

/-! # Recognize a unit gcd in any of the shared inverse banks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep S)
open VG.Impl.Rsa.X86.Keys (aT1 aT2 sT)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem gcdIsOne_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    (h : Ws s B Z n N) (space : 15 ≤ N) (hw : w ≠ .correction) :
    WP isa (gcdIsOne w) s fun t => Ws t B Z n N ∧
      Keep B (w.words n) [aT2, aT1] [sT, kFlag] s.mem t.mem ∧
      VG.Proof.Rsa.X86.Keys.slot t.mem B kFlag = (if num s.mem B (w.words n) 1 = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have H := h.runtime hw
  have fit := H.ws.arr_fit (j := aT2) (by unfold aT2; omega_using [space])
  have f1 := H.ws.fit64 (j := 1) (by omega_using [space])
  have positive := H.ws.wpos
  rw [kw_words h.width] at fit f1 positive
  unfold gcdIsOne
  refine WP.seq (WP.mono (small_ok h w 1 (by rw [offset_array]; exact fit))
    fun u ⟨hu, Ou, V, Ku⟩ => ?_)
  rw [offset_array] at Ou V
  change val32 u.mem B (VG.Proof.Rsa.X86.Keys.arr (w.words n) aT2) (w.words n + 2) = 1 at V
  have ou : Keep B (w.words n) [aT2] [] s.mem u.mem :=
    VG.Proof.Rsa.X86.Keys.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou)
      (by simp only [S]; omega_using []) (by simp)
  have constant : num u.mem B (w.words n) aT2 = 1 := by
    have bound : 1 < 2 ^ (32 * w.words n) := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega_using [positive] : 1 ≤ 32 * w.words n)
      omega_using [this]
    exact (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [] : w.words n ≤ w.words n + 2)
      (by rw [V]; exact bound)).trans V
  have core := VG.Proof.Rsa.X86.KeyRt.eqS_ok (d := kFlag) (a := 1) (b := aT2) (t := aT1) (hu.runtime hw)
    (by unfold aT1; omega_using [space]) (by omega_using [space]) (by unfold aT2; omega_using [space])
    (by decide) (by decide) (by decide)
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, Ot, result, Kt⟩ => ?_
  have original : num u.mem B (w.words n) 1 = num s.mem B (w.words n) 1 :=
    ou.num (by decide) (by simp) f1
  rw [original, constant] at result
  refine ⟨hu.afterBank hw Kt Ot (by intro j hj; have hsmall :=
      (by decide : ∀ j ∈ ([aT1] : List Nat), j < 15) j hj; omega_using [space, hsmall]) (by decide),
    ou.join Ot (js := [aT2, aT1]) (ds := [sT, kFlag]), result, (Ku.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.LcmFrame`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.Lcm`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyGcdPart`, which only this module used -/

section

/-! # Complete native GCD stage for the RSA LCM -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def canonU (u v : Nat) : Nat := if v % 2 = 0 then v else u
def canonV (u v : Nat) : Nat := if v % 2 = 0 then u else v

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.GcdFrom`, which only this module used -/

section

/-! # Prime-width GCD computation preserves the full RSA workspace

A saved bit chooses the computed gcd or one. The bit is retained across
the smaller inverse, and widening clears every unused output word.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aU aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (gcdRanges inverse_workspace inverse_array_layout inverse_end_le
  InverseLayout)

theorem gcdFrom_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundM : num s.mem B n aDen < 2 ^ (32 * k))
    (odd : num s.mem B n aDen % 2 = 1) (large : 1 < num s.mem B n aDen)
    (one : num s.mem B n aOne = 1) (bit : slot s.mem B kFlag ≤ 1) :
    WP isa gcdFrom s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (gcdRanges n k) s.mem t.mem ∧
      num t.mem B n aDen = (if slot s.mem B kFlag = 0 then 1 else
        Nat.gcd (num s.mem B n aU) (num s.mem B n aDen)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  obtain small : k ≤ n := by omega_using [width]
  obtain hk := inverse_workspace h.old positive small
  obtain layout := inverse_array_layout h.old small (a := aU) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  obtain U := VG.Proof.RsaKeyGen.WordBounds32.low_eq small boundU
  obtain M := VG.Proof.RsaKeyGen.WordBounds32.low_eq small boundM
  obtain divWidth : n / 2 = k := by omega_using [width]
  unfold gcdFrom seqs
  obtain layout' : InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aU).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] using layout
  refine WP.seq (WP.mono (inverseFrom_ok h (by decide) (by decide) layout' 
    (by change val32 s.mem B (arr n aDen) (n / 2) % 2 = 1; rw [divWidth, M]; exact odd)
    (by change 1 < val32 s.mem B (arr n aDen) (n / 2); rw [divWidth, M]; exact large)) fun u ⟨hu, Ou, gcd, _, _, Ku⟩ => ?_)
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] at Ou gcd
  change num u.mem B k 1 = Nat.gcd (val32 s.mem B (arr n aU) k) (val32 s.mem B (arr n aDen) k) at gcd
  rw [U, M] at gcd
  obtain oneU : num u.mem B n aOne = 1 := by
    rw [h.inverse_num small (by decide) (by decide) Ou, one]
  obtain flagU : slot u.mem B kFlag = slot s.mem B kFlag := h.inverse_slot (by decide) Ou
  obtain sourceBound : arr k 1 + 4 * k ≤ Z := by
    obtain F := hk.arr_fit (j := 1) (by decide)
    unfold S at F
    omega_using [F]
  obtain before : arr k 1 + 4 * k ≤ arr n aDen := by
    obtain F := arr_end (w := k) (show 1 < 15 by decide)
    obtain E := inverse_end_le small (j := aDen) (by decide)
    unfold S at F
    omega_using [F, E]
  obtain widenProof := widen_ok hu .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)
    (.array .prime 1) (by change n / 2 ≤ n; omega_using [])
    (by exact h.arr_fit (by decide))
    (by simpa only [offset_array, Width.words, divWidth] using sourceBound)
    (Or.inl (by simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] using before))
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] at widenProof
  refine WP.seq (WP.mono widenProof
    fun v ⟨hv, Ov, _, widened, Kv⟩ => ?_)
  obtain denV : num v.mem B n aDen = Nat.gcd (num s.mem B n aU) (num s.mem B n aDen) := widened.trans gcd
  obtain oneV : num v.mem B n aOne = 1 := by
    change val32 v.mem B (arr n aOne) n = 1
    rw [Ov.val32 (d := arr n aOne) (k := n) (by unfold arr S aOne aDen; omega_using []) (by have := h.fit64 (j := aOne) (by decide); unfold S at this; omega_using [this])]
    exact oneU
  obtain flagV : slot v.mem B kFlag = slot s.mem B kFlag := by
    change w32 v.mem B kFlag = w32 s.mem B kFlag
    rw [Ov.w32 (d := kFlag) (by unfold arr aDen kFlag hdr; omega_using []) (by decide)]
    exact flagU
  refine WP.mono (sel_ok hv (by decide) (by decide) (by decide) (by decide)
    (by rw [flagV]; exact bit) (by decide)) fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, ?_, by rw [selected, flagV, oneV, denV],
    Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  obtain first : OutsS B (s.gpr .esp) (gcdRanges n k) s.mem u.mem :=
    Ou.mono (fun r hr => List.mem_append_left _ hr)
  obtain middle : OutsS B (s.gpr .esp) (gcdRanges n k) u.mem v.mem :=
    OutsS.of_outs (Outs.of_outside Ov (List.mem_append_right _ (List.mem_singleton_self _)))
  obtain last : OutsS B (s.gpr .esp) (gcdRanges n k) v.mem t.mem := by
    change Outs B [(arr n aDen, S n)] v.mem t.mem at Ot
    exact OutsS.of_outs (Ot.mono (fun r hr => List.mem_append_right _ hr))
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The native RSA LCM agrees with the shared integer algorithm

The proof includes arbitrary predecessors, including zero. The inverse
runs at prime width, while products and division retain modulus width.
-/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/GcdPart.lean`, which only this module imported.
section

/-! # Complete native GCD stage for the RSA LCM -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aU aV aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (gcdPartRanges gcdPartArrays canonU canonV)

theorem gcdPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundV : num s.mem B n aV < 2 ^ (32 * k))
    (odd : 2 ≤ canonV (num s.mem B n aU) (num s.mem B n aV) →
      canonV (num s.mem B n aU) (num s.mem B n aV) % 2 = 1)
    (one : num s.mem B n aOne = 1) :
    WP isa gcdPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (gcdPartRanges n k) s.mem t.mem ∧
      num t.mem B n aDen =
        (if canonV (num s.mem B n aU) (num s.mem B n aV) ≤ 1 then 1 else
          Nat.gcd (canonU (num s.mem B n aU) (num s.mem B n aV))
            (canonV (num s.mem B n aU) (num s.mem B n aV))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let A := num s.mem B n aU
  let C := num s.mem B n aV
  obtain cbU : canonU A C < 2 ^ (32 * k) := by
    unfold canonU
    split
    · exact boundV
    · exact boundU
  obtain cbV : canonV A C < 2 ^ (32 * k) := by
    unfold canonV
    split
    · exact boundU
    · exact boundV
  obtain bound3 : 3 < 2 ^ (32 * k) := by
    obtain P : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have oddLocal : 2 ≤ canonV A C → canonV A C % 2 = 1 := odd
  obtain valid : canonV A C % 2 = 1 ∧ 3 ≤ canonV A C ↔ ¬canonV A C ≤ 1 := by
    constructor
    · intro H
      omega
    · intro H
      obtain O := oddLocal (by omega)
      exact ⟨O, by omega⟩
  unfold gcdPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (oddSecond_ok h) fun u ⟨hu, Ou, U, V, Ku⟩ => ?_)
  change num u.mem B n aU = canonU A C at U
  change num u.mem B n aV = canonV A C at V
  obtain oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (oddModulus_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, flag, modulus, Kv⟩ => ?_)
  rw [V] at flag modulus
  obtain Uv : num v.mem B n aU = canonU A C := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), U]
  obtain oneV : num v.mem B n aOne = 1 := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), oneU]
  obtain inputBound : num v.mem B n aU < 2 ^ (32 * k) := by rw [Uv]; exact cbU
  obtain modulusBound : num v.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact cbV
    · exact bound3
  obtain modulusOdd : num v.mem B n aDen % 2 = 1 := by
    rw [modulus]
    split
    · next H => exact H.1
    · decide
  obtain modulusLarge : 1 < num v.mem B n aDen := by rw [modulus]; split <;> omega
  obtain bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (gcdFrom_ok hv width positive inputBound modulusBound modulusOdd modulusLarge oneV bit)
    fun t ⟨ht, Ot, computed, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  · have first : Outs B (gcdPartRanges n k) s.mem u.mem :=
      VG.Proof.Mont.Outs.mono (Ou.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    obtain middle : Outs B (gcdPartRanges n k) u.mem v.mem :=
      VG.Proof.Mont.Outs.mono (Ov.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    obtain spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
    rw [spV] at Ot
    exact (OutsS.of_outs (first.trans middle)).trans (Ot.mono (fun r hr => List.mem_append_left _ hr))
  · change num t.mem B n aDen = if canonV A C ≤ 1 then 1 else Nat.gcd (canonU A C) (canonV A C)
    rw [computed, flag, Uv, modulus]
    by_cases H : canonV A C ≤ 1
    · have inactive : ¬(canonV A C % 2 = 1 ∧ 3 ≤ canonV A C) := fun P => valid.mp P H
      simp [H, inactive]
    · have active := valid.mpr H
      simp [H, active]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPm aQm aPhi aU aV aDen aOne aL kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (canonU canonV gcdPartRanges gcdPart_preserves_num)

def lcmDivisionRanges (n : Nat) : List (Nat × Nat) :=
  arrayDivisionRanges n aL aT1

def lcmRanges (n k : Nat) : List (Nat × Nat) :=
  ranges n halveArrays [kFlag] ++ (gcdPartRanges n k ++ lcmDivisionRanges n)

theorem lcmPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundP : num s.mem B n aPm < 2 ^ (32 * k)) (boundQ : num s.mem B n aQm < 2 ^ (32 * k))
    (product : num s.mem B n aPhi = num s.mem B n aPm * num s.mem B n aQm)
    (one : num s.mem B n aOne = 1) :
    WP isa lcmPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (lcmRanges n k) s.mem t.mem ∧
      num t.mem B n aL = Nat.lcm (num s.mem B n aPm) (num s.mem B n aQm) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := num s.mem B n aPm
  let Q := num s.mem B n aQm
  let T := VG.Proof.RsaKeyGen.halveIter (32 * n) (P, Q, P * Q)
  obtain small : k ≤ n := by omega_using [width]
  obtain powBound : 2 ^ (32 * k) ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega_using [width])
  have productLocal : num s.mem B n aPhi = P * Q := product
  obtain phiBound : P * Q < 2 ^ (32 * n) := by
    rw [← productLocal]
    exact val32_lt _ _ _ _
  obtain bounds : T.1 < 2 ^ (32 * k) ∧ T.2.1 < 2 ^ (32 * k) ∧ T.2.2 < 2 ^ (32 * n) :=
    VG.Proof.RsaKeyGen.halveIter_bounds (32 * n) ⟨boundP, boundQ, phiBound⟩
  obtain arithmetic : (2 ≤ canonV T.1 T.2.1 → canonV T.1 T.2.1 % 2 = 1) ∧
      Nat.lcm P Q = T.2.2 / (if canonV T.1 T.2.1 ≤ 1 then 1 else Nat.gcd (canonU T.1 T.2.1) (canonV T.1 T.2.1)) :=
    VG.Proof.RsaKeyGen.lcm_eq (Nat.lt_of_lt_of_le boundP powBound) (Nat.lt_of_lt_of_le boundQ powBound)
  unfold lcmPart seqs
  refine WP.seq (WP.mono (twos_ok h) fun u ⟨hu, Ou, tripleValue, Ku⟩ => ?_)
  rw [productLocal] at tripleValue
  obtain U : num u.mem B n aU = T.1 := congrArg Prod.fst tripleValue
  obtain V : num u.mem B n aV = T.2.1 := congrArg (fun p => p.2.1) tripleValue
  obtain F : num u.mem B n aPhi = T.2.2 := congrArg (fun p => p.2.2) tripleValue
  obtain oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (gcdPart_ok hu width positive
    (by rw [U]; exact bounds.1) (by rw [V]; exact bounds.2.1)
    (by rw [U, V]; exact arithmetic.1) oneU) fun v ⟨hv, Ov, denominator, Kv⟩ => ?_)
  rw [U, V] at denominator
  obtain phiV : num v.mem B n aPhi = T.2.2 := by
    rw [hu.read_num (by decide) Ov (gcdPart_preserves_num small (by decide) (by decide) (by decide) (by decide)
      (h.fit64 (by decide))), F]
  obtain denPositive : 0 < num v.mem B n aDen := by
    rw [denominator]
    split
    · decide
    · next notSmall => exact Nat.gcd_pos_of_pos_right _ (by omega_using [notSmall])
  refine WP.mono (arrayDivision_ok hv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) denPositive)
    fun t ⟨ht, Ot, quotient, _, Kt⟩ => ?_
  change num t.mem B n aL = num v.mem B n aPhi / num v.mem B n aDen at quotient
  rw [phiV, denominator] at quotient
  refine ⟨ht, ?_, quotient.trans arithmetic.2.symm, Ku.trans (Kv.trans Kt)⟩
  obtain first : Outs B (lcmRanges n k) s.mem u.mem :=
    VG.Proof.Mont.Outs.mono Ou (fun r hr => List.mem_append_left _ hr)
  obtain spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  obtain middle : OutsS B (s.gpr .esp) (lcmRanges n k) u.mem v.mem := by
    rw [← spU]
    exact Ov.mono (fun r hr => List.mem_append_right _ (List.mem_append_left _ hr))
  obtain last : Outs B (lcmRanges n k) v.mem t.mem :=
    Ot.mono (fun r hr => List.mem_append_right _ (List.mem_append_right _ hr))
  exact ((OutsS.of_outs first).trans middle).trans (OutsS.of_outs last)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The complete native LCM leaves the factors and public exponent intact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.RsaKeyGen.X86.Key (lcmArrays stageRanges gcdPartRanges gcdRanges gcdPartArrays
  inverseRanges StageCovers stage_cover_array stage_cover_header stage_cover_temp stage_cover_bank)

theorem lcm_stage_frame {m m' : Mem} {B : Addr} {n k : Nat} (width : k ≤ n)
    (O : Outs B (lcmRanges n k) m m') : Outs B (stageRanges n lcmArrays) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  change r ∈ ranges n halveArrays [kFlag] ++ (gcdPartRanges n k ++ lcmDivisionRanges n) at hr
  rcases List.mem_append.mp hr with half | other
  · simp only [ranges, List.mem_append, List.mem_map] at half
    rcases half with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
    · have included : ∀ j ∈ halveArrays, j ∈ lcmArrays := by decide
      exact stage_cover_array (included j hj) (Nat.le_refl _)
    · obtain rfl := List.mem_singleton.mp hd
      exact stage_cover_header (by decide) (by decide)
  · rcases List.mem_append.mp other with gcd | division
    · change r ∈ gcdRanges n k ++ ranges n gcdPartArrays [kFlag] at gcd
      rcases List.mem_append.mp gcd with inv | other
      · change r ∈ inverseRanges k invSlots ++ [(arr n aDen, S n)] at inv
        rcases List.mem_append.mp inv with bank | den
        · simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at bank
          rcases bank with rfl | rfl | rfl | rfl
          · exact stage_cover_bank width
          all_goals exact stage_cover_header (by decide) (by decide)
        · obtain rfl := List.mem_singleton.mp den
          exact stage_cover_array (by decide) (Nat.le_refl _)
      · simp only [ranges, List.mem_append, List.mem_map] at other
        rcases other with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
        · have included : ∀ j ∈ gcdPartArrays, j < 15 ∨ j ∈ lcmArrays := by decide
          rcases included j hj with temp | array
          · exact stage_cover_temp (Nat.le_add_right ..) (arr_end (w := n) temp)
          · exact stage_cover_array array (Nat.le_refl _)
        · obtain rfl := List.mem_singleton.mp hd
          exact stage_cover_header (by decide) (by decide)
    · simp only [lcmDivisionRanges, arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at division
      rcases division with rfl | rfl | rfl | rfl | rfl
      · exact stage_cover_temp (Nat.le_refl _) (by unfold S; omega_using [])
      · exact stage_cover_header (by decide) (by decide)
      · exact stage_cover_header (by decide) (by decide)
      · exact stage_cover_array (by decide) (by unfold S; omega_using [])
      · have last := arr_end (w := n) (show aT1 < 15 by decide)
        change arr n aT1 + S n ≤ hdr + 15 * S n at last
        exact stage_cover_temp (Nat.le_add_right ..) (by unfold S at last ⊢; omega_using [last])

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyCorrectionGeometry`, which only this module used -/

section

/-! # The fixed 128-bit correction bank fits every native RSA workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem correction_workspace {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) : Ws s B Z 4 4 := by
  refine ⟨h.workspace, ?_, by decide, by decide⟩
  change 256 ≤ Z
  have lower : 256 ≤ 160 + 32 * (4 * (n + 2)) :=
    Nat.le_trans (by decide : 256 ≤ 160 + 32 * (4 * 2))
      (Nat.add_le_add_left (Nat.mul_le_mul_left 32
        (Nat.mul_le_mul_left 4 (Nat.le_add_left 2 n))) 160)
  exact Nat.le_trans lower h.fits

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyOddPrepared`, which only this module used -/

section

/-! # The quotient, remainder, and tiny inverse ready for native assembly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

structure OddPrepared (B : Addr) (n e L : Nat) (s : State) : Prop where
  exponent : val32 s.mem B kEv 2 = e
  lcm : num s.mem B n aL = L
  quotient : num s.mem B n aU = L / e
  remainder : num s.mem B n aV = L % e
  one : num s.mem B n aOne = 1
  coefficient : num s.mem B 2 3 < e
  congruence : (e : Int) ∣ (num s.mem B 2 3 : Int) * (L % e) - Nat.gcd (L % e) e
  mask : slot s.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyOddPrepareFrame`, which only this module used -/

section

/-! # Frames for preparing the quotient-based inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponent_mask_coefficient {m m' : Mem} {B : Addr} {n : Nat}
    (O : Keep B n [aT1, aT2] [kOk] m m') : num m' B 2 3 = num m B 2 3 := by
  change val32 m' B (arr 2 3) 2 = val32 m B (arr 2 3) 2
  apply O.val32 _ (by decide)
  intro r hr
  simp only [ranges, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  all_goals simp only [arr, S, aT1, aT2, hdr, kOk]
  all_goals omega_using []

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.CorrectionNumerator`, which only this module used -/

section

/-! # Form the correction's exact 128-bit numerator with native products -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aV aDen kProduct)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem correctionNumerator_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (_width : 2 ≤ n)
    (fits : val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 < 2 ^ 128) :
    WP isa correctionNumerator s fun t =>
      Ws t B Z n 32 ∧ Outs B correctionScratch s.mem t.mem ∧
      val32 t.mem B (arr 4 0) 4 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hn := h.old.workspace.nowrap
  obtain fr := h.arr_fit (j := aV) (by decide)
  obtain ft := h.arr_fit (j := aDen) (by decide)
  obtain bank := VG.Proof.RsaKeyGen.X86.Key.correction_workspace h.old
  have hz : 256 ≤ Z := bank.fits
  obtain L : ProductGeometry Z 2 2 (arr 4 1) (arr n aV) (arr n aDen) := by
    refine ⟨⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp only [arr, S, aV, aDen, hdr] at *
    all_goals omega_arith
  unfold correctionNumerator seqs
  refine WP.seq (WP.mono (product_ok (left := .exponent) (right := .exponent)
    (out := .array .correction 1) (a := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV)
    (b := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) h L) fun u ⟨hu, Ou, V, Ku⟩ => ?_)
  change Outs B [(kProduct, 28), (arr 4 1, 24)] s.mem u.mem at Ou
  change val32 u.mem B (arr 4 1) 6 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 at V
  obtain low : num u.mem B 4 1 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 4 ≤ 6) (by rw [V]; omega_arith)).trans V
  refine WP.seq (WP.mono (small_ok (j := 2) hu .correction 1 (by change 232 ≤ Z; omega_arith))
    fun v ⟨hv, Ov, wideOne, Kv⟩ => ?_)
  change Outside B (arr 4 2) 24 u.mem v.mem at Ov
  change val32 v.mem B (arr 4 2) 6 = 1 at wideOne
  obtain one : val32 v.mem B (arr 4 2) 4 = 1 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 4 ≤ 6)
      (by rw [wideOne]; decide)).trans wideOne
  obtain productV : val32 v.mem B (arr 4 1) 4 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 :=
    (Ov.val32 (by decide) (by decide)).trans low
  refine WP.mono (chainAddW_ok hv.old.workspace (by decide : 0 < 4)
    (by change 176 ≤ Z; omega_arith) (by change 200 ≤ Z; omega_arith) (by change 224 ≤ Z; omega_arith)
    (by decide) (by decide)) fun t ⟨Ot, ⟨carry, _, sum⟩, Kt⟩ => ?_
  change Outside B (arr 4 0) 16 v.mem t.mem at Ot
  change val32 t.mem B (arr 4 0) 4 + 2 ^ 128 * carry.toNat =
    val32 v.mem B (arr 4 1) 4 + val32 v.mem B (arr 4 2) 4 at sum
  rw [productV] at sum
  change val32 v.mem B (arr 4 2) 4 = 1 at one
  rw [one] at sum
  obtain result : val32 t.mem B (arr 4 0) 4 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 := by
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at sum <;> omega_arith
  obtain rest := Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))
  obtain frame : Outs B correctionScratch s.mem t.mem := by
    obtain first : Outs B correctionScratch s.mem u.mem := VG.Proof.Rsa.outs_cover Ou (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(kProduct, 28), by simp [correctionScratch], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(hdr, 96), by simp [correctionScratch], by decide, by decide⟩)
    exact (first.trans (correction_scratch_arr (by decide) Ov)).trans
      (correction_scratch_outside (by decide) (by decide) Ot)
  refine ⟨h.keep rest (VG.Proof.Rsa.X86.KeyRt.outs_outside frame ?_), frame, result, rest.mono (by decide)⟩
  intro region member
  simp only [correctionScratch, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only [kProduct, hdr] <;> omega_arith

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.DProduct`, which only this module used -/

section

/-! # Assemble the private exponent from a quotient and a two-word scalar -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aD aU aV aDen)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

def dProductRanges (n : Nat) : List (Nat × Nat) :=
  [(128, 28), (arr n 0, 4 * (n + 4)), (arr n aD, S n)]

theorem dProduct_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (fits : num s.mem B n aU * val32 s.mem B (arr n aDen) 2 + num s.mem B n aV < 2 ^ (32 * n)) :
    WP isa dProduct s fun t =>
      Ws t B Z n 32 ∧ Outs B (dProductRanges n) s.mem t.mem ∧
      num t.mem B n aD = num s.mem B n aU * val32 s.mem B (arr n aDen) 2 + num s.mem B n aV ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hn := h.old.workspace.nowrap
  obtain f0 := h.arr_fit (j := 0) (by decide)
  obtain f1 := h.arr_fit (j := 1) (by decide)
  obtain fu := h.arr_fit (j := aU) (by decide)
  obtain ft := h.arr_fit (j := aDen) (by decide)
  obtain fc := h.arr_fit (j := aV) (by decide)
  obtain fd := h.arr_fit (j := aD) (by decide)
  obtain L : ProductGeometry Z n 2 (arr n 0) (arr n aU) (arr n aDen) := by
    refine ⟨⟨h.wpos, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp only [arr, S, aU, aDen, VG.Impl.Rsa.X86.Keys.hdr] at *
    all_goals omega_arith
  unfold dProduct
  refine WP.seq (WP.mono (product_ok (left := .modulus) (right := .exponent)
    (out := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr 0)
    (a := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aU)
    (b := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) h L) fun u ⟨hu, Ou, V, Ku⟩ => ?_)
  change Outs B [(128, 28), (arr n 0, 4 * (n + 4))] s.mem u.mem at Ou
  change val32 u.mem B (arr n 0) (n + 4) =
    val32 s.mem B (arr n aU) n * val32 s.mem B (arr n aDen) 2 at V
  change val32 s.mem B (arr n aU) n * val32 s.mem B (arr n aDen) 2 + val32 s.mem B (arr n aV) n < 2 ^ (32 * n) at fits
  obtain low : val32 u.mem B (arr n 0) n = val32 s.mem B (arr n aU) n * val32 s.mem B (arr n aDen) 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_arith : n ≤ n + 4) (by rw [V]; omega_arith)).trans V
  obtain C : val32 u.mem B (arr n aV) n = val32 s.mem B (arr n aV) n := by
    apply Ou.val32 _ (by unfold S at fc; omega_arith)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals simp only [arr, S, aV, VG.Impl.Rsa.X86.Keys.hdr]
    all_goals omega_arith
  obtain addition := VG.Proof.Rsa.X86.KeyRt.chainAdd_ok (o := aD) (a := 0) (b := aV)
    hu.full (by decide) (by decide) (by decide) false
  simp only [kw_full h.width, VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_false, Nat.add_zero] at addition
  refine WP.mono addition fun t ⟨_, Ot, ⟨carry, _, sum⟩, Kt⟩ => ?_
  change val32 t.mem B (arr n aD) n + 2 ^ (32 * n) * carry.toNat =
    val32 u.mem B (arr n 0) n + val32 u.mem B (arr n aV) n at sum
  rw [low, C] at sum
  obtain result : num t.mem B n aD = num s.mem B n aU * val32 s.mem B (arr n aDen) 2 + num s.mem B n aV := by
    change val32 t.mem B (arr n aD) n = _
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at sum <;> omega_arith
  obtain keep := Ku.trans (Kt.mono (by decide))
  obtain ht := hu.afterKeep Kt Ot (by decide) (by simp)
  refine ⟨ht, ?_, result, keep.mono (by decide)⟩
  obtain first : Outs B (dProductRanges n) s.mem u.mem := Ou.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [dProductRanges])
  exact first.trans (VG.Proof.Mont.Outs.mono Ot (by
    intro r hr
    change r ∈ [(arr n aD, S n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    simp [dProductRanges]))

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.Complement`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.PairSubtract`, which only this module used -/

section

/-! # Paired native subtraction for the private-exponent complement -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem subtractPair_ok {s : State} {B : Addr} {Z out a b : Nat} (h : Scr s B Z) (P : PtrAt s B .ebp out)
    (fa : a + 8 ≤ Z) (fb : b + 8 ≤ Z) (fo : out + 8 ≤ Z) :
    WP isa (.block (subtractPair a b)) s fun t =>
      Outside B out 8 s.mem t.mem ∧
      (∃ borrow : Bool, val32 t.mem B out 2 + val32 s.mem B b 2 =
        val32 s.mem B a 2 + 2 ^ 64 * borrow.toNat) ∧ Keeps [.eax, .edx] s t := by
  have hn := h.nowrap
  unfold subtractPair
  refine wp_movS (readSrc_sc h (by omega_using [fa])) fun u U _ => ?_
  obtain hu := h.of_keeps U.keeps (by decide)
  refine wp_movS (readSrc_sc hu (by omega_using [fa])) fun v V _ => ?_
  obtain Kv : Keeps [.eax, .edx] s v := (U.keeps.mono (by decide)).widen V.keeps
  obtain hv := h.of_keeps Kv (by decide)
  obtain loRead := readSrc_sc hv (d := b) (by omega_using [fb])
  rw [V.mem, U.mem] at loRead
  refine wp_subS loRead fun w W cfW => ?_
  obtain Kw : Keeps [.eax, .edx] s w := Kv.widen W.keeps
  obtain hw := h.of_keeps Kw (by decide)
  obtain hiRead := readSrc_sc hw (d := b + 4) (by omega_using [fb])
  rw [W.mem, V.mem, U.mem] at hiRead
  refine wp_sbbS hiRead cfW fun x X _ => ?_
  obtain Kx : Keeps [.eax, .edx] s x := Kw.widen X.keeps
  obtain hx := h.of_keeps Kx (by decide)
  obtain Px : PtrAt x B .ebp out := by rw [PtrAt, Kx.1 _ (by decide)]; exact P
  obtain Rx : VG.Proof.Mont.X86.Rt.Ws x B Z := ⟨hx.wr, hx.nowrap⟩
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr Rx Px (d := 0) (by omega_using [fo]))
    (VG.Proof.Mont.X86.Rt.ws_write Rx (by omega_using [fo])) fun y Y => ?_
  obtain hy := hx.of_keeps (Y.keeps []) (by decide)
  obtain Py : PtrAt y B .ebp out := by rw [PtrAt, Y.gpr]; exact Px
  obtain Ry : VG.Proof.Mont.X86.Rt.Ws y B Z := ⟨hy.wr, hy.nowrap⟩
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr Ry Py (d := 4) (by omega_using [fo]))
    (VG.Proof.Mont.X86.Rt.ws_write Ry (by omega_using [fo])) fun t T => WP.block_nil ?_
  simp only [Nat.add_zero] at Y
  let lowBorrow := decide ((v.gpr .eax).toNat < (s.mem.readW (off B b) 32).toNat)
  let highBorrow := decide ((w.gpr .edx).toNat < (s.mem.readW (off B (b + 4)) 32).toNat + lowBorrow.toNat)
  obtain low : (w.gpr .eax).toNat + w32 s.mem B b = (v.gpr .eax).toNat + 2 ^ 32 * lowBorrow.toNat := by
    rw [W.gpr]
    obtain H := sbb_rel (v.gpr .eax) (s.mem.readW (off B b) 32) false
    simpa only [show (BitVec.ofBool false).setWidth 32 = 0#32 from rfl, BitVec.sub_zero,
      Bool.toNat_false, Nat.add_zero] using H
  obtain high : (x.gpr .edx).toNat + w32 s.mem B (b + 4) + lowBorrow.toNat =
      (w.gpr .edx).toNat + 2 ^ 32 * highBorrow.toNat := by rw [X.gpr]; exact sbb_rel ..
  rw [V.other _ (by decide), U.gpr] at low
  rw [W.other _ (by decide), V.gpr, U.mem] at high
  change (w.gpr .eax).toNat + w32 s.mem B b = w32 s.mem B a + 2 ^ 32 * lowBorrow.toNat at low
  change (x.gpr .edx).toNat + w32 s.mem B (b + 4) + lowBorrow.toNat =
    w32 s.mem B (a + 4) + 2 ^ 32 * highBorrow.toNat at high
  obtain oldMem : x.mem = s.mem := X.mem.trans (W.mem.trans (V.mem.trans U.mem))
  obtain Oy : Outside B out 4 s.mem y.mem := by
    rw [Y.mem, oldMem]
    exact writeW32_outside _ _ _ (by omega_using [fo, hn])
  obtain Ot : Outside B (out + 4) 4 y.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by omega_using [fo, hn])
  obtain lowT : w32 t.mem B out = (x.gpr .eax).toNat := by
    rw [Ot.w32 (Or.inl (Nat.le_refl _)) (by omega_using [fo, hn]), Y.mem, w32_write_self]
  obtain highT : w32 t.mem B (out + 4) = (x.gpr .edx).toNat := by
    rw [T.mem, w32_write_self, Y.gpr]
  refine ⟨(Oy.mono (Nat.le_refl _) (by omega_using [])).trans (Ot.mono (by omega_using []) (by omega_using [])),
    ⟨highBorrow, ?_⟩, Kx.trans ((Y.keeps _).trans (T.keeps _))⟩
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [lowT, highT, X.other _ (by decide)]
  omega_using [low, high]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end


/-! # Form the public-exponent complement from the tiny inverse coefficient -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aDen kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem complement_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (less : val32 s.mem B (arr 2 3) 2 < val32 s.mem B kEv 2) :
    WP isa complement s fun t =>
      Ws t B Z n 32 ∧ Outside B (arr n aDen) (S n) s.mem t.mem ∧
      val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      num t.mem B n aDen = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  obtain fit := h.arr_fit (j := aDen) (by decide)
  have fits := h.old.fits
  have hn := h.old.workspace.nowrap
  obtain eBound : kEv + 8 ≤ Z := by have := h.hdr_le; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [this]
  obtain xBound : arr 2 3 + 8 ≤ Z := by unfold arr S VG.Impl.Rsa.X86.Keys.hdr at fits ⊢; omega_using [fits]
  obtain beforeE : kEv + 8 ≤ arr n aDen := by unfold arr S kEv aDen VG.Impl.Rsa.X86.Keys.hdr; omega_using []
  obtain beforeX : arr 2 3 + 8 ≤ arr n aDen := by unfold arr S aDen VG.Impl.Rsa.X86.Keys.hdr; omega_using []
  unfold complement
  refine WP.seq (WP.mono (zero_ok h .modulus (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) fit)
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change Outside B (arr n aDen) (4 * (n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (arr n aDen) (n + 2) = 0 at zero
  obtain E : val32 u.mem B kEv 2 = val32 s.mem B kEv 2 := Ou.val32 (Or.inl beforeE) (by omega_using [hn, eBound])
  obtain X : val32 u.mem B (arr 2 3) 2 = val32 s.mem B (arr 2 3) 2 := Ou.val32 (Or.inl beforeX) (by omega_using [hn, xBound])
  refine hu.ptr_ok (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) (by decide) (by decide)
    (by simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words]; unfold S at fit; omega_using [fit, hn])
    fun v Kv mv P => ?_
  obtain hv := hu.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine WP.mono (subtractPair_ok hv.old.workspace P eBound xBound
    (by change arr n aDen + 8 ≤ Z; unfold S at fit; omega_using [fit])) fun t ⟨Ot, ⟨borrow, value⟩, Kt⟩ => ?_
  rw [mv] at Ot value
  change Outside B (arr n aDen) 8 u.mem t.mem at Ot
  change val32 t.mem B (arr n aDen) 2 + val32 u.mem B (arr 2 3) 2 =
    val32 u.mem B kEv 2 + 2 ^ 64 * borrow.toNat at value
  rw [E, X] at value
  obtain noBorrow := (VG.Proof.Rsa.borrow_iff value (val32_lt t.mem B (arr n aDen) 2) (Bool.toNat_le borrow)).mpr
    (Nat.le_of_lt less)
  rw [noBorrow, Nat.mul_zero, Nat.add_zero] at value
  obtain result : val32 t.mem B (arr n aDen) 2 = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by omega_using [value]
  obtain high : val32 u.mem B (arr n aDen + 8) n = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 2) (c := n) (by omega_using [])
  obtain highT : val32 t.mem B (arr n aDen + 8) n = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by unfold S at fit; omega_using [fit, hn]), high]
  obtain full : val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by
    rw [show n + 2 = 2 + n by omega_using [], val32_append, highT, Nat.mul_zero, Nat.add_zero, result]
  obtain bound : val32 t.mem B (arr n aDen) (n + 2) < 2 ^ (32 * n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (val32_lt s.mem B kEv 2))
      (Nat.pow_le_pow_right (by decide) (by omega_using [width]))
  obtain frame := Ou.trans (Ot.mono (Nat.le_refl _) (by omega_using []))
  have K : Keeps [.eax, .ecx, .edx, .ebp] s t := Ku.trans
    ((Kv.mono (by decide)).trans (Kt.mono (by decide)))
  exact ⟨h.keep K (frame.mono (Nat.zero_le _) (by unfold S at fit; omega_using [fit])), frame, full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [] : n ≤ n + 2) bound).trans full,
    K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.DEven`, which only this module used -/

section

/-! # A modulus-width fallback for public even exponents -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aE aL aDen aU aV aD kEv kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges exponentTemps exponent_keep_frame
  exponent_temps_inverse inverse_array_layout)

theorem dEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (even : val32 s.mem B kEv 2 % 2 = 0)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa dEven s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let e := val32 s.mem B kEv 2
  let L := num s.mem B n aL
  let valid := L % 2 = 1 ∧ 3 ≤ L
  let M := if valid then L else 3
  have eo : e % 2 = 0 := even
  obtain mo : M % 2 = 1 := by
    unfold M
    split
    · next H => exact H.1
    · decide
  obtain ml : 1 < M := by unfold M; split <;> omega
  unfold dEven seqs
  refine WP.seq (WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, flag, modulus, Ku⟩ => ?_)
  change num u.mem B n aDen = M at modulus
  change slot u.mem B kFlag = (if valid then 1 else 0) at flag
  obtain Eu : num u.mem B n aE = e :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans loaded
  obtain frameU := exponent_keep_frame (by decide) (by decide) Ou
  refine WP.seq (WP.mono (saveSlot_ok hu (by decide) (by decide))
    fun v ⟨hv, Ov, saved, Kv⟩ => ?_)
  obtain maskV : slot v.mem B kOk = (if valid then 1 else 0) := saved.trans flag
  obtain Mv : num v.mem B n aDen = M :=
    (Ov.num (by simp) (by decide) (h.fit64 (by decide))).trans modulus
  obtain Ev : num v.mem B n aE = e :=
    (Ov.num (by simp) (by decide) (h.fit64 (by decide))).trans Eu
  obtain frameV := exponent_keep_frame (by decide) (by decide) Ov
  refine WP.seq (WP.mono (arrayDivision_ok hv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [Mv]; omega_using [mo]))
    fun w ⟨hw, Ow, _, R, Kw⟩ => ?_)
  rw [Ev, Mv] at R
  obtain Mw : num w.mem B n aDen = M :=
    (arrayDivision_preserves_num (by decide) (by decide) (by decide) (h.fit64 (by decide)) Ow).trans Mv
  obtain maskW : slot w.mem B kOk = (if valid then 1 else 0) :=
    (arrayDivision_preserves_slot (by decide) Ow).trans maskV
  obtain frameW := exponent_division_frame Ow
  obtain layout := inverse_array_layout hw.old (Nat.le_refl n) (by decide : aV < 32)
    (by decide : aDen < 32) (by decide) (by decide)
  refine WP.seq (WP.mono (inverseFrom_ok (w := .modulus)
    (src := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV)
    (mo := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) hw (by decide) (by decide) layout (by change num w.mem B n aDen % 2 = 1; rw [Mw]; exact mo)
    (by change 1 < num w.mem B n aDen; rw [Mw]; exact ml))
    fun a ⟨ha, Oa, gcd, congruence, boundX, Ka⟩ => ?_)
  change num a.mem B n 1 = Nat.gcd (num w.mem B n aV) (num w.mem B n aDen) at gcd
  change (num w.mem B n aDen : Int) ∣ (num a.mem B n 3 : Int) * num w.mem B n aV - num a.mem B n 1 at congruence
  change num a.mem B n 3 < num w.mem B n aDen at boundX
  rw [R, Mw] at gcd congruence
  rw [Mw] at boundX
  rw [gcd] at congruence
  obtain maskA : slot a.mem B kOk = (if valid then 1 else 0) :=
    (hw.inverse_slot (by decide) Oa).trans maskW
  obtain spW : w.gpr .esp = s.gpr .esp := by
    rw [Kw.1 .esp (by decide), Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
  obtain frameA : OutsS B (s.gpr .esp) (exponentRanges n) w.mem a.mem := by
    rw [← spW]
    exact OutsS.lift (fun _ _ O => (exponent_temps_inverse (Nat.le_refl n) O).mono
      (fun r hr => List.mem_append_left _ hr)) Oa
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .modulus) ha (by decide) (by decide)) fun b ⟨hb, Ob, flagB, Kb⟩ => ?_)
  simp only [Width.words] at Ob
  change slot b.mem B kFlag = (if num a.mem B n 1 = 1 then 1 else 0) at flagB
  rw [gcd] at flagB
  obtain maskB : slot b.mem B kOk = (if valid then 1 else 0) :=
    (Ob.slot (by decide) (by decide)).trans maskA
  obtain Xb : num b.mem B n 3 = num a.mem B n 3 :=
    Ob.num (by decide) (by decide) (h.fit64 (by decide))
  obtain frameB := exponent_keep_frame (by decide) (by decide) Ob
  refine WP.seq (WP.mono (andS_ok hb (by decide) (by decide) (by decide)
    (by rw [maskB]; split <;> omega_using []) (by rw [flagB]; split <;> omega_using []))
    fun c ⟨hc, Oc, maskC, Kc⟩ => ?_)
  rw [maskB, flagB] at maskC
  obtain Xc : num c.mem B n 3 = num a.mem B n 3 :=
    (Oc.num (by simp) (by decide) (h.fit64 (by decide))).trans Xb
  obtain frameC := exponent_keep_frame (by decide) (by decide) Oc
  refine WP.mono (copy_ok hc (by decide) (by decide) (by decide)) fun t ⟨ht, Ot, copied, Kt, _⟩ => ?_
  rw [Xc] at copied
  obtain maskT : slot t.mem B kOk =
      (if (if valid then 1 else 0) = 1 ∧ (if Nat.gcd (e % M) M = 1 then 1 else 0) = 1 then 1 else 0) :=
    (Ot.slot (by decide) (by simp)).trans maskC
  obtain frameT := exponent_keep_frame (by decide) (by simp) Ot
  refine ⟨ht, (((((OutsS.of_outs ((frameU.trans frameV).trans frameW)).trans frameA).trans
      (OutsS.of_outs frameB)).trans (OutsS.of_outs frameC)).trans (OutsS.of_outs frameT)),
    ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans
      (Kw.trans (Ka.trans ((Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kt.mono (by decide)))))))⟩
  · rw [maskT]
    by_cases V : valid <;> by_cases G : Nat.gcd (e % M) M = 1 <;> simp [V, G]
  · change Spec.Rsa.inverse e L = _
    by_cases V : valid
    · have ME : M = L := ite_eq_left V
      have V' : L % 2 = 1 ∧ 3 ≤ L := V
      by_cases G : Nat.gcd (e % M) M = 1
      · have C : (L : Int) ∣ (num a.mem B n 3 : Int) * (e % L) - 1 := by
          rw [G, ME] at congruence
          exact congruence
        obtain I := VG.Proof.RsaKeyGen.inverse_even V'.2 C (by simpa only [ME] using boundX)
        simpa only [maskT, V, G, ite_true, true_and, Nat.one_ne_zero, ite_false, copied] using I
      · have I := VG.Proof.RsaKeyGen.inverse_even_none eo (by
          intro H; exact G (by simpa only [ME] using H.2.2))
        simpa only [maskT, V, G, ite_true, ite_false, Nat.zero_ne_one, and_false, ↓reduceIte] using I
    · have I := VG.Proof.RsaKeyGen.inverse_even_none eo (by
        intro H; exact V ⟨H.1, H.2.1⟩)
      simpa only [maskT, V, ite_false, Nat.zero_ne_one, false_and, ↓reduceIte] using I

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The native factor, LCM, and private-inverse stages compose -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DOne.lean`, which only this module imported.
section

/-! # The unit public exponent at a runtime width -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aD aOne aL kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem dOne_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa dOne s fun t => Ws t B Z n 32 ∧
      Keep B n [aD, aT1] [sT, kFlag, kOk] s.mem t.mem ∧ num t.mem B n aD = 1 ∧
      slot t.mem B kOk = (if num s.mem B n aL = 1 then 0 else 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hf : kFlag + 4 ≤ hdr := by decide
  unfold dOne seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide) (by decide)) fun u ⟨hu, Ou, D, Ku, _⟩ => ?_)
  rw [one] at D
  obtain L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  obtain O : num u.mem B n aOne = 1 := by rw [Ou.num (by decide) (by simp) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (eq_ok hu (by decide) (by decide) (by decide) (by decide) (by decide) hf)
    fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [L, O] at flag
  obtain bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (notSlot_ok hv (by decide) hf bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aD, aT1]) (ds := [sT, kFlag, kOk])).join Ot
    (js := [aD, aT1]) (ds := [sT, kFlag, kOk]), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  · rw [Ot.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; decide)
      (h.fit64 (by decide)), Ov.num (by decide) (by decide) (h.fit64 (by decide)), D]
  · rw [mask, flag]
    by_cases p : num s.mem B n aL = 1 <;> simp [p]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/LAtLeastTwo.lean`, which only this module imported.
section

/-! # The public-exponent inverse also needs an LCM of at least two -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem lAtLeastTwo_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kFlag ≤ 1) :
    WP isa lAtLeastTwo s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hf : kFlag + 4 ≤ hdr := by decide
  unfold lAtLeastTwo seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (2 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 2 at constant
  obtain L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [L, constant] at subtract
  obtain iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  obtain flag : slot v.mem B kFlag = slot s.mem B kFlag := by
    rw [Ov.slot hf (by simp), Ou.slot hf (by simp)]
  refine WP.mono (borrowMask_ok hv borrow (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  obtain validMask : slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) := by
    simpa only [iffBorrow, flag] using value
  exact ⟨ht, (Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ot
    (js := [aT1, aT2]) (ds := [kOk]), validMask,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/OddPrepare.lean`, which only this module imported.
section

/-! # Prepare the private exponent using only a two-word inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL aE aU aV aOne kEv kFlag kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (OddPrepared exponentRanges exponentTemps
  exponent_preserves_e exponent_preserves_num exponent_temps_inverse exponent_temps_keep
  exponent_temps_preserves_num exponent_mask_coefficient InverseLayout inverse_end_le)

theorem dOddPrepare_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dOddPrepare s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧
      OddPrepared B n (val32 s.mem B kEv 2) (num s.mem B n aL) t ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let e := val32 s.mem B kEv 2
  let L := num s.mem B n aL
  have e3 : 3 ≤ e := large
  have eo : e % 2 = 1 := odd
  obtain e64 : e < 2 ^ 64 := val32_lt s.mem B kEv 2
  obtain re : L % e < e := Nat.mod_lt _ (by omega)
  unfold dOddPrepare seqs
  refine WP.seq (WP.mono (arrayDivision_ok h (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [loaded]; exact Nat.zero_lt_of_lt large)) fun u ⟨hu, Ou, Q, R, Ku⟩ => ?_)
  rw [loaded] at Q R
  change num u.mem B n aU = L / e at Q
  change num u.mem B n aV = L % e at R
  obtain divisionFrame := exponent_division_frame Ou
  obtain Eu : val32 u.mem B kEv 2 = e := exponent_preserves_e divisionFrame
  obtain remainderBound : val32 u.mem B (arr n aV) n < 2 ^ 64 := by
    change num u.mem B n aV < 2 ^ 64
    rw [R]
    exact Nat.lt_trans re e64
  obtain remainderLow : val32 u.mem B (arr n aV) 2 = L % e :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width remainderBound).trans R
  obtain layout : InverseLayout Z 2 (arr n aV) kEv := by
    obtain fit := hu.arr_fit (j := aV) (by decide)
    have head := hu.hdr_le
    refine ⟨?_, ?_, Or.inr (inverse_end_le width (by decide)), Or.inl (by decide)⟩
    · unfold S at fit
      omega
    · unfold kEv hdr at *
      omega
  refine WP.seq (WP.mono (inverseFrom_ok (w := .exponent)
    (src := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV) (mo := .fixed kEv)
    hu (by decide) (by decide) layout
    (by change val32 u.mem B kEv 2 % 2 = 1; rw [Eu]; exact eo) (by change 1 < val32 u.mem B kEv 2; rw [Eu]; omega)) fun v ⟨hv, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  change num v.mem B 2 1 = Nat.gcd (val32 u.mem B (arr n aV) 2) (val32 u.mem B kEv 2) at gcd
  change (val32 u.mem B kEv 2 : Int) ∣ (num v.mem B 2 3 : Int) * val32 u.mem B (arr n aV) 2 - num v.mem B 2 1 at congruence
  rw [remainderLow, Eu] at gcd congruence
  rw [gcd] at congruence
  change num v.mem B 2 3 < val32 u.mem B kEv 2 at boundX
  rw [Eu] at boundX
  obtain spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  obtain inverseFrame : OutsS B (s.gpr .esp) (exponentTemps n) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => exponent_temps_inverse width) Ov
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .exponent) hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  simp only [Width.words] at Ow
  change slot w.mem B kFlag = (if num v.mem B 2 1 = 1 then 1 else 0) at flag
  rw [gcd] at flag
  obtain coefficientW : num w.mem B 2 3 = num v.mem B 2 3 :=
    Ow.num (by decide) (by decide) (by simpa only [kw_words hv.width, Width.words] using
      (hv.runtime (w := .exponent) (by decide)).ws.fit64 (j := 3) (by decide))
  obtain compareFrame : Outs B (exponentTemps n) v.mem w.mem :=
    exponent_temps_keep width (by decide) (by decide) Ow
  obtain prefixFrame : OutsS B (s.gpr .esp) (exponentRanges n) s.mem w.mem :=
    (OutsS.of_outs divisionFrame).trans ((inverseFrame.trans (OutsS.of_outs compareFrame)).mono
      (fun r hr => List.mem_append_left _ hr))
  obtain Lw : num w.mem B n aL = L :=
    h.read_num (by decide) prefixFrame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  obtain bit : slot w.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (lAtLeastTwo_ok hw bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  obtain maskFrame : Outs B (exponentTemps n) w.mem t.mem :=
    exponent_temps_keep (Nat.le_refl n) (by decide) (by decide) Ot
  obtain tailFrame := (inverseFrame.trans (OutsS.of_outs compareFrame)).trans (OutsS.of_outs maskFrame)
  obtain frame : OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem :=
    (OutsS.of_outs divisionFrame).trans (tailFrame.mono (fun r hr => List.mem_append_left _ hr))
  obtain coefficientT : num t.mem B 2 3 = num v.mem B 2 3 :=
    (exponent_mask_coefficient Ot).trans coefficientW
  obtain finalMask : slot t.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0) := by
    by_cases G : Nat.gcd (L % e) e = 1 <;> simpa [Lw, flag, G] using mask
  have tailOld : OutsS B (s.gpr .esp) (exponentTemps n) u.mem t.mem := tailFrame
  refine ⟨ht, frame, ⟨h.read_val32 (by decide) frame exponent_preserves_e, ?_, ?_, ?_, ?_, ?_, ?_, finalMask⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · exact h.read_num (by decide) frame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  · exact (h.read_num (by decide) tailOld (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)))).trans Q
  · exact (h.read_num (by decide) tailOld (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)))).trans R
  · rw [h.read_num (by decide) frame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide))), one]
  · rw [coefficientT]
    exact boundX
  · rw [coefficientT]
    exact congruence

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Correction.lean`, which only this module imported.
section

/-! # Exact small correction for the quotient-based private exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aV aDen kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (correction_workspace divisionGeometry division_context division_frame)

def correctionRanges (n : Nat) : List (Nat × Nat) := correctionScratch ++ [(arr n aV, S n)]

theorem correction_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (positive : 0 < val32 s.mem B kEv 2)
    (fits : val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 < 2 ^ 128)
    (quotientFits : (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) /
      val32 s.mem B kEv 2 < 2 ^ 64) :
    WP isa correction s fun t =>
      Ws t B Z n 32 ∧ Outs B (correctionRanges n) s.mem t.mem ∧
      num t.mem B n aV = (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) /
        val32 s.mem B kEv 2 ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have hn := h.old.workspace.nowrap
  unfold correction seqs
  refine WP.seq (WP.mono (correctionNumerator_ok h width fits) fun u ⟨hu, Ou, numerator, Ku⟩ => ?_)
  obtain h4 := correction_workspace hu.old
  have hz : 256 ≤ Z := h4.fits
  obtain E := correction_preserves_exponent Ou
  refine WP.seq (WP.mono (widenTo_ok hu .correction .exponent (.array .correction 2) (.fixed kEv)
    (by change 2 ≤ 4; decide) (by change 232 ≤ Z; omega) (by change 88 ≤ Z; omega) (Or.inl (by change 88 ≤ 208; decide))) fun v ⟨hv, Ov, fullDivisor, _, Kv⟩ => ?_)
  change Outside B (arr 4 2) (S 4) u.mem v.mem at Ov
  change val32 v.mem B (arr 4 2) 6 = val32 u.mem B kEv 2 at fullDivisor
  rw [E] at fullDivisor
  obtain numeratorV : (divisionGeometry B Z 4).value v.mem 0 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 := by
    change val32 v.mem B (arr 4 0) 4 = _
    exact (Ov.val32 (by decide) (by decide)).trans numerator
  obtain divisorV : (divisionGeometry B Z 4).value v.mem 2 = val32 s.mem B kEv 2 := by
    obtain bound : val32 v.mem B (arr 4 2) 6 < 2 ^ (32 * 5) := by
      rw [fullDivisor]
      exact Nat.lt_of_lt_of_le (val32_lt s.mem B kEv 2) (Nat.pow_le_pow_right (by decide) (by decide))
    exact (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 5 ≤ 6) bound).trans fullDivisor
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.code_ok (division_context (correction_workspace hv.old)))
    fun w ⟨_, Ow, Kw, computed⟩ => ?_)
  obtain result := computed (by rw [divisorV]; exact positive)
    (by
      rw [divisorV]
      exact Nat.lt_of_lt_of_le (val32_lt s.mem B kEv 2)
        (Nat.pow_le_pow_right (by decide) (by change 64 ≤ 128; decide)))
  rw [numeratorV, divisorV] at result
  have quotient := result.2
  change val32 w.mem B (arr 4 0) 4 = _ at quotient
  obtain quotientLow : val32 w.mem B (arr 4 0) 2 =
      (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) / val32 s.mem B kEv 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 2 ≤ 4) (by rw [quotient]; exact quotientFits)).trans quotient
  obtain changed : Outside B hdr 96 v.mem w.mem := division_frame Ow
  obtain hw := hv.keep Kw (changed.mono (Nat.zero_le _) (by unfold hdr; omega))
  obtain endSmall : arr 4 0 + 8 ≤ arr n aV := by unfold arr S aV hdr; omega
  refine WP.mono (widen_ok hw .exponent (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV)
    (.array .correction 0) width (h.arr_fit (by decide))
    (by change 168 ≤ Z; omega) (Or.inl endSmall)) fun t ⟨ht, Ot, _, value, Kt⟩ => ?_
  obtain scratch : Outs B correctionScratch s.mem w.mem :=
    (Ou.trans (correction_scratch_arr (by decide) Ov)).trans
      (correction_scratch_outside (Nat.le_refl _) (Nat.le_refl _) changed)
  refine ⟨ht, ?_, value.trans quotientLow,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kw.trans (Kt.mono (by decide))))⟩
  exact (scratch.mono (fun r hr => List.mem_append_left _ hr)).trans
    (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ExponentResultFrame.lean`, which only this module imported.
section

/-! # Result arithmetic preserves the already-computed inverse status -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges exponentTemps exponentArrays)

def exponentResultRanges (n : Nat) : List (Nat × Nat) :=
  (kProduct, 28) :: (hdr, 15 * S n) :: ranges n exponentArrays []

theorem exponent_result_frame {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (exponentResultRanges n) m m') : Outs B (exponentRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [exponentResultRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | array
  · exact ⟨(kOk, 68), by simp [exponentRanges, exponentTemps], by decide, by decide⟩
  · exact ⟨(hdr, 15 * S n), by simp [exponentRanges, exponentTemps], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨r, List.mem_append_right _ array, Nat.le_refl _, Nat.le_refl _⟩

theorem exponent_result_header {m m' : Mem} {B : Addr} {n d count : Nat}
    (bound : d + 4 * count ≤ kProduct) (O : Outs B (exponentResultRanges n) m m') :
    val32 m' B d count = val32 m B d count := by
  apply O.val32 _ (by unfold kProduct at bound; omega)
  intro r hr
  simp only [exponentResultRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | array
  · exact Or.inl bound
  · exact Or.inl (Nat.le_trans bound (by decide : kProduct ≤ hdr))
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at array
    obtain ⟨a, _, rfl⟩ := array
    obtain lower : hdr ≤ arr n a := Nat.le_add_right ..
    exact Or.inl (Nat.le_trans bound (Nat.le_trans (by decide : kProduct ≤ hdr) lower))

theorem exponent_result_slot {m m' : Mem} {B : Addr} {n d : Nat}
    (bound : d + 4 ≤ kProduct) (O : Outs B (exponentResultRanges n) m m') :
    slot m' B d = slot m B d := by
  obtain H := exponent_result_header (count := 1) bound O
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem exponent_result_complement {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outside B (arr n aDen) (S n) m m') : Outs B (exponentResultRanges n) m m' :=
  Outs.of_outside O (by simp [exponentResultRanges, ranges, exponentArrays])

theorem correction_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (unchanged : j ≠ aV) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (correctionRanges n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [correctionRanges, correctionScratch, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · have lower : hdr ≤ arr n j := Nat.le_add_right ..
    exact Or.inr (Nat.le_trans (by decide : kProduct + 28 ≤ hdr) lower)
  · have lower : 256 ≤ arr n 15 :=
      Nat.le_trans (by decide : 256 ≤ 160 + 15 * (4 * 2))
        (Nat.add_le_add_left (Nat.mul_le_mul_left 15 (Nat.mul_le_mul_left 4 (Nat.le_add_left 2 n))) 160)
    exact Or.inr (Nat.le_trans lower (arr_mono persistent))
  · have D := arr_disj (w := n) unchanged
    simp only at D ⊢
    unfold S at D ⊢
    omega

theorem exponent_result_correction {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (correctionRanges n) m m') : Outs B (exponentResultRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [correctionRanges, correctionScratch, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨(kProduct, 28), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], Nat.le_refl _, ?_⟩
    unfold S
    omega
  · exact ⟨(arr n aV, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, Nat.le_refl _⟩

theorem exponent_result_product {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (dProductRanges n) m m') : Outs B (exponentResultRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [dProductRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨(kProduct, 28), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], ?_, ?_⟩
    · unfold arr
      omega
    · unfold arr S
      omega
  · exact ⟨(arr n aD, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, by unfold S; omega⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/OddFinish.lean`, which only this module imported.
section

/-! # Finish the private exponent and recover the shared inverse result -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aD aDen aU aV kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (OddPrepared)

theorem dOddFinish_ok {s : State} {B : Addr} {Z n e L : Nat}
    (h : Ws s B Z n 32) (width : 2 ≤ n) (large : 3 ≤ e) (P : OddPrepared B n e L s) :
    WP isa dOddFinish s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentResultRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse e L = (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let x := num s.mem B 2 3
  obtain e64 : e < 2 ^ 64 := by rw [← P.exponent]; exact val32_lt _ _ _ _
  obtain Lbound : L < 2 ^ (32 * n) := by rw [← P.lcm]; exact val32_lt _ _ _ _
  obtain re : L % e < e := Nat.mod_lt _ (by omega)
  obtain QR : L = e * (L / e) + L % e := by
    obtain H := Nat.mod_add_div L e
    omega
  obtain Tbound : e - x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) e64
  unfold dOddFinish seqs
  refine WP.seq (WP.mono (complement_ok h width
    (by rw [P.exponent]; exact P.coefficient)) fun u ⟨hu, Ou, _, complement, Ku⟩ => ?_)
  rw [P.exponent] at complement
  change num u.mem B n aDen = e - x at complement
  obtain compFrame := exponent_result_complement Ou
  obtain Eu : val32 u.mem B kEv 2 = e := (exponent_result_header (by decide) compFrame).trans P.exponent
  obtain compKeep : Keep B n [aDen] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by omega) (by simp)
  obtain Qu : num u.mem B n aU = L / e :=
    (compKeep.num (by decide) (by simp) (h.fit64 (by decide))).trans P.quotient
  obtain Ru : num u.mem B n aV = L % e :=
    (compKeep.num (by decide) (by simp) (h.fit64 (by decide))).trans P.remainder
  obtain Rpair : val32 u.mem B (arr n aV) 2 = L % e :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width (by change num u.mem B n aV < 2 ^ 64; rw [Ru]; exact Nat.lt_trans re e64)).trans Ru
  obtain Tpair : val32 u.mem B (arr n aDen) 2 = e - x :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width (by change num u.mem B n aDen < 2 ^ 64; rw [complement]; exact Tbound)).trans complement
  refine WP.seq (WP.mono (correction_ok hu width (by rw [Eu]; omega)
    (by rw [Rpair, Tpair]; exact VG.Proof.RsaKeyGen.odd_numerator_fits e64 re)
    (by rw [Rpair, Tpair, Eu]; exact VG.Proof.RsaKeyGen.odd_correction_fits (by omega) e64 re))
    fun v ⟨hv, Ov, correction, Kv⟩ => ?_)
  rw [Rpair, Tpair, Eu] at correction
  obtain Qv : num v.mem B n aU = L / e :=
    (correction_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov).trans Qu
  obtain Tv : num v.mem B n aDen = e - x :=
    (correction_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov).trans complement
  obtain TpairV : val32 v.mem B (arr n aDen) 2 = e - x :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width (by change num v.mem B n aDen < 2 ^ 64; rw [Tv]; exact Tbound)).trans Tv
  obtain fits : num v.mem B n aU * val32 v.mem B (arr n aDen) 2 + num v.mem B n aV < 2 ^ (32 * n) := by
    rw [Qv, TpairV, correction]
    exact Nat.lt_of_le_of_lt (VG.Proof.RsaKeyGen.oddQuotient_le (by omega) QR) Lbound
  refine WP.mono (dProduct_ok hv width fits) fun t ⟨ht, Ot, product, Kt⟩ => ?_
  rw [Qv, TpairV, correction] at product
  have value : num t.mem B n aD = VG.Proof.RsaKeyGen.oddQuotient e (L / e) (L % e) x := product
  obtain frame := (compFrame.trans (exponent_result_correction Ov)).trans (exponent_result_product Ot)
  obtain mask : slot t.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0) := by
    rw [exponent_result_slot (by decide) frame, P.mask]
  refine ⟨ht, frame, ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  · rw [mask]
    split <;> omega
  · by_cases valid : 2 ≤ L ∧ Nat.gcd (L % e) e = 1
    · have congruence := P.congruence
      rw [valid.2] at congruence
      obtain inverse := VG.Proof.RsaKeyGen.oddQuotient_inverse large valid.1 QR congruence P.coefficient
      rw [mask, value]
      simpa only [valid, true_and, ite_true, Nat.one_ne_zero, ite_false] using inverse
    · have inverse := VG.Proof.RsaKeyGen.inverse_odd_none large QR valid
      rw [mask]
      simpa only [valid, ite_false, ite_true] using inverse

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DOdd.lean`, which only this module imported.
section

/-! # The native private exponent with a public odd exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aE aL aD aOne kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges)

theorem dOdd_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dOdd s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dOdd
  refine WP.seq (WP.mono (dOddPrepare_ok h width large odd loaded one)
    fun u ⟨hu, Ou, P, Ku⟩ => ?_)
  refine WP.mono (dOddFinish_ok hu width large P) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  exact ⟨ht, Ou.trans (OutsS.of_outs (exponent_result_frame Ot)), bit, inverse, Ku.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DSelect.lean`, which only this module imported.
section

/-! # Select the specified private inverse using only the public exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aD aE aL aOne kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges exponent_keep_frame)

theorem dSelect_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dSelect s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dSelect
  refine WP.seq (WP.mono (equalExponent_ok h 0) fun u ⟨hu, Mu, flag0, Ku⟩ => ?_)
  change isa.eval .e u = some (decide (val32 s.mem B kEv 2 = 0)) at flag0
  refine WP.ite _ flag0 (fun zero => ?_) (fun nonzero => ?_)
  · have E : val32 s.mem B kEv 2 = 0 := of_decide_eq_true zero
    refine WP.mono (dZero_ok hu) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
    refine ⟨ht, ?_, by rw [mask]; decide, ?_, (Ku.mono (by decide)).trans (Kt.mono (by decide))⟩
    · exact OutsS.of_outs (by simpa only [Mu] using exponent_keep_frame (by simp) (by decide) Ot)
    · rw [E, mask, VG.Proof.RsaKeyGen.inverse_zero]
      rfl
  · have E0 : val32 s.mem B kEv 2 ≠ 0 := of_decide_eq_false nonzero
    refine WP.seq (WP.mono (equalExponent_ok hu 1) fun v ⟨hv, Mv, flag1, Kv⟩ => ?_)
    obtain memoryV : v.mem = s.mem := Mv.trans Mu
    rw [Mu] at flag1
    change isa.eval .e v = some (decide (val32 s.mem B kEv 2 = 1)) at flag1
    refine WP.ite _ flag1 (fun unit => ?_) (fun nonunit => ?_)
    · have E : val32 s.mem B kEv 2 = 1 := of_decide_eq_true unit
      refine WP.mono (dOne_ok hv (by rw [memoryV]; exact one)) fun t ⟨ht, Ot, D, mask, Kt⟩ => ?_
      rw [memoryV] at mask
      refine ⟨ht, ?_, ?_, ?_, (Ku.mono (by decide)).trans
        ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
      · exact OutsS.of_outs (by simpa only [memoryV] using exponent_keep_frame (by decide) (by decide) Ot)
      · rw [mask]
        split <;> decide
      · rw [E, VG.Proof.RsaKeyGen.inverse_one, mask, D]
        by_cases L : num s.mem B n aL = 1 <;> simp [L]
    · have E1 : val32 s.mem B kEv 2 ≠ 1 := of_decide_eq_false nonunit
      refine WP.seq (WP.mono (parityExponent_ok hv) fun w ⟨hw, Mw, parity, Kw⟩ => ?_)
      obtain memoryW : w.mem = s.mem := Mw.trans memoryV
      rw [memoryV] at parity
      refine WP.ite _ parity (fun even => ?_) (fun odd => ?_)
      · refine WP.mono (dEven_ok hw (by rw [memoryW]; exact of_decide_eq_true even)
          (by rw [memoryW]; exact loaded)) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
        obtain spW : w.gpr .esp = s.gpr .esp := by
          rw [Kw.1 .esp (by decide), Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
        rw [memoryW, spW] at Ot
        rw [memoryW] at inverse
        exact ⟨ht, Ot, bit, inverse, (Ku.mono (by decide)).trans
          ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans Kt))⟩
      · have O : val32 s.mem B kEv 2 % 2 = 1 := by
          obtain H := of_decide_eq_false odd
          omega
        refine WP.mono (dOdd_ok hw width (by rw [memoryW]; omega)
          (by rw [memoryW]; exact O) (by rw [memoryW]; exact loaded)
          (by rw [memoryW]; exact one)) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
        obtain spW : w.gpr .esp = s.gpr .esp := by
          rw [Kw.1 .esp (by decide), Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
        rw [memoryW, spW] at Ot
        rw [memoryW] at inverse
        exact ⟨ht, Ot, bit, inverse, (Ku.mono (by decide)).trans
          ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans Kt))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

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
  obtain small : k ≤ n := by omega_using [width]
  obtain wide : 2 ≤ n := by omega_using [width, positive]
  obtain pBound : max (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  obtain qBound : min (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  unfold prepareLoaded seqs
  refine WP.seq (WP.mono (primes_ok h width positive even boundP boundQ zero one)
    fun u ⟨hu, Ou, P, Q, Pm, Qm, product, Ku⟩ => ?_)
  obtain oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  obtain frameU : Outs B (stageRanges n prepareArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  refine WP.seq (WP.mono (lcmPart_ok hu width positive
    (by rw [Pm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound) product oneU)
    fun v ⟨hv, Ov, L, Kv⟩ => ?_)
  rw [Pm, Qm] at L
  obtain spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  obtain spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), spU]
  obtain narrowFrame := OutsS.lift (fun _ _ => lcm_stage_frame small) Ov
  obtain Pv : num v.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans P
  obtain Qv : num v.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Q
  obtain Pmv : num v.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pm
  obtain Qmv : num v.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qm
  obtain frameV : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => stage_mono (by decide)) narrowFrame
  obtain prefixFrame := (OutsS.of_outs frameU).trans frameV
  obtain E : val32 v.mem B kEv 2 = val32 s.mem B kEv 2 := h.read_val32 (by decide) prefixFrame stage_preserves_e
  obtain loadedV : num v.mem B n aE = val32 v.mem B kEv 2 :=
    (h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans (loaded.trans E.symm)
  obtain oneV : num v.mem B n aOne = 1 :=
    (h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one
  refine WP.mono (dSelect_ok hv wide loadedV oneV) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  rw [E, L] at inverse
  obtain frameT : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) v.mem t.mem := by
    rw [← spV]
    exact OutsS.lift (fun _ _ => stage_mono (js := exponentArrays) (by decide)) Ot
  obtain frame := prefixFrame.trans frameT
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
