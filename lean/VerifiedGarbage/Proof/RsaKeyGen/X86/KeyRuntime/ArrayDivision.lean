module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
import VerifiedGarbage.Proof.Mont.RangeCover
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
public import VerifiedGarbage.Proof.Rsa.X86.DivContext

/-! ### `RsaKeyGen.X86.KeyDivisionGeometry`, which this module and modules that import it used -/

section

/-! # The four-array native RSA division bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys

def divisionGeometry (B : Addr) (Z n : Nat) : VG.Proof.Rsa.X86.Div.Geometry :=
  { base := B, size := Z, n := n, offsets := fun i => arr n i.val }

theorem division_context {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 4) :
    VG.Proof.Rsa.X86.Div.Context (divisionGeometry B Z n) s := by
  refine ⟨h.workspace, h.wpos, by have := h.wle; change n < 2 ^ 24; omega_using [this], ?_, ?_⟩
  · intro i
    have fit := h.arr_fit i.isLt
    change arr n i.val + 4 * (if i = 0 then n else n + 1) ≤ Z
    unfold S at fit
    split <;> omega_using [fit]
  · intro i j ne
    have indices : i.val ≠ j.val := fun e => ne (Fin.ext e)
    have disj := arr_disj (w := n) indices
    change arr n i.val + 4 * (if i = 0 then n else n + 1) ≤ arr n j.val ∨
      arr n j.val + 4 * (if j = 0 then n else n + 1) ≤ arr n i.val
    unfold S at disj
    split <;> split <;> omega_using [disj]

theorem division_frame {m m' : Mem} {B : Addr} {Z n : Nat}
    (O : Outs B (divisionGeometry B Z n).ranges m m') :
    Outside B VG.Impl.Rsa.X86.Keys.hdr (4 * (4 * (n + 2))) m m' := by
  intro x hx
  apply O x
  intro r hr
  simp only [VG.Proof.Rsa.X86.Div.Geometry.ranges, divisionGeometry,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  all_goals simp only [arr, S] at hx ⊢
  all_goals omega_using [hx]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyDivisionStore`, which only this module used -/

section

/-! # Export native division results to persistent workspace arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure DivisionOutputs (Z n quotient remainder : Nat) : Prop where
  quotient_bound : quotient + 4 * n ≤ Z
  remainder_bound : remainder + 4 * n ≤ Z
  quotient_outside : quotient + 4 * n ≤ hdr ∨ arr n 4 ≤ quotient
  remainder_outside : remainder + 4 * n ≤ hdr ∨ arr n 4 ≤ remainder
  separate : quotient + 4 * n ≤ remainder ∨ remainder + 4 * n ≤ quotient

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyDivisionLoad`, which this module and modules that import it used -/

section

/-! # Load the native division bank without clearing its temporary arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure DivisionInputs (Z n src divisor : Nat) : Prop where
  source_bound : src + 4 * n ≤ Z
  divisor_bound : divisor + 4 * n ≤ Z
  source_outside : src + 4 * n ≤ hdr ∨ arr n 4 ≤ src
  divisor_outside : divisor + 4 * n ≤ hdr ∨ arr n 4 ≤ divisor

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.DivisionLoad`, which only this module used -/

section

/-! # Load the shared division bank at the public runtime width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ClearTop.lean`, which only this module imported.
section

/-! # The division bank's extra divisor word is explicitly zero -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem clearTop_ok {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N)
    (w : Width) (fit : Loc.offset n (.array w j) + 4 * w.words n + 4 ≤ Z) :
    WP isa (clearTop w j) s fun t => Ws t B Z n N ∧
      Outside B (Loc.offset n (.array w j) + 4 * w.words n) 4 s.mem t.mem ∧
      w32 t.mem B (Loc.offset n (.array w j) + 4 * w.words n) = 0 ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold clearTop
  simp only [List.append_assoc]
  refine h.ptr_ok (.array w j) (by decide) (by decide) (by omega) fun a K1 m1 P1 => ?_
  have ha := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine ha.bytes_ok w .edx fun b K2 m2 count => ?_
  refine wp_addS rfl fun c C _ => wp_movS rfl fun d U _ => ?_
  have K : Keeps [.eax, .edx, .ebp] s d :=
    ((K1.mono (by decide)).trans (K2.mono (by decide))).trans
      ((C.keeps.mono (by decide)).trans (U.keeps.mono (by decide)))
  have hw := h.full.rt.of_keeps K
  have P2 : PtrAt b B .ebp (Loc.offset n (.array w j)) := by
    rw [PtrAt, K2.1 _ (by decide)]; exact P1
  have P : PtrAt d B .ebp (Loc.offset n (.array w j) + 4 * w.words n) := by
    rw [PtrAt, U.other _ (by decide), C.gpr, VG.Proof.Mont.X86.Rt.ptr_add P2, count]
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hw P (d := 0) (by omega))
    (VG.Proof.Mont.X86.Rt.ws_write hw (y := Loc.offset n (.array w j) + 4 * w.words n + 0)
      (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have memory : t.mem = s.mem.writeW (off B (Loc.offset n (.array w j) + 4 * w.words n)) (0#32) := by
    rw [T.mem, U.mem, C.mem, m2, m1, U.gpr, Nat.add_zero]
    rfl
  have O : Outside B (Loc.offset n (.array w j) + 4 * w.words n) 4 s.mem t.mem := by
    rw [memory]; exact writeW32_outside _ _ _ (by omega)
  have allK := K.trans (T.keeps _)
  refine ⟨h.keep allK (O.mono (Nat.zero_le _) (by omega)), O, ?_, allK⟩
  rw [memory, w32_write_self]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num arr S)
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs)

theorem divisionLoad_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src divisor : Loc}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (L : DivisionInputs Z (w.words n) (src.offset n) (divisor.offset n)) :
    WP isa (divisionLoad w src divisor) s fun t =>
      Ws t B Z n N ∧ Outside B hdr (4 * (4 * (w.words n + 2))) s.mem t.mem ∧
      num t.mem B (w.words n) 0 = val32 s.mem B (src.offset n) (w.words n) ∧
      num t.mem B (w.words n) 2 = val32 s.mem B (divisor.offset n) (w.words n) ∧
      w32 t.mem B (arr (w.words n) 2 + 4 * w.words n) = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have H := shrinkRt (h.runtime hw) bound
  have hn := h.old.workspace.nowrap
  have f0 := H.ws.arr_fit (j := 0) (by decide)
  have f2 := H.ws.arr_fit (j := 2) (by decide)
  rw [kw_words h.width] at f0 f2
  have srcBound := L.source_bound
  have divBound := L.divisor_bound
  have srcSep := L.source_outside
  have divSep := L.divisor_outside
  have sepSource : (Loc.array w 0).offset n + 4 * w.words n ≤ src.offset n ∨
      src.offset n + 4 * w.words n ≤ (Loc.array w 0).offset n := by
    simp only [offset_array, arr, S] at *
    omega_using [srcSep]
  have sepDivisor : (Loc.array w 2).offset n + 4 * w.words n ≤ divisor.offset n ∨
      divisor.offset n + 4 * w.words n ≤ (Loc.array w 2).offset n := by
    simp only [offset_array, arr, S] at *
    omega_using [divSep]
  unfold divisionLoad VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clearTop_ok h w (j := 2)
    (by rw [offset_array]; unfold S at f2; omega_using [f2])) fun u ⟨hu, Ou, topU, Ku⟩ => ?_)
  rw [offset_array] at Ou topU
  have uFrame : Outside B hdr (4 * (4 * (w.words n + 2))) s.mem u.mem :=
    Ou.mono (by unfold arr; omega_using []) (by unfold arr S; omega_using [])
  have source : val32 u.mem B (src.offset n) (w.words n) =
      val32 s.mem B (src.offset n) (w.words n) :=
    uFrame.val32 (by simp only [arr, S] at srcSep; omega_using [srcSep]) (by omega_using [hn, srcBound])
  refine WP.seq (WP.mono (copy_loc_ok hu w (.array w 0) src
    (by rw [offset_array]; unfold S at f0; omega_using [f0]) srcBound sepSource)
    fun v ⟨hv, Ov, input, Kv⟩ => ?_)
  rw [offset_array] at Ov input
  change num v.mem B (w.words n) 0 = val32 u.mem B (src.offset n) (w.words n) at input
  have vFrame : Outside B hdr (4 * (4 * (w.words n + 2))) s.mem v.mem :=
    uFrame.trans (Ov.mono (by unfold arr; omega_using []) (by unfold arr S; omega_using []))
  have topV : w32 v.mem B (arr (w.words n) 2 + 4 * w.words n) = 0 := by
    rw [Ov.w32 (by unfold arr S; omega_using []) (by unfold S at f2; omega_using [hn, f2]), topU]
  have modulus : val32 v.mem B (divisor.offset n) (w.words n) =
      val32 s.mem B (divisor.offset n) (w.words n) :=
    vFrame.val32 (by simp only [arr, S] at divSep; omega_using [divSep]) (by omega_using [hn, divBound])
  refine WP.mono (copy_loc_ok hv w (.array w 2) divisor
    (by rw [offset_array]; unfold S at f2; omega_using [f2]) divBound sepDivisor)
    fun t ⟨ht, Ot, valueD, Kt⟩ => ?_
  rw [offset_array] at Ot valueD
  change num t.mem B (w.words n) 2 = val32 v.mem B (divisor.offset n) (w.words n) at valueD
  have topT : w32 t.mem B (arr (w.words n) 2 + 4 * w.words n) = 0 := by
    rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by unfold S at f2; omega_using [hn, f2]), topV]
  refine ⟨ht, vFrame.trans (Ot.mono (by unfold arr; omega_using []) (by unfold arr S; omega_using [])),
    ?_, valueD.trans modulus, topT, (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  change val32 t.mem B (arr (w.words n) 0) (w.words n) = _
  rw [Ot.val32 (by unfold arr S; omega_using []) (by unfold S at f0; omega_using [hn, f0])]
  exact input.trans source

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.DivisionStore`, which only this module used -/

section

/-! # The shared division bank exports quotient and remainder through one copy loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num arr S)
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionOutputs)

theorem divisionStore_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {quotient remainder : Loc}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (L : DivisionOutputs Z (w.words n) (quotient.offset n) (remainder.offset n)) :
    WP isa (divisionStore w quotient remainder) s fun t =>
      Ws t B Z n N ∧ Outs B [(quotient.offset n, 4 * w.words n),
        (remainder.offset n, 4 * w.words n)] s.mem t.mem ∧
      val32 t.mem B (quotient.offset n) (w.words n) = num s.mem B (w.words n) 0 ∧
      val32 t.mem B (remainder.offset n) (w.words n) = num s.mem B (w.words n) 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have H := shrinkRt (h.runtime hw) bound
  have hn := h.old.workspace.nowrap
  have f0 := H.ws.arr_fit (j := 0) (by decide)
  have f1 := H.ws.arr_fit (j := 1) (by decide)
  rw [kw_words h.width] at f0 f1
  have qBound := L.quotient_bound
  have rBound := L.remainder_bound
  have qSep := L.quotient_outside
  have rSep := L.remainder_outside
  have sep := L.separate
  have sepQ : quotient.offset n + 4 * w.words n ≤ (Loc.array w 0).offset n ∨
      (Loc.array w 0).offset n + 4 * w.words n ≤ quotient.offset n := by
    simp only [offset_array, arr, S] at *
    omega_using [qSep]
  have sepR : remainder.offset n + 4 * w.words n ≤ (Loc.array w 1).offset n ∨
      (Loc.array w 1).offset n + 4 * w.words n ≤ remainder.offset n := by
    simp only [offset_array, arr, S] at *
    omega_using [rSep]
  unfold divisionStore
  refine WP.seq (WP.mono (copy_loc_ok h w quotient (.array w 0) qBound
    (by rw [offset_array]; unfold S at f0; omega_using [f0]) sepQ) fun u ⟨hu, Ou, Q, Ku⟩ => ?_)
  rw [offset_array] at Q
  have R : val32 u.mem B (Loc.array w 1 |>.offset n) (w.words n) = num s.mem B (w.words n) 1 := by
    rw [offset_array]
    exact Ou.val32 (by simp only [arr, S] at qSep; unfold arr S; omega_using [qSep])
      (by unfold S at f1; omega_using [hn, f1])
  refine WP.mono (copy_loc_ok hu w remainder (.array w 1) rBound
    (by rw [offset_array]; unfold S at f1; omega_using [f1]) sepR) fun t ⟨ht, Ot, V, Kt⟩ => ?_
  refine ⟨ht, (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp)),
    ?_, V.trans R, Ku.trans Kt⟩
  rw [Ot.val32 sep (by omega_using [hn, qBound])]
  exact Q

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Divide persistent arrays in the full native RSA workspace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Divide.lean`, which only this module imported.
section

/-! # The runtime division kernel is shared with RSA key checking -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Impl.Rsa.X86.KeyRt (sCy sQb)

theorem divide_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (top : w32 s.mem B (arr (w.words n) 2 + 4 * w.words n) = 0) :
    WP isa (divide w) s fun t => Ws t B Z n N ∧
      Keep B (w.words n) [0, 1, 3] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      (0 < num s.mem B (w.words n) 2 →
        num t.mem B (w.words n) 0 = num s.mem B (w.words n) 0 / num s.mem B (w.words n) 2 ∧
        num t.mem B (w.words n) 1 = num s.mem B (w.words n) 0 % num s.mem B (w.words n) 2) := by
  have code : divide w = VG.Impl.Rsa.X86.KeyRt.div w.lay 0 1 2 3 := by
    cases w <;> simp_all [divide]
  rw [code]
  have H := shrinkRt (h.runtime hw) bound
  have core := VG.Proof.Rsa.X86.KeyRt.div_ok H
    (by decide : 0 < 4) (by decide : 1 < 4) (by decide : 2 < 4) (by decide : 3 < 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa only [kw_words h.width] using top)
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, O, K, V⟩ => ⟨h.afterBank hw K O ?_ (by decide), O, K, V⟩
  intro j hj
  have small := (by decide : ∀ j ∈ ([0, 1, 3] : List Nat), j < 4) j hj
  omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Division.lean`, which only this module imported.
section

/-! # Quotient and remainder share the runtime RSA division kernel

Division uses four arrays of the shared temporary bank. Its frame also
includes the two saved division bits.
-/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.Rsa.X86.KeyRt (sCy sQb)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs DivisionOutputs inverseRanges
  inverse_frame inverse_frame_clear)

def divisionRanges (d q r : Nat) : List (Nat × Nat) :=
  [(hdr, 4 * (4 * (d + 2))), (sCy, 4), (sQb, 4), (q, 4 * d), (r, 4 * d)]

theorem divisionFrom_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    {src divisor quotient remainder : Loc} (h : Ws s B Z n N) (bound : 4 ≤ N)
    (hw : w ≠ .correction)
    (input : DivisionInputs Z (w.words n) (src.offset n) (divisor.offset n))
    (output : DivisionOutputs Z (w.words n) (quotient.offset n) (remainder.offset n))
    (positive : 0 < val32 s.mem B (divisor.offset n) (w.words n)) :
    WP isa (divisionFrom w src divisor quotient remainder) s fun t =>
      Ws t B Z n N ∧ Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
        s.mem t.mem ∧
      val32 t.mem B (quotient.offset n) (w.words n) =
        val32 s.mem B (src.offset n) (w.words n) / val32 s.mem B (divisor.offset n) (w.words n) ∧
      val32 t.mem B (remainder.offset n) (w.words n) =
        val32 s.mem B (src.offset n) (w.words n) % val32 s.mem B (divisor.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold divisionFrom
  refine WP.seq (WP.mono (divisionLoad_ok h bound hw input)
    fun u ⟨hu, Ou, numerator, modulus, top, Ku⟩ => ?_)
  refine WP.seq (WP.mono (divide_ok hu bound hw top) fun v ⟨hv, Ov, Kv, computed⟩ => ?_)
  have result := computed (by rw [modulus]; exact positive)
  rw [numerator, modulus] at result
  refine WP.mono (divisionStore_ok hv bound hw output) fun t ⟨ht, Ot, Q, R, Kt⟩ => ?_
  refine ⟨ht, ?_, Q.trans result.1, R.trans result.2,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  have first : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      s.mem u.mem := Outs.of_outside Ou (List.mem_cons_self ..)
  have middle : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      u.mem v.mem := Ov.cover (by
    intro region member
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map] at member
    rcases member with ⟨j, hj, rfl⟩ | ⟨slot, hs, rfl⟩
    · refine ⟨(hdr, 4 * (4 * (w.words n + 2))), List.mem_cons_self .., Nat.le_add_right .., ?_⟩
      have small : j < 4 := by
        have bounds := (by decide : ∀ j ∈ ([0, 1, 3] : List Nat), j < 4) j hj
        exact bounds
      have last := VG.Proof.Rsa.X86.Keys.arr_end (w := w.words n) small
      simpa only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
        Nat.mul_assoc, Nat.mul_left_comm] using last
    · refine ⟨(slot, 4), ?_, Nat.le_refl _, Nat.le_refl _⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [divisionRanges])
  have last : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      v.mem t.mem := Ot.mono (by
    intro region member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs DivisionOutputs)

def arrayDivisionRanges (n q r : Nat) : List (Nat × Nat) :=
  [(VG.Impl.Rsa.X86.Keys.hdr, 4 * S n), (136, 4), (140, 4),
    (arr n q, 4 * n), (arr n r, 4 * n)]

theorem arrayDivision_ok {s : State} {B : Addr} {Z n a d q r : Nat} (h : Ws s B Z n 32)
    (ha : a < 32) (hd : d < 32) (hq : q < 32) (hr : r < 32)
    (pa : 4 ≤ a) (pd : 4 ≤ d) (pq : 4 ≤ q) (pr : 4 ≤ r) (qr : q ≠ r)
    (positive : 0 < num s.mem B n d) :
    WP isa (divFull a d q r) s fun t =>
      Ws t B Z n 32 ∧ Outs B (arrayDivisionRanges n q r) s.mem t.mem ∧
      num t.mem B n q = num s.mem B n a / num s.mem B n d ∧
      num t.mem B n r = num s.mem B n a % num s.mem B n d ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fa := h.arr_fit ha
  have fd := h.arr_fit hd
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have input : DivisionInputs Z n (arr n a) (arr n d) := by
    refine ⟨?_, ?_, Or.inr (arr_mono pa), Or.inr (arr_mono pd)⟩
    · unfold S at fa
      omega_using [fa]
    · unfold S at fd
      omega_using [fd]
  have output : DivisionOutputs Z n (arr n q) (arr n r) := by
    refine ⟨?_, ?_, Or.inr (arr_mono pq), Or.inr (arr_mono pr), ?_⟩
    · unfold S at fq
      omega_using [fq]
    · unfold S at fr
      omega_using [fr]
    · have disj := arr_disj (w := n) qr
      unfold S at disj
      omega_using [disj]
  refine WP.mono (divisionFrom_ok h (by decide) (by decide)
    (show DivisionInputs Z (Width.modulus.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr a).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr d).offset n) from input)
    (show DivisionOutputs Z (Width.modulus.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr q).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr r).offset n) from output) positive)
    fun t ⟨ht, O, Q, R, K⟩ => ?_
  exact ⟨ht, by simpa only [arrayDivisionRanges, divisionRanges, Width.words,
    VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, S,
    VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb, Nat.mul_assoc] using O,
    Q, R, K.mono (by decide)⟩

theorem arrayDivision_preserves_num {m m' : Mem} {B : Addr} {n q r j : Nat}
    (persistent : 4 ≤ j) (jq : j ≠ q) (jr : j ≠ r) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (arrayDivisionRanges n q r) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega_using [fit])
  intro region mem
  simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (arr_mono persistent)
  · exact Or.inr (Nat.le_trans (by decide : 136 + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (Nat.le_add_right ..))
  · exact Or.inr (Nat.le_trans (by decide : 140 + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (Nat.le_add_right ..))
  · have D := arr_disj (w := n) jq
    simp only at D ⊢
    unfold S at D
    omega_using [D]
  · have D := arr_disj (w := n) jr
    simp only at D ⊢
    unfold S at D
    omega_using [D]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
