module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Mont.Words32
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentMarker
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassWord
import VerifiedGarbage.Proof.Mont.Halve32
import Init.Prelude
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGaps

/-! ### `RsaKeyGen.X86.Exponent`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.HalfPassLoop`, which only this module used -/

section

/-! # A single masked pass halves or retains the complete native exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem code_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * n ≤ size)
    (sep : src = out ∨ src + 4 * (n + 1) ≤ out ∨ out + 4 * n ≤ src)
    (top : w32 s.mem base (src + 4 * n) = 0)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (code n src out) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if choice then val32 s.mem base src n / 2 else val32 s.mem base src n) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  let P (j : Nat) (t : State) : Prop :=
    Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside base out (4 * j) s.mem t.mem ∧
    ∀ i < j, w32 t.mem base (out + 4 * i) =
      if choice then w32 s.mem base (src + 4 * i) / 2 +
        2 ^ 31 * (w32 s.mem base (src + 4 * i + 4) % 2) else w32 s.mem base (src + 4 * i)
  refine wordLoop_ok P positive (by have := scratch.size_lt; omega_using [srcFit, this])
    (fun j t u ⟨K, O, V⟩ ⟨M, rd, wr, regs⟩ =>
      ⟨⟨fun r hr => (regs r (by simp_all) (by simp_all)).trans (K.1 r hr), rd.trans K.2.1, wr.trans K.2.2⟩,
        M ▸ O, M ▸ V⟩)
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_
  · intro j hj t ⟨K, O, V⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine WP.mono (step_ok (choice := choice) St pointer (by omega_using [srcFit, hj]) (by omega_using [outFit, hj]) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Ku⟩ => ?_
    have sameLo : w32 t.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      O.w32 (by rcases sep with h | h | h <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
    have sameHi : w32 t.mem base (src + 4 * j + 4) = w32 s.mem base (src + 4 * j + 4) :=
      O.w32 (by rcases sep with h | h | h <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
    refine ⟨⟨K.widen Ku, (O.mono (by omega_using []) (by omega_using [])).trans (Ou.mono (by omega_using []) (by omega_using [])), ?_⟩,
      Ku.1 .ebp (by decide), Ku.1 .edi (by decide)⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega_using [before]) (by have := scratch.nowrap; omega_using [outFit, hj, hi, this])]
      exact V i before
    · rw [value, sameLo, sameHi]
  · intro t ⟨K, O, V⟩
    refine ⟨O, ?_, K⟩
    cases choice
    · exact val32_congr_at s.mem t.mem base n src out V
    · apply val32_halve_at s.mem t.mem base n src out
      intro i hi
      rw [V i hi, show src + 4 * i + 4 = src + 4 * (i + 1) by omega_using []]
      by_cases last : i + 1 = n
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

end VG.Proof.RsaKeyGen.X86.HalfPass

end

end

/-! # Complete native exponent and alignment-marker preparation -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentClear.lean`, which only this module imported.
section

/-! # Zero top sentinels supply the incoming bits for fixed masked halving -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem clearTops_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (.block (clearTops n src out)) s fun t =>
      w32 t.mem base (src + 4 * n) = 0 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      t.gpr .ecx = cmask true ∧
      Outs base [(src + 4 * n, 4), (out + 4 * n, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold clearTops
  refine wp_movS rfl fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun b B => ?_
  have Kb : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (by omega)) fun c C => wp_movS rfl fun t T _ => WP.block_nil ?_
  have Mb : b.mem = s.mem.writeW (off base (src + 4 * n)) (0#32) := by
    rw [B.mem, A.mem, A.gpr]
    rfl
  have Mc : c.mem = b.mem.writeW (off base (out + 4 * n)) (0#32) := by
    rw [C.mem, (B.keeps []).1 .eax (by decide), A.gpr]
    rfl
  have Os : Outside base (src + 4 * n) 4 s.mem b.mem := by
    rw [Mb]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have Oo : Outside base (out + 4 * n) 4 b.mem c.mem := by
    rw [Mc]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  refine ⟨?_, ?_, T.gpr, ?_, ((Kb.mono (by decide : ∀ r : Reg, r ∈ [.eax] → r ∈ [.eax, .ecx])).widen (C.keeps [])).widen T.keeps⟩
  · rw [T.mem, Oo.w32 (by omega) (by have := scratch.nowrap; omega), Mb, w32_write_self]
    rfl
  · rw [T.mem, Mc, w32_write_self]
    rfl
  · rw [T.mem]
    exact (Outs.of_outside Os (List.mem_cons_self ..)).trans
      (Outs.of_outside Oo (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFirst.lean`, which only this module imported.
section

/-! # The first native pass copies c/2 into the exponent and retains its zero sentinel -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def firstRanges (n src out : Nat) : List (Nat × Nat) :=
  [(src + 4 * n, 4), (out + 4 * n, 4), (out, 4 * n)]

theorem firstPass_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (firstPass n src out) s fun t =>
      val32 t.mem base out n = val32 s.mem base src n / 2 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      Outs base (firstRanges n src out) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (clearTops_ok scratch srcFit outFit sep) fun a ⟨srcTop, outTop, mask, Oa, Ka⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps Ka (by decide)) positive srcFit (by omega)
    (Or.inr (Or.inl sep)) srcTop mask) fun t ⟨Ot, V, Kt⟩ => ?_
  have before : val32 a.mem base src n = val32 s.mem base src n :=
    Oa.val32 (fun r mem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> left <;> omega) (by have := scratch.nowrap; omega)
  refine ⟨by rw [before] at V; exact V, ?_, ?_, (Ka.mono (by decide)).widen Kt⟩
  · rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by have := scratch.nowrap; omega)]
    exact outTop
  · exact (Oa.mono (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl <;> simp)).trans
      (Outs.of_outside Ot (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShift.lean`, which only this module imported.
section

/-! # An alignment pass halves exactly when sigma exceeds its public index -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem halfIf_ok {s : State} {base : Addr} {size n marker out j k : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : out + 4 * (n + 1) ≤ size) (markerFit : marker + 8 ≤ size)
    (top : w32 s.mem base (out + 4 * n) = 0) (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3)
    (value : word s.mem base marker = BitVec.twoPow 64 k) :
    WP isa (halfIf n marker out j) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (SigMask.code_sig scratch markerFit index choice value) fun a ⟨mask, M, K⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps K (by decide)) positive fit (by omega) (Or.inl rfl)
    (by rw [M]; exact top) mask) fun t ⟨O, V, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, by simpa only [decide_eq_true_eq] using V, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftContext.lean`, which only this module imported.
section

/-! # Alignment marker and top sentinel remain available across all three passes -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

structure Context (base : Addr) (size n marker out k : Nat) (s : State) : Prop where
  scratch : Scr s base size
  positive : 0 < n
  fit : out + 4 * (n + 1) ≤ size
  markerFit : marker + 8 ≤ size
  apart : marker + 8 ≤ out
  index : k < 64
  value : word s.mem base marker = BitVec.twoPow 64 k
  top : w32 s.mem base (out + 4 * n) = 0

theorem halfIf_context {s : State} {base : Addr} {size n marker out j k : Nat}
    (C : Context base size n marker out k s) (choice : 1 ≤ j ∧ j ≤ 3) :
    WP isa (halfIf n marker out j) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (halfIf_ok C.scratch C.positive C.fit C.markerFit C.top C.index choice C.value)
    fun t ⟨O, V, K⟩ => ?_
  refine ⟨⟨C.scratch.of_keeps K (by decide), C.positive, C.fit, C.markerFit, C.apart, C.index, ?_, ?_⟩, O, V, K⟩
  · rw [O.word (Or.inl C.apart) (by have := C.scratch.nowrap; have := C.markerFit; omega)]
    exact C.value
  · rw [O.w32 (Or.inr (Nat.le_refl _)) (by have := C.scratch.nowrap; have := C.fit; omega)]
    exact C.top

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftPasses.lean`, which only this module imported.
section

/-! # The three masked native passes produce the reviewed exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem passes_ok {s : State} {base : Addr} {size n marker out k : Nat}
    (C : Context base size n marker out k s) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n =
        (let x := val32 s.mem base out n
         let x1 := if 1 < VG.Proof.RsaKeyGen.sigOf k then x / 2 else x
         let x2 := if 2 < VG.Proof.RsaKeyGen.sigOf k then x1 / 2 else x1
         if 3 < VG.Proof.RsaKeyGen.sigOf k then x2 / 2 else x2) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (halfIf_context C (j := 1) (by decide)) fun a ⟨A, Oa, Va, Ka⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_context A (j := 2) (by decide)) fun b ⟨B, Ob, Vb, Kb⟩ => ?_)
  refine WP.mono (halfIf_context B (j := 3) (by decide)) fun t ⟨T, Ot, Vt, Kt⟩ => ?_
  exact ⟨T, (Oa.trans Ob).trans Ot, by rw [Vt, Vb, Va], (Ka.trans Kb).trans Kt⟩

theorem passes_exponent {s : State} {base : Addr} {size n marker out c : Nat}
    (C : Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) s)
    (odd : c % 2 = 1) (value : val32 s.mem base out n = c / 2) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) t ∧
      Outside base out (4 * n) s.mem t.mem ∧ val32 t.mem base out n = Proof.MillerRabin.Round.exponent c ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (passes_ok C) fun t ⟨T, O, V, K⟩ => ?_
  rw [value, VG.Proof.RsaKeyGen.sigOf_mod] at V
  exact ⟨T, O, V.trans (VG.Proof.RsaKeyGen.mrE_halves odd), K⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFinish.lean`, which only this module imported.
section

/-! # Store the complete paired alignment marker after the prepared exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem finish_ok {s : State} {base : Addr} {size n out : Nat} (scratch : Scr s base size)
    (markerFit : markerOffset + 8 ≤ size) (outFit : out + 4 * n + 8 ≤ size) :
    WP isa (.block (finish n out)) s fun t =>
      word t.mem base (out + 4 * n) = word s.mem base markerOffset ∧
      Outside base (out + 4 * n) 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) outFit) fun t ⟨M, O, Kt⟩ => ?_
  have pair : b.gpr .edx ++ b.gpr .eax = word s.mem base markerOffset := by
    rw [B.gpr, B.other .eax (by decide), A.gpr, A.mem,
      VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [VG.Proof.Mont.word, M, Mem.readW_writeW_self64, pair]
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def ranges (w src out : Nat) : List (Nat × Nat) := [(markerOffset, 8), (src + 8 * w, 4), (out, 8 * w + 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w minusOne src out c : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (minusFit : minusOne + 8 * w ≤ size) (srcFit : src + 8 * w + 4 ≤ size)
    (outFit : out + 8 * w + 8 ≤ size) (lo : markerOffset + 8 ≤ src) (sep : src + 8 * w + 4 ≤ out)
    (candidate : val32 s.mem base src (2 * w) = c)
    (minusValue : val32 s.mem base minusOne (2 * w) = c - 1) (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (code w minusOne src out) s fun t =>
      val32 t.mem base out (2 * w) = Proof.MillerRabin.Round.exponent c ∧
      word t.mem base (out + 8 * w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs base (ranges w src out) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.seq (WP.mono (ExponentMarker.code_ok scratch minusFit minusValue (by omega_using [large]))
    fun a ⟨marker, Ma, Ka⟩ => ?_)
  have Sa := scratch.of_keeps Ka (by decide)
  have markerFit : markerOffset + 8 ≤ size := by omega_using [srcFit, lo]
  refine WP.seq (WP.mono (Header.storePair_ok Sa markerFit) fun b ⟨Mb, Ob, Kb⟩ => ?_)
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  have Sb := scratch.of_keeps Ksb (by unfold clob; decide)
  have candidateB : val32 b.mem base src (2 * w) = c := by
    rw [Ob.val32 (Or.inr lo) (by have := scratch.nowrap; omega_using [srcFit, this]), Ma]
    exact candidate
  have markerB : word b.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [VG.Proof.Mont.word, Mb, Mem.readW_writeW_self64, marker]
  refine WP.seq (WP.mono (firstPass_ok Sb (by omega_using [positive]) (by omega_using [srcFit]) (by omega_using [outFit]) (by omega_using [sep]))
    fun d ⟨valueD, topD, Od, Kd⟩ => ?_)
  have Ksd : Keeps clob s d := Ksb.widen Kd
  have Sd := scratch.of_keeps Ksd (by unfold clob; decide)
  have markerD : word d.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [Od.word (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> left <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, lo, this])]
    exact markerB
  have C : ExponentShift.Context base size (2 * w) markerOffset out
      ((Spec.Rsa.splitTwos (c - 1)).1 % 64) d :=
    ⟨Sd, by omega_using [positive], by omega_using [outFit], markerFit, by omega_using [lo, sep], Nat.mod_lt _ (by decide), markerD, topD⟩
  have valueD' : val32 d.mem base out (2 * w) = c / 2 := by rw [valueD, candidateB]
  refine WP.seq (WP.mono (ExponentShift.passes_exponent C odd valueD') fun e ⟨Ce, Oe, Ve, Ke⟩ => ?_)
  refine WP.mono (finish_ok Ce.scratch markerFit (by omega_using [outFit])) fun t ⟨markerT, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (Ksd.widen Ke).widen Kt⟩
  · rw [Ot.val32 (Or.inl (by omega_using [])) (by have := scratch.nowrap; omega_using [outFit, this])]
    exact Ve
  · have : out + 4 * (2 * w) = out + 8 * w := by omega_using []
    rw [this] at markerT
    exact markerT.trans Ce.value
  · have Fsb : Outs base (ranges w src out) s.mem b.mem := by
      rw [← Ma]
      exact Outs.of_outside Ob (List.mem_cons_self ..)
    have Fd : Outs base (ranges w src out) b.mem d.mem := Od.cover (by
      intro r mem
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact ⟨(src + 8 * w, 4), by simp [ranges], by omega_using [], by omega_using []⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega_using [], by omega_using []⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega_using [], by omega_using []⟩)
    have Fe : Outs base (ranges w src out) d.mem e.mem :=
      Outs.of_outside (Oe.mono (by omega_using []) (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have Ft : Outs base (ranges w src out) e.mem t.mem :=
      Outs.of_outside (Ot.mono (by omega_using []) (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    exact ((Fsb.trans Fd).trans Fe).trans Ft

end VG.Proof.RsaKeyGen.X86.Exponent

end

end


/-! # Preparing the exponent retains the prepared Montgomery context and constants -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def preparedRanges (g : Geometry) : List (Nat × Nat) := ranges g.w (g.array 0) (g.array 27)

theorem prepared_preserve {g : Geometry} (v : g.Valid) {s t : Mem} (O : Outs g.W (preparedRanges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 5 ∨ j = 9 ∨ j = 10) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply O.val32
  · intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl | rfl <;> rcases mem with rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_using []
  · have bound := v.maxWidth
    rcases index with rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [bound]

/-- `Ready` kept by writes to the exponent's ranges. -/
theorem ready_keep {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (O : Outs g.W (preparedRanges g) s.mem t.mem) (K : Keeps clob s t) :
    Ready g c capacity p t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  have fits : ∀ r ∈ preparedRanges g, r.1 + r.2 ≤ g.L := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith
  have metadata : ∀ r ∈ preparedRanges g, (128 ≤ r.1 ∧ r.1 + r.2 ≤ 224) ∨ 256 ≤ r.1 := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · left; decide
    · right; have := v.arrayHeader 0; omega
    · right; exact v.arrayHeader 27
  have F := WorkspaceFrame.of_outs S.scratch.nowrap O
  refine ⟨Prepared.keepGaps v S.context K (by unfold clob; decide) O metadata,
    S.modulus.keep v F (fun r mem => by have := metadata r mem; omega_using [this]) ?_,
    S.caller.keepOuts K (by unfold clob; decide) O fits,
    S.scratch.of_keeps K (by unfold clob; decide)⟩
  intro r mem
  simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
  have top := v.arrayHeader 0
  have before := g.arrayBefore (i := 0) (j := 27) (by decide)
  rcases mem with rfl | rfl | rfl
  · right; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [top]
  · left; unfold Geometry.words; omega_using []
  · left; exact before

theorem ready_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1)
    (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.Exponent.code g.w (g.array 5) (g.array 0) (g.array 27)) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c ∧
      word t.mem g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps clob s t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have apart := Prepared.paddedBefore g (i := 0) (j := 27) (by decide)
  have head := v.headerFit
  refine WP.mono (code_ok S.scratch (by have := v.minWidth; omega_using [this])
    (by have := v.arrayFit (j := 5) (by decide); unfold Geometry.words at this; omega_using [this])
    (by omega_using [srcFit]) (by omega_using [outFit]) (by have := v.arrayHeader 0; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [this])
    (by omega_using [apart]) S.modulus.candidate minusOne odd large) fun t ⟨E, marker, O, K⟩ => ?_
  exact ⟨ready_keep v S O K, E, marker, O, K⟩

end VG.Proof.RsaKeyGen.X86.Exponent
