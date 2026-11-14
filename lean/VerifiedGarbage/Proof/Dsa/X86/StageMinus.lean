module
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Validate
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Impl.Dsa.X86.Minus
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

/-! ### `Dsa.X86.ValidateMinus`, which only this module used -/

section

/-! ### `Dsa.X86.Minus`, which only this module used -/

section

/-! # Exact non-underflowing subtraction from the loaded modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem modulusMinus_ok {s : State} {base : Addr} {size n m amount : Nat}
    (hs : Scr s base size) (hn0 : 0 < n) (hz : contextBytes n ≤ size)
    (hv : wordsVal s.mem base (slot n 0) n = m) (ha : amount ≤ m) :
    WP isa (modulusMinus n amount) s fun t =>
      wordsVal t.mem base (slot n 6) n = m - amount ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hm : m < 2 ^ (64 * n) := by rw [← hv]; exact wordsVal_lt _ _ _ _
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have := slot_bound (n := n) hj
    have := hz
    simp only [stride] at *
    omega_arith
  have sep60 := slot_sep (n := n) (i := 6) (j := 0) (by decide)
  have sep67 := slot_sep (n := n) (i := 6) (j := 7) (by decide)
  have sep70 := slot_sep (n := n) (i := 7) (j := 0) (by decide)
  simp only [stride] at sep60 sep67 sep70
  unfold modulusMinus
  refine WP.seq (WP.mono (setConstW_ok hs (k := 2 * n) (o := slot n 7) (x := amount) (by omega_arith)
    (by have := bounds 7 (by decide); omega_arith)
    (by rw [show 32 * (2 * n) = 64 * n by omega_arith]; exact Nat.lt_of_le_of_lt ha hm)) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  rw [show 4 * (2 * n) = 8 * n by omega_arith] at Ou
  rw [← wordsVal_eq_val32] at Vu
  have Hu := hs.of_keeps Ku (by decide)
  have Mu : wordsVal u.mem base (slot n 0) n = m :=
    (Ou.wordsVal (by omega_arith) (by have := hs.nowrap; have := bounds 0 (by decide); omega_arith)).trans hv
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega_arith⟩
  rw [hk]
  refine WP.mono (chainSubW_ok Hu (k := k + 1) (by omega_arith) (by have := bounds 6 (by decide); omega_arith)
    (by have := bounds 0 (by decide); omega_arith) (by have := bounds 7 (by decide); omega_arith)
    (by omega_arith) (by omega_arith)) fun t ⟨Ot, ⟨c, _, Vt⟩, Kt⟩ => ?_
  have Ol : Outside base (slot n 6) (8 * n) u.mem t.mem := by
    simpa only [show 4 * (k + 1) = 8 * n by omega_arith] using Ot
  refine ⟨?_, (slotOutside_whole Ou (by decide)).trans (slotOutside_whole Ol (by decide)),
    (Ku.mono (by decide)).trans (Kt.mono (by decide))⟩
  rw [wordsVal_eq_val32, hk] at Mu Vu ⊢
  rw [Mu, Vu] at Vt
  have lt := val32_lt t.mem base (slot n 6) (k + 1)
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vt <;> omega_arith

end VG.Proof.Dsa.X86

end

end


/-! # Encoded p - 1 and q - 2 for domain checks and exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem validateMinus_ok {s : State} {base : Addr} {size len n m amount output : Nat} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base n (.input modulus) len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (ham : amount ≤ m)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Validate.minus len modulus amount output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len (m - amount) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  unfold Validate.minus
  dsimp only
  rw [← hn]
  have hn0 : 0 < n := by omega_using [hn, h4]
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsaved : 8256 ≤ size := hz
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega_using [hz, hn, h4, hmax, hw4, ho, hfar, b0, b6, hn0, hn48, cb, hsaved]) h4 (by omega_using [hn]) hw4
    R.toReadableComponent (R.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have Hu := hs.of_keeps Ku (by decide)
  have Oload : Outside base 0 (contextBytes n) s.mem u.mem :=
    slotOutside_whole Ou (by decide)
  refine WP.seq (WP.mono (modulusMinus_ok Hu hn0 (by omega_using [ho, hfar]) (Vu.trans hm) ham)
    fun v ⟨Vv, Ov, Kv⟩ => ?_)
  have Hv := Hu.of_keeps Kv (by decide)
  refine WP.mono (coreStore_ok Hv hz hn.symm (by omega_using [hz, hn, h4, hmax, hw4, ho, hfar, b0, b6, hn0, hn48, cb, hsaved]) h4 (by omega_using [hn]) hw4 ho (by omega_using [hfar, b6]))
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Vv], (Outs.of_outside (Oload.trans Ov) (by simp)).trans (Outs.of_outside Ot (by simp)),
    ((Ku.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.Dsa.X86

end

end


/-! # Persistent modulus-minus-constant stages -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stageMinusP_ok {base : Addr} {size pLen qLen p q amount output : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (ha : amount ≤ p)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Validate.minus pLen .p amount output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output pLen (p - amount) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (validateMinus_ok M.scr M.saved rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.pReady M.pValue
    ha (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (p - amount) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageMinusQ_ok {base : Addr} {size pLen qLen p q amount output : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (ha : amount ≤ q)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Validate.minus qLen .q amount output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output qLen (q - amount) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (validateMinus_ok M.scr M.saved rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady M.qValue
    ha (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (q - amount) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
