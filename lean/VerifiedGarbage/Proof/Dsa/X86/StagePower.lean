module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.CorePowerLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.PowCall
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Dsa.X86.CorePower`, which only this module used -/

section

/-! # Complete modular exponentiation call, including byte I/O -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem corePower_ok {s : State} {base : Addr} {size len expLen n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 16 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (he4 : 8 ≤ expLen) (he : expLen ≤ len) (hwe : expLen % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b expLen)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.power len expLen modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) ^
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) expLen) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n≤48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len≤8*n := by omega_using [hn]
  have bound (j : Nat) (hj : j<9) : slot n j+8*n≤contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j<9) : slot n j+8*n≤size := by have := bound j hj; omega_using [hz, hused, hn, h4, hmax, hw4, he, ho, hfar, hn48, cb, hl, this]
  unfold Core.power
  dsimp only
  rw [←hn]
  apply WP.assoc
  refine WP.seq (WP.mono (coreLoadPower_ok hs hz hn (by omega_using [h4]) hmax hw4 he4 he hwe Rq Ra Rb hm (by omega_using [ho, hfar]))
    fun w ⟨Mw,Aw,Ew,Opre,Ksw⟩ => ?_)
  have ek : (expLen+3)/4≤2*n := by omega_using [hn, he]
  have Wscr := hs.of_keeps Ksw (by decide)
  refine WP.seq (WP.mono (Pow.call_ok Wscr (by rw [Ksw.1 _ (by decide)]; exact room)
    (by omega_using [ho, hfar]) hused (by omega_using [hn, h4]) hn48 (by omega_using [he4]) ek Mw hm1 hodd) fun v ⟨Vv, Ov, Kv⟩ => ?_)
  refine WP.mono (coreStore_ok (Wscr.of_keeps Kv (by decide)) hz hn.symm
    (bounds 6 (by decide)) (by omega_using [h4]) hl hw4 ho (by have := bound 6 (by decide); omega_using [hfar, this])) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vv, Aw, Ew], ?_, ?_⟩
  · rw [Ksw.1 _ (by decide)] at Ov
    have Of : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] w.mem v.mem :=
      Ov.mono fun r hr => ⟨(0, contextBytes n), by simp, by omega_using [], by simpa only [Nat.zero_add] using Pow.scratch_fits (Nat.le_refl _) r hr⟩
    exact ((StackOuts.of_outs (Outs.of_outside Opre (by simp))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp)))
  · exact ((Ksw.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86

end

end


/-! # Fixed-iteration powers preserving validated DSA inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stagePowerP_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a e : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen + 7) / 8) a pLen)
    (Re : OperandReady s base ((pLen + 7) / 8) e qLen)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Core.power pLen qLen .p a e output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output pLen (operandValue s base a pLen ^ operandValue s base e qLen % p) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (corePower_ok M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) (by omega_using [L]) (by omega_using [L]) (by omega_using [A])
    M.pReady Ra Re M.pValue M.pLarge M.pOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (operandValue s base a pLen ^ operandValue s base e qLen % p) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stagePowerQ_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a e : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen)
    (Re : OperandReady s base ((qLen + 7) / 8) e qLen)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.power qLen qLen .q a e output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen (operandValue s base a qLen ^ operandValue s base e qLen % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (corePower_ok M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) (by omega_using [L]) (by omega_using []) (by omega_using [A])
    M.qReady Ra Re M.qValue (by have := M.qLarge; omega_using [this]) M.qOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base a qLen ^ operandValue s base e qLen % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
