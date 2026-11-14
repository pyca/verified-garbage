module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.CoreReduce
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.MulCall
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.CoreInputs
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame

/-! ### `Dsa.X86.CoreProduct`, which only this module used -/

section

/-! # Complete ordinary modular product call, including byte I/O

The modulus and both operands are loaded into the context's slots 0, 5 and
8, the width's shared product (`vg_dsa_mulmod_{n}`, `Mul.call_ok`) leaves
their product in slot 6, and it is stored as bytes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- The modulus and both operands, at full width, into slots 0, 5 and 8. -/
theorem coreLoadProduct_ok {s : State} {base : Addr} {size len n m : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (contextRoom : contextBytes n ≤ size) :
    WP isa (Core.loadPower n len len modulus a b) s fun t =>
      wordsVal t.mem base (slot n 0) n = m ∧
      wordsVal t.mem base (slot n 5) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) ∧
      wordsVal t.mem base (slot n 8) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps loadClob s t := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len ≤ 8 * n := by omega_using [hn]
  have nw := hs.nowrap
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega_using [contextRoom, this]
  unfold Core.loadPower
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bounds 0 (by decide)) h4 hl hw4
    Rq.toReadableComponent (Rq.slot (by decide))) fun u ⟨Mu, Ku, Ou⟩ => ?_)
  have Ou' := slotOutside_whole Ou (by decide)
  have Rau := Ra.keep Ku (by decide) Ou' hn48
  have Rbu := Rb.keep Ku (by decide) Ou' hn48
  refine WP.seq (WP.mono (coreLoad_ok (hs.of_keeps Ku (by decide)) hz
    (bounds 5 (by decide)) h4 hl hw4 Rau.toReadableComponent (Rau.slot (by decide)))
    fun v ⟨Av, Kv, Ov⟩ => ?_)
  have Ov' := slotOutside_whole Ov (by decide)
  have Rbv := Rbu.keep Kv (by decide) Ov' hn48
  have Ksv := Ku.trans Kv
  have Osv := Ou'.trans Ov'
  refine WP.mono (coreLoad_ok (hs.of_keeps Ksv (by decide)) hz (bounds 8 (by decide))
    h4 hl hw4 Rbv.toReadableComponent (Rbv.slot (by decide))) fun w ⟨Bw, Kw, Ow⟩ => ?_
  refine ⟨?_, ?_, ?_, Osv.trans (slotOutside_whole Ow (by decide)), Ksv.trans Kw⟩
  · rw [slotOutside_val Ow (by decide) (by have := bounds 0 (by decide); omega_using [nw, this]),
      slotOutside_val Ov (by decide) (by have := bounds 0 (by decide); omega_using [nw, this]), Mu, hm]
  · rw [slotOutside_val Ow (by decide) (by have := bounds 5 (by decide); omega_using [nw, this]), Av,
      Ra.bytes Ku (by decide) Ou' hn48]
  · rw [Bw, Rb.bytes Ksv (by decide) Osv hn48]

theorem coreProductMod_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.productMod len modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) *
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len ≤ 8 * n := by omega_using [hn]
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega_using [ho, hfar, this]
  unfold Core.productMod
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoadProduct_ok hs hz hn h4 hmax hw4 Rq Ra Rb hm (by omega_using [ho, hfar]))
    fun w ⟨Mw, Aw, Bw, Opre, Ksw⟩ => ?_)
  have Wscr := hs.of_keeps Ksw (by decide)
  refine WP.seq (WP.mono (Mul.call_ok Wscr (by rw [Ksw.1 _ (by decide)]; exact room)
    (by omega_using [ho, hfar]) hused (by omega_using [hn, h4]) hn48 Mw hm1 hodd) fun v ⟨Vv, Ov, Kv⟩ => ?_)
  refine WP.mono (coreStore_ok (Wscr.of_keeps Kv (by decide)) hz hn.symm
    (bounds 6 (by decide)) h4 hl hw4 ho (by have := bound 6 (by decide); omega_using [hfar, this])) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vv, Aw, Bw], ?_, ?_⟩
  · rw [Ksw.1 _ (by decide)] at Ov
    have Of : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] w.mem v.mem :=
      Ov.mono fun r hr => ⟨(0, contextBytes n), by simp, by omega_using [],
        by simpa only [Nat.zero_add] using Pow.scratch_fits (Nat.le_refl _) r hr⟩
    exact ((StackOuts.of_outs (Outs.of_outside Opre (by simp))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp)))
  · exact ((Ksw.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))

theorem coreProduct_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.product len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) *
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t :=
  coreProductMod_ok hs hz room hused hn h4 hmax hw4 Rq Ra Rb hm hm1 hodd ho hfar

end VG.Proof.Dsa.X86

end

end

/-! # Scalar arithmetic stages preserve validated caller parameters -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreSum.lean`, which only this module imported.
section

/-! # Complete reduced modular addition call, including byte I/O -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreSum_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ha : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) < m)
    (hb : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) < m)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.sum len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) +
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len)) % m) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega
  have hl : len ≤ 8 * n := by omega
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  unfold Core.sum
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreSetup_ok hs hz hn h4 hmax hw4 Rq.toReadableComponent (Rq.slot (by decide)) hm hm1 hodd)
    fun u ⟨Cu, _, _, Ou, Ku⟩ => ?_)
  have Rau := Ra.keep Ku (by decide) Ou hn48
  have Rbu := Rb.keep Ku (by decide) Ou hn48
  refine WP.seq (WP.mono (coreInputs_ok Cu hz hn48 h4 hl h4 hl hw4 hw4 Rau Rbu)
    fun v ⟨Cv, Av, Bv, _, Ov, Kv⟩ => ?_)
  rw [Ra.bytes Ku (by decide) Ou hn48] at Av
  rw [Rb.bytes Ku (by decide) Ou hn48] at Bv
  refine WP.seq (WP.mono (ordinaryAdd_ok Cv (by rw [Av]; exact ha) (by rw [Bv]; exact hb)) fun w ⟨Cw, Kw, Vw⟩ => ?_)
  have bw : slot n 6 + 8 * n ≤ size := Nat.le_trans (by omega) Cw.size_le
  refine WP.mono (coreStore_ok Cw.scr hz hn.symm bw h4 hl hw4 ho (by omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vw, Av, Bv], ?_, ?_⟩
  · have Opre := (Ou.trans Ov).trans (resultKeep_whole Kw)
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))
  · exact (((Ku.trans (Kv.mono (by decide))).trans ((OpKeep.keeps Kw).mono (by decide))).trans (Kt.mono (by decide)))

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stageProduct_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen) (Rb : OperandReady s base ((qLen + 7) / 8) b qLen)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.product qLen a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen (operandValue s base a qLen * operandValue s base b qLen % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreProduct_ok M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady Ra Rb M.qValue
    (by have := M.qLarge; omega_using [this]) M.qOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base a qLen * operandValue s base b qLen % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageProductP_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen + 7) / 8) a pLen) (Rb : OperandReady s base ((pLen + 7) / 8) b pLen)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Core.productMod pLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output pLen (operandValue s base a pLen * operandValue s base b pLen % p) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreProductMod_ok M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.pReady Ra Rb M.pValue
    M.pLarge M.pOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (operandValue s base a pLen * operandValue s base b pLen % p) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageSum_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen) (Rb : OperandReady s base ((qLen + 7) / 8) b qLen)
    (ha : operandValue s base a qLen < q) (hbb : operandValue s base b qLen < q)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.sum qLen a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen ((operandValue s base a qLen + operandValue s base b qLen) % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreSum_ok M.scr M.saved rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady Ra Rb M.qValue
    (by have := M.qLarge; omega_using [this]) M.qOdd ha hbb (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen ((operandValue s base a qLen + operandValue s base b qLen) % q) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageReduce_ok {base : Addr} {size pLen qLen p q output len : Nat} {s : State} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size ((qLen + 7) / 8) s src len)
    (M : Moduli base size pLen qLen p q s)
    (Ri : StreamInput s base (contextBytes ((qLen + 7) / 8)) (pointerValue base s input) len)
    (Rs : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, len⟩ (callStack (s.gpr .esp)))
    (hi : len < 2 ^ 32) (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.reduce qLen src input output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output qLen (operandValue s base input len % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreReduce_ok hsrc M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady
    Ri Rs hi M.qValue M.qLarge M.qOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base input len % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
