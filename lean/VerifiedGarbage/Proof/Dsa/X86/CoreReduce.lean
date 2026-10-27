module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame

public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Dsa.X86.RedCall
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete big-endian reduction call -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- `src` reads the public length `len` in every state that differs from
`s` only in the arithmetic context. -/
def LenOperand (base : Addr) (size n : Nat) (s : State) (src : Src) (len : Nat) : Prop :=
  ∀ t : State, Scr t base size → t.rd = s.rd → t.wr = s.wr → Outside base 0 (contextBytes n) s.mem t.mem →
    readSrc t src = some (BitVec.ofNat 32 len)

theorem LenOperand.imm (base : Addr) (size n : Nat) (s : State) (len : Nat) :
    LenOperand base size n s (.imm (BitVec.ofNat 32 len)) len := fun _ _ _ _ _ => rfl

/-- The saved digest-prefix length, as `Core.digestPrefix` reads it. -/
theorem LenOperand.prefix {base : Addr} {size n len : Nat} {s : State}
    (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : n ≤ 48)
    (h : pointerValue base s (.input .digestPrefixLen) = BitVec.ofNat 32 len) :
    LenOperand base size n s Core.digestPrefix len := by
  intro t ht _ _ O
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hs : 8256 ≤ size := hz
  show readSrc t (.mem (VG.Impl.Mont.X86.sc (VG.Impl.Dsa.X86.Layout.field .digestPrefixLen))) = _
  rw [readSrc_sc ht (by change 8244 ≤ size; omega)]
  congr 1
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  have f : VG.Impl.Dsa.X86.Layout.field .digestPrefixLen = 8240 := rfl
  rw [f] at *
  exact O.w32 (.inr (by omega)) (by omega)

/-- The modulus into slot 0, and the bytes' address and length into `esi` and
`ebx`: the state `Red.call_ok` reduces from. -/
theorem reduceHead_ok {s : State} {base : Addr} {size len inputLen n m : Nat} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size n s src inputLen)
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ri : StreamInput s base (contextBytes n) (pointerValue base s input) inputLen)
    (Rs : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, inputLen⟩ (callStack (s.gpr .esp)))
    (hi : inputLen < 2 ^ 32)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm255 : 255 < m) (hodd : m % 2 = 1) :
    WP isa (.seq (Core.load n len (slot n 0) (.input .q)) (.block (Core.pointer input ++ [.mov .ebx src]))) s
      fun w => Red.CallIn n m w base size (pointerValue base s input) inputLen ∧
        Outside base 0 (contextBytes n) s.mem w.mem ∧ Keeps powerClob s w := by
  have hn48 : n ≤ 48 := by omega
  have hl : len ≤ 8 * n := by omega
  have hz' : 8256 ≤ size := hz
  have cb : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bounds 0 (by decide)) h4 hl hw4 Rq.toReadableComponent
    (Rq.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have Ou' : Outside base 0 (contextBytes n) s.mem u.mem :=
    Ou.mono (by omega) (by have := bound 0 (by decide); omega)
  have Su : Scr u base size := hs.of_keeps Ku (by decide)
  have Pu := pointerValue_keep Ku (by decide) Ou' cb input
  refine WP.block_append (WP.mono (pointer_ok Su hz input) fun v ⟨Pv, Kv, Mv⟩ => ?_)
  have Sv : Scr v base size := Su.of_keeps Kv (by decide)
  have Ov : Outside base 0 (contextBytes n) s.mem v.mem := by rw [Mv]; exact Ou'
  refine wp_movS (hsrc v Sv (by rw [Kv.2.1, Ku.2.1]) (by rw [Kv.2.2, Ku.2.2]) Ov) fun w W _ => WP.block_nil ?_
  have Kuw : Keeps [.esi, .ebx] u w := (Kv.mono (by decide)).trans (W.keeps.mono (by decide))
  have Ksw : Keeps powerClob s w := (Ku.mono (by decide)).trans (Kuw.mono (by decide))
  have Mw : w.mem = u.mem := W.mem.trans Mv
  refine ⟨{ scr := Su.of_keeps Kuw (by decide)
            room := by rw [Ksw.1 _ (by decide)]; exact room
            context := by omega
            modulus := by rw [Mw, Vu, hm]
            large := hm255
            odd := hodd
            esi := by rw [W.other _ (by decide), Pv, Pu]
            ebx := W.gpr
            lenFit := hi
            input := Ri.keep Ksw
            stack := by rw [Ksw.1 _ (by decide)]; exact Rs }, by rw [Mw]; exact Ou', Ksw⟩

theorem coreReduce_ok {s : State} {base : Addr} {size len inputLen n m output : Nat} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size n s src inputLen)
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ri : StreamInput s base (contextBytes n) (pointerValue base s input) inputLen)
    (Rs : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, inputLen⟩ (callStack (s.gpr .esp)))
    (hi : inputLen < 2 ^ 32)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm255 : 255 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.reduce len src input output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) inputLen) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega
  have hl : len ≤ 8 * n := by omega
  have hz' : 8256 ≤ size := hz
  have cb : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega
  unfold Core.reduce
  dsimp only
  rw [← hn]
  apply WP.assoc
  refine WP.seq (WP.mono (reduceHead_ok hsrc hs hz room hn h4 hmax hw4 Rq Ri Rs hi hm hm255 hodd)
    fun w ⟨C, Ow, Ksw⟩ => ?_)
  refine WP.seq (WP.mono (Red.call_ok C hused (by omega) hn48) fun x ⟨Vx, Ox, Kx⟩ => ?_)
  refine WP.mono (coreStore_ok (C.scr.of_keeps Kx (by decide)) hz hn.symm (bounds 6 (by decide)) h4 hl hw4 ho
    (by have := bound 6 (by decide); omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vx, Ri.bytes Ow], ?_, ?_⟩
  · rw [Ksw.1 _ (by decide)] at Ox
    have Of : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] w.mem x.mem :=
      Ox.mono fun r hr => ⟨(0, contextBytes n), by simp, by omega,
        by simpa only [Nat.zero_add] using Pow.scratch_fits (Nat.le_refl _) r hr⟩
    exact ((StackOuts.of_outs (Outs.of_outside Ow (by simp))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp)))
  · exact (Ksw.trans (Kx.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86
