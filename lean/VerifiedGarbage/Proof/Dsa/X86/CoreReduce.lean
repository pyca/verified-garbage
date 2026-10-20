module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame

import VerifiedGarbage.Proof.Dsa.X86.CoreStreamSource
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.Stream
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
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

theorem LenOperand.stream {base : Addr} {size n len : Nat} {s v : State} {src : Src}
    (h : LenOperand base size n s src len) (hr : v.rd = s.rd) (hw : v.wr = s.wr)
    (O : Outside base 0 (contextBytes n) s.mem v.mem) : LenSrc base size n v src len :=
  fun t ht hr' hw' ho => h t ht (hr'.trans hr) (hw'.trans hw) (O.trans (streamRanges_whole (Nat.le_refl _) ho))

theorem coreReduce_ok {s : State} {base : Addr} {size len inputLen n m output : Nat} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size n s src inputLen)
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ri : StreamInput s base (contextBytes n) (pointerValue base s input) inputLen)
    (hi : inputLen < 2 ^ 32)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm255 : 255 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.reduce len src input output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) inputLen) % m) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega
  have hl : len ≤ 8 * n := by omega
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  have cb : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  unfold Core.reduce
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreSetup_ok hs hz hn h4 hmax hw4 Rq.toReadableComponent
    (Rq.slot (by decide)) hm (by omega) hodd) fun u ⟨Cu, _, _, Ou, Ku⟩ => ?_)
  refine WP.seq (WP.mono (streamSource_ok Cu hz input) fun v ⟨Cv, Pv, Mv, Kv⟩ => ?_)
  rw [pointerValue_keep Ku (by decide) Ou cb input] at Pv
  have Ov : Outside base 0 (contextBytes n) u.mem v.mem := by rw [Mv]; exact Outside.refl _ _ _ _
  have Iv := (Ri.keep Ku).keep Kv
  have Kuv : Keeps powerClob s v := Ku.trans (Kv.mono (by decide))
  refine WP.seq (WP.mono (reduceStream_ok Cv hm255 hi (hsrc.stream Kuv.2.1 Kuv.2.2 (Ou.trans Ov)) Iv Pv)
    fun w ⟨Cw, Vw, Ow, Kw⟩ => ?_)
  rw [Ri.bytes (Ou.trans Ov)] at Vw
  have bw : slot n 6 + 8 * n ≤ size := Nat.le_trans (by omega) Cw.size_le
  refine WP.mono (coreStore_ok Cw.scr hz hn.symm bw h4 hl hw4 ho (by omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vw], ?_, ?_⟩
  · have Opre := (Ou.trans Ov).trans (streamRanges_whole (Nat.le_refl _) Ow)
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))
  · exact ((Ku.trans (Kv.mono (by decide))).trans Kw).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86
