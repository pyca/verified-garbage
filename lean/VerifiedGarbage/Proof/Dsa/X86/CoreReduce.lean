module

public import VerifiedGarbage.Proof.Dsa.X86.CoreStreamSource
public import VerifiedGarbage.Proof.Dsa.X86.CoreStore

/-! # Complete big-endian reduction call -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreReduce_ok {s : State} {base : Addr} {size len inputLen n m output : Nat} {input : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (Rq : OperandReady s base n (.input .q) len)
    (Ri : StreamInput s base (contextBytes n) (pointerValue base s input) inputLen)
    (hi : inputLen < 2 ^ 32)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm255 : 255 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.reduce len inputLen input output) s fun t =>
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
  refine WP.seq (WP.mono (coreSetup_ok hs hz hn h4 hmax Rq.toReadableComponent
    (Rq.slot (by decide)) hm (by omega) hodd) fun u ⟨Cu, _, _, Ou, Ku⟩ => ?_)
  refine WP.seq (WP.mono (streamSource_ok Cu hz input) fun v ⟨Cv, Pv, Ov, Kv⟩ => ?_)
  rw [pointerValue_keep Ku (by decide) Ou cb input] at Pv
  have Iv := (Ri.keep Ku).keep Kv
  refine WP.seq (WP.mono (reduceStream_ok Cv hm255 hi Iv Pv) fun w ⟨Cw, Vw, Ow, Kw⟩ => ?_)
  rw [Ri.bytes (Ou.trans Ov)] at Vw
  have bw : slot n 6 + 8 * n ≤ size := Nat.le_trans (by omega) Cw.size_le
  refine WP.mono (coreStore_ok Cw.scr hz bw h4 hl ho (by omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vw], ?_, ?_⟩
  · have Opre := (Ou.trans Ov).trans (streamRanges_whole (Nat.le_refl _) Ow)
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))
  · exact ((Ku.trans (Kv.mono (by decide))).trans Kw).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86
