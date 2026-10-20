module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Dsa.X86.CoreInputs
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame

/-! # Complete reduced modular addition call, including byte I/O -/

@[expose] public section
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
