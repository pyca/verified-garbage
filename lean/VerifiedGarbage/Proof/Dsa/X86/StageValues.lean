module

public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Reading stage outputs and retaining other persistent intermediates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem StageResult.local_value {base : Addr} {s t : State} {size output len value : Nat}
    (R : StageResult base s t output len value) (hs : Scr s base size)
    (hl : 0 < len) (hb : output + len ≤ size) (hv : value < 256 ^ len) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem ((pointerValue base t (.local output)).setWidth 64) len) = value := by
  rw [local_pointer (R.toStageFrame.scr hs) hl hb]
  exact R.value hv

theorem StageFrame.local_value_keep {base : Addr} {s t : State} {size output len d count : Nat}
    (F : StageFrame base s t output len) (hs : Scr s base size) (hc : 0 < count)
    (hd : contextBytes 48 ≤ d) (hb : d + count ≤ size) (ho : output + len ≤ size) (hused : d + count ≤ VG.Impl.Dsa.Layout.usedBytes)
    (hsep : d + count ≤ output ∨ output + len ≤ d) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem ((pointerValue base t (.local d)).setWidth 64) count) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.local d)).setWidth 64) count) := by
  rw [local_pointer (F.scr hs) hc hb, local_pointer hs hc hb,
    F.local_bytes hd hused (by have := hs.nowrap; omega) hsep]

theorem localStream {s : State} {base : Addr} {size offset len n : Nat}
    (hs : Scr s base size) (hlen : 0 < len) (hb : offset + len ≤ size) (hfar : contextBytes n ≤ offset) :
    StreamInput s base (contextBytes n) (pointerValue base s (.local offset)) len := by
  have R := localReady hs hlen hb hfar
  have ptr := local_pointer hs hlen hb
  refine ⟨R.fits, ?_, ?_⟩
  · intro i hi
    rw [ptr]
    change InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact hs.read (by omega)
  · intro i hi
    rw [ptr, ofs_off base (by have := hs.nowrap; omega)]
    omega

end VG.Proof.Dsa.X86
