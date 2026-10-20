module

public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.KeyCopy

/-! # Copy one component from its saved pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem keyCopyPart_ok {s : State} {base : Addr} {size len : Nat} {out : BitVec 32}
    {input : VG.Impl.Dsa.Layout.Pointer} {mask : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (R : KeyPartReady s base (out.setWidth 64) len (input, len))
    (hl : len < 2 ^ 32) (ho : out.toNat + len ≤ 2 ^ 32)
    (hd : s.gpr .edx = out) (hm : s.gpr .ebx = mask)
    (write : ∀ i < len, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (Generate.copyPart input len) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len).map
          (fun b => (b.setWidth 32 &&& mask).setWidth 8) ∧
      t.gpr .edx = out + BitVec.ofNat 32 len ∧
      t.gpr .ebx = mask ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .esi] s t := by
  unfold Generate.copyPart
  refine WP.seq (WP.block_append (WP.mono (pointer_ok hs hz input) fun u ⟨P, K, O⟩ => ?_))
  refine wp_movS rfl fun v uv _ => WP.block_nil ?_
  have Ksv : Keeps [.eax, .ecx, .edx, .esi] s v :=
    (K.mono (by decide)).trans (uv.keeps.mono (by decide))
  have mem : v.mem = s.mem := uv.mem.trans O
  refine WP.mono (keyCopy_ok (mask := mask) R.positive hl R.fits ho R.apart
    (by rw [uv.other _ (by decide), P]) (by rw [uv.other _ (by decide), K.1 _ (by decide)]; exact hd)
    uv.gpr (by rw [Ksv.1 _ (by decide)]; exact hm)
    (by rw [Ksv.2.1, Ksv.2.2]; exact R.read)
    (by rw [Ksv.2.2]; exact write)) fun t I => ?_
  refine ⟨?_, I.dest, I.maskReg, ?_, Ksv.trans I.keeps⟩
  · rw [I.result, mem]
  · rw [← mem]; exact I.mem

end VG.Proof.Dsa.X86
