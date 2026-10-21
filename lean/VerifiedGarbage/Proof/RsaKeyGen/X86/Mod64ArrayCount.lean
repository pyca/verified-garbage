module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack

/-! # Decrement the public native-word count in the caller's frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem countDown_ok {p : BitVec 32} {s : State} (C : Sieve.StackContext p s) {q : Nat}
    (positive : 0 < q) (bound : q < 2 ^ 32)
    (value : s.mem.readW (off (p.setWidth 64) 4) 32 = BitVec.ofNat 32 q) :
    WP isa (.block countDown) s fun t =>
      t.mem.readW (off (p.setWidth 64) 4) 32 = BitVec.ofNat 32 (q - 1) ∧
      t.zf = some (decide (q - 1 = 0)) ∧ Outside (p.setWidth 64) 4 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold countDown
  refine wp_movS (C.read 4 (by decide)) fun a A _ => wp_subS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have next : b.gpr .eax = BitVec.ofNat 32 (q - 1) := by
    rw [B.gpr, A.gpr, value]
    change BitVec.ofNat 32 q - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  have stack := C.keep K (by decide)
  refine wp_storeS (stack.address 4 (by decide))
    (VG.Proof.Mont.X86.Rt.ws_write stack.ws (y := 4) (n := 4) (by decide)) fun c S => ?_
  have Kc := S.keeps []
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, K.widen (Kc.trans (T.keeps []))⟩
  · rw [T.mem, S.mem, Mem.readW_writeW_self32, next]
  · rw [Z, Kc.1 .eax (by decide), next]
    change some (BitVec.ofNat 32 (q - 1) - 0#32 == 0) = _
    rw [BitVec.sub_zero, ofNat_beq_zero (by omega)]
  · rw [T.mem, S.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.RsaKeyGen.X86.Mod64
