module

public import VerifiedGarbage.Proof.Bignum.X86.CrtMaskFrame
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn

/-! # Apply the saved acceptance mask after exponentiation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

theorem maskResult_ok {s : State} {base : Addr} {bytes n y : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) (accept : Bool)
    (V : wordsVal s.mem base (slot n resultSlot) n = y)
    (Mask : s.mem.readW (off base 8) 32 = if accept then BitVec.allOnes 32 else 0) :
    WP isa (Crt.maskResult n) s fun t =>
      wordsVal t.mem base (slot n resultSlot) n = (if accept then y else 0) ∧
      t.mem.readW (off base 8) 32 = (if accept then BitVec.allOnes 32 else 0) ∧
      Outside base 64 (bytes - 64) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have sz := size_eq n
  unfold Crt.maskResult
  refine WP.seq (wp_movS (readSrc_sc hs (by change 8 + 4 ≤ bytes; omega)) fun u U _ => WP.block_nil ?_)
  refine WP.mono (maskOutput_ok (hs.of_keeps U.keeps (by decide)) hn hz accept
    (by rw [U.gpr]; exact Mask)) fun t ⟨Y, O, K⟩ => ?_
  refine ⟨?_, ?_, ?_, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩
  · rw [Y, U.mem, V]
  · rw [mask_header O (by decide), U.mem, Mask]
  · rw [← U.mem]
    exact mask_saved O hz

end VG.Proof.Bignum.X86.Crt
