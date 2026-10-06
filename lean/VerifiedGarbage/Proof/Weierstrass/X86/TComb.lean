import VerifiedGarbage.Proof.Weierstrass.X86.TCombInit

/-! # Correctness of the 32-bit x86 fixed-base comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

/-- Save the table address in the scratch header before initializing the comb. -/
theorem savePtr_ok {K : TCombCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hL : TCombLay K size) :
    WP isa (.block [.store (sc K.ptr) .eax]) s fun t =>
      t.mem.readW (off base K.ptr) 32 = s.gpr .eax ∧ Keeps [] s t ∧
        Outside base K.ptr 4 s.mem t.mem := by
  have hn := hs.nowrap
  have hp := hL.ptr_le
  refine wp_storeS (hs.ea (by omega)) (hs.write (n := 4) hp) fun t u => WP.block_nil ?_
  refine ⟨?_, u.keeps _, ?_⟩
  · rw [u.mem, Mem.readW_writeW_self32]
  · rw [u.mem]; exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86
