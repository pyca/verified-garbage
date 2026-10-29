module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.Words
/-! # Native RSA product rows reuse the proved paired Montgomery loop -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ProductLoad.lean`, which only this module imported.
section

/-! # Loading a native multiplication row -/

section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86

theorem load_ok {s : State} {base : Addr} {size i a mult : Nat}
    (hs : Scr s base size)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : 4 * i + a + 4 ≤ size) (hm : mult + 4 ≤ size) :
    WP isa (.block (Impl.RsaKeyGen.X86.Product.load a mult)) s fun t =>
      t.mem = s.mem.writeW (off base mult) (s.mem.readW (off base (4 * i + a)) 32) ∧
      Keeps [.eax] s t := by
  unfold Impl.RsaKeyGen.X86.Product.load
  refine wp_movS (readSrc_at hs hp ha) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write hm) fun t T => WP.block_nil ?_
  exact ⟨by rw [T.mem, U.mem, U.gpr], U.keeps.trans (T.keeps _)⟩

end VG.Proof.RsaKeyGen.X86.Product
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- One schoolbook row, including its multiplier load. The only writes
are the current product window and the single multiplier slot. -/
theorem accumulate_ok {s : State} {base : Addr} {size i right out a b mult : Nat}
    (hs : Scr s base size) (positive : 0 < right) (even : right % 2 = 0)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : 4 * i + a + 4 ≤ size) (hb : b + 4 * right ≤ size)
    (ho : 4 * i + out + 4 * right + 8 ≤ size) (hm : mult + 4 ≤ size)
    (sepB : b + 4 * right ≤ 4 * i + out ∨ 4 * i + out + 4 * right + 8 ≤ b)
    (sepM : mult + 4 ≤ 4 * i + out ∨ 4 * i + out + 4 * right + 8 ≤ mult)
    (sepMB : mult + 4 ≤ b ∨ b + 4 * right ≤ mult)
    (fits : val32 s.mem base (4 * i + out) (right + 2) +
      w32 s.mem base (4 * i + a) * val32 s.mem base b right < 2 ^ (32 * (right + 2))) :
    WP isa (Impl.RsaKeyGen.X86.Product.accumulate right out a b mult) s fun t =>
      Outs base [(mult, 4), (4 * i + out, 4 * right + 8)] s.mem t.mem ∧
      val32 t.mem base (4 * i + out) (right + 2) =
        val32 s.mem base (4 * i + out) (right + 2) +
          w32 s.mem base (4 * i + a) * val32 s.mem base b right ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have hn := hs.nowrap
  unfold Impl.RsaKeyGen.X86.Product.accumulate
  refine WP.seq (WP.mono (load_ok hs hp ha hm) fun u ⟨memory, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  have O : Outside base mult 4 s.mem u.mem := by
    rw [memory]
    exact writeW32_outside _ _ _ (by omega)
  have value : w32 u.mem base mult = w32 s.mem base (4 * i + a) := by
    rw [memory, w32_write_self]
  have B : val32 u.mem base b right = val32 s.mem base b right := O.val32 (by omega) (by omega)
  have W : val32 u.mem base (4 * i + out) (right + 2) =
      val32 s.mem base (4 * i + out) (right + 2) := O.val32 (by omega) (by omega)
  have ptr : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K.1 _ (by decide), K.1 _ (by decide), hp]
  refine WP.mono (mulRowW_ok hu positive even ptr rfl hb ho sepB hm sepM ?_)
    fun t ⟨O', V, K'⟩ => ?_
  · rw [W, value, B]
    exact fits
  · refine ⟨?_, ?_, (K.mono (by decide)).trans K'⟩
    · intro x hx
      exact (O' x (hx (4 * i + out, 4 * right + 8) (by simp))).trans
        (O x (hx (mult, 4) (by simp)))
    · rw [V, W, value, B]

end VG.Proof.RsaKeyGen.X86.Product
