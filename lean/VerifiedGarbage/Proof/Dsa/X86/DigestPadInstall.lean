module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Impl.Dsa.X86.DigestPad

/-! # Selecting the prepared digest buffer for the arithmetic body -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86

theorem digestPadInstall_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (space : DigestPad.output + 32 ≤ size) :
    WP isa (.block (Core.pointer (.local DigestPad.output) ++
      ([.store (sc (Layout.field .digest)) .esi] : List Instr))) s fun t =>
      pointerValue base t (.input .digest) = s.gpr .edi + BitVec.ofNat 32 DigestPad.output ∧
      Outside base (Layout.field .digest) 4 s.mem t.mem ∧ Keeps [.esi] s t := by
  have hz : Layout.saved ≤ size := by change 15712 + 32 ≤ size at space; change 8256 ≤ size; omega
  have hb : Layout.field .digest + 4 ≤ size := by change 15712 + 32 ≤ size at space; change 8224 ≤ size; omega
  refine WP.block_append (WP.mono (pointer_ok hs hz (.local DigestPad.output)) fun u ⟨P, K, O⟩ => ?_)
  have S := hs.of_keeps K (by decide)
  refine wp_storeS (S.ea (by omega)) (S.write hb) fun t U => WP.block_nil ⟨?_, ?_, K.trans (U.keeps _)⟩
  · change t.mem.readW (off base (Layout.field .digest)) 32 = _
    rw [U.mem]
    change (u.mem.writeW _ (u.gpr .esi)).readW _ (8 * 4) = _
    rw [Mem.readW_writeW_self _ _ 4 _ (by decide), P]
    rfl
  · rw [U.mem, O]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

theorem outside_suffix_bytes {base : Addr} {offset count d len : Nat} {m m' : Mem}
    (O : Outside base offset count m m') (lower : offset + count ≤ d) (bound : d + len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off base d) len = Spec.Rsa.bytesAt m (off base d) len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have H := List.mem_range.mp hi
  apply O _ (.inr ?_)
  rw [Offset.add_add, ofs_off base (by omega)]
  omega

end VG.Proof.Dsa.X86
