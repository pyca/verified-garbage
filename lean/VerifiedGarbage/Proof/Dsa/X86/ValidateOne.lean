module

public import VerifiedGarbage.Proof.Dsa.X86.ValidateEqual
public import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-! # Checking that a public subgroup power equals one -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateOne_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (R : OperandReady s base n input len) :
    WP isa (.block (Validate.isOne len input)) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) = 1) ∧
      Keeps [.esi, .eax, .ebx, .edx] s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b5 b8
  have fit : 1 < 2 ^ (64 * n) := Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 64)
    (Nat.pow_le_pow_right (by decide) (by omega))
  unfold Validate.isOne Validate.accumulate
  dsimp only
  rw [← hn]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (coreLoad_ok hs hz (by omega) h4 (by omega) R.toReadableComponent
    (R.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Weierstrass.X86.setConst_ok (hs.of_keeps Ku (by decide))
    (by omega) fit) fun v ⟨Vv, Kv, Ov⟩ => ?_)
  have Opre := (slotOutside_whole Ou (by decide)).trans (slotOutside_whole Ov (by decide))
  have Ksv := Ku.widen Kv
  have Fu : flagW base (Layout.field .mask) v = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ksv (by decide) Opre (by omega) (.input .mask)
  refine WP.mono (accumulateEqual_ok (hs.of_keeps Ksv (by decide)) (by omega) (by omega) (by omega)
    (by change 8248 ≤ size; omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Ksv.mono (by decide)).widen Kt,
    (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))⟩
  rw [Vt, Fu, Vv, slotOutside_val Ov (by decide) (by omega), Vu]

end VG.Proof.Dsa.X86
