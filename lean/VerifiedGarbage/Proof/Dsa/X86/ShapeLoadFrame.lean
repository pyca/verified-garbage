module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Public-header preservation while inspecting the second modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem loadWidths_header {s t : State} {base : Addr} {n output d : Nat}
    (O : Outs base [(slot n 0, 8 * n), (slot n 8, 8 * n), (output, 12)] s.mem t.mem)
    (hd : d + 4 ≤ 64) (hsep : d + 4 ≤ output ∨ output + 12 ≤ d) :
    shapeWord t base d = shapeWord s base d := by
  have h0 := slot_header n 0
  have h8 := slot_header n 8
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base d 1 = val32 s.mem base d 1 := by
    apply O.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> omega
    · omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem loadWidths_whole {s t : State} {base : Addr} {n output : Nat}
    (O : Outs base [(slot n 0, 8 * n), (slot n 8, 8 * n), (output, 12)] s.mem t.mem)
    (hn : n ≤ 48) (ho : output + 12 ≤ 64) : Outside base 0 (contextBytes 48) s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  simp only [stride] at b0 b8
  intro x hx
  apply O x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  change ofs base x < 0 ∨ 7048 ≤ ofs base x at hx
  rcases hr with rfl | rfl | rfl <;> omega

theorem OperandReady.smaller {s : State} {base : Addr} {len n : Nat} {p : VG.Impl.Dsa.Layout.Pointer}
    (R : OperandReady s base 48 p len) (hn : n ≤ 48) : OperandReady s base n p len := by
  refine ⟨R.toReadableComponent, R.apart.sub_right ?_⟩
  intro x hx
  change (x - base).toNat + 1 ≤ contextBytes n at hx
  change (x - base).toNat + 1 ≤ 7048
  have := VG.Proof.Dsa.X86.Layout.context_bound hn
  omega

theorem outside_shapeWord {s t : State} {base : Addr} {o n d : Nat}
    (O : Outside base o n s.mem t.mem) (hd : d + 4 ≤ 2 ^ 64)
    (hsep : d + 4 ≤ o ∨ o + n ≤ d) : shapeWord t base d = shapeWord s base d :=
  BitVec.eq_of_toNat_eq (O.w32 hsep hd)

end VG.Proof.Dsa.X86
