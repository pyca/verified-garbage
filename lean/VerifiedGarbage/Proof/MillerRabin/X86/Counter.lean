module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

/-! # A positive public counter is decremented and determines the loop branch -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (count1_zf)

theorem counterDown_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (d q : Nat) (scratch : scratchWord d) (positive : 0 < q) (bound : q < 2 ^ 32)
    (count : s.mem.readW (off g.W d) 32 = BitVec.ofNat 32 q) :
    WP isa (.block [.mov .eax (.mem (slot d)), .alu .sub .eax (.imm 1), .store (slot d) .eax]) s fun t =>
      w32 t.mem g.W d = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax] s t ∧ Context g t := by
  have fit : d + 4 ≤ g.L := by have := v.headerFit; unfold scratchWord at scratch; omega
  refine wp_movS (C.readScalar d fit) fun a A _ => wp_subZ rfl fun b B Z => ?_
  have Ka : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have Cb := C.keepMem Ka (by decide) Mb
  refine wp_storeS (ea_ptr Cb.ws Cb.base (d := d) (by omega))
    (ws_write Cb.ws (y := 0 + d) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have ax : (a.gpr .eax).toNat = q - 0 := by
    rw [A.gpr, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.sub_zero]
  obtain ⟨V, last⟩ := count1_zf (N := q) (j := 0) ax positive
  have O : Outside g.W d 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add, Mb]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)
  have Kt : Keeps [.eax] s t := Ka.widen (T.keeps [])
  refine ⟨?_, ?_, O, Kt, C.keepScalar Kt (by decide) O scratch⟩
  · rw [T.mem, Nat.zero_add, w32_write_self, B.gpr]
    exact V
  · rw [T.zf, Z, last]
    congr 1
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.MillerRabin.X86
