module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.SquareBits
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # The square loop branches only on its public countdown -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem squareFlag_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {q r : Nat} (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (count : s.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 q)
    (threshold : s.mem.readW (off g.W sThreshold) 32 = BitVec.ofNat 32 r)
    (eqBit : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat) :
    WP isa (.block squareFlag) s fun t =>
      w32 t.mem g.W sFlag = (F || (E && decide (r < q))).toNat ∧
      w32 t.mem g.W sSquares = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outs g.W [(sFlag, 4), (sSquares, 4)] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Context g t := by
  have header := v.headerFit
  have ff : sFlag + 4 ≤ g.L := by unfold sFlag; omega
  have sf : sSquares + 4 ≤ g.L := by unfold sSquares; omega
  change WP isa (.block (squareFlag.take 8 ++
    [.store (slot sFlag) .edx, .alu .sub .eax (.imm 1), .store (slot sSquares) .eax])) s _
  refine WP.block_append (WP.mono (squareBits_ok v C qBound rBound E F count threshold eqBit flag)
    fun a ⟨AX, Flag, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := sFlag) (by omega))
    (ws_write Ca.ws (y := 0 + sFlag) (n := 4) (by omega)) fun b B => ?_
  have O₁ : Outside g.W sFlag 4 a.mem b.mem := by
    rw [B.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)
  have Cb := Ca.keepScalar (B.keeps []) (by decide) O₁ (by unfold scratchWord sFlag; simp)
  refine wp_subZ rfl fun c D Z => ?_
  have Cc := Cb.keepMem D.keeps (by decide) D.mem
  refine wp_storeS (ea_ptr Cc.ws Cc.base (d := sSquares) (by omega))
    (ws_write Cc.ws (y := 0 + sSquares) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have O₂ : Outside g.W sSquares 4 b.mem t.mem := by
    rw [T.mem, Nat.zero_add, D.mem]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)
  have Kall : Keeps [.eax, .ecx, .edx] s t :=
    (((Ka.widen (B.keeps [])).widen D.keeps).widen (T.keeps []))
  refine ⟨?_, ?_, ?_, ?_, Kall,
    Cc.keepScalar (T.keeps []) (by decide) (by rw [D.mem]; exact O₂)
      (by unfold scratchWord sSquares; simp)⟩
  · rw [O₂.w32 (by unfold sFlag sSquares; omega) (by unfold sFlag; decide),
      B.mem, Nat.zero_add, w32_write_self]
    exact Flag
  · rw [T.mem, Nat.zero_add, w32_write_self, D.gpr, B.gpr, AX,
      BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)]
    change (2 ^ 32 - 1 + q) % 2 ^ 32 = q - 1
    rw [show 2 ^ 32 - 1 + q = (q - 1) + 2 ^ 32 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [T.zf, Z, B.gpr, AX]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)]
    change (2 ^ 32 - 1 + q) % 2 ^ 32 = 0 ↔ q = 1
    omega
  · rw [Ma] at O₁
    exact (Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))

end VG.Proof.MillerRabin.X86
