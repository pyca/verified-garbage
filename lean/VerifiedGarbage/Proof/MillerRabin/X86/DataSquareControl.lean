module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Round

import VerifiedGarbage.Proof.MillerRabin.X86.DataSlots
import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.FlagMath
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
/-! # A square's flag update as a known-value transition -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/SquareBits.lean`, which only this module imported.
section

/-! # A square includes minus-one equality only above its secret threshold -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem squareBits_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {q r : Nat} (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (count : s.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 q)
    (threshold : s.mem.readW (off g.W sThreshold) 32 = BitVec.ofNat 32 r)
    (eqBit : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat) :
    WP isa (.block (squareFlag.take 8)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 q ∧ (t.gpr .edx).toNat = (F || (E && decide (r < q))).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have header := v.headerFit
  change WP isa (.block [.mov .eax (.mem (slot sSquares)), .mov .edx (.mem (slot sThreshold)),
    .alu .sub .edx (.reg .eax), .shift .shr .edx 31, .mov .ecx (.mem (slot sEq2)),
    .alu .and .ecx (.reg .edx), .mov .edx (.mem (slot sFlag)), .alu .or .edx (.reg .ecx)]) s _
  refine wp_movS (C.readScalar sSquares (by unfold sSquares; omega)) fun a A _ => ?_
  refine wp_movS (C.readScalarAfter A.keeps (by decide) A.mem sThreshold
    (by unfold sThreshold; omega)) fun b B _ => ?_
  refine wp_subS rfl fun c D _ => wp_shr (by decide) fun d H _ => ?_
  have Kd : Keeps [.eax, .edx] s d := (((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen H.keeps
  have Md : d.mem = s.mem := by rw [H.mem, D.mem, B.mem, A.mem]
  refine wp_movS (C.readScalarAfter Kd (by decide) Md sEq2 (by unfold sEq2; omega)) fun e I _ => ?_
  refine wp_logicS (.inl rfl) rfl fun f J => ?_
  have Kf : Keeps [.eax, .ecx, .edx] s f := (Kd.mono (by decide)).widen I.keeps |>.widen J.keeps
  have Mf : f.mem = s.mem := J.mem.trans (I.mem.trans Md)
  refine wp_movS (C.readScalarAfter Kf (by decide) Mf sFlag (by unfold sFlag; omega)) fun h K _ => ?_
  refine wp_orS rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (K.mem.trans Mf), (Kf.widen K.keeps).widen T.keeps⟩
  · rw [T.other .eax (by decide), K.other .eax (by decide), J.other .eax (by decide),
      I.other .eax (by decide), H.other .eax (by decide), D.other .eax (by decide),
      B.other .eax (by decide), A.gpr, count]
  · rw [T.gpr, K.gpr, K.other .ecx (by decide), J.gpr, I.gpr, I.other .edx (by decide),
      H.gpr, D.gpr, B.gpr, B.other .eax (by decide), A.gpr,
      count, threshold, eqBit, flag]
    change ((BitVec.ofNat 32 F.toNat) ||| ((BitVec.ofNat 32 E.toNat) &&&
      ((BitVec.ofNat 32 r - BitVec.ofNat 32 q) >>> 31))).toNat = _
    exact squareFlag_value rBound qBound E F

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/SquareControl.lean`, which only this module imported.
section

/-! # The square loop branches only on its public countdown -/

section
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
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def squareSlots (V : Nat → BitVec 32) (q r : Nat) (E F : Bool) : Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (F || (E && decide (r < q))).toNat))
    sSquares (BitVec.ofNat 32 (q - 1))

theorem Data.squareFlag {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    {q r : Nat} (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sEq2, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (eqBit : V sEq2 = BitVec.ofNat 32 E.toNat) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (.block squareFlag) s fun t =>
      Data g A Js (squareSlots V q r E F) ([sFlag, sSquares] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧
      Outs g.W [(sFlag, 4), (sSquares, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have read (d : Nat) (mem : d ∈ [sSquares, sThreshold, sEq2, sFlag]) := (D.slotValues d (known d mem)).2
  refine WP.mono (squareFlag_ok v D.context positive qBound rBound E F
    ((read _ (by simp)).trans count) ((read _ (by simp)).trans threshold)
    ((read _ (by simp)).trans eqBit) ((read _ (by simp)).trans flag))
    fun t ⟨Flag, Count, Z, O, K, C⟩ => ?_
  have flagWord : t.mem.readW (off g.W sFlag) 32 =
      BitVec.ofNat 32 (F || (E && decide (r < q))).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sFlag = _
    rw [Flag]
    cases F || (E && decide (r < q)) <;> rfl
  have countWord : t.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sSquares = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨D.afterSlots v C [sFlag, sSquares] ?_ ?_ O, Z, O, K⟩
  · intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · refine ⟨by unfold scratchWord sFlag; simp, ?_⟩
      change t.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 (F || (E && decide (r < q))).toNat
      exact flagWord
    · refine ⟨by unfold scratchWord sSquares; simp, ?_⟩
      change t.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 (q - 1)
      exact countWord
  · intro d _ none
    have nf : d ≠ sFlag := fun eq => none (by simp [eq])
    have ns : d ≠ sSquares := fun eq => none (by simp [eq])
    exact (setAt_other _ _ ns).trans (setAt_other _ _ nf)

end VG.Proof.MillerRabin.X86
