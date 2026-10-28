module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Readonly
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.DisjointBounds

/-! # Public original arguments in a workspace-only arithmetic run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

theorem context_argumentWindow {s : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (C : Context B Z p args s) (large : 160 ≤ Z) :
    (⟨VG.X86.Taint.argByte s 16, 76⟩ : Region).Disjoint ⟨B, Z⟩ := by
  have fit := C.fit
  have nowrap := C.scratch.nowrap
  have nat20 : (argsRegion p).base.toNat = p.toNat + 20 := by
    simp only [argsRegion, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have nat16 : (VG.X86.Taint.argByte s 16).toNat = p.toNat + 16 := by
    simp only [VG.X86.Taint.argByte, C.sp, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have bound := p.isLt
    omega
  have bounds := VG.Proof.RsaKeyGen.X86.Key.disjoint_bounds (by decide : 0 < 72) (by omega) C.separate
  change (argsRegion p).base.toNat + 72 ≤ B.toNat ∨ B.toNat + Z ≤ (argsRegion p).base.toNat at bounds
  rw [nat20] at bounds
  have stack := C.scratch.stk
  rw [C.sp] at stack
  rcases stack.2 with before | after
  · have above : p.toNat + 92 ≤ B.toNat := by omega
    apply Offset.disjoint_of_le
    · change (VG.X86.Taint.argByte s 16).toNat + 76 ≤ B.toNat
      rw [nat16]
      omega
    · change B.toNat + Z ≤ 2 ^ 64
      omega
  · apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change B.toNat + Z ≤ (VG.X86.Taint.argByte s 16).toNat
      rw [nat16]
      omega
    · change (VG.X86.Taint.argByte s 16).toNat + 76 ≤ 2 ^ 64
      rw [nat16]
      omega

theorem readonly_wf {s : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (C : Context B Z p args s) (large : 160 ≤ Z) : VG.X86.Taint.Wf runtimeTaint (readonly s B Z) := by
  have fit := C.fit
  refine {
    lens := fun h => False.elim (h rfl)
    bases := by intro p hp; cases hp
    wbases := by intro p hp; cases hp
    args := ?_
    argBases := by intro p hp; cases hp
    stk := ?_
    frames := by intro p hp; cases hp
    room := by intro h; cases h }
  · intro _
    refine ⟨?_, ?_⟩
    · change (s.gpr .esp).toNat + 16 + 76 ≤ 2 ^ 32
      rw [C.sp]
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change (⟨VG.X86.Taint.argByte s 16, 76⟩ : Region).Disjoint ⟨B, Z⟩
      exact context_argumentWindow C large
  · change (s.gpr .esp).toNat + 16 < 2 ^ 32
    rw [C.sp]
    omega

theorem readonly_agree {s t : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (S : Context B Z p args s) (T : Context B Z p args t) (large : 160 ≤ Z)
    (esi : s.gpr .esi = t.gpr .esi) :
    VG.X86.Taint.Agree runtimeTaint (readonly s B Z) (readonly t B Z) := by
  have sp : s.gpr .esp = t.gpr .esp := S.sp.trans T.sp.symm
  have fitS : (s.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [S.sp]; exact S.fit
  have fitT : (t.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [T.sp]; exact T.fit
  refine {
    rf := ⟨?_, by intro h; cases h⟩
    wr := fun h => False.elim (h rfl)
    wf₁ := readonly_wf S large
    wf₂ := readonly_wf T large
    ok := VG.X86.Taint.slotsOk_empty
    slots := VG.X86.Taint.slotsAgree_empty
    sp := fun _ => sp
    argMem := ?_ }
  · intro r hr
    simp only [runtimeTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact BitVec.eq_of_toNat_eq (S.scratch.edi_toNat.trans T.scratch.edi_toNat.symm)
    · exact esi
    · exact sp
  · intro k h4 hk
    change k < 76 at hk
    change s.mem (VG.X86.Taint.argByte s (16 + k)) = t.mem (VG.X86.Taint.argByte t (16 + k))
    rw [VG.X86.Taint.argByte_eq fitS (by omega) (by omega),
      VG.X86.Taint.argByte_eq fitT (by omega) (by omega),
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide : 0 < 4)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide : 0 < 4))]
    have index : (16 + k - 4) / 4 = (k - 4) / 4 + 4 := by omega
    have same := (context_argument S (i := (k - 4) / 4) (by change k < 76 at hk; omega)).value.trans
      (context_argument T (i := (k - 4) / 4) (by change k < 76 at hk; omega)).value.symm
    change arg s ((k - 4) / 4 + 4) = arg t ((k - 4) / 4 + 4) at same
    rw [index]
    exact congrArg _ same

end VG.Proof.RsaKeyGen.X86.KeyRuntime
