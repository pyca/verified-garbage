module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RawArgs
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Cached public pointers and width from the prepared header -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def cacheTail : List Instr := [
  .mov .edx (.mem (rawArg 3)),
  .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
  .alu .add .edx (.reg .eax), .mov .esi (.mem (at_ .edx 64)),
  .mov .ebx (.mem (at_ .eax 48)), .mov .ebp (.mem (at_ .eax 64)), .mov .edi (.reg .ecx)]

theorem cacheTail_ok {s : State} {W : Addr} {L N S a b : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : RawArgs s W L A) (base : (A 0).toNat = W.toNat)
    (M : Compact.Metadata s.mem W A N S 256 a b) (header : 128 ≤ L)
    (eax : s.gpr .eax = A 0) (ecx : s.gpr .ecx = BitVec.ofNat 32 (W.toNat + S)) :
    WP isa (.block cacheTail) s fun t =>
      t.gpr .eax = A 0 ∧ t.gpr .ebx = s.mem.readW (off W 48) 32 ∧
      t.gpr .esi = A 0 + BitVec.ofNat 32 a ∧ t.gpr .ebp = A 0 + BitVec.ofNat 32 256 ∧
      PtrAt t W .edi S ∧ t.mem = s.mem ∧ Keeps [.edx, .ebx, .esi, .ebp, .edi] s t := by
  unfold cacheTail
  refine wp_movS (ha.read 3 (by decide)) fun s1 U1 _ => wp_addS rfl fun s2 U2 _ =>
    wp_addS rfl fun s3 U3 _ => wp_addS rfl fun s4 U4 _ => wp_addS rfl fun s5 U5 _ => ?_
  have K5 : Keeps [.edx] s s5 := U1.keeps.trans (U2.keeps.trans (U3.keeps.trans (U4.keeps.trans U5.keeps)))
  have mem5 : s5.mem = s.mem := by rw [U5.mem, U4.mem, U3.mem, U2.mem, U1.mem]
  have scaled : (s4.gpr .edx).toNat = 8 * (A 3).toNat := by
    rw [U4.gpr, U3.gpr, U2.gpr, U1.gpr]
    simp only [BitVec.toNat_add]
    have := M.aIndex
    omega
  have indexPtr : PtrAt s5 W .edx (8 * (A 3).toNat) := by
    rw [PtrAt, U5.gpr, U4.other .eax (by decide), U3.other .eax (by decide), U2.other .eax (by decide),
      U1.other .eax (by decide), eax, BitVec.toNat_add, scaled, base]
    omega
  have hw5 := hw.of_keeps K5
  refine wp_movS (readSrc_ptr hw5 indexPtr (d := 64) (by have := M.aIndex; omega)) fun s6 U6 _ => ?_
  have K6 : Keeps [.edx, .esi] s s6 := (K5.mono (by decide)).trans (U6.keeps.mono (by decide))
  have eax6 : PtrAt s6 W .eax 0 := by
    rw [PtrAt, K6.1 _ (by decide), eax, base, Nat.add_zero, Nat.mod_eq_of_lt]
    rw [← base]
    exact (A 0).isLt
  have hw6 := hw.of_keeps K6
  refine wp_movS (readSrc_ptr hw6 eax6 (d := 48) (by omega)) fun s7 U7 _ => ?_
  have K7 : Keeps [.edx, .esi, .ebx] s s7 := (K6.mono (by decide)).trans (U7.keeps.mono (by decide))
  have eax7 : PtrAt s7 W .eax 0 := by rw [PtrAt, U7.other _ (by decide)]; exact eax6
  refine wp_movS (readSrc_ptr (hw.of_keeps K7) eax7 (d := 64) (by omega)) fun s8 U8 _ =>
    wp_movS rfl fun t U9 _ => WP.block_nil ?_
  have K : Keeps [.edx, .ebx, .esi, .ebp, .edi] s t :=
    (K7.mono (by decide)).trans ((U8.keeps.mono (by decide)).trans (U9.keeps.mono (by decide)))
  have mem6 : s6.mem = s.mem := U6.mem.trans mem5
  have left : t.gpr .esi = BitVec.ofNat 32 (W.toNat + a) := by
    rw [U9.other _ (by decide), U8.other _ (by decide), U7.other _ (by decide), U6.gpr, mem5,
      show 8 * (A 3).toNat + 64 = 64 + 8 * (A 3).toNat by omega]
    exact M.left_word
  have modulus : t.gpr .ebp = BitVec.ofNat 32 (W.toNat + 256) := by
    rw [U9.other _ (by decide), U8.gpr, U7.mem, mem6, Nat.zero_add]
    apply BitVec.eq_of_toNat_eq
    exact M.modulus
  have wordBase : A 0 = BitVec.ofNat 32 W.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← base, Nat.mod_eq_of_lt (A 0).isLt]
  refine ⟨(K.1 _ (by decide)).trans eax, ?_, ?_, ?_, ?_, ?_, K⟩
  · rw [U9.other _ (by decide), U8.other _ (by decide), U7.gpr, mem6, Nat.zero_add]
  · rw [left, wordBase, ← BitVec.ofNat_add]
  · rw [modulus, wordBase, ← BitVec.ofNat_add]
  · rw [PtrAt, U9.gpr, U8.other _ (by decide), U7.other _ (by decide), U6.other _ (by decide),
      K5.1 _ (by decide), ecx, BitVec.toNat_ofNat]
  · rw [U9.mem, U8.mem, U7.mem, mem6]

end VG.Proof.Mont.X86.PreparedSquare
