module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Restore the caller's four preserved registers from the scratch prefix -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem restore_ok {s : State} {W : Addr} {L S : Nat} {A : Nat → BitVec 32} {g : Reg → BitVec 32}
    (hw : Ws s W L) (ha : Compact.Args s W L A) (base : (A 0).toNat = W.toNat)
    (scratch : w32 s.mem W 80 = (W.toNat + S) % 2 ^ 32)
    (header : 128 ≤ L) (fit : S + 16 ≤ L) (saved : SavedAt s.mem W S g) :
    WP isa (.block PreparedSquare.restore) s fun t =>
      t.gpr .ebx = g .ebx ∧ t.gpr .esi = g .esi ∧ t.gpr .ebp = g .ebp ∧ t.gpr .edi = g .edi ∧
      t.mem = s.mem ∧ Keeps [.ecx, .ebx, .esi, .ebp, .edi] s t := by
  unfold PreparedSquare.restore Compact.scratchPtr
  refine WP.block_append (WP.mono (Compact.arrayPtr_ok hw ha base (r := .edi) (j := 2) (by omega)) ?_)
  rintro s1 ⟨p, mem1, K1⟩
  refine wp_movS rfl fun s2 U2 _ => ?_
  have K2 : Keeps [.ecx, .edi] s s2 := (K1.mono (by decide)).trans (U2.keeps.mono (by decide))
  have ptr2 : PtrAt s2 W .ecx S := by
    rw [PtrAt, U2.gpr, p]
    exact scratch
  refine wp_movS (readSrc_ptr (hw.of_keeps K2) ptr2 (d := 0) (by omega)) fun s3 U3 _ => ?_
  have K3 : Keeps [.ecx, .edi, .ebx] s s3 := (K2.mono (by decide)).trans (U3.keeps.mono (by decide))
  have ptr3 : PtrAt s3 W .ecx S := by rw [PtrAt, U3.other .ecx (by decide)]; exact ptr2
  refine wp_movS (readSrc_ptr (hw.of_keeps K3) ptr3 (d := 4) (by omega)) fun s4 U4 _ => ?_
  have K4 : Keeps [.ecx, .edi, .ebx, .esi] s s4 := (K3.mono (by decide)).trans (U4.keeps.mono (by decide))
  have ptr4 : PtrAt s4 W .ecx S := by rw [PtrAt, U4.other .ecx (by decide)]; exact ptr3
  refine wp_movS (readSrc_ptr (hw.of_keeps K4) ptr4 (d := 8) (by omega)) fun s5 U5 _ => ?_
  have K5 : Keeps [.ecx, .edi, .ebx, .esi, .ebp] s s5 := (K4.mono (by decide)).trans (U5.keeps.mono (by decide))
  have ptr5 : PtrAt s5 W .ecx S := by rw [PtrAt, U5.other .ecx (by decide)]; exact ptr4
  refine wp_movS (readSrc_ptr (hw.of_keeps K5) ptr5 (d := 12) (by omega)) fun t U6 _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, (K5.mono (by decide)).trans (U6.keeps.mono (by decide))⟩
  · rw [U6.other .ebx (by decide), U5.other .ebx (by decide), U4.other .ebx (by decide),
      U3.gpr, U2.mem, mem1, Nat.add_zero]
    exact saved.1
  · rw [U6.other .esi (by decide), U5.other .esi (by decide), U4.gpr, U3.mem, U2.mem, mem1]
    exact saved.2.1
  · rw [U6.other .ebp (by decide), U5.gpr, U4.mem, U3.mem, U2.mem, mem1]
    exact saved.2.2.1
  · rw [U6.gpr, U5.mem, U4.mem, U3.mem, U2.mem, mem1]
    exact saved.2.2.2
  · rw [U6.mem, U5.mem, U4.mem, U3.mem, U2.mem, mem1]

end VG.Proof.Mont.X86.PreparedSquare
