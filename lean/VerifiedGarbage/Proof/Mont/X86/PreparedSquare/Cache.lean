module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RawArgs

public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.CacheTail
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Cache the prepared square's public pointers while saving the caller -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem cache_ok {s : State} {W : Addr} {L N S a b : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : RawArgs s W L A) (base : (A 0).toNat = W.toNat)
    (M : Compact.Metadata s.mem W A N S 256 a b) (header : 128 ≤ S) (fit : S + 16 ≤ L) :
    WP isa (.block PreparedSquare.cache) s fun t =>
      t.gpr .eax = A 0 ∧ t.gpr .ebx = s.mem.readW (off W 48) 32 ∧
      t.gpr .esi = A 0 + BitVec.ofNat 32 a ∧ t.gpr .ebp = A 0 + BitVec.ofNat 32 256 ∧
      PtrAt t W .edi S ∧ SavedAt t.mem W S s.gpr ∧ Outside W S 16 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  change WP isa (.block ([.mov .eax (.mem (rawArg 0)), .mov .ecx (.mem (at_ .eax 80))] ++
    saveCode ++ cacheTail)) s _
  refine WP.block_append (WP.block_append ?_)
  refine wp_movS (ha.read 0 (by decide)) fun s1 U1 _ => ?_
  have ptr : PtrAt s1 W .eax 0 := by
    rw [PtrAt, U1.gpr, base, Nat.add_zero, Nat.mod_eq_of_lt]
    rw [← base]
    exact (A 0).isLt
  refine wp_movS (readSrc_ptr (hw.of_keeps U1.keeps) ptr (d := 80) (by omega)) fun s2 U2 _ =>
    WP.block_nil ?_
  have K2 : Keeps [.eax, .ecx] s s2 := (U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))
  have mem2 : s2.mem = s.mem := U2.mem.trans U1.mem
  have cp : PtrAt s2 W .ecx S := by
    rw [PtrAt, U2.gpr, U1.mem, Nat.zero_add]
    exact M.scratch
  refine WP.mono (saveCode_ok (hw.of_keeps K2) cp fit) ?_
  rintro s3 ⟨_, saved, outside, K3⟩
  have K23 : Keeps [.eax, .ecx] s s3 := K2.trans (K3.mono (by decide))
  have outside0 : Outside W S 16 s.mem s3.mem := by simpa only [mem2] using outside
  have O3 : Outs W [(0, L)] s2.mem s3.mem :=
    Outs.of_outside (outside.mono (o' := 0) (n' := L) (by omega) (by omega)) (by simp)
  have args3 := (ha.of_keeps K2 (by decide) (by rw [mem2]; exact Outs.refl _ _ _)).of_keeps
    K3 (by decide) O3
  have ecx3 : s3.gpr .ecx = BitVec.ofNat 32 (W.toNat + S) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, K3.1 .ecx (by decide)]
    exact cp
  have eax3 : s3.gpr .eax = A 0 := by rw [K3.1 .eax (by decide), U2.other .eax (by decide), U1.gpr]
  refine WP.mono (cacheTail_ok ((hw.of_keeps K2).of_keeps K3) args3 base
    (M.keep outside0 header) (by omega) eax3 ecx3) ?_
  rintro t ⟨eax, ebx, esi, ebp, edi, mem, K⟩
  refine ⟨eax, ?_, esi, ebp, edi, ?_, ?_, (K23.mono (by decide)).trans (K.mono (by decide))⟩
  · rw [ebx]
    apply BitVec.eq_of_toNat_eq
    exact outside0.w32 (by omega) (by omega)
  · rw [mem]
    exact ⟨saved.1.trans (K2.1 .ebx (by decide)), saved.2.1.trans (K2.1 .esi (by decide)),
      saved.2.2.1.trans (K2.1 .ebp (by decide)), saved.2.2.2.trans (K2.1 .edi (by decide))⟩
  · rw [mem]
    exact outside0

end VG.Proof.Mont.X86.PreparedSquare
