module

import VerifiedGarbage.Proof.Rsa.X86.PrivRelease
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-! # Private-result release writes masked output and erases its temporary buffer -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem releaseBuffer_ok (s : State) {src dst : BitVec 32} {n : Nat} {accepted : Bool}
    (hn : 0 < n) (hn' : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (srcWrite : InRegions s.wr (byteAddr src) n) (dstWrite : InRegions s.wr (byteAddr dst) n)
    (sep : Region.Disjoint ⟨byteAddr src, n⟩ ⟨byteAddr dst, n⟩)
    (source : s.gpr .esi = src) (output : s.gpr .edi = dst) (count : s.gpr .ecx = BitVec.ofNat 32 n)
    (mask : s.gpr .edx = -BitVec.ofNat 32 accepted.toNat) :
    WP isa releaseLoop s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr dst) n =
        (if accepted then Spec.Rsa.bytesAt s.mem (byteAddr src) n else List.replicate n 0) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr src) n = List.replicate n 0 ∧
      Frame [⟨byteAddr dst, n⟩, ⟨byteAddr src, n⟩] s.mem t.mem ∧ Keeps [.edi, .esi, .eax, .ecx] s t := by
  have srcRead : InRegions (s.rd ++ s.wr) (byteAddr src) n := by
    obtain ⟨r, hr, hc⟩ := srcWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have copy := copyCtx_of_regions s src dst hn' srcFit dstFit srcRead dstWrite sep
  have clear (i : Nat) (hi : i < n) :
      InRegions s.wr (byteAddr (src + BitVec.ofNat 32 i)) 1 := by
    rw [byteAddr_add (by omega)]
    obtain ⟨r, hr, hc⟩ := srcWrite
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  have distinct (i : Nat) (hi : i < n) (j : Nat) (hj : j < n)
      (he : byteAddr (src + BitVec.ofNat 32 i) = byteAddr (src + BitVec.ofNat 32 j)) : i = j := by
    rw [byteAddr_add (by omega), byteAddr_add (by omega)] at he
    have eq := congrArg (fun a => (a - byteAddr src).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64)] using eq
  have ctx : ReleaseCtx s src dst n :=
    ⟨hn', copy.readable, copy.writable, clear, distinct, copy.separate, copy.distinct⟩
  refine WP.mono (release_ok s ctx hn source output count) ?_
  intro t inv
  have bytes : Spec.Rsa.bytesAt t.mem (byteAddr dst) n =
      (Spec.Rsa.bytesAt s.mem (byteAddr src) n).map (· &&& (s.gpr .edx).setWidth 8) := by
    simp only [Spec.Rsa.bytesAt, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j < n := List.mem_range.mp hj
    have value := inv.copied j hj'
    rw [byteAddr_add (by omega), byteAddr_add (by omega)] at value
    exact value
  rw [mask, acceptance_bytes_mask] at bytes
  have length : (Spec.Rsa.bytesAt s.mem (byteAddr src) n).length = n := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [length] at bytes
  refine ⟨bytes, ?_, ?_, inv.rest⟩
  · change (List.range n).map (fun j => t.mem (byteAddr src + BitVec.ofNat 64 j)) = _
    have cleared : (List.range n).map (fun j => t.mem (byteAddr src + BitVec.ofNat 64 j)) =
        (List.range n).map (fun _ => (0 : Byte)) := by
      apply List.map_congr_left
      intro j hj
      have hj' : j < n := List.mem_range.mp hj
      have value := inv.cleared j hj'
      rw [byteAddr_add (by omega)] at value
      exact value
    rw [cleared, List.map_const', List.length_range]
  · intro a ha
    apply inv.outside a
    · intro j hj he
      apply ha ⟨byteAddr dst, n⟩ (by simp)
      rw [he, byteAddr_add (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    · intro j hj he
      apply ha ⟨byteAddr src, n⟩ (by simp)
      rw [he, byteAddr_add (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
end VG.Proof.Rsa.X86.PrivChecked
