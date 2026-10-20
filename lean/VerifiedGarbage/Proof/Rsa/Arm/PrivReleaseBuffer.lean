module
public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Rsa.Arm.PrivRelease
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput

/-! # Private-result release writes masked output and erases its temporary buffer -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem releaseBuffer_ok (s : State) {src dst : BitVec 32} {n : Nat} {accepted : Bool}
    (hn : 0 < n) (hn' : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (srcWrite : InRegions s.wr (State.addr src) n) (dstWrite : InRegions s.wr (State.addr dst) n)
    (sep : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩)
    (source : s.gpr .r1 = src) (output : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n)
    (mask : s.gpr .r2 = -BitVec.ofNat 32 accepted.toNat) (zero : s.gpr .r12 = 0) :
    WP isa release s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n =
        (if accepted then Spec.Rsa.bytesAt s.mem (State.addr src) n else List.replicate n 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr src) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr src, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r3, .lr] s t := by
  have srcRead : InRegions (s.rd ++ s.wr) (State.addr src) n := by
    obtain ⟨r, hr, hc⟩ := srcWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have copy := copyCtx_of_regions s src dst hn' srcFit dstFit srcRead dstWrite sep
  have clear := maskCtx_of_region s hn' srcFit srcWrite
  have ctx : ReleaseCtx s src dst n :=
    ⟨hn', copy.readable, copy.writable, clear.writable, clear.distinct, zero, copy.separate, copy.distinct⟩
  refine WP.mono (release_ok s ctx hn source output count) ?_
  intro t inv
  have bytes : Spec.Rsa.bytesAt t.mem (State.addr dst) n =
      (Spec.Rsa.bytesAt s.mem (State.addr src) n).map (· &&& (s.gpr .r2).setWidth 8) := by
    simp only [Spec.Rsa.bytesAt, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j < n := List.mem_range.mp hj
    have value := inv.copied j hj'
    rw [addr_add (by omega), addr_add (by omega)] at value
    exact value
  rw [mask, acceptance_bytes_mask] at bytes
  have length : (Spec.Rsa.bytesAt s.mem (State.addr src) n).length = n := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [length] at bytes
  refine ⟨bytes, ?_, ?_, inv.rest⟩
  · change (List.range n).map (fun j => t.mem (State.addr src + BitVec.ofNat 64 j)) = _
    have cleared : (List.range n).map (fun j => t.mem (State.addr src + BitVec.ofNat 64 j)) =
        (List.range n).map (fun _ => (0 : Byte)) := by
      apply List.map_congr_left
      intro j hj
      have hj' : j < n := List.mem_range.mp hj
      have value := inv.cleared j hj'
      rw [addr_add (by omega)] at value
      exact value
    rw [cleared, List.map_const', List.length_range]
  · intro a ha
    apply inv.outside a
    · intro j hj he
      apply ha ⟨State.addr dst, n⟩ (by simp)
      rw [he, addr_add (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    · intro j hj he
      apply ha ⟨State.addr src, n⟩ (by simp)
      rw [he, addr_add (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
end VG.Proof.Rsa.Arm
