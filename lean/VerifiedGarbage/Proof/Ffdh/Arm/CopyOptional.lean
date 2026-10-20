module

import VerifiedGarbage.Proof.Ffdh.Arm.ZeroOptional
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Isa

/-! Copy the possibly empty suffix after a key scalar's masked leading byte. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem copyOptional_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (fits : n < 2 ^ 32) (sourceFits : src.toNat + n ≤ 2 ^ 32) (destFits : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) n) (write : InRegions s.wr (State.addr dst) n)
    (separate : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩)
    (source : s.gpr .r1 = src) (dest : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr VG.Impl.Bignum.Arm.copyBytes) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr src) n ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero, WP.seq_iff]
  refine WP.mono (zeroCount_ok s) ?_
  rintro u ⟨⟨zeroU, memU⟩, restU⟩
  by_cases empty : n = 0
  · subst n
    refine WP.ite true (by change some u.z = some true; rw [zeroU, count]; rfl) ?_ (by intro hf; cases hf)
    intro _
    exact WP.block_nil ⟨rfl, by rw [memU]; exact Frame.refl _ _, restU.mono (by simp)⟩
  · refine WP.ite false (by
      change some u.z = some false
      rw [zeroU, count]
      change some (BitVec.ofNat 32 n == (0 : BitVec 32)) = some false
      rw [ofNat_beq_zero fits, decide_eq_false empty]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (copyBytes_ok u (copyCtx_of_regions u src dst fits sourceFits destFits
      (by rw [restU.rd, restU.wr]; exact read) (by rw [restU.wr]; exact write) separate)
      (by omega) ((restU.gpr .r1 (by simp)).trans source) ((restU.gpr .r0 (by simp)).trans dest)
      ((restU.gpr .lr (by simp)).trans count)) ?_
    intro t inv
    refine ⟨?_, ?_, (restU.mono (by simp)).trans inv.rest⟩
    · unfold Spec.Rsa.bytesAt
      apply List.map_congr_left
      intro j hj
      have bound := List.mem_range.mp hj
      have byte := inv.copied j bound
      rw [addr_add (by omega), addr_add (by omega), memU] at byte
      exact byte
    · have frame := inv.frame destFits
      rw [memU] at frame
      exact frame

end VG.Proof.Ffdh.Arm
