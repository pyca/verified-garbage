module
public import VerifiedGarbage.Impl.Bignum.Arm.Minv64
public import VerifiedGarbage.Proof.Bignum.Arm.Newton64

import VerifiedGarbage.Proof.Bignum.Arm.Minv64Steps
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Block

/-! # ARMv7 proves the same 64-bit Montgomery inverse as the native 64-bit targets -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure InverseState (s0 : State) (a b : Addr) (bits : Nat) (s : State) : Prop where
  value : (((s0.mem.readW b 32 ++ s0.mem.readW a 32).toNat : Int) *
    (s.gpr .r10 ++ s.gpr .r1).toNat - 1) % (2 ^ bits : Int) = 0
  mem : s.mem = s0.mem
  rest : Rest newtonClobbers s0 s

theorem newton64_lift {s0 s : State} {a b : Addr} {j : Nat}
    (pa : State.addr (s0.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s0.gpr .r0 + BitVec.ofNat 32 4) = b)
    (ra : InRegions (s0.rd ++ s0.wr) a 4) (rb : InRegions (s0.rd ++ s0.wr) b 4)
    (hj : 2 * j ≤ 64) (inv : InverseState s0 a b j s) :
    WP isa (.block newton64) s (InverseState s0 a b (2 * j)) := by
  refine WP.mono (newton64_step_ok s a b
    (by rw [inv.rest.gpr .r0 (by simp [newtonClobbers])]; exact pa)
    (by rw [inv.rest.gpr .r0 (by simp [newtonClobbers])]; exact pb)
    (by rw [inv.rest.rd, inv.rest.wr]; exact ra)
    (by rw [inv.rest.rd, inv.rest.wr]; exact rb) hj (by rw [inv.mem]; exact inv.value)) ?_
  rintro t ⟨value, mem, rest⟩
  exact ⟨by rw [inv.mem] at value; exact value, mem.trans inv.mem, inv.rest.trans rest⟩

/-- Compute `-m^-1 mod 2^64` without modifying the modulus or other memory. -/
theorem minv64_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4)
    (odd : (s.mem.readW b 32 ++ s.mem.readW a 32).toNat % 2 = 1) :
    WP isa (.block minv64) s fun t =>
      ((s.mem.readW b 32 ++ s.mem.readW a 32).toNat * (t.gpr .r11 ++ t.gpr .r2).toNat + 1) % 2 ^ 64 = 0 ∧
      t.mem = s.mem ∧ Rest newtonClobbers s t := by
  simp only [minv64, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (minv64Start_ok s a b pa pb ra rb) ?_
  rintro s0 ⟨start, mem0, rest0⟩
  have inv0 : InverseState s a b 3 s0 := by
    refine ⟨?_, mem0, rest0⟩
    rw [start]
    have h := VG.Proof.Bignum.odd_sq _ odd
    have h' := congrArg (fun n : Nat => (n : Int)) h
    simp only [Int.natCast_emod, Int.natCast_mul] at h'
    change (_ - 1) % (8 : Int) = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton64_lift pa pb ra rb (by decide) inv0) ?_
  intro s1 inv1
  rw [WP.block_append_iff]
  refine WP.mono (newton64_lift pa pb ra rb (by decide) inv1) ?_
  intro s2 inv2
  rw [WP.block_append_iff]
  refine WP.mono (newton64_lift pa pb ra rb (by decide) inv2) ?_
  intro s3 inv3
  rw [WP.block_append_iff]
  refine WP.mono (newton64_lift pa pb ra rb (by decide) inv3) ?_
  intro s4 inv4
  have inv32 : InverseState s a b 32 s4 :=
    ⟨VG.Proof.Bignum.emod_pow_weaken (by decide) inv4.value, inv4.mem, inv4.rest⟩
  rw [WP.block_append_iff]
  refine WP.mono (newton64_lift pa pb ra rb (by decide) inv32) ?_
  intro s5 inv5
  refine WP.mono (minv64End_ok s5) ?_
  rintro t ⟨neg, mem, rest⟩
  refine ⟨?_, mem.trans inv5.mem, inv5.rest.trans rest⟩
  rw [neg, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
  exact VG.Proof.Bignum.neg_inv (s5.gpr .r10 ++ s5.gpr .r1).isLt inv5.value

end VG.Proof.Bignum.Arm
