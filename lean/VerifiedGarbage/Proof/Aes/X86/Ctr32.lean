module

public import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES counter mode on x86 (32-bit): the counter block

What every implementation of `vg_aes_ctr32_to` on x86 proves with: the
counter block as a block of GCM's (`icb_lo`, `ctr_after`), and its
postcondition in place and out of place (`ctrPost`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.Proof.Aes

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

/-- The counter, as the scratch buffer holds it. -/
theorem icb_lo (m : Mem) {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) :
    bswap (m.readW (addr C 12) 32) = (Spec.Gcm.blockAt m (C.setWidth 64)).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  obtain e : t = 8 * (t / 8) + t % 8 := by omega_arith
  rw [e, bswap_bit _ (by omega_arith) (by omega_arith), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega_arith : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega_arith,
    blockAt_bit _ _ (by omega_arith) (by omega_arith), readW_bit _ _ (by omega_arith) (by omega_arith),
    addr_add64 (by omega_arith), show 12 + (3 - t / 8) = 15 - t / 8 by omega_arith, addr_eq (by omega_arith)]

/-- The counter block after the prologue: its first twelve bytes, and the
last four big-endian `c + n`. -/
theorem ctr_after {m m' : Mem} {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) {N : BitVec 32} {n : Nat}
    (hN : N = BitVec.ofNat 32 n)
    (h12 : ∀ k < 12, m' (addr C k) = m (addr C k))
    (hw : m'.readW (addr C 12) 32 = bswap (bswap (m.readW (addr C 12) 32) + N)) :
    Spec.Gcm.blockAt m' (C.setWidth 64) = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m (C.setWidth 64)) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, ctrBlock_byte _ _ hk, ← addr_eq (by omega_arith)]
  split
  · rename_i h; rw [toBytes_blockAt _ _ hk, ← addr_eq (by omega_arith), h12 k h]
  · rename_i h
    rw [← icb_lo m hC, ← hN]
    refine byte_ext fun j hj => ?_
    have := readW_bit m' (addr C 12) (i := k - 12) (t := j) (by omega_arith) hj
    rw [addr_add64 (by omega_arith), show 12 + (k - 12) = k by omega_arith, hw, bswap_bit _ (by omega_arith) hj] at this
    rw [← this, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega_arith

/-- What `ctr32X86` and `ctr32ToX86` promise, in place and out of place. -/
def ctrPost (to : Bool) (s s' : State) : Prop :=
  let ciph := Spec.Gcm.aesWith (arg s 1).toNat
    (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
  Spec.Gcm.blocksAt s'.mem ((dstP to s).setWidth 64) (arg s 4).toNat =
      Spec.Gcm.ctr32 ciph (Spec.Gcm.blockAt s.mem ((arg s 2).setWidth 64))
        (Spec.Gcm.blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) ∧
    Spec.Gcm.blockAt s'.mem ((arg s 2).setWidth 64) =
      Nat.repeat Spec.Gcm.inc32 (arg s 4).toNat (Spec.Gcm.blockAt s.mem ((arg s 2).setWidth 64))

end VG.Proof.Aes.X86
