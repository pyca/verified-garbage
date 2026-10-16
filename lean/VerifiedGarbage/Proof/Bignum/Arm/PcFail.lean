module

public import VerifiedGarbage.Proof.Bignum.Arm.PcFailArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
public import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Invalid RSA moduli return zero and clear every precomputation word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem pcFail_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (stack : PcStack base dst src len k s) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (fit : dst.toNat + 16 * Spec.Rsa.modulusWords k ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) (16 * Spec.Rsa.modulusWords k))
    (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa PcFn.fail s fun t => t.gpr .r0 = 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) =
        List.replicate (2 * Spec.Rsa.modulusWords k) 0 ∧
      Frame [⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := Spec.Rsa.modulusWords k
  have hw : 0 < w := by simp only [w, Spec.Rsa.modulusWords]; omega
  rw [PcFn.fail, WP.seq_iff]
  refine WP.mono (pcFailArgs_ok s stack hk' count) ?_
  rintro u ⟨ptr, limbs, zero, mem, rest⟩
  rw [WP.seq_iff]
  refine WP.mono (zero_ok u (base := dst) (size := 16 * w) (o := 0) (n := 4 * w)
    ⟨fit, by omega, by rw [rest.wr]; exact write⟩ (by omega) (by simpa using ptr) limbs zero) ?_
  intro v inv
  have value := inv.value
  have frame := inv.frame
  rw [mem, show 4 * (4 * w) = 16 * w by omega] at frame
  refine wp_mov (op2_imm (by decide)) fun t result => WP.block_nil ?_
  refine ⟨result.gpr, ?_, by rw [result.mem]; exact frame,
    (rest.mono (by simp [roundClobbers])).trans
      ((inv.rest.mono (by simp [roundClobbers])).trans (result.rest (by simp [roundClobbers])))⟩
  apply wordsAt_zero_read
  rw [result.mem, show 8 * (2 * Spec.Rsa.modulusWords k) = 4 * (4 * w) by dsimp [w]; omega]
  have read := read_eq_val32 v.mem (State.addr dst) (4 * w) 0
  simp only [BitVec.add_zero] at read
  exact read.trans value

end VG.Proof.Bignum.Arm
