import VerifiedGarbage.Proof.Bignum.X86_64.IfmaBranch
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain

/-!
# RSA with AVX512_IFMA on x86-64: the computation for a valid modulus

`main`: `vg_rsa_private_crt`'s front, then the IFMA branch for a modulus of
32 words and primes of 16 (`sizes`), the CRT one otherwise, and its finish.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem ofNat_eq_iff {n v : Nat} (hn : n < 2 ^ 64) (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 n = BitVec.ofNat 64 v ↔ n = v :=
  ⟨fun h => by
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hv] at this,
   fun h => h ▸ rfl⟩

/-- `sizes`: ZF exactly if `n` has 32 words and `p` and `q` 16. -/
theorem sizes_ok {t : State} {B : Addr} {Z w op oq wp wq : Nat} {minv mp mq : BitVec 64}
    (hg : Good t B Z w minv) (hlo : slot w 8 ≤ op) (hoq : op ≤ oq) (hq : oq + slot wq 8 ≤ Z)
    (hsp : word t.mem B (8 * sWsP) = off B op) (hsq : word t.mem B (8 * sWsQ) = off B oq)
    (hwsp : WsAt t.mem B op wp mp) (hwsq : WsAt t.mem B oq wq mq) (hw : w < 2 ^ 64) (hwp : wp < 2 ^ 64)
    (hwq : wq < 2 ^ 64) :
    WP isa (.block CrtIfma.sizes) t fun t' =>
      t'.zf = some (decide (w = 32 ∧ wp = 16 ∧ wq = 16)) ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hq8 := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hlp : InRegions (t.rd ++ t.wr) (off (off B op) (8 * sW)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sW; omega)
  have hlq : InRegions (t.rd ++ t.wr) (off (off B oq) (8 * sW)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sW; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.zf = some (decide (w = 32 ∧ wp = 16 ∧ wq = 16)) ∧
    t'.mem = t.mem) (by
      xrun [CrtIfma.sizes, State.ea, hdr, ws, hg.rdi, hdrOff, hl sW (by decide), hl sWsP (by decide),
        hl sWsQ (by decide), hg.hdr.hw, hsp, hsq, hlp, hlq, hwsp.hdr.hw, hwsq.hdr.hw]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show (0 : BitVec 64) = 0#64 from rfl,
        BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff,
        BitVec.xor_eq_zero_iff, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_eq_iff hw (by decide), ofNat_eq_iff hwp (by decide),
        ofNat_eq_iff hwq (by decide), and_assoc]) rfl) fun t' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

end VG.Proof.Bignum.X86_64
