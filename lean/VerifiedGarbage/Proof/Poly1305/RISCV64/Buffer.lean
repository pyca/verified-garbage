module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Poly1305.Spec

/-!
# Poly1305 on RISC-V: the buffer

The buffer (bytes 56–71 of the state) as `update` and `finalize` fill it, and
absorbing it as a block, as on PPC64LE (`Proof/Poly1305/PPC64LE/Buffer.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

theorem off_56 (p : Addr) : off p 56 = p + 56 := rfl

/-- `x &&& 15`. -/
theorem and15 (x : BitVec 64) : x &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega)]

/-- The buffer. -/
abbrev bfR (st : Addr) : Region := ⟨off st 56, 16⟩

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

/-- The two words of the buffer, as a number. -/
theorem leNum_buf (m : Mem) (st : Addr) :
    word m st 56 + 2 ^ 64 * word m st (56 + 8) = leNum (bytesAt m (off st 56) 16) := by
  rw [leNum_key, word, word, word, word, add_ofNat_zero, off, Offset.add_add]

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) (pad : Bool) {R : Nat} (hk : Keys R s)
    (hw : sR (s.gpr .a0) ∈ s.wr) :
    WP isa (.block (absorb .a0 56 pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (leNum (bytesAt s.mem (off (s.gpr .a0) 56) 16) +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  have hin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => in_st' (List.mem_append_right _ hw) hd
  refine WP.mono (absorb_key_ok s .a0 56 pad false hk (by decide) (hin 56 (by decide))
    (hin (56 + 8) (by decide)) (fun h => by cases h)) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, k⟩
  obtain ⟨hv', hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  rw [hv', leNum_buf]

/-- The `k + n` bytes at `base` after `n` bytes are written from `base + k` on. -/
theorem bytesAt_after {m m' : Mem} {base : Addr} {k n : Nat} (hkn : k + n ≤ 16)
    (hf : Frame [⟨base + BitVec.ofNat 64 k, n⟩] m m') (src : Nat → Byte)
    (hc : ∀ i < n, m' (base + BitVec.ofNat 64 k + BitVec.ofNat 64 i) = src i) :
    bytesAt m' base (k + n) = bytesAt m base k ++ (List.range n).map src := by
  rw [Poly1305.bytesAt_add]
  congr 1
  · refine Poly1305.bytesAt_frame hf (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint base (by omega) (by omega)
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.RISCV64
