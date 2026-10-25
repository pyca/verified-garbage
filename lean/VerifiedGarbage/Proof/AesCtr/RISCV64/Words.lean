module

public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-CTR on RISC-V: the counter block's words

The counter block's words as RISC-V loads and stores them, a byte at a time
and big-endian (`Impl/Words/RISCV64.lean`), as the big-endian numbers of its
bytes (`Spec.Ctr.toNat`, `ofNat`): the last 32 bits as `loadBE32` loads them
(`lo32_beWord`), the halves as `loadBE64` loads them (`toNat_be64`), the
bytes `storeBE` stores (`beBytes_eq`), and the block after its second half
plus `d` and its first half plus the carry are stored (`add_halves`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (toNat ofNat)

theorem lt_256_8 (x : BitVec 64) : x.toNat < 256 ^ 8 :=
  Nat.lt_of_lt_of_eq x.isLt (by decide)

/-- The big-endian word of eight bytes is the byte-reversed little-endian one. -/
theorem be64_eq (m : Mem) (p : Addr) (off : Nat) :
    be64 m p off = AesCtr.rv64 (m.readW (p + BitVec.ofNat 64 off) 64) := by
  unfold be64 AesCtr.rv64
  have e : ∀ i < 8, m (p + BitVec.ofNat 64 (off + i)) =
      (m.readW (p + BitVec.ofNat 64 off) 64).extractLsb' (8 * i) 8 := fun i hi => by
    rw [Bytes.readW64_byte _ _ hi, Offset.add_add]
  have e0 : m (p + BitVec.ofNat 64 off) = (m.readW (p + BitVec.ofNat 64 off) 64).extractLsb' 0 8 := by
    simpa using e 0 (by decide)
  rw [e0, e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide)]

/-- `loadBE64`'s word, as a number: the eight bytes', big-endian. -/
theorem toNat_be64 (m : Mem) (p : Addr) (off : Nat) :
    (be64 m p off).toNat = toNat (bytesAt m (p + BitVec.ofNat 64 off) 8) := by
  rw [be64_eq, AesCtr.bytesAt_rv64, AesCtr.toNat_ofNat, Nat.mod_eq_of_lt (lt_256_8 _)]

/-- The last 32 bits of the counter block at `Q`, as `loadBE32` loads them. -/
theorem lo32_beWord (m : Mem) (Q : Addr) : AesCtr.lo32 (bytesAt m Q 16) = (beWord m Q 12).toNat := by
  rw [AesCtr.lo32_bytesAt, Proof.Aes.RISCV64.beWord_eq]
  rfl

/-- The bytes `storeBE 8` stores: the word's, big-endian. -/
theorem beBytes_eq (x : BitVec 64) : beBytes 8 x = ofNat x.toNat 8 := by
  unfold beBytes ofNat
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- The block at `Q` after its second half is replaced by `L + d` and its
first half by `H` plus the carry out of that, with `H` and `L` its halves
as numbers. -/
theorem add_halves (m : Mem) (Q : Addr) (H L : BitVec 64) (d : Nat)
    (hH : H.toNat = toNat (bytesAt m Q 8)) (hL : L.toNat = toNat (bytesAt m (Q + BitVec.ofNat 64 8) 8)) :
    ofNat ((H.toNat + (L.toNat + d) / 2 ^ 64) % 2 ^ 64) 8 ++ ofNat ((L.toNat + d) % 2 ^ 64) 8 =
      ofNat (toNat (bytesAt m Q 16) + d) 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append,
    show 8 + 8 = (bytesAt m Q 8).length + (bytesAt m (Q + BitVec.ofNat 64 8) 8).length by simp [bytesAt],
    AesCtr.ofNat_toNat_append_add]
  simp only [AesCcm.length_bytesAt]
  rw [← hH, ← hL]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [Nat.reducePow]; omega_arith)
  · exact AesCtr.ofNat_congr (by simp only [Nat.reducePow]; omega_arith)

/-- The counter block after both halves are written. -/
theorem bytesAt_halves (m : Mem) (Q : Addr) (H L : BitVec 64) :
    bytesAt (writeBytes (writeBytes m (Q + BitVec.ofNat 64 8) (beBytes 8 L)) (Q + BitVec.ofNat 64 0)
      (beBytes 8 H)) Q 16 = ofNat H.toNat 8 ++ ofNat L.toNat 8 := by
  rw [AesCcm.bytesAt_writeBytes_at _ _ _ (by simp [beBytes_length]) (by decide),
    AesCcm.bytesAt_writeBytes_at _ _ _ (by simp [beBytes_length]) (by decide)]
  simp [AesCcm.length_bytesAt, beBytes_eq, AesCtr.length_ofNat]

/-- The first half after the second is written. -/
theorem bytesAt_lo_write (m : Mem) (Q : Addr) (L : BitVec 64) :
    bytesAt (writeBytes m (Q + BitVec.ofNat 64 8) (beBytes 8 L)) (Q + BitVec.ofNat 64 0) 8 = bytesAt m Q 8 := by
  have e := AesCcm.bytesAt_writeBytes_at m Q (o := 8) (n := 16) (beBytes 8 L) (by simp [beBytes_length])
    (by decide)
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append, AesCtr.bytesAt_append m] at e
  have e' := congrArg (List.take 8) e
  rw [List.take_left' (by simp [AesCcm.length_bytesAt]),
    List.take_append_of_le_length (by simp [AesCcm.length_bytesAt]),
    List.take_append_of_le_length (by simp [AesCcm.length_bytesAt]),
    List.take_take, List.take_left' (by simp [AesCcm.length_bytesAt])] at e'
  simpa using e'

end VG.Proof.AesCtr.RISCV64
