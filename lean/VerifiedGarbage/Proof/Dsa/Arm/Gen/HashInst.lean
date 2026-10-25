module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Hash
public import VerifiedGarbage.Proof.Sha1.Arm.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on ARMv7: SHA-1 and SHA-256

The two hash functions of parameter generation (`Impl.Dsa.Arm.Generation.sha1`,
`sha256`) as `HashOk`: their streaming instances, their compression
functions' proofs, and the hash of a message of fewer than 56 bytes as the
compression of its one padded block (`hash_blk`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation

/-- A message of fewer than 56 bytes pads to one block, `blk`. -/
theorem hash_blk {N : Nat} (md : MdStream.Md 64 N 8) (iv : md.HV) {msg : List Byte} (h : msg.length < 56) :
    md.hash iv msg = md.digest (md.compress iv (md.parse fun t => (blk md msg).getD t 0)) := by
  have hp : md.pad msg = blk md msg := by
    simp only [MdStream.Md.pad, blk, Nat.mod_eq_of_lt (show msg.length < 64 by omega)]
    rw [show (2 * 64 - 8 - 1 - msg.length) % 64 = 55 - msg.length by omega]
  have hl : (blk md msg).length = 64 := by
    simp only [blk, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      md.lenBytes_length]
    omega
  rw [MdStream.Md.hash, hp, hl, Nat.div_self (by decide), MdStream.Md.compressList_one]

def sha1Ok : HashOk sha1 where
  P := Impl.Sha1.Arm.Stream.params
  md := Proof.Sha1.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := rfl
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha1.Arm.Stream.callee
  ct := Proof.Sha1.Arm.compress_verified.2.1
  H0 := Spec.Sha1.H0
  iv m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    rw [h j (by simpa [sha1] using hj)]
    simp [sha1]
  digest := Proof.Sha1.digest_eq
  H := Spec.Sha1.hash
  hash msg h := (Proof.Sha1.hash_eq msg).trans (hash_blk _ _ h)
  cert1 L := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
    (.block (scr 128 .r0 sState ++ ivStore sha1.iv ++ scr 128 .r1 sMsg ++ scr 128 .r3 sA)), by kernel_rfl⟩
  cert3 L dst := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r8])
    (.block (scr 128 .r6 192 ++ VG.Impl.MdStream.Arm.out32 5 true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (128 / 4)))])),
    by kernel_rfl⟩

def sha256Ok : HashOk sha256 where
  P := Impl.Sha256.Arm.Stream.params
  md := Proof.Sha256.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := rfl
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha256.Arm.Stream.callee
  ct := Proof.Sha256.Arm.compress_verified.2.1
  H0 := Spec.Sha256.H0
  iv m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    rw [h j (by simpa [sha256] using hj)]
    simp [sha256]
  digest := Proof.Sha256.digest_eq
  H := Spec.Sha256.hash
  hash msg h := (Proof.Sha256.hash_eq msg).trans (hash_blk _ _ h)
  cert1 L := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
    (.block (scr 128 .r0 sState ++ ivStore sha256.iv ++ scr 128 .r1 sMsg ++ scr 128 .r3 sA)), by kernel_rfl⟩
  cert3 L dst := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r8])
    (.block (scr 128 .r6 192 ++ VG.Impl.MdStream.Arm.out32 8 true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (128 / 4)))])),
    by kernel_rfl⟩

end VG.Proof.Dsa.Arm.Gen
