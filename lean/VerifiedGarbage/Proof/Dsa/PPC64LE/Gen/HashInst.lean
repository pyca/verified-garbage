module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Hash
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: SHA-1 and SHA-256

The two hash functions of parameter generation (`Impl.Dsa.PPC64LE.Generation.sha1`,
`sha256`) as `HashOk`: the parameters of the streaming code (SHA-1's own;
for SHA-256, whose streaming code is its own, `sha256Params`), their
compression functions' proofs, and the hash of a message of fewer than 56
bytes as the compression of its one padded block (`hash_blk`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

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

/-- SHA-256's compression function as the streaming code's callee. -/
def sha256Params : VG.Impl.MdStream.PPC64LE.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := VG.Impl.MdStream.PPC64LE.len64 88 true
  out := VG.Impl.MdStream.PPC64LE.out32 8 true

theorem sha256_callee : VG.Proof.MdStream.PPC64LE.CalleeOk (P := sha256Params) Proof.Sha256.md
    Impl.Sha256.PPC64LE.compress :=
  ⟨Proof.Sha256.PPC64LE.compress_verified.1, by decide +kernel⟩

def sha1Ok : HashOk sha1 where
  P := Impl.Sha1.PPC64LE.Stream.params
  md := Proof.Sha1.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := by decide
  hso0 := by decide
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha1.PPC64LE.Stream.callee
  ct := Proof.Sha1.PPC64LE.compress_verified.2.1
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
  cert1 L := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block (ivStore sha1.iv ++ [scr .r26 sState, scr .r27 (wB L), scr .r4 sMsg])), rfl⟩
  cert3 dst := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r26])
    (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 5 true ++ [.subi .r28 .r28 dst])), rfl⟩

def sha256Ok : HashOk sha256 where
  P := sha256Params
  md := Proof.Sha256.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := by decide
  hso0 := by decide
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := sha256_callee
  ct := Proof.Sha256.PPC64LE.compress_verified.2.1
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
  cert1 L := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block (ivStore sha256.iv ++ [scr .r26 sState, scr .r27 (wB L), scr .r4 sMsg])), rfl⟩
  cert3 dst := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r26])
    (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 8 true ++ [.subi .r28 .r28 dst])), rfl⟩

theorem sha1_length (bs : List Byte) : (Spec.Sha1.hash bs).length = 20 := by
  rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _

theorem sha256_length (bs : List Byte) : (Spec.Sha256.hash bs).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

end VG.Proof.Dsa.PPC64LE.Gen
