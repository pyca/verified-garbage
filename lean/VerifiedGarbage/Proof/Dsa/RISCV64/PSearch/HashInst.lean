module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Hash
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha1.RISCV64.Compress
public import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
public import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: only the search's instances import it, and it imports both compression functions' proofs

/-! # DSA parameter search on RISC-V: SHA-1 and SHA-256

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/HashInst.lean`). The two hash
functions of parameter generation (`Impl.Dsa.RISCV64.ParameterSearch.sha1`,
`sha256`) as `HashOk`: their compression functions' proofs, and the hash of a
message of fewer than 56 bytes as the compression of its one padded block
(`hash_blk`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.Proof.MdStream.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch

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

theorem sha256_callee : CalleeOk Proof.Sha256.md Impl.Sha256.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha256.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha256.RISCV64.Stream.compress_noFrames⟩

def sha1Ok : HashOk sha1 where
  md := Proof.Sha1.md
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha1.RISCV64.Stream.callee
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp := Proof.Sha1.RISCV64.compress_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂'
    ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1⟩ ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2.1⟩ hp
  H0 := Spec.Sha1.H0
  iv m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    rw [h j (by simpa [sha1] using hj), getElem!_pos _ j (by simpa [sha1] using hj)]
    simp [sha1]
  digest := Proof.Sha1.digest_eq
  H := Spec.Sha1.hash
  hash msg h := (Proof.Sha1.hash_eq msg).trans (hash_blk _ _ h)
  cert1 := ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.seq (.block [scr .a0 sState]) (Impl.MdStream.RISCV64.initWords sha1.iv)), by kernel_rfl⟩
  cert3 dst := ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.block ([scr .s1 sState, scr .s3 dst] ++ Impl.MdStream.RISCV64.outBE 5)), by kernel_rfl⟩

def sha256Ok : HashOk sha256 where
  md := Proof.Sha256.md
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := sha256_callee
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp := Proof.Sha256.RISCV64.compress_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂'
    ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1⟩ ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2.1⟩ hp
  H0 := Spec.Sha256.H0
  iv m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    rw [h j (by simpa [sha256] using hj), getElem!_pos _ j (by simpa [sha256] using hj)]
    simp [sha256]
  digest := Proof.Sha256.digest_eq
  H := Spec.Sha256.hash
  hash msg h := (Proof.Sha256.hash_eq msg).trans (hash_blk _ _ h)
  cert1 := ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.seq (.block [scr .a0 sState]) (Impl.MdStream.RISCV64.initWords sha256.iv)), by kernel_rfl⟩
  cert3 dst := ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.block ([scr .s1 sState, scr .s3 dst] ++ Impl.MdStream.RISCV64.outBE 8)), by kernel_rfl⟩

theorem sha1_length (bs : List Byte) : (Spec.Sha1.hash bs).length = 20 := by
  rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _

theorem sha256_length (bs : List Byte) : (Spec.Sha256.hash bs).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

end VG.Proof.Dsa.RISCV64.PSearch
