module
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Taint


/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): argument words

Byte `k` of the arguments, as a byte of the argument word holding it: what
the taint analyses of `update` and `finalize` read their arguments by.
-/

@[expose] public section

namespace VG.Proof.MdStream.X86

open VG VG.X86

theorem argWord_eq {s : State} {n : Nat} (hsp : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.MdStream.X86
