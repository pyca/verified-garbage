module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TableWrites
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy

/-! Read one bounded RSA prime entry and advance the sieve cursor. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

private theorem advance (base : BitVec 32) (offset i : Nat) :
    (base + BitVec.ofNat 32 (offset + 4 * i)) + 4 = base + BitVec.ofNat 32 (offset + 4 * (i + 1)) := by
  change (base + BitVec.ofNat 32 (offset + 4 * i)) + BitVec.ofNat 32 4 = _
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have equal : offset + 4 * i + 4 = offset + 4 * (i + 1) := by omega
  rw [equal]

theorem sieveEntry_ok {s : State} {dst base : BitVec 32} {n i : Nat}
    (h : SieveContext dst base n s) (bound : i < (trialCount n))
    (cursor : s.gpr .r10 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * i)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveEntry) s fun t =>
      (t.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry i) ∧
        t.gpr .r10 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * (i + 1)) ∧ t.mem = s.mem) ∧
        Rest [.r7, .r10] s t := by
  have limitBound := trialCount_bound n
  have indexBound : i < 1024 := by omega
  have read := h.tableReadable i indexBound
  have word : s.mem.readW (off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i)) 32 =
      BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := tableEntry_small indexBound; omega :
      VG.Impl.RsaKeyGen.tabEntry i < 2 ^ 32)]
    exact h.table i indexBound
  have address : State.addr (base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * i)) =
      off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i) :=
    VG.Arm.addr_add (by have := h.tableFits; omega)
  refine withRest_all [.r7, .r10] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveEntry
  ffrun [BitVec.add_zero, cursor, address, read, word, advance base (arrAt ((n + 7) / 8) 34) i]

end VG.Proof.Ffdh.Arm.ParameterCandidate
