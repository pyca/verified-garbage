module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupHash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupReads
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate

/-! Hash, shape, load, and test a subgroup candidate with one continuous witness tape. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure SubgroupResult (s₀ : State) (base : Addr) (bytes len candidate : Nat)
    (result : Option (Bool × List Byte)) (r : List Byte) (ptr : BitVec 32) (s : State) : Prop where
  tape : WitnessTape base bytes (s₀.gpr .esp) ptr r s
  cursor : s.mem.readW (off base witnessCursor) 32 = ptr
  remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length
  answer : match result with
    | none => s.gpr .eax = 0#32
    | some (b, rest) => r = rest ∧ s.gpr .eax = BitVec.ofNat 32 (if b then 1 else 3)
  candidate : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.q) len) = candidate
  frame : Frame [⟨base, bytes⟩, below (s₀.gpr .esp) 1184] s₀.mem s.mem
  regs : Keeps loopRegs s₀ s

theorem subgroup_ok (v : RoundImpl) {H : Hash} (ok : HashOK H) {s : State}
    {base : Addr} {bytes : Nat} {seed r : List Byte} {ptr : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (seedTape : WitnessTape base bytes (s.gpr .esp) (s.gpr .esi) seed s)
    (seedPositive : seed ≠ []) (seedSmall : seed.length < 2 ^ 32)
    (hash : ok.SH.H.hash seed = Spec.Dsa.seedHash (8 * H.D) seed)
    (digestLength : (Spec.Dsa.seedHash (8 * H.D) seed).length = H.D)
    (digestWidth : H.D = 20 ∨ H.D = 32)
    (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (startBound : r.length < 2 ^ 32) :
    WP isa (subgroup H v.name v.code seed.length) s fun t => ∃ rest next,
      SubgroupResult s base bytes H.D (Spec.Dsa.qCandidate (8 * H.D) seed)
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * H.D) seed) r) rest next t := by
  have lower : 4 ≤ H.D := by rcases digestWidth with h | h <;> omega
  have upper : H.D ≤ 32 := by rcases digestWidth with h | h <;> omega
  have aligned : H.D % 4 = 0 := by rcases digestWidth with h | h <;> rw [h]
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape (by omega : 2 ≤ 8 * H.D) seed
  have power : 8161 < 2 ^ (8 * H.D - 1) := by rcases digestWidth with h | h <;> rw [h] <;> decide
  unfold subgroup
  refine WP.seq (WP.mono (subgroup_hash ok scr capacity room seedTape seedPositive seedSmall
    hash digestLength rfl (by omega) upper) fun a ⟨value, F, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
  have stackA : StkOk (a.gpr .esp - 16#32) base bytes := by rw [K.1 .esp (by decide)]; exact stack
  have stage := subgroup_enclose F capacity room
  have tapeA : WitnessTape base bytes (a.gpr .esp) ptr r a := by
    rw [K.1 .esp (by decide)]
    exact tape.keep_enclosed stage K.2.1 K.2.2
  have controls := subgroup_control F capacity room
  refine WP.mono (check_candidate v Sa capacity Ra stackA tapeA
    (by rw [controls witnessCursor (by decide) (by decide)]; exact cursor)
    (by rw [controls witnessRemaining (by decide) (by decide)]; exact remaining)
    (by decide : 4 ≤ 4) (by decide : 4 ≤ 48) lower (by omega) aligned (by decide) (by unfold Layout.q; omega)
    value (Nat.lt_of_lt_of_le power shape.2.1) shape.1
    (VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega) seed)
    (by constructor <;> intro h <;> omega) startBound) fun t ⟨rest, next, R⟩ => ?_
  have finalTape := R.tape
  have finalFrame := sample_round_enclose R.frame capacity (by omega : H.D ≤ 384)
  rw [K.1 .esp (by decide)] at finalTape finalFrame
  refine ⟨rest, next, finalTape, R.cursor, R.remaining, R.answer, ?_, stage.trans finalFrame,
    (K.mono (by decide)).trans R.regs⟩
  rw [sample_saved_bytes R.frame capacity Ra (by decide) (by unfold Layout.q Layout.witness; omega) (by omega)]
  exact value

end VG.Proof.Dsa.X86.Generation
