module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportBufferMasked
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Exact accepted output and zero rejected output from a wide CRT buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure ExportBufferInput (src dst : BitVec 32) (n k : Nat) (accepted : Bool) (s : State) : Prop where
  positive : 0 < k
  prefixFits : k ≤ n
  sourceFits : src.toNat + k ≤ 2 ^ 32
  outputFits : dst.toNat + k ≤ 2 ^ 32
  countFits : k < 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr src) k
  write : InRegions s.wr (State.addr dst) k
  separate : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr dst, k⟩
  source : s.gpr .r1 = src
  output : s.gpr .r4 = dst
  count : s.gpr .r6 = BitVec.ofNat 32 k
  valueFits : accepted = true → (s.mem.read (State.addr src) n).toNat < 2 ^ (8 * k)
  stackFits : s.sp.toNat + 52 ≤ 2 ^ 32
  stackRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4
  stackSep : Region.Disjoint ⟨off (State.addr s.sp) 48, 4⟩ ⟨State.addr dst, k⟩
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat

theorem exportBuffer_ok (s : State) {src dst : BitVec 32} {n k : Nat} {accepted : Bool}
    (h : ExportBufferInput src dst n k accepted s) :
    WP isa exportBuffer s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k = Spec.Rsa.i2osp (s.mem.read (State.addr src) k).toNat k ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r5, .lr] s t := by
  rw [exportBuffer, WP.seq_iff]
  refine WP.mono (exportBETail_ok s h.positive h.count) ?_
  rintro u ⟨output, source, count, _, memU, restU⟩
  rw [h.source] at source
  refine WP.mono (reverseBuffer_ok u h.positive h.sourceFits h.outputFits h.countFits
    (by rw [restU.rd, restU.wr]; exact h.read) (by rw [restU.wr]; exact h.write)
    h.separate (output.trans h.output) source count) ?_
  rintro v ⟨bytes, frame, _, restV⟩
  rw [memU] at bytes frame
  have rest : Rest [.r0, .r1, .r2, .r5, .lr] s v :=
    (restU.mono (by decide)).trans (restV.mono (by decide))
  exact ⟨bytes, frame, rest⟩

theorem exportBufferMasked_ok (s : State) {src dst : BitVec 32} {n k : Nat} {accepted : Bool}
    (h : ExportBufferInput src dst n k accepted s) :
    WP isa exportBufferMasked s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if accepted then Spec.Rsa.i2osp (s.mem.read (State.addr src) n).toNat k else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 accepted.toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [exportBufferMasked, WP.seq_iff]
  refine WP.mono (exportBuffer_ok s h) ?_
  rintro v ⟨bytes, frame, rest⟩
  have eq := WorkspaceEq.of_frame (by decide : 4 < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackSep)
  have flag : v.mem.readW (off (State.addr v.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat := by
    rw [rest.sp]
    have keep := eq.word (d := 0) (bits := 32) (by decide)
    simp only [off, BitVec.add_zero] at keep
    exact keep.trans h.flag
  refine WP.mono (maskOutput_ok v h.positive h.countFits h.outputFits
    (by rw [rest.wr]; exact h.write) (by rw [rest.sp]; exact h.stackFits)
    (by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead) flag
    ((rest.gpr .r4 (by decide)).trans h.output) ((rest.gpr .r6 (by decide)).trans h.count)) ?_
  rintro t ⟨value, status, frameT, restT⟩
  rw [bytes] at value
  refine ⟨?_, status, frame.trans frameT,
    (rest.mono (by decide)).trans (restT.mono (by decide))⟩
  cases accepted with
  | false => exact value
  | true =>
    rw [read_prefix_value s.mem _ h.prefixFits (h.valueFits rfl)] at value
    exact value

end VG.Proof.Bignum.Arm
