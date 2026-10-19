module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivCompareArgs
public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseTail
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Framework.Block

/-! # Compare the public re-exponentiation before releasing any private bytes -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure TailInput (dst tmp xp : BitVec 32) (k : Nat) (s : State) : Prop where
  release : ReleaseInput dst tmp k s
  workspace : Workspace s s.sp frameBytes
  input : s.mem.readW (off (State.addr s.sp) oIn) 32 = xp
  inputFit : xp.toNat + k ≤ 2 ^ 32
  inputRead : InRegions (s.rd ++ s.wr) (State.addr xp) k

theorem TailInput.of_mem {s t : State} {dst tmp xp : BitVec 32} {k : Nat} {rs : List Reg}
    (h : TailInput dst tmp xp k s) (mem : t.mem = s.mem) (rest : Rest rs s t) : TailInput dst tmp xp k t :=
  ⟨h.release.of_mem mem rest, by rw [rest.sp]; exact h.workspace.congr rest.wr,
    by rw [mem, rest.sp]; exact h.input, h.inputFit, by rw [rest.rd, rest.wr]; exact h.inputRead⟩

def tailAccepted (s : State) : Bool := decide (successBits (s.gpr .r0)
  (s.mem.readW (off (State.addr s.sp) oR1) 32) (s.mem.readW (off (State.addr s.sp) oR3) 32) = 1)
def tailEqual (s : State) (dst xp : BitVec 32) (k : Nat) : Bool :=
  decide (Spec.Rsa.bytesAt s.mem (State.addr dst) k = Spec.Rsa.bytesAt s.mem (State.addr xp) k)

theorem tail_ok (s : State) {dst tmp xp : BitVec 32} {k : Nat} (h : TailInput dst tmp xp k s) :
    WP isa tail s fun t =>
      t.gpr .r0 = (if tailAccepted s then if tailEqual s dst xp k then 1 else 2 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if tailAccepted s && tailEqual s dst xp k then Spec.Rsa.bytesAt s.mem (State.addr tmp) k else List.replicate k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr tmp) k = List.replicate k 0 ∧
      Frame [⟨State.addr dst, k⟩, ⟨State.addr tmp, k⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r12, .lr] s t := by
  rw [tail, WP.seq_iff]
  refine WP.mono (cmpArgs_ok s h.workspace) ?_
  rintro u ⟨output, input, count, zero, good, memU, restU⟩
  have outRead : InRegions (s.rd ++ s.wr) (State.addr dst) k := by
    obtain ⟨r, hr, hc⟩ := h.release.outputWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [WP.seq_iff]
  refine WP.mono (compareBuffer_ok u h.release.positive h.release.countFit h.release.outputFit h.inputFit
    (by rw [restU.rd, restU.wr]; exact outRead) (by rw [restU.rd, restU.wr]; exact h.inputRead)
    (output.trans h.release.output) (input.trans h.input) (count.trans h.release.count) zero) ?_
  rintro v ⟨equal, memV, restV⟩
  have goodV : v.gpr .r4 = BitVec.ofNat 32 (tailAccepted s).toNat := by
    rw [restV.gpr .r4 (by simp), good]
    unfold tailAccepted
    rcases successBits_cases (s.gpr .r0) (s.mem.readW (off (State.addr s.sp) oR1) 32)
      (s.mem.readW (off (State.addr s.sp) oR3) 32) with hz | ho
    · rw [hz]; rfl
    · rw [ho]; rfl
  have eqV : (v.gpr .r2 = 0) ↔ tailEqual s dst xp k = true := by
    rw [equal, memU]
    simp only [tailEqual, decide_eq_true_eq]
  have inputV := (h.release.of_mem memU restU).of_mem memV restV
  refine WP.mono (releaseTail_ok v inputV goodV eqV) ?_
  rintro t ⟨status, bytes, cleared, frame, rest⟩
  rw [memV, memU] at bytes frame
  exact ⟨status, bytes, cleared, frame,
    (restU.mono (by simp)).trans ((restV.mono (by simp)).trans rest)⟩
end VG.Proof.Rsa.Arm
