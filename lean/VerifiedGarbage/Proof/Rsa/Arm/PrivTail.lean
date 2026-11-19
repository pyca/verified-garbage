module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.Rsa.SuccessBits32
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask

/-! ### `Rsa.Arm.PrivReleaseTail`, which this module and modules that import it used -/

section

/-! # Fault status, branchless release, and temporary erasure as one verified stage -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

structure ReleaseInput (dst tmp : BitVec 32) (k : Nat) (s : State) : Prop where
  positive : 0 < k
  countFit : k < 2 ^ 32
  stackFit : s.sp.toNat + 76 ≤ 2 ^ 32
  outRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) oOut) 4
  countRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) oK) 4
  output : s.mem.readW (off (State.addr s.sp) oOut) 32 = dst
  count : s.mem.readW (off (State.addr s.sp) oK) 32 = BitVec.ofNat 32 k
  temp : s.sp + BitVec.ofNat 32 oM = tmp
  tempFit : tmp.toNat + k ≤ 2 ^ 32
  outputFit : dst.toNat + k ≤ 2 ^ 32
  tempWrite : InRegions s.wr (State.addr tmp) k
  outputWrite : InRegions s.wr (State.addr dst) k
  separate : Region.Disjoint ⟨State.addr tmp, k⟩ ⟨State.addr dst, k⟩

theorem ReleaseInput.of_mem {s t : State} {dst tmp : BitVec 32} {k : Nat} {rs : List Reg}
    (h : ReleaseInput dst tmp k s) (mem : t.mem = s.mem) (rest : Rest rs s t) : ReleaseInput dst tmp k t :=
  ⟨h.positive, h.countFit, by rw [rest.sp]; exact h.stackFit,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.outRead,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.countRead,
    by rw [mem, rest.sp]; exact h.output, by rw [mem, rest.sp]; exact h.count,
    by rw [rest.sp]; exact h.temp, h.tempFit, h.outputFit,
    by rw [rest.wr]; exact h.tempWrite, by rw [rest.wr]; exact h.outputWrite, h.separate⟩

theorem releaseTail_ok (s : State) {dst tmp : BitVec 32} {k : Nat} {accepted equal : Bool}
    (h : ReleaseInput dst tmp k s) (good : s.gpr .r4 = BitVec.ofNat 32 accepted.toNat)
    (eq : (s.gpr .r2 = 0) ↔ equal = true) :
    WP isa releaseTail s fun t =>
      t.gpr .r0 = (if accepted then if equal then 1 else 2 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if accepted && equal then Spec.Rsa.bytesAt s.mem (State.addr tmp) k else List.replicate k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr tmp) k = List.replicate k 0 ∧
      Frame [⟨State.addr dst, k⟩, ⟨State.addr tmp, k⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r12, .lr] s t := by
  rw [releaseTail, WP.seq_iff]
  refine WP.mono (maskCore_ok s good eq) ?_
  rintro u ⟨mask, status, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (releaseArgs_ok u (by rw [restU.sp]; exact h.stackFit)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.outRead)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.countRead)) ?_
  rintro v ⟨output, temp, count, zero, memV, restV⟩
  have outV : v.gpr .r0 = dst := by rw [output, memU, restU.sp]; exact h.output
  have tmpV : v.gpr .r1 = tmp := by rw [temp, restU.sp]; exact h.temp
  have countV : v.gpr .lr = BitVec.ofNat 32 k := by rw [count, memU, restU.sp]; exact h.count
  rw [WP.seq_iff]
  refine WP.mono (releaseBuffer_ok v h.positive h.countFit h.tempFit h.outputFit
    (by rw [restV.wr, restU.wr]; exact h.tempWrite)
    (by rw [restV.wr, restU.wr]; exact h.outputWrite) h.separate tmpV outV countV
    ((restV.gpr .r2 (by simp)).trans mask) zero) ?_
  rintro z ⟨bytes, cleared, frame, restZ⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [moved.gpr, restZ.gpr .r4 (by simp), restV.gpr .r4 (by simp), status]
  · rw [moved.mem, bytes, memV, memU]
  · rw [moved.mem]; exact cleared
  · rw [moved.mem]
    rw [memV, memU] at frame
    exact frame
  · exact (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
      ((restZ.mono (by simp)).trans (moved.rest (by simp))))
end VG.Proof.Rsa.Arm

end

end

/-! ### `Rsa.Arm.PrivCompareArgs`, which only this module used -/

section

/-! # Set up the private fault comparison and accumulate the three call-status bits -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_reg op2_imm dpVal)

abbrev successBits := VG.Proof.Rsa.successBits

theorem successBits_cases (r2 r1 r3 : BitVec 32) : successBits r2 r1 r3 = 0 ∨ successBits r2 r1 r3 = 1 :=
  VG.Proof.Rsa.successBits_cases r2 r1 r3

theorem cmpArgs_ok (s : State) (ws : Workspace s s.sp frameBytes) :
    WP isa (.block cmpArgs) s fun t =>
      t.gpr .r0 = s.mem.readW (off (State.addr s.sp) oOut) 32 ∧
      t.gpr .r1 = s.mem.readW (off (State.addr s.sp) oIn) 32 ∧
      t.gpr .lr = s.mem.readW (off (State.addr s.sp) oK) 32 ∧ t.gpr .r2 = 0 ∧
      t.gpr .r4 = successBits (s.gpr .r0) (s.mem.readW (off (State.addr s.sp) oR1) 32)
        (s.mem.readW (off (State.addr s.sp) oR3) 32) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .lr] s t := by
  have fit := ws.nowrap
  unfold cmpArgs
  refine wp_loadStack (a := off (State.addr s.sp) oR1) (by decide)
    (addr_add (by simp only [oR1, frameBytes] at *; omega_using [fit])) (ws.read (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oR3) (by decide)
    (by rw [u2.sp, u1.sp]; exact addr_add (by simp only [oR3, frameBytes] at *; omega_using [fit]))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  have status : s5.gpr .r4 = successBits (s.gpr .r0) (s.mem.readW (off (State.addr s.sp) oR1) 32)
      (s.mem.readW (off (State.addr s.sp) oR3) 32) := by
    rw [u5.gpr, dpVal, u4.gpr, dpVal, u3.other .r4 (by decide), u2.gpr, dpVal,
      u1.gpr, u1.other .r0 (by decide), u3.gpr, u2.mem, u1.mem]
    rfl
  have keep5 : Rest [.r3, .r4] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
  have mem5 : s5.mem = s.mem := u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))
  refine wp_loadStack (a := off (State.addr s.sp) oOut) (by decide)
    (by rw [keep5.sp]; exact addr_add (by simp only [oOut, frameBytes] at *; omega_using [fit]))
    (by rw [keep5.rd, keep5.wr]; exact ws.read (by decide)) fun s6 u6 => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oIn) (by decide)
    (by rw [u6.sp, keep5.sp]; exact addr_add (by simp only [oIn, frameBytes] at *; omega_using [fit]))
    (by rw [u6.rd, u6.wr, keep5.rd, keep5.wr]; exact ws.read (by decide)) fun s7 u7 => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oK) (by decide)
    (by rw [u7.sp, u6.sp, keep5.sp]; exact addr_add (by simp only [oK, frameBytes] at *; omega_using [fit]))
    (by rw [u7.rd, u7.wr, u6.rd, u6.wr, keep5.rd, keep5.wr]; exact ws.read (by decide)) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u9 => WP.block_nil ?_
  exact ⟨by rw [u9.other .r0 (by decide), u8.other .r0 (by decide), u7.other .r0 (by decide), u6.gpr, mem5],
    by rw [u9.other .r1 (by decide), u8.other .r1 (by decide), u7.gpr, u6.mem, mem5],
    by rw [u9.other .lr (by decide), u8.gpr, u7.mem, u6.mem, mem5], u9.gpr,
    by rw [u9.other .r4 (by decide), u8.other .r4 (by decide), u7.other .r4 (by decide), u6.other .r4 (by decide), status],
    u9.mem.trans (u8.mem.trans (u7.mem.trans (u6.mem.trans mem5))),
    (keep5.mono (by simp)).trans ((u6.rest (by simp)).trans
      ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))⟩
end VG.Proof.Rsa.Arm

end

end


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
