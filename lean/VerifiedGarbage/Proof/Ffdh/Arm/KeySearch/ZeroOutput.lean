module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The native retry controller clears rejected or incomplete outputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem zeroOutputArgs_ok (s : State) {base dst : BitVec 32} {j n : Nat}
    (h : Controller base s) (slot : j < 16)
    (pointer : lowWord s.mem base j = dst) (length : lowWord s.mem base 2 = BitVec.ofNat 32 n) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 j,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .lr 2, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
      Rest [.r0, .r2, .lr] s t := by
  refine withRest [.r0, .r2, .lr] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 j,
        VG.Impl.Ffdh.Arm.KeySearch.ldf .lr 2, .mov .r2 (.imm 0)] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [(by omega : 8 * j < 4096), h.addr slot, h.read slot,
    h.addr (by decide : 2 < 16), h.read (by decide : 2 < 16), pointer, length]

theorem zeroOutput_ok (s : State) {base dst : BitVec 32} {j n : Nat}
    (h : Controller base s) (slot : j < 16) (positive : 0 < n) (fits : n < 2 ^ 32)
    (pointer : lowWord s.mem base j = dst) (length : lowWord s.mem base 2 = BitVec.ofNat 32 n)
    (output : VG.Proof.Ffdh.Arm.OutputBuffer dst n s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.zeroOutput j) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.zeroOutput, WP.seq_iff]
  refine WP.mono (zeroOutputArgs_ok s h slot pointer length) ?_
  rintro u ⟨⟨ptr, count, zero, mem⟩, restU⟩
  refine WP.mono (zeroBuffer_ok false u positive fits output.fits
    (by rw [restU.wr]; exact output.writable) zero (src := u.gpr .r1) rfl ptr count) ?_
  rintro t ⟨bytes, _, _, frame, rest⟩
  exact ⟨bytes, by rw [mem] at frame; exact frame,
    (restU.mono (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.KeySearch
