module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskBits
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskStore
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut32
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Exact native witness truncation, using RSA's fixed-step word-mask
construction and the existing packed Montgomery operand. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt arrAt Keeps)

theorem witnessMask_ok {s : State} {base : BitVec 32} {capacity w bits : Nat}
    (ready : ArithmeticReady base capacity w s) (stack : Workspace s s.sp 72)
    (positive : 0 < bits) (bound : bits ≤ 8192) (fitsBits : bits ≤ 64 * w)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits)
    (small : numAt s.mem (State.addr base) w 1 < 2 ^ (32 * ((bits - 1) / 32 + 1))) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask s fun t =>
      ArithmeticReady base capacity w t ∧
      numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 % 2 ^ bits ∧
      Keeps (State.addr base) capacity w 1 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let j := (bits - 1) / 32
  let k := (bits - 1) % 32 + 1
  have geometry := witness_geometry positive fitsBits
  have jBound : j < 2 * w := geometry.1
  have kBound : k ≤ 32 := geometry.2.1
  have bitWidth : 32 * j + k = bits := geometry.2.2.1
  have fit : arrAt w 1 + 8 * (w + 2) ≤ 8 * capacity :=
    Nat.le_trans (array_end_le (w := w) (j := 1) (k := 8) (by decide)) (ready.width ▸ ready.layout.2.2.1)
  have nowrap := ready.workspace.nowrap
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (witnessMaskHead_ok stack positive bound saved) ?_)
  rintro u ⟨⟨indexU, countU, memU⟩, restU⟩
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  refine WP.seq (WP.mono (witnessMaskBits_ok kBound countU) ?_)
  rintro v ⟨maskV, memV, restV⟩
  have readyV := readyU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans readyU.ptr)
  have indexV : v.gpr .r5 = BitVec.ofNat 32 j := (restV.gpr .r5 (by simp)).trans indexU
  refine WP.seq (WP.mono (witnessMaskStore_ok readyV jBound indexV) ?_)
  rintro t ⟨⟨memT, ptrT⟩, restT⟩
  rw [maskV, memV, memU] at memT
  have outside := writeW32_outside s.mem (State.addr base)
    (s.mem.readW (off (State.addr base) (arrAt w 1 + 4 * j)) 32 &&& BitVec.ofNat 32 (2 ^ k - 1))
    (d := arrAt w 1 + 4 * j) (by omega)
  rw [← memT] at outside
  have wide := outside.mono (o' := arrAt w 1) (n' := 8 * w) (by omega) (by omega)
  have keeps := outside_array_keeps wide (len := capacity) (by omega)
  have frame := outside_workspace wide (size := 8 * capacity) (by omega)
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    ((restV.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers])))
  have value : numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 % 2 ^ bits := by
    rw [numAt_native, numAt_native, ← bitWidth]
    apply VG.Proof.Ffdh.ParameterCandidate.val32_cut kBound
    · rwa [← numAt_native]
    · rw [memT, Mem.readW_writeW_self32]
    · intro i bound different
      rw [memT, Mem.readW_writeW_sep (w := 32) (w' := 32)
        (Offset.sep _ (d := arrAt w 1 + 4 * i) (n := 4) (e := arrAt w 1 + 4 * j) (k := 4)
          (by omega) (by omega) (by omega)) (by decide)]
  exact WP.block_nil ⟨(ready.after_array (by decide) keeps frame rest ptrT).1, value, keeps, frame, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
