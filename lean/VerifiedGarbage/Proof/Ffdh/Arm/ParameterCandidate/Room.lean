module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Native entropy guards compare unsigned byte counts without wrapping
the subtraction of bytes already consumed. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem geFlag_ok (s : State) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.geFlag) s fun t =>
      (t.z = decide ((s.gpr .r1).toNat < (s.gpr .r2).toNat) ∧ t.mem = s.mem) ∧ Rest [.r3] s t := by
  refine withRest [.r3] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.geFlag : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.geFlag
  by_cases ge : (s.gpr .r2).toNat ≤ (s.gpr .r1).toNat
  · have lt : ¬ (s.gpr .r1).toNat < (s.gpr .r2).toNat := by omega
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]
  · have lt : (s.gpr .r1).toNat < (s.gpr .r2).toNat := by omega
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]

private theorem initialHead_ok {s : State} {length width : Nat} (stack : Workspace s s.sp 72)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block [.ldrSp .r1 20, .ldrSp .r2 12]) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 length ∧ t.gpr .r2 = BitVec.ofNat 32 width ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2] s t := by
  have reads (d : Nat) (fit : d + 4 ≤ 72) : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read fit
  refine withRest [.r1, .r2] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.ldrSp .r1 20, .ldrSp .r2 12] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  ffrun [BitVec.add_zero, reads 20 (by decide), reads 12 (by decide), savedLength, savedWidth]

theorem initialRoom_ok {s : State} {length width : Nat} (stack : Workspace s s.sp 72)
    (lengthBound : length < 2 ^ 32) (widthBound : width < 2 ^ 32)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) s fun t =>
      (t.z = decide (length < width) ∧ t.mem = s.mem) ∧ Rest [.r1, .r2, .r3] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom, WP.block_append_iff]
  refine WP.mono (initialHead_ok stack savedLength savedWidth) ?_
  rintro u ⟨⟨lenU, widthU, memU⟩, restU⟩
  refine WP.mono (geFlag_ok u) ?_
  rintro t ⟨⟨zeroT, memT⟩, restT⟩
  rw [lenU, widthU, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound,
    Nat.mod_eq_of_lt widthBound] at zeroT
  exact ⟨⟨zeroT, memT.trans memU⟩, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

private theorem witnessHead_ok {s : State} {length used width : Nat} (stack : Workspace s s.sp 72)
    (lengthBound : length < 2 ^ 32) (enough : used ≤ length)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedUsed : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used)
    (savedWidth : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block [.ldrSp .r1 20, .ldrSp .r2 40, .dp .sub .r1 .r1 (.reg .r2), .ldrSp .r2 48]) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 (length - used) ∧ t.gpr .r2 = BitVec.ofNat 32 width ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2] s t := by
  have reads (d : Nat) (fit : d + 4 ≤ 72) : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read fit
  have subtract : BitVec.ofNat 32 length - BitVec.ofNat 32 used = BitVec.ofNat 32 (length - used) := by
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) enough
  refine withRest [.r1, .r2] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.ldrSp .r1 20, .ldrSp .r2 40, .dp .sub .r1 .r1 (.reg .r2), .ldrSp .r2 48] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  ffrun [BitVec.add_zero, reads 20 (by decide), reads 40 (by decide), reads 48 (by decide),
    savedLength, savedUsed, savedWidth, subtract]

theorem witnessRoom_ok {s : State} {length used width : Nat} (stack : Workspace s s.sp 72)
    (lengthBound : length < 2 ^ 32) (widthBound : width < 2 ^ 32) (enough : used ≤ length)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedUsed : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used)
    (savedWidth : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) s fun t =>
      (t.z = decide (length - used < width) ∧ t.mem = s.mem) ∧ Rest [.r1, .r2, .r3] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom, WP.block_append_iff]
  refine WP.mono (witnessHead_ok stack lengthBound enough savedLength savedUsed savedWidth) ?_
  rintro u ⟨⟨lenU, widthU, memU⟩, restU⟩
  refine WP.mono (geFlag_ok u) ?_
  rintro t ⟨⟨zeroT, memT⟩, restT⟩
  rw [lenU, widthU, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : length - used < 2 ^ 32),
    Nat.mod_eq_of_lt widthBound] at zeroT
  exact ⟨⟨zeroT, memT.trans memU⟩, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
