module

public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.TCB.Arm.Isa

/-! Retain the key-generation ABI's domain, entropy, and two output pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure KeyIncoming (p : Inputs) (s : State) : Prop where
  domain : IncomingWord p.domain 128 s
  domainLength : IncomingWord (BitVec.ofNat 32 p.dom.length) 132 s
  count : IncomingWord (BitVec.ofNat 32 p.k) 136 s
  entropy : IncomingWord p.entropy 140 s
  scratch : IncomingWord p.base 148 s

theorem keyEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : KeyIncoming p s) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (outputY : p.output = p.publicValue)
    (privateLength : p.privateLength = p.k) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry) s fun t =>
      Context p [0, 48, 44, 32, 28, 24, 4, 36, 40] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  have rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  have args0 := h.of_mem moved.mem rest0
  have frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  have stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 40 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans privateValue) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  have rest1 := rest0.trans (stepRest1.mono (by simp))
  have stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  have frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r2 36 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r2 (by simp)).trans publicValue) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  have rest2 := rest1.trans (stepRest2.mono (by simp))
  have stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  have frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r2 4 args2 (by decide) (by decide) (by decide)
    (by change s2.gpr .r2 = p.output; rw [outputY]; exact (rest2.gpr .r2 (by simp)).trans publicValue) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  have rest3 := rest2.trans (stepRest3.mono (by simp))
  have stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  have frame3 := frame2.trans stepFrame3
  have allRest3 : Rest roundClobbers s s3 := rest3.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args3 (by decide)
    (incoming.domain.after (by decide) frame3 allRest3) (by decide) (by decide) (by decide) stack3
    fun s4 args4 stepFrame4 stepRest4 value4 stack4 => ?_
  have allRest4 := allRest3.trans (stepRest4.mono (by simp [roundClobbers]))
  rw [allRest3.sp] at stepFrame4
  have frame4 := frame3.trans stepFrame4
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.domainLength.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  have allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  have frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.count.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  have allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  have frame6 := frame5.trans stepFrame6
  refine wp_store_arg .r3 44 args6 (by decide) (by decide) (by decide)
    (by change s6.gpr .r3 = BitVec.ofNat 32 p.privateLength; rw [privateLength]; exact value6)
    stack6 fun s7 args7 stepFrame7 stepRest7 => ?_
  have stack7 := (stepRest7.gpr .r12 (by simp)).trans (stack6.trans stepRest7.sp.symm)
  have allRest7 := allRest6.trans (stepRest7.mono (by simp [roundClobbers]))
  rw [allRest6.sp] at stepFrame7
  have frame7 := frame6.trans stepFrame7
  refine wp_retain_incoming .r3 (by decide) args7 (by decide)
    (incoming.entropy.after (by decide) frame7 allRest7) (by decide) (by decide) (by decide) stack7
    fun s8 args8 stepFrame8 stepRest8 value8 stack8 => ?_
  have allRest8 := allRest7.trans (stepRest8.mono (by simp [roundClobbers]))
  rw [allRest7.sp] at stepFrame8
  have frame8 := frame7.trans stepFrame8
  refine wp_retain_incoming .r0 (by decide) args8 (by decide)
    (incoming.scratch.after (by decide) frame8 allRest8) (by decide) (by decide) (by decide) stack8
    fun s9 args9 stepFrame9 stepRest9 value9 stack9 => ?_
  apply WP.block_nil
  refine ⟨⟨args9, value9⟩, ?_⟩
  rw [allRest8.sp] at stepFrame9
  exact frame8.trans stepFrame9

end VG.Proof.Ffdh.Arm
