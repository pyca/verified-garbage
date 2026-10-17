module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveResult
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyRetained
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
public import VerifiedGarbage.Proof.Rsa.Arm.PrivStoreTemporary
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Prepare all six stack arguments for the public re-exponentiation check -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def pdPrefixMem (g : PrivGeometry) (s : State) : Mem :=
  ((((((s.mem.writeW (off (State.addr g.stack) oR3) (s.gpr .r0)).writeW
    (off (State.addr g.stack) 0) (g.sources 1)).writeW
    (off (State.addr g.stack) 4) (BitVec.ofNat 32 g.exponentLength)).writeW
    (off (State.addr g.stack) 8) g.temporary).writeW
    (off (State.addr g.stack) 12) (BitVec.ofNat 32 g.length)).writeW
    (off (State.addr g.stack) 16) g.workspace).writeW
    (off (State.addr g.stack) 20) (BitVec.ofNat 32 g.scratchLength)

def pdPrefixWrites (g : PrivGeometry) : List Region :=
  [⟨State.addr g.stack, 24⟩, ⟨off (State.addr g.stack) oR3, 4⟩]

theorem pdPrefix_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pdPrefix) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.mem = pdPrefixMem g s ∧ Frame (pdPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  unfold pdPrefix
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveResult_ok s h slots (by decide : 88 ≤ oR3) (by decide : oR3 + 4 ≤ 96)) ?_
  rintro s0 ⟨h0, slots0, ptr0, mem0, frame0, rest0⟩
  refine WP.mono (copyRetained_ok s0 h0 slots0 (by decide : 3 < 6) (by decide : 0 + 4 ≤ 56) ptr0) ?_
  rintro s1 ⟨h1, slots1, mem1, frame1, rest1⟩
  have ptr1 : s1.gpr .r12 = g.stack := (rest1.gpr .r12 (by simp)).trans ptr0
  refine WP.mono (copyRetained_ok s1 h1 slots1 (by decide : 4 < 6) (by decide : 4 + 4 ≤ 56) ptr1) ?_
  rintro s2 ⟨h2, slots2, mem2, frame2, rest2⟩
  have ptr2 : s2.gpr .r12 = g.stack := (rest2.gpr .r12 (by simp)).trans ptr1
  refine WP.mono (storeTemporary_ok s2 h2 slots2 ptr2) ?_
  rintro s3 ⟨h3, slots3, mem3, frame3, rest3⟩
  have ptr3 : s3.gpr .r12 = g.stack := (rest3.gpr .r12 (by simp)).trans ptr2
  refine WP.mono (copyRetained_ok s3 h3 slots3 (by decide : 2 < 6) (by decide : 12 + 4 ≤ 56) ptr3) ?_
  rintro s4 ⟨h4, slots4, mem4, frame4, rest4⟩
  have ptr4 : s4.gpr .r12 = g.stack := (rest4.gpr .r12 (by simp)).trans ptr3
  refine WP.mono (copyIncoming_ok s4 h4 slots4 (by decide : 14 < 16) (by decide : 16 + 4 ≤ 56) ptr4) ?_
  rintro s5 ⟨h5, slots5, mem5, frame5, rest5⟩
  have ptr5 : s5.gpr .r12 = g.stack := (rest5.gpr .r12 (by simp)).trans ptr4
  refine WP.mono (copyIncoming_ok s5 h5 slots5 (by decide : 15 < 16) (by decide : 20 + 4 ≤ 56) ptr5) ?_
  rintro s6 ⟨h6, slots6, mem6, frame6, rest6⟩
  refine ⟨h6, slots6, ?_, ?_, ?_⟩
  · rw [mem6, mem5, mem4, mem3, mem2, mem1, mem0]; rfl
  · have f0 : Frame (pdPrefixWrites g) s.mem s0.mem := frame0.mono (by simp [pdPrefixWrites])
    have f1 : Frame (pdPrefixWrites g) s0.mem s1.mem := frame1.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 0 + 4 ≤ 24)⟩)
    have f2 : Frame (pdPrefixWrites g) s1.mem s2.mem := frame2.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 4 + 4 ≤ 24)⟩)
    have f3 : Frame (pdPrefixWrites g) s2.mem s3.mem := frame3.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 8 + 4 ≤ 24)⟩)
    have f4 : Frame (pdPrefixWrites g) s3.mem s4.mem := frame4.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 12 + 4 ≤ 24)⟩)
    have f5 : Frame (pdPrefixWrites g) s4.mem s5.mem := frame5.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 16 + 4 ≤ 24)⟩)
    have f6 : Frame (pdPrefixWrites g) s5.mem s6.mem := frame6.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 20 + 4 ≤ 24)⟩)
    exact f0.trans (f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6)))))
  · exact (rest0.mono (by simp)).trans ((rest1.mono (by simp)).trans ((rest2.mono (by simp)).trans ((rest3.mono (by simp)).trans ((rest4.mono (by simp)).trans ((rest5.mono (by simp)).trans ((rest6.mono (by simp))))))))
end VG.Proof.Rsa.Arm
