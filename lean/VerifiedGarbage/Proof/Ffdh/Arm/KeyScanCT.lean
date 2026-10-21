module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanStep
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
meta import VerifiedGarbage.Proof.Ffdh.Arm.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanBlocks
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanBlocks
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.TCB.Arm.Isa

/-! The bound scan's addresses and branches depend only on the public bound
bytes and their length. Every continuing step decreases that public length. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure KeyScanState (base src : BitVec 32) (len : Nat) (bs : List Byte) (s : State) : Prop where
  source : Octets base src len bs s
  ptr : s.gpr .r4 = src
  count : s.gpr .r6 = BitVec.ofNat 32 bs.length

theorem keyScanAdvance_ct : RelCT isa (fun _ _ => True)
    VG.Impl.Ffdh.Arm.Domain.GenerateKey.advance (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _; exact Taint.agree_ofRegs (by simp)

theorem keyScanStop_ct : RelCT isa (fun _ _ => True)
    VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _; exact Taint.agree_ofRegs (by simp)

theorem keyScanCount_ct (n : Nat) (positive : 0 < n) (fits : n < 2 ^ 32) :
    RelCT isa (fun s t => s.gpr .r6 = BitVec.ofNat 32 n ∧ t.gpr .r6 = BitVec.ofNat 32 n ∧ s.sp = t.sp)
      (.seq (.block [.cmp .r6 (.imm 1)])
        (.ite .ne VG.Impl.Ffdh.Arm.Domain.GenerateKey.advance VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop)) (fun _ _ => True) := by
  have cmp : RelCT isa (fun s t => s.gpr .r6 = BitVec.ofNat 32 n ∧ t.gpr .r6 = BitVec.ofNat 32 n ∧ s.sp = t.sp)
      (.block [.cmp .r6 (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : s.gpr .r6 = BitVec.ofNat 32 n) :
      WP isa (.block [.cmp .r6 (.imm 1)]) s (fun t => t.z = decide (n = 1)) := by
    exact WP.mono (scanCount_ok s positive fits h) (fun _ h => h.1.1)
  have branch : RelCT isa (fun s t => s.z = decide (n = 1) ∧ t.z = decide (n = 1) ∧ s.sp = t.sp)
      (.ite .ne VG.Impl.Ffdh.Arm.Domain.GenerateKey.advance VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop) (fun _ _ => True) := by
    apply iteKnown_ct (!decide (n = 1)) (fun s h => by change some (!s.z) = _; rw [h])
    · intro _; exact keyScanAdvance_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · intro _; exact keyScanStop_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  exact relCT_chain cmp wp wp branch

theorem keyScanStep_ct {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (positive : 0 < bs.length) (fits : bs.length < 2 ^ 32) :
    RelCT isa (fun s t => KeyScanState base src len bs s ∧ KeyScanState base src len bs t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.scanStep (fun _ _ => True) := by
  have head : RelCT isa (fun s t => KeyScanState base src len bs s ∧ KeyScanState base src len bs t ∧ s.sp = t.sp)
      (.block [.ldrb .r3 .r4 0, .cmp .r3 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact h.1.ptr.trans h.2.1.ptr.symm
  let Q := fun s : State => s.gpr .r6 = BitVec.ofNat 32 bs.length ∧ s.z = decide (bs.getD 0 0 = 0)
  have wp (s : State) (h : KeyScanState base src len bs s) :
      WP isa (.block [.ldrb .r3 .r4 0, .cmp .r3 (.imm 0)]) s Q := by
    refine WP.mono (scanRead_ok s h.source positive h.ptr) ?_
    rintro t ⟨⟨_, zero, _⟩, rest⟩
    exact ⟨(rest.gpr .r6 (by simp)).trans h.count, zero⟩
  have branch : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq (.seq (.block [.cmp .r6 (.imm 1)])
        (.ite .ne VG.Impl.Ffdh.Arm.Domain.GenerateKey.advance VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop))
        VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop) (fun _ _ => True) := by
    apply iteKnown_ct (decide (bs.getD 0 0 = 0)) (fun s h => by change some s.z = _; rw [h.2])
    · intro _
      exact (keyScanCount_ct bs.length positive fits).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact keyScanStop_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.scanStep VG.Impl.Ffdh.Arm.PublicScan.step
  exact relCT_chain head wp wp branch

theorem keyScanTail {base src : BitVec 32} {len : Nat} {bs : List Byte} {s t : State}
    (h : KeyScanState base src len bs s) (positive : 1 < bs.length)
    (mem : t.mem = s.mem) (rest : Rest [.r3, .r4, .r6, .r11] s t)
    (ptr : t.gpr .r4 = src + 1) (count : t.gpr .r6 = BitVec.ofNat 32 (bs.length - 1)) :
    KeyScanState base (src + 1) len (bs.drop 1) t := by
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  have source := (h.source.after_frame frame rest (by simp)).slice
    (d := 1) (k := bs.length - 1) (by omega) (by omega)
  rw [List.take_of_length_le (by simp only [List.length_drop]; omega)] at source
  refine ⟨?_, ptr, ?_⟩
  · exact source
  · simpa only [List.length_drop] using count

theorem keyScan_ct {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (positive : 0 < bs.length) (fits : bs.length < 2 ^ 32) :
    RelCT isa (fun s t => KeyScanState base src len bs s ∧ KeyScanState base src len bs t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.scan (fun _ _ => True) := by
  let I := fun n (s t : State) => ∃ (ptr : BitVec 32) (octets : List Byte), octets.length = n ∧
    0 < n ∧ n < 2 ^ 32 ∧ KeyScanState base ptr len octets s ∧ KeyScanState base ptr len octets t ∧ s.sp = t.sp
  have step (n : Nat) : RelCT isa (I n) VG.Impl.Ffdh.Arm.Domain.GenerateKey.scanStep fun s t =>
      eval .ne s = eval .ne t ∧ (eval .ne s = some false → True) ∧
      (eval .ne s = some true → ∃ m < n, I m s t) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨ptr, octets, size, pos, fit, hs, ht, sp⟩ := h
    have leak := (keyScanStep_ct (by omega) (by omega)) s t tr1 tr2 u v ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, u', run1, post1, rest1⟩ := scanStep_ok s hs.source (by omega) (by omega) hs.ptr hs.count
    obtain ⟨_, rfl⟩ := Exec.det e1 run1
    obtain ⟨_, v', run2, post2, rest2⟩ := scanStep_ok t ht.source (by omega) (by omega) ht.ptr ht.count
    obtain ⟨_, rfl⟩ := Exec.det e2 run2
    obtain ⟨_, mem1, result1⟩ := post1
    obtain ⟨_, mem2, result2⟩ := post2
    by_cases go : octets.getD 0 0 = 0 ∧ 1 < octets.length
    · rw [ite_eq_left go] at result1 result2
      obtain ⟨ptr1, count1, zero1⟩ := result1
      obtain ⟨ptr2, count2, zero2⟩ := result2
      have eval1 : eval .ne u = some true := by simp only [eval, zero1, Bool.not_false]
      have eval2 : eval .ne v = some true := by simp only [eval, zero2, Bool.not_false]
      refine ⟨leak.1, eval1.trans eval2.symm, fun _ => trivial, fun _ => ?_⟩
      refine ⟨n - 1, by omega, ptr + 1, octets.drop 1, ?_, by omega, by omega,
        keyScanTail hs go.2 mem1 rest1 ptr1 count1, keyScanTail ht go.2 mem2 rest2 ptr2 count2, ?_⟩
      · simp only [List.length_drop, size]
      · exact rest1.sp.trans (sp.trans rest2.sp.symm)
    · rw [ite_eq_right go] at result1 result2
      obtain ⟨_, _, zero1⟩ := result1
      obtain ⟨_, _, zero2⟩ := result2
      have eval1 : eval .ne u = some false := by simp only [eval, zero1, Bool.not_true]
      have eval2 : eval .ne v = some false := by simp only [eval, zero2, Bool.not_true]
      exact ⟨leak.1, eval1.trans eval2.symm, fun _ => trivial, fun impossible => by rw [eval1] at impossible; cases impossible⟩
  exact (RelCT.loop I step bs.length).mono
    (fun _ _ h => ⟨src, bs, rfl, positive, fits, h⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm
