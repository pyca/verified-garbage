module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTRoundCall
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundKernel
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Prepare the shared RSA primality call with the existing Montgomery encoder. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Spec.Rsa.Mont (numAt arrAt Operand)

structure RoundKernelData where
  math : MontMathData
  modulus : Nat

structure RoundKernelStart (p : RoundKernelData) (s : State) : Prop where
  ready : ArithmeticReady p.math.base p.math.capacity p.math.words s
  data : RoundData p.math.base p.math.capacity p.math.words p.modulus s.mem
  stack : Workspace s s.sp 72
  stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.math.capacity
  below : 56 ≤ s.sp.toNat
  belowSep : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩

private structure RoundEncoded (p : RoundKernelData) (s : State) : Prop where
  start : RoundKernelStart p s
  encoded : numAt s.mem (State.addr p.math.base) p.math.words 5 < p.modulus

private theorem encodeReady_ok (p : RoundKernelData) (s : State) (h : RoundKernelStart p s) :
    WP isa (VG.Impl.Bignum.Arm.montOp 5 1 4) s (RoundEncoded p) := by
  have operand (j : Nat) (member : j = 1 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  refine WP.mono (montEncode_ok s h.ready (operand 5 (by simp)) (operand 1 (by simp)) (by decide)
    h.data.modulus h.data.odd h.data.r2) ?_
  rintro t ⟨ready, _, encoded, keeps, frame, rest⟩
  have saved : t.mem.readW (State.addr (t.sp + 36#32)) 32 = BitVec.ofNat 32 p.math.capacity := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 36#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.saved
    · intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [VG.Arm.addr_add (by have := h.stack.nowrap; omega)]
      exact h.stackSep.sub_left (Offset.sub_base _ (by decide : 36 + 4 ≤ 72))
  refine ⟨⟨ready, h.data.after_operand (by decide) (by decide) (by decide) keeps,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.stackSep, saved,
    by rw [rest.sp]; exact h.below,
    by rw [rest.sp]; exact h.belowSep⟩, ?_⟩
  rw [encoded]
  exact Nat.mod_lt _ (by have := h.data.large; omega)

private theorem encodeReady_ct : RelCT isa (Two RoundKernelStart)
    (VG.Impl.Bignum.Arm.montOp 5 1 4) (Two RoundEncoded) := by
  refine two_post ?_ encodeReady_ok
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  have op (j : Nat) (member : j = 1 ∨ j = 4 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have fit : arrAt p.math.words 3 + 32 ≤ 8 * p.math.capacity := by
    have fits : arrAt p.math.words 8 ≤ 8 * p.math.capacity := left.ready.width ▸ left.ready.layout.2.2.1
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits ⊢
    omega
  have boundL : numAt s.mem (State.addr p.math.base) p.math.words 4 < numAt s.mem (State.addr p.math.base) p.math.words 0 := by
    rw [left.data.r2, left.data.modulus]
    exact Nat.mod_lt _ (by have := left.data.large; omega)
  have boundR : numAt t.mem (State.addr p.math.base) p.math.words 4 < numAt t.mem (State.addr p.math.base) p.math.words 0 := by
    rw [right.data.r2, right.data.modulus]
    exact Nat.mod_lt _ (by have := right.data.large; omega)
  exact montOp_ct (op 5 (by simp)) (op 1 (by simp)) (op 4 (by simp)) fit
    _ _ _ _ _ _ ⟨⟨left.ready, boundL⟩, ⟨right.ready, boundR⟩, sp⟩ runS runT

private theorem callReady_ok (p : RoundKernelData) (s : State) (h : RoundEncoded p s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r1 36]) s (SharedRoundStart p.math) := by
  refine WP.mono (roundArgs_ok h.start.ready h.start.stack h.start.saved) ?_
  rintro t ⟨⟨ptr, length, mem⟩, rest⟩
  have data : RoundData p.math.base p.math.capacity p.math.words p.modulus t.mem := mem ▸ h.start.data
  exact ⟨h.start.ready.workspace.congr rest.wr, ptr, length,
    by have := h.start.ready.workspace.nowrap; omega,
    data.data.width, data.layout, data.prepared (by rw [mem]; exact h.encoded),
    by rw [rest.sp]; exact h.start.below,
    by rw [rest.sp]; exact h.start.belowSep⟩

theorem roundPrepared_ct : RelCT isa (Two RoundKernelStart)
    (.seq (VG.Impl.Bignum.Arm.montOp 5 1 4) (.block [.ldrSp .r0 0, .ldrSp .r1 36]))
    (Two SharedRoundStart) := by
  have args : RelCT isa (Two RoundEncoded) (.block [.ldrSp .r0 0, .ldrSp .r1 36]) (Two SharedRoundStart) :=
    (two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) callReady_ok).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.math, left, right, sp⟩)
  exact encodeReady_ct.seq args

end VG.Proof.Ffdh.Arm.ParameterCandidate
