module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.StepTiming
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Prf
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Squeeze
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.StepTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Prf
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Slot
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Slot

/-!
# A PRF slot leaks only public pointers

As `Hybrid.step3_relCT`: the PRF's padded block (`prfBlock`) by the taint
analysis from `x28`, the call by `Hybrid.x3call_relCT`, and the squeeze's tail
with the copy of the PRF output (`prfOut`) by the taint analysis from `x19`,
`x20`, `x21` and `x28`. Each piece differs from one output to another only in
immediates and offsets, which the analysis does not read: it checks one copy
without them (`Code.eraseOff`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (CallLay x3call_relCT regEq)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Spec.Sha3 (stateAt)

theorem prfWords_eraseOff (dst : Reg) (off : Nat → Nat) (N : Nat) :
    (Impl.MlKem.AArch64.Kem16P.prfWords dst off N).map Instr.eraseOff =
      (Impl.MlKem.AArch64.Kem16P.prfWords dst (fun _ => 0) 0).map Instr.eraseOff := by
  simp only [Impl.MlKem.AArch64.Kem16P.prfWords, List.map_flatMap]
  refine congrArg (List.flatMap · (List.range 25)) (funext fun k => ?_)
  simp only [Impl.MlKem.AArch64.Kem16P.prfWord]
  split <;> (try split) <;> (try split) <;> simp only [List.map_cons, List.map_nil, Instr.eraseOff]

/-- `prfBlock` without its immediates and offsets. -/
def prfBlockE : Prog isa :=
  .block ((Impl.MlKem.AArch64.Kem16P.prfWords .x28 (fun _ => 0) 0).map Instr.eraseOff)

theorem prfBlock_eraseOff (N : Nat) :
    Code.eraseOff (.block (Impl.MlKem.AArch64.Kem16P.prfBlock N)) = prfBlockE := by
  simp only [Code.eraseOff, Impl.MlKem.AArch64.Kem16P.prfBlock, prfBlockE, prfWords_eraseOff]

/-- The squeeze's tail and `prfOut`, without their immediates and offsets. -/
def outE : Prog isa :=
  .block ((Impl.MlKem.AArch64.Hybrid.squeezeTail ++
    ([.movz .x .x2 0 0, .add .x .x2 .x28 .x2] : List Instr) ++
    (List.range 16).flatMap fun _ => ([.ldr .x .x9 .x28 0, .str .x .x9 .x2 0] : List Instr)).map Instr.eraseOff)

theorem out_eraseOff (L : Impl.MlKem.AArch64.KemLay) (N : Nat)
    (h : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N) :
    Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.squeezeTail ++ Impl.MlKem.AArch64.Kem16P.prfOut L N)) =
      outE := by
  simp only [Code.eraseOff, outE, Impl.MlKem.AArch64.Kem16P.prfOut, Impl.MlKem.AArch64.ptrTo,
    ite_eq_right (show ¬ Impl.MlKem.AArch64.Kem16P.bufOff L N < 4096 by omega), List.map_append,
    List.map_flatMap, List.append_assoc]
  rfl

theorem prfBlockE_taint : ∃ h, (taint.check (Taint.ofRegs [.x28]) prfBlockE h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem outE_taint :
    ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x28]) outE h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem SlotLay.callLay {p a b st R Bf : Addr} {s : State} (h : SlotLay p a b st R Bf s) :
    CallLay p (p + 1536) st s :=
  ⟨rfl, h.dPS, h.dPC, h.dSC, h.sp, h.fP, h.fS, h.fC, h.cov⟩

/-- **A PRF slot** leaks only its public pointers. -/
theorem slotPrf_relCT (L : Impl.MlKem.AArch64.KemLay) {N : Nat} (hN : N < 256)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N) {σ₁ σ₂ : State} {p a b st R Bf : Addr}
    (h19₁ : σ₁.gpr .x19 = p) (h20₁ : σ₁.gpr .x20 = a) (h21₁ : σ₁.gpr .x21 = b) (h28₁ : σ₁.gpr .x28 = st)
    (h19₂ : σ₂.gpr .x19 = p) (h20₂ : σ₂.gpr .x20 = a) (h21₂ : σ₂.gpr .x21 = b) (h28₂ : σ₂.gpr .x28 = st)
    (sp : σ₁.sp = σ₂.sp) (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    {A₁ B₁ A₂ B₂ : Spec.Sha3.State} (pair₁ : PairAt σ₁.mem p A₁ B₁) (pair₂ : PairAt σ₂.mem p A₂ B₂)
    (hl₁ : SlotLay p a b st R Bf σ₁) (hl₂ : SlotLay p a b st R Bf σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.MlKem.AArch64.Kem16P.slotPrf L N) TT := by
  unfold Impl.MlKem.AArch64.Kem16P.slotPrf
  refine rel_seq (rel_taint [.x28] sp (by
      intro r hr; rw [List.mem_singleton.mp hr, h28₁, h28₂])
      (by obtain ⟨hc, h⟩ := prfBlockE_taint
          exact ⟨hc, VG.AArch64.Taint.isSome_check_of_eraseOff (prfBlock_eraseOff N) h⟩))
    (prfBlock_ok hN (by rw [h28₁]; exact hR)
      (by rw [h28₁]; exact Hybrid.covers_mono hl₁.cov (by simp)) (by rw [h28₁]; exact hl₁.dSR) hl₁.rin)
    (prfBlock_ok hN (by rw [h28₂]; exact hR)
      (by rw [h28₂]; exact Hybrid.covers_mono hl₂.cov (by simp)) (by rw [h28₂]; exact hl₂.dSR) hl₂.rin)
    fun u₁ u₂ ⟨ku₁, fu₁, su₁⟩ ⟨ku₂, fu₂, su₂⟩ => ?_
  rw [h28₁] at fu₁ su₁
  rw [h28₂] at fu₂ su₂
  have pu₁ : PairAt u₁.mem p A₁ B₁ :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair₁ fu₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl₁.dPS)
  have pu₂ : PairAt u₂.mem p A₂ B₂ :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair₂ fu₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl₂.dPS)
  have c₁ := hl₁.callLay.frame ku₁.wr ku₁.sp
  have c₂ := hl₂.callLay.frame ku₂.wr ku₂.sp
  have u19₁ : u₁.gpr .x19 = p := by rw [ku₁.get .x19, h19₁]
  have u19₂ : u₂.gpr .x19 = p := by rw [ku₂.get .x19, h19₂]
  have u28₁ : u₁.gpr .x28 = st := by rw [ku₁.get .x28, h28₁]
  have u28₂ : u₂.gpr .x28 = st := by rw [ku₂.get .x28, h28₂]
  refine rel_seq (x3call_relCT c₁ c₂ u19₁ u19₂ u28₁ u28₂ (by rw [ku₁.sp, ku₂.sp, sp]))
    (Hybrid.x3call_ok (S := stateAt u₁.mem st) u19₁ c₁.hq u28₁ pu₁ rfl c₁.d01 c₁.d02 c₁.d12 c₁.sp c₁.f0
      c₁.f1 c₁.f2 c₁.cov)
    (Hybrid.x3call_ok (S := stateAt u₂.mem st) u19₂ c₂.hq u28₂ pu₂ rfl c₂.d01 c₂.d02 c₂.d12 c₂.sp c₂.f0
      c₂.f1 c₂.f2 c₂.cov)
    fun v₁ v₂ ⟨kv₁, _⟩ ⟨kv₂, _⟩ => ?_
  have k₁ := ku₁.trans kv₁
  have k₂ := ku₂.trans kv₂
  refine rel_taint [.x19, .x20, .x21, .x28] (by rw [k₁.sp, k₂.sp, sp]) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [k₁.get .x19 (by simp [Hybrid.clobbered]), k₂.get .x19 (by simp [Hybrid.clobbered]), h19₁, h19₂]
      · rw [k₁.get .x20 (by simp [Hybrid.clobbered]), k₂.get .x20 (by simp [Hybrid.clobbered]), h20₁, h20₂]
      · rw [k₁.get .x21 (by simp [Hybrid.clobbered]), k₂.get .x21 (by simp [Hybrid.clobbered]), h21₁, h21₂]
      · rw [k₁.get .x28 (by simp [Hybrid.clobbered]), k₂.get .x28 (by simp [Hybrid.clobbered]), h28₁, h28₂])
    (by obtain ⟨hc, h⟩ := outE_taint
        exact ⟨hc, VG.AArch64.Taint.isSome_check_of_eraseOff (out_eraseOff L N h4) h⟩)

end VG.Proof.MlKem.AArch64.Kem16P
