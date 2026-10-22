module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFinish
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # SHA finalization inherits the backend's timing contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure FinishReady {H : Hash} (ok : HashOK H) (st data digest scratch sp : BitVec 32) (len : Nat) (s : State) : Prop
    extends HashReady ok st data digest scratch sp len s where
  edx : s.gpr .edx = digest

structure FinishCallReady {H : Hash} (ok : HashOK H) (st data digest scratch sp : BitVec 32) (len : Nat) (s : State) : Prop
    extends FinishReady ok st data digest scratch sp len s where
  eax : s.gpr .eax = BitVec.ofNat 32 len
  ecx : s.gpr .ecx = 0

theorem hash_finish_ready {H : Hash} {ok : HashOK H} {st data digest scratch sp : BitVec 32} {len : Nat} {s : State}
    (h : FinishReady ok st data digest scratch sp len s) :
    WP isa (.block [.mov .eax (.reg .edi), .mov .ecx (.imm 0)]) s
      (FinishCallReady ok st data digest scratch sp len) := by
  refine WP.mono (hash_finish_setup h.registers h.edx) ?_
  rintro t ⟨R, edx, ecx, eax, _, K⟩
  exact ⟨⟨⟨h.geometry.of_regions K.2.1 K.2.2 (K.1 _ (by decide)), R,
    (K.1 _ (by decide)).trans h.stack⟩, edx⟩, eax, ecx⟩

private theorem setup_cert : ∃ hc, (VG.Taint.check taint (τr [])
    (.block [.mov .eax (.reg .edi), .mov .ecx (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem hash_finish_ct {H : Hash} (ok : HashOK H) {st data digest scratch sp : BitVec 32} {len : Nat} :
    RelCT isa (fun s t => FinishReady ok st data digest scratch sp len s ∧ FinishReady ok st data digest scratch sp len t)
      (Impl.Dsa.X86.Generation.hashFinish H) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := setup_cert
  have setupCT := (RelCT.taint (A := taint) (τr [])
    (P := fun s t => FinishReady ok st data digest scratch sp len s ∧ FinishReady ok st data digest scratch sp len t)
    (fun _ _ _ => agree_regs (by simp)) checked).wp
    (F₁ := FinishCallReady ok st data digest scratch sp len) (F₂ := FinishCallReady ok st data digest scratch sp len)
    (fun _ _ ⟨a, b⟩ => ⟨hash_finish_ready a, hash_finish_ready b⟩)
  exact setupCT.seq (fin_rel ok (r := .ebx) (sp := sp)
    (P := fun s t => True ∧ FinishCallReady ok st data digest scratch sp len s ∧ FinishCallReady ok st data digest scratch sp len t)
    (fun _ _ ⟨_, a, b⟩ => ⟨a.geometry.finish_args a.registers a.eax a.ecx a.edx,
      b.geometry.finish_args b.registers b.eax b.ecx b.edx, a.stack, b.stack⟩))

end VG.Proof.Dsa.X86.Generation
