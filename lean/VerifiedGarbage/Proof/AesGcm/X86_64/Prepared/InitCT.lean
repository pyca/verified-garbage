import VerifiedGarbage.Proof.AesGcm.X86_64.InitPCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Init

/-! # Constant-time key setup with prepared GHASH powers -/

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

theorem initPrepared_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.initPreparedX86_64.pre s₀)
    (hp' : Proof.AesGcm.initPreparedX86_64.pre s₀') (hq : Proof.AesGcm.initPreparedX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Prepared.init v.callees) fun _ _ => True := by
  obtain ⟨L, pC, pW⟩ := IPLay.of hp
  obtain ⟨-, pC', pW'⟩ := IPLay.of hp'
  have hq' := hq
  obtain ⟨-, -, q₃, q₄, q₅⟩ := hq'
  rw [← q₃] at pC'
  rw [← q₄] at pW'
  refine initWith_rel v (by decide) hp hp' hq ?_
  have hS : ∀ {rd wr : List Region}, Covers [⟨s₀.gpr .rdx, 1024⟩] wr → ∀ t,
      InitTail (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) rd wr t →
      WP isa (.block (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
        .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272)) t
        (PowRegs (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) rd wr 0) := fun pC t ⟨h13, h15, hsp, hrd, hwr⟩ =>
    WP.mono (powStart_ok L (by rw [hwr]; exact pC) h13 h15 hsp) fun _ I =>
      ⟨I.r13, I.r15, I.rbp, I.rsp, I.rd.trans hrd, I.wr.trans hwr⟩
  have a := rel_wp (rel_taint (P := fun t₁ t₂ => InitTail (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀.rd s₀.wr t₁ ∧
      InitTail (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀'.rd s₀'.wr t₂) [.r13, .r15, .rsp]
      (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.1, h.2.1]
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (hS pC) (hS pC')
  have b := powSteps_rel v L (rd₁ := s₀.rd) (rd₂ := s₀'.rd) pC pW pC' pW' 47 (Nat.le_refl _)
  have c := rel_taint (P := fun t₁ t₂ => PowRegs (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀.rd s₀.wr 47 t₁ ∧
      PowRegs (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀'.rd s₀'.wr 47 t₂) (c := .block ([.mov .rdi (.reg .r13)] ++ Prepared.convert ++ restore)) [.r13, .r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]
      · rw [h.1.2.2.2.1, h.2.2.2.2.1]) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => h.2) (RelCT.seq b c)

theorem initPrepared_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.initPreparedX86_64.pre Proof.AesGcm.initPreparedX86_64.pub
      (Prepared.init v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => initPrepared_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
