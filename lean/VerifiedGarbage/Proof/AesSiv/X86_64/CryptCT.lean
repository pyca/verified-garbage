import VerifiedGarbage.Proof.AesSiv.X86_64.Open

/-!
# AES-SIV on x86-64: the ends of `encrypt` and `decrypt` are constant time

Both are put together from pieces: `finish` and CTR, from the registers that
hold the arguments (`finish_rel`, `ctr_rel'`), with what correctness says
about the slots of the data and the counter; and the rest, by the taint
analysis from those registers. `decrypt` compares the IVs and masks the data
without a branch, so nothing it does depends on the result.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem finish_spre (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s : State} (hs : SPre s₀ C D P W R L s) :
    WP isa (finish v.callee v.suffix 0) s (SPre s₀ C D P W R L) := by
  refine WP.mono (finish_wp v h hs.regs (Or.inl rfl)) fun t ht => ⟨ht.regs, ?_, ?_⟩
  · rw [ht.frame.readW (Region.contains_self _ _) (fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d208]
  · rw [ht.frame.readW (Region.contains_self _ _) (fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d216]

theorem counter_ctrPre (h : Env s₀ C D P W R L) {s : State} (hs : SPre s₀ C D P W R L s) :
    WP isa (.block (counter 0)) s (CtrPre s₀ C D P W R L) := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := counter_ok h hs.regs.r15 hs.regs.rd hs.regs.wr
  have fc : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, hs.regs.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁, ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃⟩, ?_, ?_⟩
  · rw [fc.readW (Region.contains_self _ _) (cnt_dis (by decide) (by decide)) (by decide), hs.d208]
  · rw [fc.readW (Region.contains_self _ _) (cnt_dis (by decide) (by decide)) (by decide), hs.d216]

/-- `encrypt`'s end, from the registers and slots in both runs. -/
theorem sealTail_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b)
      (.seq (finish v.callee v.suffix 0) (.seq (.block (counter 0)) (.seq (ctr v.callee) (.block restore))))
      fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block restore) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have f := ((finish_rel v h h' q1 (Or.inl rfl)).mono (P' := fun a b => SPre s₀ C D P W R L a ∧
      SPre s₀' C D P W R L b) (fun _ _ p => ⟨p.1.regs, p.2.regs⟩) fun _ _ p => p).wp
    (F₁ := SPre s₀ C D P W R L) (F₂ := SPre s₀' C D P W R L) fun a b hab =>
      ⟨finish_spre v h hab.1, finish_spre v h' hab.2⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b) _
    (fun a b hab => regs_agree q1 hab.1.regs hab.2.regs) hB).wp
    (F₁ := CtrPre s₀ C D P W R L) (F₂ := CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨counter_ctrPre h hab.1, counter_ctrPre h' hab.2⟩
  have r := RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hC
  exact (f.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((c.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((ctr_rel' v h h' q1 hcp hPw hPw').seq r))

/-- `decrypt`'s end, from the registers and slots in both runs: it compares
the IVs and masks the data without a branch, so nothing it does depends on
the result. -/
theorem openTail_rel (v : Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L) (h' : Env s₀' C D P W R L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b)
      (.seq (.block (counter 0)) (.seq (ctr v.callee) (.seq (finish v.callee v.suffix tOff)
        (.seq (.block Impl.AesSiv.X86_64.compare)
          (.seq maskData (.block ([.mov .rax (.mem (at_ .r15 dbOff))] ++ restore)))))))
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq (.block Impl.AesSiv.X86_64.compare)
        (.seq maskData (.block ([.mov .rax (.mem (at_ .r15 dbOff))] ++ restore)))) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b) _
    (fun a b hab => regs_agree q1 hab.1.regs hab.2.regs) hA).wp
    (F₁ := CtrPre s₀ C D P W R L) (F₂ := CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨counter_ctrPre h hab.1, counter_ctrPre h' hab.2⟩
  have t := RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _
    (fun a b hab => regs_agree q1 hab.1 hab.2) hB
  exact (c.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((ctr_rel' v h h' q1 hcp hPw hPw').seq
    ((finish_rel v h h' q1 (Or.inr rfl)).seq t))

end VG.Proof.AesSiv.X86_64
