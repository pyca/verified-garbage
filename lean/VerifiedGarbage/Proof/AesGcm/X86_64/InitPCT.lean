import VerifiedGarbage.Proof.AesGcm.X86_64.InitP
import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init_precomputed` is constant time

Untrusted: everything here is checked by Lean. `init`'s code is
(`initWith_rel`); then both runs copy the hash subkey and call `vg_ghash` 47
times with the same arguments, which depend only on the pointers
(`PowRegs`, `powStep_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- One run of the powers, after `j` of them: the registers and the
permissions. -/
def PowRegs (Ctx W SP : Addr) (rd wr : List Region) (j : Nat) (t : State) : Prop :=
  t.gpr .r13 = Ctx ∧ t.gpr .r15 = W ∧ t.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j) ∧
    t.gpr .rsp = SP ∧ t.rd = rd ∧ t.wr = wr

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : IPLay Ctx W SP) {rd₁ wr₁ rd₂ wr₂ : List Region}
  (pC₁ : Covers [⟨Ctx, 1024⟩] wr₁) (pW₁ : Covers [⟨W, 2560⟩] wr₁)
  (pC₂ : Covers [⟨Ctx, 1024⟩] wr₂) (pW₂ : Covers [⟨W, 2560⟩] wr₂)
include L pC₁ pW₁ pC₂ pW₂

omit L pC₁ pW₁ pC₂ pW₂ in
theorem powNext_ok {Y : Addr} {j : Nat} {t : State} (hY : Y = Ctx + BitVec.ofNat 64 (272 + 16 * j))
    {rd wr : List Region} (h13 : t.gpr .r13 = Ctx) (h15 : t.gpr .r15 = W) (hbp : t.gpr .rbp = Y)
    (hsp : t.gpr .rsp = SP) (hrd : t.rd = rd) (hwr : t.wr = wr) :
    WP isa (.block [.alu .add .rbp (imm 16)]) t (PowRegs Ctx W SP rd wr (j + 1)) := by
  refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, h13]
  · simp [gpr_setReg, gpr_arithFlags, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbp, hY, imm_eq (show 16 < 2 ^ 31 by decide),
      add_ofNat_assoc]
    congr 2
  · simp [gpr_setReg, gpr_arithFlags, hsp]
  · simp [rd_setReg, rd_arithFlags, hrd]
  · simp [wr_setReg, wr_arithFlags, hwr]

/-- One more power, in two runs. -/
theorem powStep_rel {j : Nat} (hj : j < 47) :
    RelCT isa (fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ j t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ j t₂) (powStep v.callees)
      fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ (j + 1) t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ (j + 1) t₂ := by
  let G : List Region → List Region → State → Prop := fun rd wr t₁ =>
    GhCall t₁ (Ctx + BitVec.ofNat 64 240) (Ctx + BitVec.ofNat 64 (272 + 16 * j))
      (Ctx + BitVec.ofNat 64 (256 + 16 * j)) (W + BitVec.ofNat 64 512) 1 ∧ t₁.gpr .r13 = Ctx ∧
      t₁.gpr .r15 = W ∧ t₁.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j) ∧ t₁.gpr .rsp = SP ∧
      t₁.rd = rd ∧ t₁.wr = wr
  have hA : ∀ {rd wr : List Region}, Covers [⟨Ctx, 1024⟩] wr → Covers [⟨W, 2560⟩] wr → ∀ t,
      PowRegs Ctx W SP rd wr j t → WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .rbp 0) .rax,
        .store (at_ .rbp 8) .rax] : List Instr) ++ ptr .rdi .r13 240 ++ ([.mov .rsi (.reg .rbp),
        .mov .rdx (.reg .rbp), .alu .sub .rdx (imm 16), .mov32 .rcx (imm 1)] : List Instr) ++
        ptr .r8 .r15 scrO)) t (G rd wr) := fun pC pW t ⟨h13, h15, hbp, hsp, hrd, hwr⟩ =>
    WP.mono (powArgs_ok L hj h13 h15 hbp hsp (by rw [hwr]; exact pC) (by rw [hwr]; exact pW))
      fun t₁ ⟨gc, _, hcs, hrd₁, hwr₁⟩ => ⟨gc, by rw [hcs .r13 (by decide), h13], by rw [hcs .r15 (by decide), h15],
        by rw [hcs .rbp (by decide), hbp], by rw [hcs .rsp (by decide), hsp], hrd₁.trans hrd, hwr₁.trans hwr⟩
  have a := rel_wp (rel_taint (P := fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ j t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ j t₂)
      [.r13, .r15, .rbp, .rsp] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.1.1, h.2.1]
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]
        · rw [h.1.2.2.2.1, h.2.2.2.2.1]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (hA pC₁ pW₁) (hA pC₂ pW₂)
  let H : List Region → List Region → State → Prop := fun rd wr t₂ =>
    t₂.gpr .r13 = Ctx ∧ t₂.gpr .r15 = W ∧ t₂.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j) ∧
      t₂.gpr .rsp = SP ∧ t₂.rd = rd ∧ t₂.wr = wr
  have hB : ∀ {rd wr : List Region} (t₁ : State), G rd wr t₁ → WP isa (.call v.gh.fn.name v.gh.fn.code) t₁ (H rd wr) :=
    fun t₁ ⟨gc, h13, h15, hbp, hsp, hrd, hwr⟩ => WP.mono (gh_call v.gh gc) fun _ g =>
      ⟨by rw [g.saved .r13 (by decide), h13], by rw [g.saved .r15 (by decide), h15],
        by rw [g.saved .rbp (by decide), hbp], by rw [g.saved .rsp (by decide), hsp], g.rd.trans hrd, g.wr.trans hwr⟩
  have b := rel_wp (gh_rel v.gh (P := fun t₁ t₂ => True ∧ G rd₁ wr₁ t₁ ∧ G rd₂ wr₂ t₂) fun _ _ h =>
      ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.2.2.2.1, h.2.2.2.2.2.2.1]⟩)
    (fun _ _ h => h.2) (hB (rd := rd₁)) (hB (rd := rd₂))
  have c := rel_wp (rel_taint (P := fun t₁ t₂ => True ∧ H rd₁ wr₁ t₁ ∧ H rd₂ wr₂ t₂) (c := .block [.alu .add .rbp (imm 16)])
      [.rbp] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; rw [h.2.1.2.2.1, h.2.2.2.2.1]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun t h => powNext_ok rfl h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun t h => powNext_ok rfl h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  exact (RelCT.seq a (RelCT.seq b c)).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `n` more powers, in two runs. -/
theorem powSteps_rel : ∀ n, n ≤ 47 →
    RelCT isa (fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ 0 t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ 0 t₂) (powSteps v.callees n)
      fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ n t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ n t₂
  | 0, _ => RelCT.block_nil fun _ _ h => h
  | n + 1, hn => RelCT.seq (powSteps_rel n (by omega)) (powStep_rel v L pC₁ pW₁ pC₂ pW₂ (by omega))

end


theorem initP_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.initPrecomputedX86_64.pre s₀)
    (hp' : Proof.AesGcm.initPrecomputedX86_64.pre s₀') (hq : Proof.AesGcm.initPrecomputedX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (initPrecomputed v.callees) fun _ _ => True := by
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
      PowRegs (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsp) s₀'.rd s₀'.wr 47 t₂) (c := .block restore) [.r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.2.1, h.2.2.1]
      · rw [h.1.2.2.2.1, h.2.2.2.2.1]) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => h.2) (RelCT.seq b c)

theorem initP_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.initPrecomputedX86_64.pre Proof.AesGcm.initPrecomputedX86_64.pub
      (initPrecomputed v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => initP_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
