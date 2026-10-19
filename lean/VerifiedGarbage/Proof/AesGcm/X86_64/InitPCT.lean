module

public import VerifiedGarbage.Proof.AesGcm.X86_64.InitP
meta import VerifiedGarbage.Proof.AesGcm.X86_64.InitP
import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Init
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init_precomputed` is constant time

Untrusted: everything here is checked by Lean. `init`'s code is
(`initWith_rel`); then both runs copy the hash subkey and call `vg_ghash` 47
times with the same arguments, which depend only on the pointers
(`PowRegs`, `powStep_rel`).
-/

@[expose] public section

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

omit L pC₁ pW₁ pC₂ pW₂ in
theorem powEndRegs_ok {rd wr : List Region} {k : Nat} (hk : k ≤ 47) {t : State}
    (h : PowRegs Ctx W SP rd wr k t) :
    WP isa (.block (ptr .rax .r13 1024 ++ ([.alu .cmp .rbp (.reg .rax)] : List Instr))) t fun t' =>
      PowRegs Ctx W SP rd wr k t' ∧ isa.eval .ne t' = some (decide (k ≠ 47)) := by
  obtain ⟨h13, h15, hbp, hsp, hrd, hwr⟩ := h
  obtain ⟨t', run, hg, -, hrd', hwr', he⟩ := powEnd_run hk h13 hbp
  exact WP.of_runBlock ⟨t', run, ⟨by rw [hg _ (by decide)]; exact h13, by rw [hg _ (by decide)]; exact h15,
    by rw [hg _ (by decide)]; exact hbp, by rw [hg _ (by decide)]; exact hsp, hrd'.trans hrd,
    hwr'.trans hwr⟩, he⟩

/-- The loop of the 47 powers, in two runs: the loop's test depends only on
`rbp`, which both runs advance alike. -/
theorem powLoop_rel :
    RelCT isa (fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ 0 t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ 0 t₂) (powLoop v.callees)
      fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ 47 t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ 47 t₂ := by
  refine (RelCT.loop (M := isa) (fun m t₁ t₂ => ∃ j, j < 47 ∧ m = 47 - j ∧
      PowRegs Ctx W SP rd₁ wr₁ j t₁ ∧ PowRegs Ctx W SP rd₂ wr₂ j t₂) (fun m => ?_) 47).mono
    (fun _ _ h => ⟨0, by decide, rfl, h⟩) (fun _ _ h => h)
  apply RelCT.exists_
  intro j
  intro t₁ t₂ tr ur u₁ u₂ ⟨hj, hm, h⟩ e₁ e₂
  have hend := rel_wp (rel_taint (P := fun t₁ t₂ => PowRegs Ctx W SP rd₁ wr₁ (j + 1) t₁ ∧
      PowRegs Ctx W SP rd₂ wr₂ (j + 1) t₂)
      (c := .block (ptr .rax .r13 1024 ++ ([.alu .cmp .rbp (.reg .rax)] : List Instr))) [.r13, .rbp]
      (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.1, h.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun _ h => powEndRegs_ok (by omega) h) (fun _ h => powEndRegs_ok (by omega) h)
  obtain ⟨htr, -, ⟨g₁, he₁⟩, ⟨g₂, he₂⟩⟩ :=
    RelCT.seq (powStep_rel v L pC₁ pW₁ pC₂ pW₂ hj) hend t₁ t₂ tr ur u₁ u₂ h e₁ e₂
  refine ⟨htr, by rw [he₁, he₂], fun hf => ?_, fun ht => ?_⟩
  · rw [he₁] at hf
    have hl : j + 1 = 47 := by simp at hf; omega
    rw [hl] at g₁ g₂
    exact ⟨g₁, g₂⟩
  · rw [he₁] at ht
    have hl : j + 1 < 47 := by simp at ht; omega
    exact ⟨47 - (j + 1), by omega, j + 1, hl, rfl, g₁, g₂⟩

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
  have b := powLoop_rel v L (rd₁ := s₀.rd) (rd₂ := s₀'.rd) pC pW pC' pW'
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
