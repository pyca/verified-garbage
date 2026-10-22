module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Init
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls
depends only on the pointers (checked by the taint analysis), and each call
of `vg_sm4_expand_key` and `vg_sm4_ctr32` has the same arguments in both runs:
the key at `key`, the schedule into `ctx`, and the zero block at `W + 96`
encrypted into `ctx + 240`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr save restore tO)
open VG.Proof.AesGcm.X86_64 (save_ok rel_taint rel_wp covers_left covers_cons covers_of_mem covers_off
  covers_prefix in_off add_ofNat_assoc ct_of_rel)

/-- After the entry of `init`: the call of `vg_sm4_expand_key`'s arguments. -/
def InitA (s₀ s : State) : Prop :=
  KeyCall s (s₀.gpr .rdi) (s₀.gpr .rsi) ∧ s.gpr .r15 = s₀.gpr .rdx ∧ s.gpr .r13 = s₀.gpr .rsi ∧
    s.gpr .rsp = s₀.gpr .rsp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- Between the calls: the registers `init` keeps. -/
def InitK (s₀ s : State) : Prop :=
  s.gpr .r15 = s₀.gpr .rdx ∧ s.gpr .r13 = s₀.gpr .rsi ∧ s.gpr .rsp = s₀.gpr .rsp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- Before the call of `vg_sm4_ctr32`: its arguments. -/
def InitB (s₀ s : State) : Prop :=
  CtrCall s (s₀.gpr .rsi) (s₀.gpr .rdx + BitVec.ofNat 64 96) (s₀.gpr .rsi + BitVec.ofNat 64 240) 1 ∧
    s.gpr .r15 = s₀.gpr .rdx ∧ s.gpr .rsp = s₀.gpr .rsp

theorem initA_ok {s : State} (hp : Proof.Sm4Gcm.initX86_64.pre s) :
    WP isa (.block (save .rdx ++ ([.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] : List Instr))) s (InitA s) := by
  simp only [Proof.Sm4Gcm.initX86_64, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_kc, -, -, -, -, k_k, k_c, -, wk, wc, -, hsp⟩ := hp
  have pW : Covers [⟨s.gpr .rdx, 2560⟩] s.wr := by
    rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨s.gpr .rsi, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := save_ok s .rdx rfl pW
  obtain ⟨s₂, run₂, h15, h13, hdi, hsi, hsp₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] s₁ = some s₂ ∧
      s₂.gpr .r15 = s.gpr .rdx ∧ s₂.gpr .r13 = s.gpr .rsi ∧ s₂.gpr .rdi = s.gpr .rdi ∧ s₂.gpr .rsi = s.gpr .rsi ∧
      s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, rd_setReg, wr_setReg, hg₁]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  refine ⟨⟨hdi, hsi, by rw [hsp₂]; exact hsp, wk, by omega, d_kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp₂]; exact k_k, by rw [hsp₂]; exact k_c.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩,
    h15, h13, hsp₂, rd₂, wr₂⟩
  · rw [rd₂, wr₂, hrd]
    exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (covers_left (covers_prefix pC (by decide)))
  · rw [wr₂]; exact covers_prefix pC (by decide)

theorem initB_ok {s₀ s : State} (hp : Proof.Sm4Gcm.initX86_64.pre s₀) (hk : InitK s₀ s) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
      .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ ([.mov32 .rcx (imm 1)] : List Instr))) s (InitB s₀) := by
  simp only [Proof.Sm4Gcm.initX86_64, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨-, hwr, -, -, d_cs, -, -, -, k_c, k_s, -, wc, ws, hsp⟩ := hp
  obtain ⟨g15, g13, gsp, rd₃, wr₃⟩ := hk
  unfold InitB
  generalize s₀.gpr .rsi = Ctx at *
  generalize s₀.gpr .rdx = W at *
  generalize s₀.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by
    rw [wr₃, hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [wr₃, hwr]; exact covers_of_mem (List.mem_cons_self ..)
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  obtain ⟨s₄, run₄, hdi₄, hsi₄, hdx₄, hcx₄, h15₄, hsp₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] ++
        ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ [.mov32 .rcx (imm 1)]) s = some s₄ ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = W + BitVec.ofNat 64 96 ∧ s₄.gpr .rdx = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .rcx = BitVec.ofNat 64 1 ∧ s₄.gpr .r15 = W ∧ s₄.gpr .rsp = SP ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by xrun [g15, g13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, gsp]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, h15₄, hsp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [hwr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [hwr₄]; exact pW
  refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, by rw [hsp₄]; exact hsp, by omega,
    by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
    by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega,
    by simpa using dCW 0 128 (by decide) 96 16 (by decide), dK0,
    (dCW 240 16 (by decide) 96 16 (by decide)).symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp₄]; exact k_c.sub_right (Region.sub_prefix (by decide))
  · rw [hsp₄]; exact k_s.sub_right (Offset.sub_base _ (by decide))
  · rw [hsp₄]; exact k_c.sub_right (Offset.sub_base _ (by decide))
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide)))
      (covers_left (covers_off pC' (by decide) (by decide))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))

theorem init_rel {s₀ s₀' : State} (hp : Proof.Sm4Gcm.initX86_64.pre s₀)
    (hp' : Proof.Sm4Gcm.initX86_64.pre s₀') (hq : Proof.Sm4Gcm.initX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') init fun _ _ => True := by
  obtain ⟨q₁, q₂, q₃, q₄⟩ := hq
  have hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s₀.gpr r = s₀'.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  -- The entry, and the call of `vg_sm4_expand_key`.
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (c := .block (save .rdx ++ ([.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] : List Instr)))
      [.rdi, .rsi, .rdx, .rsp] (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hag) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (G₁ := InitA s₀) (G₂ := InitA s₀')
    (fun s h => by subst h; exact initA_ok hp) (fun s h => by subst h; exact initA_ok hp')
  have hK : ∀ {t₀ : State}, ∀ s, InitA t₀ s → WP isa (.call keyFn.name keyFn.code) s (InitK t₀) :=
    fun s ⟨kc, h15, h13, hsp, hrd, hwr⟩ => WP.mono (key_call kc) fun _ g =>
      ⟨by rw [g.saved _ (by decide), h15], by rw [g.saved _ (by decide), h13], by rw [g.saved _ (by decide), hsp],
        g.rd.trans hrd, g.wr.trans hwr⟩
  have b := rel_wp (key_rel (P := fun s₁ s₂ => True ∧ InitA s₀ s₁ ∧ InitA s₀' s₂) fun s₁ s₂ h =>
      ⟨_, _, h.2.1.1, by rw [q₁, q₂]; exact h.2.2.1, by rw [h.2.1.2.2.2.1, h.2.2.2.2.2.1, q₄]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hK hK
  -- The arguments of the call of `vg_sm4_ctr32`, and the call.
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ InitK s₀ s₁ ∧ InitK s₀' s₂) [.r13, .r15, .rsp]
      (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1, q₂]
        · rw [h.2.1.1, h.2.2.1, q₃]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1, q₄]) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun s h => initB_ok hp h) (fun s h => initB_ok hp' h)
  have hC : ∀ {t₀ : State}, ∀ s, InitB t₀ s → WP isa (.call ctrFn.name ctrFn.code) s fun s' =>
      s'.gpr .r15 = t₀.gpr .rdx := fun s ⟨cc, h15, _⟩ => WP.mono (ctr_call cc) fun _ g =>
    by rw [g.saved _ (by decide), h15]
  have d := rel_wp (ctr_rel (P := fun s₁ s₂ => True ∧ InitB s₀ s₁ ∧ InitB s₀' s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.2.1.1, by rw [q₂, q₃]; exact h.2.2.1, by rw [h.2.1.2.2, h.2.2.2.2, q₄]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hC hC
  -- `restore`, from `W`.
  have e := rel_taint (P := fun s₁ s₂ => True ∧ s₁.gpr .r15 = s₀.gpr .rdx ∧ s₂.gpr .r15 = s₀'.gpr .rdx)
    (c := .block restore) [.r15] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1, h.2.2, q₃]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c (RelCT.seq d e)))

theorem init_ct :
    ConstantTime isa Proof.Sm4Gcm.initX86_64.pre Proof.Sm4Gcm.initX86_64.pub init :=
  ct_of_rel fun _ _ hp hp' hq => init_rel hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
