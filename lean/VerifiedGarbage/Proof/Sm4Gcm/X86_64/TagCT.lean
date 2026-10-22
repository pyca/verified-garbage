module
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag
public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flush

import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt

/-!
# SM4-GCM on x86-64: `tag` and `finTag` in two runs

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/TagCT.lean`, `FinTagCT.lean`): `tag` leaks only the
lengths, by AES-GCM's `lens_rel`, the taint analysis of the code before the
call and the call of `vg_sm4_ctr32` with the same arguments in both runs;
`finTag` branches on the length of the text, and `flush` has the same number
of buffered bytes (AES-GCM's `flush_rel`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr lens flush tlenO alenO)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env rel_taint rel_wp rel_ite_e rel_reassoc2 EnvAgree EnvAgree.regs
  env_agree lens_ok lens_rel flush_ok flush_rel and_self_beq and15 imm_eq WP.run)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

/-- `tag o`, with the same lengths. -/
theorem tag_rel {o : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (EnvAgree Ctx St W SP [.rbx, .rbp]) (tag v.callees o) fun _ _ => True := by
  have La := L.lay
  -- The arguments of the call, in each run.
  let G : State → Prop := fun s => Env Ctx St W SP s ∧ CtrCall s Ctx St (W + BitVec.ofNat 64 o) 1
  have hG : ∀ s, Env Ctx St W SP s → WP isa (.seq (lens v.callees 16)
      (.block (([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax,
        .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .r14)] : List Instr) ++ ptr .rdx .r15 o ++ ([.mov32 .rcx (imm 1)] : List Instr)))) s G :=
    fun s h => WP.mono (tagMid_ok v L ho h rfl rfl) fun _ M => ⟨M.env, M.call⟩
  have hL : ∀ s, Env Ctx St W SP s → WP isa (lens v.callees 16) s (Env Ctx St W SP) := fun s he =>
    WP.mono (lens_ok v La (.inr rfl) he rfl) fun _ h => h.1
  have hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block (([.mov .rax (.mem (at_ .r14 16)),
      .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
      .mov .rsi (.reg .r14)] : List Instr) ++ ptr .rdx .r15 o ++ ([.mov32 .rcx (imm 1)] : List Instr))) hc).isSome =
      true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have l : RelCT isa (EnvAgree Ctx St W SP [.rbx, .rbp]) (lens v.callees 16)
      fun s₁ s₂ => True ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ :=
    rel_wp (lens_rel v La (.inr rfl)) (fun _ _ h => ⟨h.1, h.2.1⟩) hL hL
  have b : RelCT isa (fun s₁ s₂ => True ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) _ fun _ _ => True :=
    rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.2.1 h.2.2) hc
  have pre : RelCT isa (EnvAgree Ctx St W SP [.rbx, .rbp]) _ fun s₁ s₂ => True ∧ G s₁ ∧ G s₂ :=
    rel_wp (RelCT.seq l b) (fun _ _ h => ⟨h.1, h.2.1⟩) (fun s h => hG s h) (fun s h => hG s h)
  refine rel_reassoc2 (RelCT.seq pre (ctr_rel fun s₁ s₂ h => ⟨_, _, _, _, h.2.1.2, h.2.2.2, ?_⟩))
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

end

/-- The lengths kept in `W`. -/
def FinS (Ctx St W SP : Addr) (aL tL : BitVec 64) (s : State) : Prop :=
  Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL

/-- After loading the lengths. -/
def FinA (Ctx St W SP : Addr) (aL tL : BitVec 64) (s : State) : Prop :=
  FinS Ctx St W SP aL tL s ∧ s.zf = some (decide (tL.toNat = 0)) ∧ s.gpr .rax = aL ∧ s.gpr .rbx = tL

/-- With the length of the buffered input in `rbx` (modulo 16 if `k`). -/
def FinB (Ctx St W SP : Addr) (aL tL : BitVec 64) (k : Bool) (s : State) : Prop :=
  FinS Ctx St W SP aL tL s ∧ s.gpr .rbx =
    if k then BitVec.ofNat 64 ((if tL = 0 then aL else tL).toNat % 16) else if tL = 0 then aL else tL

/-- With the lengths for the tag. -/
def FinD (Ctx St W SP : Addr) (aL tL : BitVec 64) (s : State) : Prop :=
  FinS Ctx St W SP aL tL s ∧ s.gpr .rbx = aL ∧ s.gpr .rbp = tL

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

omit L in
theorem FinS.keep {aL tL : BitVec 64} {s s' : State} (h : FinS Ctx St W SP aL tL s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : FinS Ctx St W SP aL tL s' :=
  ⟨h.1.keep hg hrd hwr, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem FinS.frame {aL tL : BitVec 64} {s s' : State} (h : FinS Ctx St W SP aL tL s)
    (he : Env Ctx St W SP s') (hf : Frame (AesGcm.X86_64.tFrame St W SP 16) s.mem s'.mem) :
    FinS Ctx St W SP aL tL s' := by
  have La := L.lay
  have dT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ AesGcm.X86_64.tFrame St W SP 16,
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (La.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact La.w_w (.inr (by omega)) (by omega) (by decide)
    · exact La.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (La.stk_w (by omega)).symm
  refine ⟨he, ?_, ?_⟩
  · rw [hf.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _) (dT 184 (by decide) (by decide))
      (by decide), h.2.1]
  · rw [hf.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (dT 192 (by decide) (by decide))
      (by decide), h.2.2]

omit L in
theorem finA_ok {aL tL : BitVec 64} {s : State} (h : FinS Ctx St W SP aL tL s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)),
      .alu .test .rbx (.reg .rbx)]) s (FinA Ctx St W SP aL tL) := by
  have r₁ := h.1.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := h.1.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hbx₁, hax₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)), .alu .test .rbx (.reg .rbx)] s =
        some s₁ ∧
      s₁.gpr .rbx = tL ∧ s₁.gpr .rax = aL ∧ s₁.zf = some (decide (tL.toNat = 0)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.2]
    · simp [gpr_setReg, h.2.1]
    · simp only [zf_arithFlags, h.2.2]
      have := and_self_beq tL.isLt
      rw [BitVec.ofNat_toNat] at this
      exact congrArg some this
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hzf₁, hax₁, hbx₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)

omit L in
theorem finSel_rel {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => True ∧ FinA Ctx St W SP aL tL s₁ ∧ FinA Ctx St W SP aL tL s₂)
      (.ite .e (.block [.mov .rbx (.reg .rax)]) (.block []))
      fun s₁ s₂ => FinB Ctx St W SP aL tL false s₁ ∧ FinB Ctx St W SP aL tL false s₂ := by
  refine rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1]) ?_ ?_
  · by_cases h0 : tL = 0
    swap
    · exact RelCT.of_false fun _ _ h => by
        have := h.1.2.1.2.1.symm.trans h.2; simp at this; exact h0 (BitVec.eq_of_toNat_eq (by simpa using this))
    have hM : ∀ s, FinA Ctx St W SP aL tL s → WP isa (.block [.mov .rbx (.reg .rax)]) s
        (FinB Ctx St W SP aL tL false) :=
      fun s h => WP.run (Q := fun s₂ => s₂ = s.setReg .rbx (s.gpr .rax)) ⟨_, by xrun [], rfl⟩ fun s₂ e => by
        subst e
        exact ⟨h.1.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
          by simp [gpr_setReg, h.2.2.1, h0]⟩
    exact (rel_wp (rel_taint [] (fun _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
      (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hM hM).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases h0 : tL = 0
    · exact RelCT.of_false fun _ _ h => by
        have := h.1.2.1.2.1.symm.trans h.2; simp [h0] at this
    exact RelCT.block_nil fun _ _ h => ⟨⟨h.1.2.1.1, by rw [h.1.2.1.2.2.2]; simp only [h0, ↓reduceIte, Bool.false_eq_true]⟩,
      ⟨h.1.2.2.1, by rw [h.1.2.2.2.2.2]; simp only [h0, ↓reduceIte, Bool.false_eq_true]⟩⟩

omit L in
theorem finMod_ok {aL tL : BitVec 64} {s : State} (h : FinB Ctx St W SP aL tL false s) :
    WP isa (.block [.alu .and .rbx (imm 15)]) s (FinB Ctx St W SP aL tL true) := by
  have hand := and15 (if tL = 0 then aL else tL)
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₁, run₁, hbx₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .and .rbx (imm 15)] s = some s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 ((if tL = 0 then aL else tL).toNat % 16) ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, h.2, hand, Bool.false_eq_true, ↓reduceIte]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, by simpa using hbx₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)

omit L in
theorem finD_ok {aL tL : BitVec 64} {s : State} (h : FinS Ctx St W SP aL tL s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))]) s
      (FinD Ctx St W SP aL tL) := by
  have r₃ := h.1.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have r₄ := h.1.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₅ ∧
      s₅.gpr .rbx = aL ∧ s₅.gpr .rbp = tL ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s.gpr r) ∧
      s₅.mem = s.mem ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.2.2]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₅, run₅, h.keep (fun r hr => ?_) hm₅ hrd₅ hwr₅, hbx₅, hbp₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)

/-- The buffered bytes absorbed. -/
theorem finFlush_rel {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => FinB Ctx St W SP aL tL true s₁ ∧ FinB Ctx St W SP aL tL true s₂)
      (flush v.callees 16) fun s₁ s₂ => True ∧ FinS Ctx St W SP aL tL s₁ ∧ FinS Ctx St W SP aL tL s₂ := by
  have La := L.lay
  have hF : ∀ s, FinB Ctx St W SP aL tL true s → WP isa (flush v.callees 16) s (FinS Ctx St W SP aL tL) :=
    fun s ⟨h, hbx⟩ => WP.mono (flush_ok v La (yo := 16) (.inr rfl)
      (x := List.replicate ((if tL = 0 then aL else tL).toNat % 16) 0) ⟨h.1, rfl⟩ (by simpa using hbx))
      fun _ o => h.frame L o.env o.frame
  have f : RelCT isa (fun s₁ s₂ => FinB Ctx St W SP aL tL true s₁ ∧ FinB Ctx St W SP aL tL true s₂)
      (flush v.callees 16) fun _ _ => True :=
    (flush_rel v La (.inr rfl)).mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]⟩) fun _ _ h => h
  exact rel_wp f (fun _ _ h => h) hF hF

/-- The tag. -/
theorem finTag2_rel {o : Nat} (ho : o = 0 ∨ o = 112) {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => True ∧ FinS Ctx St W SP aL tL s₁ ∧ FinS Ctx St W SP aL tL s₂)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))]) (tag v.callees o))
      fun _ _ => True := by
  have d := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ FinS Ctx St W SP aL tL s₁ ∧ FinS Ctx St W SP aL tL s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.2.1.1 h.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => finD_ok h) (fun s h => finD_ok h)
  have t : RelCT isa (fun s₁ s₂ => True ∧ FinD Ctx St W SP aL tL s₁ ∧ FinD Ctx St W SP aL tL s₂)
      (tag v.callees o) fun _ _ => True :=
    (tag_rel v L ho).mono (fun _ _ h => ⟨h.2.1.1.1, h.2.2.1.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) fun _ _ h => h
  exact RelCT.seq d t

/-- `finTag o`, with the same lengths. -/
theorem finTag_rel {o : Nat} (ho : o = 0 ∨ o = 112) {aL tL : BitVec 64} :
    RelCT isa (fun s₁ s₂ => FinS Ctx St W SP aL tL s₁ ∧ FinS Ctx St W SP aL tL s₂) (finTag v.callees o)
      fun _ _ => True := by
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => FinS Ctx St W SP aL tL s₁ ∧ FinS Ctx St W SP aL tL s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.1 h.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => finA_ok h) (fun s h => finA_ok h)
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => FinB Ctx St W SP aL tL false s₁ ∧ FinB Ctx St W SP aL tL false s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.1.1 h.2.1.1) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun s h => finMod_ok h) (fun s h => finMod_ok h)
  exact RelCT.seq a (RelCT.seq finSel_rel (RelCT.seq b (RelCT.seq ((finFlush_rel v L).mono (fun _ _ h => h.2)
    fun _ _ h => h) (finTag2_rel v L ho))))

end

end VG.Proof.Sm4Gcm.X86_64
