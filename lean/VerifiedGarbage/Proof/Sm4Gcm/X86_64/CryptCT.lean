module
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SM4-GCM on x86-64: `crypt` in two runs

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/CryptCT.lean`): two runs of `crypt` over data at the
same address, of the same length, after the same number of bytes modulo 16,
leak the same: the code between the calls of `vg_sm4_ctr32` is checked by the
taint analysis, from the registers `CrIn` and `CrMid` fix, and each call has
the same arguments in both runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr splitWhole cryptHead xorLoop)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.AesGcm.X86_64 (Lay Env DataW rel_regs rel_taint rel_wp rel_ite_e EnvAgree EnvAgree.regs absRegs
  wholeSplit_ok test_ok covers_left covers_cons)

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

omit L in
theorem CrMid.agree {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁) (h₂ : CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂) :
    ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r12, h₂.r12]
  · rw [h₁.rbp, h₂.rbp]
  · rw [h₁.env.r13, h₂.env.r13]
  · rw [h₁.env.r14, h₂.env.r14]
  · rw [h₁.env.r15, h₂.env.r15]
  · rw [h₁.env.rsp, h₂.env.rsp]

/-- Whole blocks. -/
theorem cryptWhole_rel {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂)
      cryptWhole fun _ _ => True := by
  let Sp : State → Prop := fun s₁ => Env Ctx St W SP s₁ ∧ DataW4 Ctx St W SP s₁ D n ∧ j ≤ n ∧
    s₁.gpr .rdx = D + BitVec.ofNat 64 j ∧ s₁.gpr .rcx = BitVec.ofNat 64 ((n - j) / 16)
  have hS : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP icb P D n m j s →
      WP isa (.block (splitWhole .rdx .rcx ++ [.alu .test .rcx (.reg .rcx)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hdx, hcx, -, -, -, hg₁, -, hrd₁, hwr₁⟩ :=
      wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) h.data.dw.ok.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le, hdx, hcx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ ∧
      CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  let Ar : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) ((n - j) / 16)
  have hA : ∀ s, Sp s → WP isa (.block (([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rsi .r14 48)) s Ar :=
    fun s ⟨he, hd, hj, hdx, hcx⟩ => by
      obtain ⟨s₂, run₂, hdi, hsi, hg₂, -, hrd₂, hwr₂⟩ := cwArgs_ok he
      have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
      exact WP.of_runBlock ⟨s₂, run₂, he₂, cwCall_of L he₂ (hd.of_eq hrd₂ hwr₂) hj (by omega_arith) hdi hsi
        (by rw [hg₂ _ (by decide) (by decide), hdx]) (by rw [hg₂ _ (by decide) (by decide), hcx])⟩
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => ((True ∧ Sp s₁ ∧ Sp s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1.2.1.1, h.1.2.2.1, fun _ h => by cases h⟩)
    ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hA hA
  refine (RelCT.seq b (ctr_rel fun s₁ s₂ h => ⟨_, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)).mono
    (fun _ _ h => ⟨⟨trivial, h.1.2.1, h.1.2.2⟩, h.2⟩) fun _ _ h => h
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

/-- The arguments of `cryptTail`'s call of `vg_sm4_ctr32`. -/
theorem ctTailArgs_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP icb P D n m₀ j s) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rsi .r14 48 ++ ptr .rdx .r14 64 ++
        ([.mov32 .rcx (imm 1)] : List Instr))) s fun s₂ =>
      Env Ctx St W SP s₂ ∧ CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) 1 ∧
      s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j) := by
  have he := h.env
  have h13 := he.r13; have h14 := he.r14
  have w₁ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13)] ++ ptr .rsi .r14 48 ++ ptr .rdx .r14 64 ++ [.mov32 .rcx (imm 1)]) s = some s₂ ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .rdx = St + BitVec.ofNat 64 64 ∧ s₂.gpr .rcx = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [h13, h14, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  refine ⟨he₂, ?_, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r12],
    by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]⟩
  refine ⟨hdi, hsi, hdx, hcx, by rw [hk]; exact L.sp, by have := L.lay.cw; omega,
    by have := L.lay.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
    by have := L.lay.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith,
    (L.lay.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    (L.lay.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    L.lay.st_st (.inl (by decide)) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [hk]; exact L.ks.sub_right (Lay.stSub (by decide))
  · rw [hk]; exact L.ks.sub_right (Lay.stSub (by decide))
  · refine covers_cons ?_ (covers_cons (covers_left (he₂.perm.stC (by decide)))
      (covers_left (he₂.perm.stC (by decide))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega_arith⟩
  · exact covers_cons (he₂.perm.stC (by decide)) (he₂.perm.stC (by decide))

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_rel {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂)
      cryptTail fun _ _ => True := by
  have hT : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP icb P D n m j s →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) s (CrMid Ctx St W SP icb P D n m j) := fun s h => by
    obtain ⟨s₁, run₁, -, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (by have := h.data.dw.ok.lt; omega)
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.le, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁, fun hc => by rw [hm₁]; exact h.ctr hc,
      fun hc => by rw [hm₁]; exact h.done hc, by rw [hm₁]; exact h.rest, h.whole, by rw [hm₁]; exact h.frame⟩
  have t := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ ∧
      CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)
  refine RelCT.seq t (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The arguments of the call, and what it keeps.
  let G : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) 1 ∧
    s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j)
  let K : State → Prop := fun s₃ => Env Ctx St W SP s₃ ∧
    s₃.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₃.gpr .rbp = BitVec.ofNat 64 (n - j)
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => ((((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => CrMid.agree h.1.2.1 h.1.2.2 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) (G₁ := G) (G₂ := G) (fun s h => ctTailArgs_ok L h)
    (fun s h => ctTailArgs_ok L h)
  have hK : ∀ s, G s → WP isa (.call ctrFn.name ctrFn.code) s K := fun s ⟨he, hc, h12, hbp⟩ =>
    WP.mono (ctr_call hc) fun _ g => ⟨he.of_saved g.saved g.rd g.wr,
      by rw [g.saved _ (by decide), h12], by rw [g.saved _ (by decide), hbp]⟩
  have c := rel_wp (ctr_rel (P := fun s₁ s₂ => True ∧ G s₁ ∧ G s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.2.1.2.1, h.2.2.2.1, by rw [h.2.1.1.rsp, h.2.2.1.rsp]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hK hK
  have d := rel_taint (P := fun s₁ s₂ => True ∧ K s₁ ∧ K s₂)
    (c := .seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r14 64 ++
      ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop)
    [.r12, .rbp, .r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]
      · rw [h.2.1.1.r13, h.2.2.1.r13]
      · rw [h.2.1.1.r14, h.2.2.1.r14]
      · rw [h.2.1.1.r15, h.2.2.1.r15]
      · rw [h.2.1.1.rsp, h.2.2.1.rsp]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq c d)

/-- `crypt`, over data at the same address, of the same length, after the
same number of bytes modulo 16. -/
theorem crypt_rel {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} (hP : P₁ % 16 = P₂ % 16) :
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP icb₂ P₂ D n s₂)
      crypt fun _ _ => True := by
  have hag : ∀ s₁ s₂, CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP icb₂ P₂ D n s₂ →
      ∀ r ∈ absRegs, s₁.gpr r = s₂.gpr r := fun s₁ s₂ h r hr => by
    simp only [absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.rbx, h.2.rbx, hP]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  have hT : ∀ {r : Reg} {icb : Block} {P : Nat} {k : Nat} (s : State), CrIn Ctx St W SP icb P D n s →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => CrIn Ctx St W SP icb P D n s' ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, -, hrd₁, hwr₁⟩ := test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁⟩, hz⟩
  have t₁ := rel_wp (rel_regs (P := fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧
      CrIn Ctx St W SP icb₂ P₂ D n s₂) absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.dw.ok.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.dw.ok.lt)
  refine RelCT.seq t₁ (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  have hr₁ := Nat.mod_lt P₁ (show 16 > 0 by decide)
  have hr₂ := Nat.mod_lt P₂ (show 16 > 0 by decide)
  have t₂ := rel_wp (rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (n = 0))) ∧
      CrIn Ctx St W SP icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega))
  have i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (P₁ % 16 = 0))) ∧
        CrIn Ctx St W SP icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (P₂ % 16 = 0)))
      (.ite .e (.block []) cryptHead) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ := by
    refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : P₁ % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, h.1.2.1.1.mid ho, h.1.2.2.1.mid (by omega)⟩
    · by_cases ho : P₁ % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (rel_wp ((rel_taint absRegs (P := fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧
          CrIn Ctx St W SP icb₂ P₂ D n s₂) hag ⟨_, by taint_decide⟩).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, CrMid Ctx St W SP icb₁ P₁ D n m (min (16 - P₁ % 16) n) s)
        (G₂ := fun s => ∃ m, CrMid Ctx St W SP icb₂ P₂ D n m (min (16 - P₂ % 16) n) s)
        (fun s h => WP.mono (cryptHead_ok h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (cryptHead_ok h hn0 (by omega)) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
        fun _ _ ⟨_, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ => ⟨_, m₁, m₂, h₁, by rw [hP]; exact h₂⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  refine RelCT.seq t₂ (RelCT.seq i₂ ?_)
  refine RelCT.exists_ fun j => RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := rel_wp (cryptWhole_rel L (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := j)) (fun _ _ h => h)
    (fun s h => cryptWhole_ok L h (h.ciph L)) (fun s h => cryptWhole_ok L h (h.ciph L))
  exact RelCT.seq hw ((cryptTail_rel L).mono (fun _ _ h => h.2) fun _ _ h => h)

/-- `cryptAl`, for data at the same address, of the same length, from the
start of a keystream block. -/
theorem cryptAl_rel {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} (hP₁ : P₁ % 16 = 0)
    (hP₂ : P₂ % 16 = 0) :
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP icb₂ P₂ D n s₂)
      cryptAl fun _ _ => True := by
  suffices k : RelCT isa (fun s₁ s₂ => ∃ m₁ m₂ : Mem, CrMid Ctx St W SP icb₁ P₁ D n m₁ 0 s₁ ∧
      CrMid Ctx St W SP icb₂ P₂ D n m₂ 0 s₂) cryptAl fun _ _ => True from
    k.mono (fun s₁ s₂ h => ⟨s₁.mem, s₂.mem, h.1.mid hP₁, h.2.mid hP₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := rel_wp (cryptWhole_rel L (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := 0)) (fun _ _ h => h)
    (fun s h => cryptWhole_ok L h (h.ciph L)) (fun s h => cryptWhole_ok L h (h.ciph L))
  exact RelCT.seq hw ((cryptTail_rel L).mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.Sm4Gcm.X86_64
