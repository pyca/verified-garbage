module

import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.J0
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.J0
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.Env
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Sm4Gcm.X86_64.CryptCT`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86-64: `crypt` in two runs

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OneBlocks/CT.lean`): two runs of `crypt` over data at the
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
variable {Ctx St W SP : Addr} {N : Nat} (L : Lay4 Ctx St W SP N)
include L

omit L in
theorem CrMid.agree {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N) (h₂ : CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N) :
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
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N)
      cryptWhole fun _ _ => True := by
  let Sp : State → Prop := fun s₁ => Env Ctx St W SP s₁ N ∧ DataW4 Ctx St W SP s₁ D n N ∧ j ≤ n ∧
    s₁.gpr .rdx = D + BitVec.ofNat 64 j ∧ s₁.gpr .rcx = BitVec.ofNat 64 ((n - j) / 16)
  have hS : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP icb P D n m j s N →
      WP isa (.block (splitWhole .rdx .rcx ++ [.alu .test .rcx (.reg .rcx)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hdx, hcx, -, -, -, hg₁, -, hrd₁, hwr₁⟩ :=
      wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) h.data.dw.ok.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le, hdx, hcx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N ∧
      CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  let Ar : State → Prop := fun s₂ => Env Ctx St W SP s₂ N ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) ((n - j) / 16)
  have hA : ∀ s, Sp s → WP isa (.block (([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rsi .r14 48)) s Ar :=
    fun s ⟨he, hd, hj, hdx, hcx⟩ => by
      obtain ⟨s₂, run₂, hdi, hsi, hg₂, -, hrd₂, hwr₂⟩ := cwArgs_ok he
      have he₂ : Env Ctx St W SP s₂ N := he.keep (fun r hr => by
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
    (h : CrMid Ctx St W SP icb P D n m₀ j s N) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rsi .r14 48 ++ ptr .rdx .r14 64 ++
        ([.mov32 .rcx (imm 1)] : List Instr))) s fun s₂ =>
      Env Ctx St W SP s₂ N ∧ CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) 1 ∧
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
  have he₂ : Env Ctx St W SP s₂ N := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  refine ⟨he₂, ?_, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r12],
    by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]⟩
  refine ⟨hdi, hsi, hdx, hcx, by rw [hk]; exact L.sp, by have := L.lay.cw; omega_using [this],
    by have := L.lay.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [this],
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
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N)
      cryptTail fun _ _ => True := by
  have hT : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP icb P D n m j s N →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) s (CrMid Ctx St W SP icb P D n m j · N) := fun s h => by
    obtain ⟨s₁, run₁, -, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (by have := h.data.dw.ok.lt; omega_using [this])
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.le, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁, fun hc => by rw [hm₁]; exact h.ctr hc,
      fun hc => by rw [hm₁]; exact h.done hc, by rw [hm₁]; exact h.rest, h.whole, by rw [hm₁]; exact h.frame⟩
  have t := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N ∧
      CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)
  refine RelCT.seq t (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The arguments of the call, and what it keeps.
  let G : State → Prop := fun s₂ => Env Ctx St W SP s₂ N ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) 1 ∧
    s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j)
  let K : State → Prop := fun s₃ => Env Ctx St W SP s₃ N ∧
    s₃.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₃.gpr .rbp = BitVec.ofNat 64 (n - j)
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => ((((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N) ∧ s₁.zf = some false))
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
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧ CrIn Ctx St W SP icb₂ P₂ D n s₂ N)
      crypt fun _ _ => True := by
  have hag : ∀ s₁ s₂, CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧ CrIn Ctx St W SP icb₂ P₂ D n s₂ N →
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
  have hT : ∀ {r : Reg} {icb : Block} {P : Nat} {k : Nat} (s : State), CrIn Ctx St W SP icb P D n s N →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => CrIn Ctx St W SP icb P D n s' N ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, -, hrd₁, hwr₁⟩ := test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁⟩, hz⟩
  have t₁ := rel_wp (rel_regs (P := fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧
      CrIn Ctx St W SP icb₂ P₂ D n s₂ N) absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.dw.ok.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.dw.ok.lt)
  refine RelCT.seq t₁ (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  have hr₁ := Nat.mod_lt P₁ (show 16 > 0 by decide)
  have hr₂ := Nat.mod_lt P₂ (show 16 > 0 by decide)
  have t₂ := rel_wp (rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧ s₁.zf = some (decide (n = 0))) ∧
      CrIn Ctx St W SP icb₂ P₂ D n s₂ N ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega_using []))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega_using []))
  have i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧ s₁.zf = some (decide (P₁ % 16 = 0))) ∧
        CrIn Ctx St W SP icb₂ P₂ D n s₂ N ∧ s₂.zf = some (decide (P₂ % 16 = 0)))
      (.ite .e (.block []) cryptHead) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        CrMid Ctx St W SP icb₁ P₁ D n m₁ j s₁ N ∧ CrMid Ctx St W SP icb₂ P₂ D n m₂ j s₂ N := by
    refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : P₁ % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, h.1.2.1.1.mid ho, h.1.2.2.1.mid (by omega_using [hP, ho])⟩
    · by_cases ho : P₁ % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (rel_wp ((rel_taint absRegs (P := fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧
          CrIn Ctx St W SP icb₂ P₂ D n s₂ N) hag ⟨_, by taint_decide⟩).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, CrMid Ctx St W SP icb₁ P₁ D n m (min (16 - P₁ % 16) n) s N)
        (G₂ := fun s => ∃ m, CrMid Ctx St W SP icb₂ P₂ D n m (min (16 - P₂ % 16) n) s N)
        (fun s h => WP.mono (cryptHead_ok h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (cryptHead_ok h hn0 (by omega_using [hP, ho])) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
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
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP icb₁ P₁ D n s₁ N ∧ CrIn Ctx St W SP icb₂ P₂ D n s₂ N)
      cryptAl fun _ _ => True := by
  suffices k : RelCT isa (fun s₁ s₂ => ∃ m₁ m₂ : Mem, CrMid Ctx St W SP icb₁ P₁ D n m₁ 0 s₁ N ∧
      CrMid Ctx St W SP icb₂ P₂ D n m₂ 0 s₂ N) cryptAl fun _ _ => True from
    k.mono (fun s₁ s₂ h => ⟨s₁.mem, s₂.mem, h.1.mid hP₁, h.2.mid hP₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := rel_wp (cryptWhole_rel L (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := 0)) (fun _ _ h => h)
    (fun s h => cryptWhole_ok L h (h.ciph L)) (fun s h => cryptWhole_ok L h (h.ciph L))
  exact RelCT.seq hw ((cryptTail_rel L).mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.Sm4Gcm.X86_64

end

end

/-! ### `Sm4Gcm.X86_64.Seal`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86_64.OneShot`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86-64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OneShot.lean`), their streaming state is in `work`, at
`W + 16`. The entry takes `W` from the stack and keeps the public arguments
in it (`oneEntry_ok`); AES-GCM's `oneAad` computes `J₀` and absorbs the
additional data, padded (`oneMid_ok`); `oneCrypt` runs counter mode over the
data from the first counter block (`oneCrypt_ok`); and `oneTag o` absorbs the
ciphertext, padded, and writes the tag to `W + o` (`oneTag_ok`). The calls of
`vg_sm4_ctr32` use the `stkN` bytes below the return address.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr save stO aadO alenO dataO lenO tlenO oneAad)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm DataOk DataW SavedAt savedR save_ok covers_of_mem covers_off
  covers_left in_off add_ofNat_assoc blockAt_frame bytesAt_frame ctxH_eq AbsIn absorbPad_ok oneR lensBlock_mod_left)

/-- What the precondition of `seal` (`k = 3`) and `open` (`k = 4`) gives. -/
structure OneCtx (s : State) (k : Nat) (Ctx W SP Np A D : Addr) (nl al n : Nat) : Prop where
  lay : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP
  perm : Perm Ctx (W + BitVec.ofNat 64 16) W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : ∀ i < k, InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 * (i + 1))) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩
  nonce : DataOk (W + BitVec.ofNat 64 16) W SP s Np nl
  aad : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  data : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩

/-- `OneCtx`, from `oneLay` and where the buffers are, with `work` the `w`-th
of `k` arguments on the stack. -/
theorem OneCtx.of {w k : Nat} {s : State} (hp : Proof.Sm4Gcm.oneLay w k s)
    (pc : Covers [⟨s.gpr .rdi, 256⟩] (s.rd ++ s.wr)) (pn : Covers [⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩] (s.rd ++ s.wr))
    (pa : Covers [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr))
    (pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * k⟩] (s.rd ++ s.wr))
    (pd : Covers [⟨s.gpr .r9, (stackArg s 0).toNat⟩] s.wr) (pW : Covers [⟨stackArg s w, 2560⟩] s.wr) :
    OneCtx s k (s.gpr .rdi) (stackArg s w) (s.gpr .rsp) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r9)
      (s.gpr .rdx).toNat (s.gpr .r8).toNat (stackArg s 0).toNat := by
  simp only [Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.args,
    Proof.Sm4Gcm.arg, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨d_cd, d_cw, -, d_nw, -, d_aw, d_dw, d_da, d_wa, r_d, r_w, t_c, t_n, t_a, t_d, t_w, wc, wn, wa, wd, ww,
    sp, wsp⟩ := hp
  obtain b8 := below8_stk (s.gpr .rsp)
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at d_da d_wa
  obtain hSt : (⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ : Region).Sub ⟨stackArg s w, 2560⟩ := Lay.wSub (by decide)
  obtain L : Lay (s.gpr .rdi) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) (s.gpr .rsp) := by
    refine ⟨wc, ?_, ww, d_cw.sub_right hSt, d_cw, ?_, ?_, t_c.sub_left b8, (t_w.sub_left b8).sub_right hSt,
      t_w.sub_left b8, by decide, by decide⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le ((stackArg s w).toNat + 16 % 2 ^ 64) (2 ^ 64)
      omega_arith
    · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
        (by omega_arith) (by omega_arith)
    · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
        (by omega_arith) (by omega_arith)
  refine ⟨⟨L, sp, t_c, t_w.sub_right hSt, t_w, by decide⟩, ⟨pc, covers_off pW (show 16 + 80 ≤ 2560 by decide) (by decide), pW⟩,
    ww, fun i hi => ?_, d_wa.symm,
    ⟨pn, by have := (s.gpr .rdx).isLt; omega_arith, wn, d_nw.sub_right hSt, d_nw, t_n.sub_left b8⟩,
    ⟨pa, by have := (s.gpr .r8).isLt; omega_arith, wa, d_aw.sub_right hSt, d_aw, t_a.sub_left b8⟩,
    ⟨⟨⟨covers_left pd, by have := (stackArg s 0).isLt; omega_arith, wd, d_dw.sub_right hSt, d_dw, t_d.sub_left b8⟩,
      pd, d_cd⟩, t_d⟩,
    r_d, r_w, d_dw, d_da.symm⟩
  have := in_off pm (d := 8 * i) (n := 8) (by omega_arith) (by omega_arith)
  rwa [add_ofNat_assoc, show 8 + 8 * i = 8 * (i + 1) by omega_arith] at this

/-- What `seal`'s precondition gives: `OneCtx`, and `tag`, 16 bytes to write
at `T` (the second argument on the stack). -/
theorem OneCtx.ofSeal {s : State} (hp : Proof.Sm4Gcm.sealPre s) :
    OneCtx s 3 (s.gpr .rdi) (stackArg s 2) (s.gpr .rsp) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r9)
      (s.gpr .rdx).toNat (s.gpr .r8).toNat (stackArg s 0).toNat ∧ Covers [⟨stackArg s 1, 16⟩] s.wr ∧
      (⟨stackArg s 1, 16⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩ ∧
      (⟨stackArg s 1, 16⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, 16⟩ ∧
      (below (s.gpr .rsp) stkN).Disjoint ⟨stackArg s 1, 16⟩ := by
  have hp' := hp
  simp only [Proof.Sm4Gcm.sealPre, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.args, Proof.Sm4Gcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, -, r_t, t_t, -⟩ := hp'
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 2) hl ?_ ?_ ?_ ?_ ?_ ?_, ?_, d_td, d_tw, r_t, t_t⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- What `open`'s precondition gives: `OneCtx`, and the received tag, the
`tag_len` (third argument on the stack) bytes to read at `T` (the second). -/
theorem OneCtx.ofOpen {s : State} (hp : Proof.Sm4Gcm.openPre s) :
    OneCtx s 4 (s.gpr .rdi) (stackArg s 3) (s.gpr .rsp) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r9)
      (s.gpr .rdx).toNat (s.gpr .r8).toNat (stackArg s 0).toNat ∧
      Covers [⟨stackArg s 1, (stackArg s 2).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩ ∧
      (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, 2560⟩ ∧
      (below (s.gpr .rsp) stkN).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩ := by
  have hp' := hp
  simp only [Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.args, Proof.Sm4Gcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, t_t, -⟩ := hp'
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 3) hl ?_ ?_ ?_ ?_ ?_ ?_, ?_, d_td, d_tw, t_t⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

/-- After `oneEntry`. -/
structure OneEntry (s₀ : State) (Ctx W SP A D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r8
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = s₀.gpr .rsi
  rbp : s.gpr .rbp = s₀.gpr .rdx
  rsp : s.gpr .rsp = SP
  saved : SavedAt s.mem W s₀
  frame : Frame [oneR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `oneEntry wo`, with `W` at `[rsp + wo]`. -/
theorem oneEntry_ok {s : State} {k : Nat} (hk : 1 ≤ k) {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) {wo : Nat} (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP)
    (hA : s.gpr .rcx = A) (hD : s.gpr .r9 = D) (hn : (stackArg s 0).toNat = n)
    (hW' : s.mem.readW (SP + BitVec.ofNat 64 wo) 64 = W) (a₂ : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 wo) 8) :
    WP isa (.block (oneEntry wo)) s (OneEntry s Ctx W SP A D n) := by
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  have a₀ := C.args 0 hk
  simp only [Nat.zero_add, Nat.mul_one] at a₀
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp wo))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, a₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := C.perm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [VG.Impl.AesGcm.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off C.perm.w (show 232 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off C.perm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off C.perm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off C.perm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off C.perm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₀
  have s8 : Region.Sub ⟨SP + BitVec.ofNat 64 8, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := Region.sub_prefix (by omega_arith)
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [hm₀] at f₁
    rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (C.dA.sub_left s8).sub_right (Lay.wSub (by decide))) (by decide), hn']
  have sA : ∀ d, 176 ≤ d → d + 8 ≤ 240 → Mem.Sep (SP + BitVec.ofNat 64 8) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d _ h₂ => by
      have dd : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ :=
        (C.dA.sub_left s8).sub_right (Lay.wSub (by omega_arith))
      exact dd.sep (Region.contains_self _ _) (Region.contains_self _ _)
  have p₁ := sA 232 (by decide) (by decide)
  have p₂ := sA 184 (by decide) (by decide)
  have p₃ := sA 200 (by decide) (by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by have := C.ww; omega_arith) (by have := C.ww; omega_arith)
  have q₀ := sep 232 184 (by decide) (by decide) (by decide)
  have q₁ := sep 232 200 (by decide) (by decide) (by decide)
  have q₂ := sep 232 208 (by decide) (by decide) (by decide)
  have q₃ := sep 232 192 (by decide) (by decide) (by decide)
  have q₄ := sep 184 200 (by decide) (by decide) (by decide)
  have q₅ := sep 184 208 (by decide) (by decide) (by decide)
  have q₆ := sep 184 192 (by decide) (by decide) (by decide)
  have q₇ := sep 200 208 (by decide) (by decide) (by decide)
  have q₈ := sep 200 192 (by decide) (by decide) (by decide)
  have q₉ := sep 208 192 (by decide) (by decide) (by decide)
  have e : oneEntry wo = [.mov .rax (.mem (at_ .rsp wo))] ++ save .rax ++
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8, .store (at_ .r15 dataO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rax, .store (at_ .r15 tlenO) .rax,
        .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)] := by
    simp [oneEntry, ptr, stO]
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .r15), .alu .add .r14 (imm 16), .mov .r13 (.reg .rdi),
        .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8, .store (at_ .r15 dataO) .r9,
        .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rax, .store (at_ .r15 tlenO) .rax,
        .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = s.gpr .rsi ∧
      s₂.gpr .rbp = s.gpr .rdx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 232) A).writeW (W + BitVec.ofNat 64 184) (s.gpr .r8)).writeW
        (W + BitVec.ofNat 64 200) D).writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n)).writeW
          (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₀], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hax₁]
    · simp [gpr_setReg, gpr_arithFlags, hrdi, hCtx]
    · simp [gpr_setReg, gpr_arithFlags, hrsi]
    · simp [gpr_setReg, gpr_arithFlags, hrdx]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags, gpr_arithFlags,
        Mem.readW_writeW_sep, hn₁, hrcx, hr8, hr9, hA, hD]
    all_goals rfl
  rw [e]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 64⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 240 → (⟨W + BitVec.ofNat 64 176, 64⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by have := C.ww; omega_arith)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 232 ∧ v = A) ∨ (d = 184 ∧ v = s.gpr .r8) ∨ (d = 200 ∧ v = D) ∨
      (d = 208 ∧ v = BitVec.ofNat 64 n) ∨ (d = 192 ∧ v = BitVec.ofNat 64 n) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64,
        Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, C.perm.of_eq hrd' hwr'⟩, rd 232 _ (.inl ⟨rfl, rfl⟩),
    rd 184 _ (.inr (.inl ⟨rfl, rfl⟩)), rd 200 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))),
    rd 208 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), rd 192 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))),
    h12, hbp, hsp, ?_, ?_, hrd', hwr'⟩
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by have := C.ww; omega_arith) (by have := C.ww; omega_arith)
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- What `seal` and `open` write after their entry: `W` but for the saved
registers and the kept values, the data and the stack. -/
abbrev oneFrame (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP stkN]

/-- What the pieces but `crypt` and the tag write: `W` but for the received
tag, the saved registers and the kept values, and the stack. -/
abbrev wFrame (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, below SP stkN]

theorem wFrame_one {W D SP : Addr} {n o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) m m') : Frame (oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by omega_arith)⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem wFrame_cons {W SP : Addr} {o : Nat} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) m m' := h.mono fun _ hr => List.mem_cons_of_mem _ hr

/-- AES-GCM's `wFrame`, with the stack below `SP` of its own calls. -/
theorem wFrame_of_aes {W SP : Addr} {m m' : Mem} (h : Frame (AesGcm.X86_64.wFrame W SP) m m') :
    Frame (wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨below SP stkN, by simp, below8_stk SP⟩

theorem w_wFrame {W SP : Addr} {d k : Nat}
    (h : (16 ≤ d ∧ d + k ≤ 128) ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ wFrame W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩

/-- What the pieces write, inside `W` and the stack. -/
theorem wFrame_w {W SP : Addr} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame [⟨W, 2560⟩, below SP stkN] m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem oneR_w {W SP : Addr} : ∃ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], Region.Sub (oneR W) r :=
  ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- A part of `W` in `oneFrame`. -/
theorem w_oneFrame {W D SP : Addr} {n d k : Nat}
    (h : d + k ≤ 128 ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r ∈ oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r := by
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W h⟩
  · exact ⟨⟨W + BitVec.ofNat 64 216, 8⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩

theorem st_oneFrame {W D SP : Addr} {n d k : Nat} (h : d + k ≤ 80) :
    ∃ r ∈ oneFrame W D SP n, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r := by
  rw [add_ofNat_assoc]; exact w_oneFrame (.inl (by omega_arith))

/-- What `crypt` writes, in `oneFrame`. -/
theorem crFrame_one {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (crFrame (W + BitVec.ofNat 64 16) SP D n) m m') :
    Frame (oneFrame W D SP n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
  · exact st_oneFrame (by decide)
  · exact ⟨below SP stkN, by simp, fun _ h => h⟩

/-- What `tag o` writes. -/
theorem tagFrame_one {W SP : Addr} {o : Nat} {m m' : Mem}
    (h : Frame (tagFrame (W + BitVec.ofNat 64 16) W SP o) m m') :
    Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r, hr, hs⟩ := w_wFrame (W := W) (SP := SP) (d := 16) (k := 32) (.inl ⟨by decide, by decide⟩)
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · obtain ⟨r, hr, hs⟩ := w_wFrame (W := W) (SP := SP) (d := 96) (k := 16) (.inl ⟨by decide, by decide⟩)
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · obtain ⟨r, hr, hs⟩ := w_wFrame (W := W) (SP := SP) (d := 512) (k := 256) (.inr (.inr ⟨by decide, by decide⟩))
    exact ⟨r, List.mem_cons_of_mem _ hr, hs⟩
  · exact ⟨below SP stkN, List.mem_cons_of_mem _ (by simp), fun _ h => h⟩

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The kept values are outside `oneFrame`. -/
theorem kept_oneFrame {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h : (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ oneFrame W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.lay.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact L.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm
  · exact (L.kw.sub_right (Lay.wSub (by omega_arith))).symm

theorem saved_oneFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ oneFrame W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.lay.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (L.kw.sub_right (Lay.wSub (by decide))).symm

end

/-- What `seal` and `open` share: `J₀`, the additional data, and their
effects so far, from the entry. -/
structure OneMid (s₀ : State) (Ctx W SP D : Addr) (n : Nat) (H : Block) (iv a : List Byte) (mE : Mem) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r8
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  abs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
    (a ++ zeros (padLen a.length))
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  saved : SavedAt s.mem W s₀
  frame : Frame [⟨W, 2560⟩, below SP stkN] s₀.mem s.mem
  fr : Frame (wFrame W SP) mE s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- AES-GCM's `oneAad`, after the entry. -/
theorem oneMid_ok (v : GcmImpl) {k : Nat} {s s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rsi = Np) (hnl : (s.gpr .rdx).toNat = nl) (hal : (s.gpr .r8).toNat = al) :
    WP isa (oneAad v.callees) s₁
      (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) s₁.mem) := by
  have L := C.lay
  obtain dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W], (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.lay.cw'.sub_left (Lay.ctxSub (by decide))))]
  obtain hiv : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame E.frame (dW _ _ C.nonce.w) (by have := C.nonce.lt; omega_arith)
  obtain haa : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame E.frame (dW _ _ C.aad.w) (by have := C.aad.lt; omega_arith)
  obtain hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (AesGcm.X86_64.oneAad_ok v L.lay E.env hH₁ (by rw [E.r12, hNp])
    (by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr)
    C.dE E.aad hal')) fun s₂ ⟨ao, hrd₂, hwr₂⟩ => ?_
  rw [hiv, haa] at ao
  obtain f₂ := AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons ao.frame)
  obtain kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (AesGcm.X86_64.kept_oneFrame L.lay C.dE hd) (by decide)
  obtain fr := wFrame_of_aes ao.frame
  refine ⟨ao.env, ao.hH, by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact E.dat,
    by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact E.len, by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact E.tlen,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact E.alen, ao.j0, ao.abs, ao.cb,
    E.saved.frame f₂ (AesGcm.X86_64.saved_oneFrame L.lay C.dE), ?_, fr, hrd₂.trans E.rd, hwr₂.trans E.wr⟩
  exact (E.frame.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact oneR_w).trans (wFrame_w fr)

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneCrypt`: counter mode over the data, from the first counter block. -/
theorem oneCrypt_ok {icb : Block} {P : Nat} (hP : P % 16 = 0) {D : Addr} {n : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa oneCrypt s fun s' => CrOut Ctx (W + BitVec.ofNat 64 16) W SP icb P D n s.mem s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (P % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hP]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have := AesGcm.X86_64.WP.with_rdwr (cryptAl_ok L (icb := icb) (P := P) ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁⟩ hP)
  rw [hm₁] at this
  exact WP.mono this fun s' ⟨h, a, b⟩ => ⟨h, a.trans hrd₁, b.trans hwr₁⟩

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneTag o`: the ciphertext absorbed, padded, and the tag into `W + o`. -/
theorem oneTag_ok {o : Nat} (ho : o = 0 ∨ o = 112) {D : Addr} {n N al : Nat} {H : Block} {x : List Byte}
    (hx16 : x.length % 16 = 0) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hCD : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (oneTag v.callees o) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
      Frame (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
              zeros (padLen (x ++ bytesAt s.mem D n).length))))
            [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx (blockAt s.mem (W + BitVec.ofNat 64 16)))) := by
  have La := L.lay
  obtain kp : ∀ {m m' : Mem}, Frame (AesGcm.X86_64.oneFrame W D SP n) m m' → ∀ d,
      (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (AesGcm.X86_64.kept_oneFrame La hDW hd) (by decide)
  obtain q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hx16]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  obtain hai : AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H x D n s₁ :=
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁, hH]⟩
  refine WP.seq (WP.mono (AesGcm.X86_64.WP.with_rdwr (absorbPad_ok v La (yo := 16) (.inr rfl) hai hx16))
    fun s₄ ⟨hf, hrd₄, hwr₄⟩ => ?_)
  rw [hm₁] at hf
  obtain ⟨m₂, fa, ft⟩ := hf.frame
  have he₄ := hf.env
  obtain g₂ := AesGcm.X86_64.absFrame_one fa
  obtain f₂ := AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons g₂)
  obtain g₄ := AesGcm.X86_64.tFrame_one ft
  obtain f₄ := AesGcm.X86_64.wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons g₄)
  obtain q₄ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain q₅ := he₄.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧ s₅.gpr .rbx = BitVec.ofNat 64 al ∧
      s₅.gpr .rbp = BitVec.ofNat 64 N ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧
      s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, q₄, q₅], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp f₄ 184 (.inl ⟨by decide, by decide⟩), kp f₂ 184 (.inl ⟨by decide, by decide⟩), hal]
    · simp [gpr_setReg, kp f₄ 192 (.inl ⟨by decide, by decide⟩), kp f₂ 192 (.inl ⟨by decide, by decide⟩), htl]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  obtain g₅ : Frame (AesGcm.X86_64.wFrame W SP) s.mem s₅.mem := by rw [hm₅]; exact g₂.trans g₄
  obtain f₅ : Frame (AesGcm.X86_64.oneFrame W D SP n) s.mem s₅.mem :=
    AesGcm.X86_64.wFrame_one (o := 0) (.inl rfl) (AesGcm.X86_64.wFrame_cons g₅)
  obtain dC : ∀ r ∈ AesGcm.X86_64.oneFrame W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact La.cw'.sub_right (Offset.sub_base W (show 0 + 128 ≤ 2560 by decide) |> fun h => by simpa using h)
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact hCD
    · exact La.kc.symm
  obtain dS0 : ∀ r ∈ AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16,
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using La.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_st (a := 0) (n := 16) (d := 32) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (La.stk_st (a := 0) (n := 16) (by decide)).symm
  obtain dT0 : ∀ r ∈ AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16,
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using La.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using La.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (La.stk_st (a := 0) (n := 16) (by decide)).symm
  obtain hJ₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [hm₅, blockAt_frame ft dT0, blockAt_frame fa dS0]
  obtain hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [hm₅, hf.hH]
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (tag_ok v L ho he₅ hH₅ hJ₅)) fun s₆ ⟨ht, hrd₆, hwr₆⟩ =>
    ⟨ht.env, (wFrame_cons (wFrame_of_aes g₅)).trans (tagFrame_one ht.frame), by rw [hrd₆, hrd₅, hrd₄, hrd₁],
      by rw [hwr₆, hwr₅, hwr₄, hwr₁], ?_, ht.j, fun hab => ?_⟩
  · have d48 : ∀ r ∈ tagFrame (W + BitVec.ofNat 64 16) W SP o,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using La.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact La.st_w (by decide) (by omega_arith)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.ks.sub_right (Lay.stSub (by decide))).symm
    obtain d48a : ∀ r ∈ AesGcm.X86_64.absFrame (W + BitVec.ofNat 64 16) W SP 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.st_st (.inr (by decide)) (by decide) (by decide)
      · exact La.st_st (.inr (by decide)) (by decide) (by decide)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (La.stk_st (by decide)).symm
    obtain d48t : ∀ r ∈ AesGcm.X86_64.tFrame (W + BitVec.ofNat 64 16) W SP 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.st_st (.inr (by decide)) (by decide) (by decide)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact La.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (La.stk_st (by decide)).symm
    rw [blockAt_frame ht.frame d48, hm₅, blockAt_frame ft d48t, blockAt_frame fa d48a]
  obtain hw := (hf.abs hab).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [ht.out, ciph_frame f₅ dC, hbx₅, hbp₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN,
    lensBlock_mod_left, hm₅, hw]

end

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. `J₀` and the additional data
(AES-GCM's `oneAad`), the data encrypted (`oneCrypt`) and the tag of the
ciphertext (`oneTag 0`, `sealRun_ok`), copied to `tag` (AES-GCM's
`tagOut_ok`): GCM-AE (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ tagOut restore oneAad)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH gctr inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk SavedAt blockAt_frame bytesAt_frame ctxH_eq exit_ok ret_kept
  covers_left tagOut_ok padded_eq length_bytesAt)

/-- The argument at `[SP + 16]` (`tag`'s address) stays where it is, outside
`W`, the data and the stack below `SP`. -/
theorem arg16_disj {W D SP : Addr} {n k : Nat} (hk : 2 ≤ k)
    (dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩)
    {r : Region} (hr : r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP stkN)) :
    (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := by
    rw [show (16 : Nat) = 8 + 8 by rfl, ← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; exact Offset.sub_base _ (by omega_using [hk])
  rcases hr with hr | hr | hr
  · exact (dA.sub_left hs).sub_right hr
  · exact (dAD.sub_left hs).sub_right hr
  · exact (Offset.disjoint_below SP (n := stkN) (d := 16) (k := 8) (by decide)).sub_right hr

/-- What `sealRun_ok` leaves, after the entry. -/
abbrev SealRunPost (s₀ : State) (Ctx W SP Np A D : Addr) (nl al n : Nat) (s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
    SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP stkN] s₀.mem s₄.mem ∧
    bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx)
      (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (bytesAt s₀.mem D n) ∧
    bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))

/-- After the entry, `seal` up to the tag at `W`: `oneAad`, `oneCrypt` and
`oneTag 0`. -/
theorem sealRun_ok (v : GcmImpl) {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 3 Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al) :
    WP isa (.seq (oneAad v.callees) (.seq oneCrypt (oneTag v.callees 0))) s₁
      (SealRunPost s₀ Ctx W SP Np A D nl al n) := by
  unfold SealRunPost
  have L := C.lay
  have La := L.lay
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₂ M => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s₀.mem A al = a at M ⊢
  have hd₂ : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq M.rd M.wr
  refine WP.seq (WP.mono (oneCrypt_ok L (icb := inc32 (Spec.Gcm.j0 H iv)) (P := 0) rfl M.env M.dat M.len hd₂)
    fun s₃ ⟨cr, hrd₃, hwr₃⟩ => ?_)
  have hc0 : Ctr s₂.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 H iv)) 0 := Proof.Gcm.ctr_zero _ _ _ _ M.cb
  have hC₃ := cr.out hc0
  have f₃ : Frame (oneFrame W D SP n) s₂.mem s₃.mem := crFrame_one cr.frame
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd)
      (by decide)
  have dSt : ∀ d k, d + k ≤ 48 → ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) SP D n,
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hd₂.dw.ok.st.sub_right (Lay.stSub (by omega_using [hk]))).symm
    · exact La.st_st (.inl (by omega_using [hk])) (by omega_using [hk]) (by decide)
    · exact (L.ks.sub_right (Lay.stSub (by omega_using [hk]))).symm
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame cr.frame fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide)), M.hH]
  have hJ₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [← M.j0]; simpa using blockAt_frame cr.frame (dSt 0 16 (by decide))
  have habs₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      H (a ++ zeros (padLen a.length)) :=
    M.abs.congr (blockAt_frame cr.frame (dSt 16 16 (by decide)))
      (bytesAt_frame cr.frame (dSt 32 _ (by omega_using [])) (by omega_using []))
  have hx16 : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [kp 184 (.inl ⟨by decide, by decide⟩), M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hd₃ : DataOk (W + BitVec.ofNat 64 16) W SP s₃ D n :=
    C.data.dw.ok.of_eq (hrd₃.trans M.rd) (hwr₃.trans M.wr)
  refine WP.mono (oneTag_ok v L (o := 0) (.inl rfl) (N := n) hx16 cr.env hH₃
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact M.dat) (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact M.len)
    (by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact M.tlen) hlt hal₃ hd₃ C.dE C.data.dw.ctx)
    fun s₄ ⟨he₄, f₄, hrd₄, hwr₄, _, _, hT⟩ => ?_
  have f₄' : Frame (oneFrame W D SP n) s₃.mem s₄.mem := wFrame_one (.inl rfl) f₄
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP stkN).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₂ : ciphOf s₂.mem Ctx = ctxCiph s₀.mem Ctx := ciph_frame M.frame (dM _ _ La.cw' L.kc)
  have hc₃ : ciphOf s₃.mem Ctx = ctxCiph s₀.mem Ctx := (ciph_frame cr.frame (ctx_crFrame L hd₂)).trans hc₂
  have hp₂ : bytesAt s₂.mem D n = bytesAt s₀.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.stk) (by omega_using [hlt])
  have dD : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.stk.symm
  have hD₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D n := bytesAt_frame f₄ dD (by omega_using [hlt])
  have hT₄ := hT habs₃
  rw [padded_eq, hJ₃, hc₃, ← hD₄, BitVec.add_zero] at hT₄
  refine ⟨he₄, hrd₄.trans (hrd₃.trans M.rd), hwr₄.trans (hwr₃.trans M.wr),
    (M.saved.frame f₃ (saved_oneFrame L C.dE)).frame f₄' (saved_oneFrame L C.dE), ?_,
    by rw [hD₄, hC₃, hc₂, hp₂, Proof.Gcm.gctr_eq], hT₄⟩
  refine (M.frame.sub fun r hr => ?_).trans ((f₃.trans f₄').sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, fun _ h => h⟩

/-- `a; (b; ((c; d); e))` from `(a; (b; c)); (d; e)`. -/
theorem WP.reassoc_seal {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) (.seq d e)) s Q) :
    WP isa (.seq a (.seq b (.seq (.seq c d) e))) s Q := by
  obtain ⟨t, s', ex, q⟩ := h
  cases ex with | seq ex₁ ex₂ => cases ex₁ with | seq ea ex₁ => cases ex₁ with | seq eb ec => cases ex₂ with
    | seq ed ee => exact ⟨_, _, .seq ea (.seq eb (.seq (.seq ec ed) ee)), q⟩

/-- `vg_sm4_gcm_seal`. -/
theorem seal_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.sealX86_64.pre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.sealX86_64.post s s' := by
  obtain ⟨C, hTw, d_td, d_tw, r_t, -⟩ := OneCtx.ofSeal hp
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hT' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  have hwa := C.args 2 (by decide)
  have hta := C.args 1 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hnl : (s.gpr .rdx).toNat = nl at *
  generalize hA : s.gpr .rcx = A at *
  generalize hal : (s.gpr .r8).toNat = al at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  generalize hT : stackArg s 1 = T at *
  generalize hW : stackArg s 2 = W at *
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW' hwa) fun s₁ E => ?_)
  refine WP.reassoc_seal (WP.seq (WP.mono (sealRun_ok v C E hNp hnl hal)
    fun s₄ ⟨he₄, hrd₄, hwr₄, hsv₄, f₄, hC, hT₄⟩ => WP.seq ?_))
  -- The tag copied to `tag`.
  have dA : ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP stkN) →
      (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have hT₄' : s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 16) 64 = T := by
    rw [he₄.rsp, f₄.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dA _ (.inl fun _ h => h)
      · exact dA _ (.inr (.inl fun _ h => h))
      · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT']
  obtain ⟨s₅, run₅, hb₅, f₅, hg₅, hrd₅, hwr₅⟩ := tagOut_ok (b := .rsp) (d := 16) he₄.r15 hT₄'
    (by rw [he₄.rsp, hrd₄, hwr₄]; exact hta) he₄.perm.w (by rw [hwr₄]; exact hTw)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have hsv₅ : SavedAt s₅.mem W s := hsv₄.frame f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (d_tw.sub_right (Lay.wSub (by decide))).symm
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₅ (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact C.rW
      · exact C.rD
      · exact ret_stk SP
    · simp only [List.mem_singleton] at hr; subst hr; exact r_t
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact d_td.symm) (by omega_using [hn])
  simp only [Proof.Sm4Gcm.sealX86_64, Proof.Sm4Gcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, Spec.Gcm.encryptWith, hm, hb₅, hT₄, hd₅, hC,
    Proof.Gcm.fullTag_eq, Proof.Gcm.length_gctr, length_bytesAt, length_bytesAt]
  simp only [Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.Sm4Gcm.X86_64

end

end

/-! ### `Sm4Gcm.X86_64.OneCT`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86-64: `seal` and its pieces in two runs

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OneBlocks/CT.lean`, `SealCT.lean`): what stays in `W` between
the pieces (`OneS`: the additional data's address and length, the data's
address and length) is the same in both runs, so each piece (`oneAad`,
`oneCrypt`, `oneTag`) leaks the same; `seal` copies the tag to the same
address, on the stack.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm oneAad absorbPad j0 aadO alenO dataO lenO tlenO tagOut restore)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk AbsIn J0In rel_taint rel_wp env_agree TagAt tagOut_rel
  fn_rel₂ ct_of_rel j0_ok j0_rel absorbPad_ok absorbPad_rel)

/-- What stays in `W` and the buffers between the pieces of `seal` and `open`. -/
structure OneS (Ctx W SP : Addr) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dA : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  dD : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem OneS.frame {A : Addr} {al : Nat} {D : Addr} {n : Nat} {s s' : State}
    (h : OneS Ctx W SP A al D n s) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (oneFrame W D SP n) s.mem s'.mem) : OneS Ctx W SP A al D n s' := by
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  exact ⟨he, by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact h.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact h.len,
    by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact h.tlen, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr⟩

omit L in
theorem OneS.keep {A : Addr} {al : Nat} {D : Addr} {n : Nat} {s s' : State}
    (h : OneS Ctx W SP A al D n s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OneS Ctx W SP A al D n s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.aad, by rw [hm]; exact h.alen, by rw [hm]; exact h.dat,
    by rw [hm]; exact h.len, by rw [hm]; exact h.tlen, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr⟩

omit L in
/-- Two slots of `W` loaded, and a constant. -/
theorem load2_ok {A : Addr} {al : Nat} {D : Addr} {n : Nat} {s : State}
    (h : OneS Ctx W SP A al D n s) {o₁ o₂ : Nat} {P : Addr} {k : Nat}
    (h₁ : s.mem.readW (W + BitVec.ofNat 64 o₁) 64 = P) (h₂ : s.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 k)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₁) 8) (q₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₂) 8) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)]) s
      fun s₁ => OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .r12 = P ∧ s₁.gpr .rbp = BitVec.ofNat 64 k ∧
        s₁.gpr .rbx = BitVec.ofNat 64 0 := by
  have h15 := h.env.r15
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 o₁)),
      .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)] s = some s₁ ∧ s₁.gpr .r12 = P ∧
      s₁.gpr .rbp = BitVec.ofNat 64 k ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h₁]
    · simp [gpr_setReg, h₂]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, h12, hbp, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)

end

theorem w_one {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (AesGcm.X86_64.wFrame W SP) m m') :
    Frame (oneFrame W D SP n) m m' :=
  wFrame_one (o := 0) (.inl rfl) (wFrame_cons (wFrame_of_aes h))

/-- Two runs in `OneS` for the same parameters. -/
abbrev OneS₂ (Ctx W SP : Addr) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s₁ s₂ : State) : Prop :=
  OneS Ctx W SP A al D n s₁ ∧ OneS Ctx W SP A al D n s₂

theorem OneS₂.env {Ctx W SP A : Addr} {al : Nat} {D : Addr} {n : Nat} {s₁ s₂ : State}
    (h : OneS₂ Ctx W SP A al D n s₁ s₂) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
  env_agree h.1.env h.2.env

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The additional data, absorbed and padded. -/
theorem aadRest_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP A al D n)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)])
      (absorbPad v.callees 16)) (OneS₂ Ctx W SP A al D n) := by
  have La := L.lay
  have hL : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.aad h.alen (h.env.perm.wR (show 232 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 184 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS Ctx W SP A al D n s ∧ s.gpr .r12 = A ∧
    s.gpr .rbp = BitVec.ofNat 64 al ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] A al s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dA, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorbPad v.callees 16) s (OneS Ctx W SP A al D n) := fun s h =>
    WP.mono (AesGcm.X86_64.WP.with_rdwr (absorbPad_ok v La (.inr rfl) (ai s h) rfl)) fun _ ⟨o, hrd, hwr⟩ => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact h.1.frame L o.env hrd hwr hDW
        (w_one ((AesGcm.X86_64.absFrame_one fa).trans (AesGcm.X86_64.tFrame_one ft)))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v La (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := A) (n := al) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `J₀` of the nonce, and the additional data. -/
theorem oneAad_rel {Np A : Addr} {nl al : Nat} {D : Addr} {n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => (OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .r12 = Np ∧ s₁.gpr .rbp = BitVec.ofNat 64 nl ∧
        DataOk (W + BitVec.ofNat 64 16) W SP s₁ Np nl) ∧ (OneS Ctx W SP A al D n s₂ ∧ s₂.gpr .r12 = Np ∧
        s₂.gpr .rbp = BitVec.ofNat 64 nl ∧ DataOk (W + BitVec.ofNat 64 16) W SP s₂ Np nl))
      (oneAad v.callees) (OneS₂ Ctx W SP A al D n) := by
  have La := L.lay
  have ji : ∀ s, (OneS Ctx W SP A al D n s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) →
      J0In Ctx (W + BitVec.ofNat 64 16) W SP (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) Np nl s :=
    fun s h => ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩
  have hJ : ∀ s, (OneS Ctx W SP A al D n s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) → WP isa (j0 v.callees) s (OneS Ctx W SP A al D n) :=
    fun s h => WP.mono (AesGcm.X86_64.WP.with_rdwr (j0_ok v La (ji s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (w_one (AesGcm.X86_64.j0Frame_one o.frame))
  have a := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      j0_rel v La (H₁ := H₁) (H₂ := H₂) (Np := Np) (n := nl)).mono
      (fun _ _ h => ⟨_, _, ji _ h.1, ji _ h.2⟩) fun _ _ h => h) (fun _ _ h => h) hJ hJ
  exact RelCT.seq a ((aadRest_rel v L hDW).mono (fun _ _ h => h.2) fun _ _ h => h)

omit v in
/-- The data encrypted or decrypted. -/
theorem oneCrypt_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP A al D n) oneCrypt (OneS₂ Ctx W SP A al D n) := by
  have hL : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let CI : State → Prop := fun s => OneS Ctx W SP A al D n s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ci : ∀ s, CI s → CrIn Ctx (W + BitVec.ofNat 64 16) W SP 0 0 D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD⟩
  have hC : ∀ s, CI s → WP isa cryptAl s (OneS Ctx W SP A al D n) := fun s h =>
    WP.mono (AesGcm.X86_64.WP.with_rdwr (cryptAl_ok L (ci s h) rfl)) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (crFrame_one o.frame)
  have b := rel_wp ((cryptAl_rel L (icb₁ := 0) (icb₂ := 0) (P₁ := 0) (P₂ := 0) (D := D) (n := n) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ CI s₁ ∧ CI s₂) (fun _ _ h => ⟨ci _ h.2.1, ci _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hC hC
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The tag of the data (as ciphertext) into `W + o`. -/
theorem oneTag_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP A al D n) (oneTag v.callees o) fun _ _ => True := by
  have La := L.lay
  have hL : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS Ctx W SP A al D n s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD.dw.ok, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorbPad v.callees 16) s (OneS Ctx W SP A al D n) := fun s h =>
    WP.mono (AesGcm.X86_64.WP.with_rdwr (absorbPad_ok v La (.inr rfl) (ai s h) rfl)) fun _ ⟨o, hrd, hwr⟩ => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact h.1.frame L o.env hrd hwr hDW
        (w_one ((AesGcm.X86_64.absFrame_one fa).trans (AesGcm.X86_64.tFrame_one ft)))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v La (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := D) (n := n) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  -- The lengths, for `tag`.
  have hT : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 n := fun s h => by
    have q₁ := h.env.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have q₂ := h.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
    have h15 := h.env.r15
    obtain ⟨s₁, run₁, hbx, hbp, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧
        s₁.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h.alen]
      · simp [gpr_setReg, h.tlen]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx, hbp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ OneS₂ Ctx W SP A al D n s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hT hT
  have t := (tag_rel v L ho).mono (P' := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 n) ∧
      (OneS Ctx W SP A al D n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 al ∧ s₂.gpr .rbp = BitVec.ofNat 64 n))
    (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) fun _ _ h => h
  exact RelCT.seq a (RelCT.seq b (RelCT.seq e t))

end

theorem one_pub {k : Nat} {s₀ s₀' : State} (hq : Proof.Sm4Gcm.onePub k s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `oneAad`'s precondition, after the entry. -/
theorem OneEntry.aadPre {s₀ s : State} {k : Nat} {Ctx W SP Np A D : Addr}
    {nl al n : Nat} (C : OneCtx s₀ k Ctx W SP Np A D nl al n)
    (E : OneEntry s₀ Ctx W SP A D n s) (hNp : s₀.gpr .rsi = Np)
    (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al) :
    OneS Ctx W SP A al D n s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl :=
  ⟨⟨E.env, E.aad, by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len, E.tlen,
    C.aad.of_eq E.rd E.wr, C.data.of_eq E.rd E.wr⟩, by rw [E.r12, hNp],
    by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq], C.nonce.of_eq E.rd E.wr⟩

/-- After the entry, `seal` up to the tag in two runs: `oneAad`, `oneCrypt`
and `oneTag 0`. -/
theorem sealRun_rel (v : GcmImpl) {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 3 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 3 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hNp' : s₀'.gpr .rsi = Np) (hnl' : (s₀'.gpr .rdx).toNat = nl) (hal' : (s₀'.gpr .r8).toNat = al) :
    RelCT isa (fun s₁ s₂ => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
      (.seq (oneAad v.callees) (.seq oneCrypt (oneTag v.callees 0))) fun _ _ => True := by
  have L := C.lay
  have hDW := C.dE
  have a := (oneAad_rel v L hDW (Np := Np) (nl := nl)).mono
    (P' := fun (s₁ s₂ : State) => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
    (fun _ _ h => ⟨h.2.1.aadPre C hNp hnl hal, h.2.2.aadPre C' hNp' hnl' hal'⟩) fun _ _ h => h
  exact (RelCT.seq a (RelCT.seq (oneCrypt_rel L hDW) (oneTag_rel v L (.inl rfl) hDW))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

/-- `e; (m; (o; f))`, related as `e; ((m; o); f)`. -/
theorem rel_reassoc_mid {P Q : State → State → Prop} {e m o f : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq m o) f)) Q) : RelCT isa P (.seq e (.seq m (.seq o f))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq m₁ e₁ => cases e₁ with | seq o₁ f₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq m₂ e₂ => cases e₂ with | seq o₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq m₁ o₁) f₁)) (.seq x₂ (.seq (.seq m₂ o₂) f₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `x; (a; (b; ((c; d); f)))`, related as `x; ((a; (b; c)); (d; f))`. -/
theorem rel_reassoc_seal {P Q : State → State → Prop} {x a b c d f : Prog isa}
    (h : RelCT isa P (.seq x (.seq (.seq a (.seq b c)) (.seq d f))) Q) :
    RelCT isa P (.seq x (.seq a (.seq b (.seq (.seq c d) f)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with
    | seq e₁ f₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with
    | seq e₂ f₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq a₁ (.seq b₁ c₁)) (.seq d₁ f₁)))
    (.seq x₂ (.seq (.seq a₂ (.seq b₂ c₂)) (.seq d₂ f₂)))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

theorem seal_rel (v : GcmImpl) {s₀ s₀' : State}
    (hp : Proof.Sm4Gcm.sealX86_64.pre s₀) (hp' : Proof.Sm4Gcm.sealX86_64.pre s₀')
    (hq : Proof.Sm4Gcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have C := (OneCtx.ofSeal hp).1
  have C' := (OneCtx.ofSeal hp').1
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩ := hq'
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  simp only [Proof.Sm4Gcm.arg] at a₀ a₁ a₂
  have ha₂ := C.args 2 (by decide); have ha₂' := C'.args 2 (by decide)
  have hw24 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 := a₂
  have hT₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s₀ 1 := rfl
  have hT₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s₀ 1 := by rw [q₇, a₁]; rfl
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₂] at C'
  have hE : ∀ {s : State} (C : OneCtx s 3 (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi) (s₀.gpr .rcx)
      (s₀.gpr .r9) (s₀.gpr .rdx).toNat (s₀.gpr .r8).toNat (stackArg s₀ 0).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .rcx = s₀.gpr .rcx →
      s.gpr .r9 = s₀.gpr .r9 → (stackArg s 0).toNat = (stackArg s₀ 0).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 →
      InRegions (s.rd ++ s.wr) (s₀.gpr .rsp + BitVec.ofNat 64 24) 8 →
      WP isa (.block (oneEntry 24)) s
        (OneEntry s (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rcx) (s₀.gpr .r9) (stackArg s₀ 0).toNat) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => oneEntry_ok (by decide) C h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl ha₂
  have hE₂ := hE C' q₁.symm q₇.symm q₄.symm q₆.symm (by rw [a₀]) (by rw [q₇, a₂]; rfl) (by rw [q₇]; exact ha₂')
  rw [oneEntry, List.append_assoc, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [«seal», oneEntry, List.append_assoc, List.append_assoc, List.append_assoc]
  refine rel_reassoc_seal (rel_reassoc_mid (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 2 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 2) (SP := s₀.gpr .rsp) (k := 24) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub hq) hw24 ha₂ ha₂' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_))
  -- The address of `tag`, at `[SP + 16]`, after the tag: by correctness.
  have dA : ∀ r : Region, r.Sub ⟨stackArg s₀ 2, 2560⟩ ∨ r.Sub ⟨s₀.gpr .r9, (stackArg s₀ 0).toNat⟩ ∨
      r.Sub (below (s₀.gpr .rsp) stkN) → (⟨s₀.gpr .rsp + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r :=
    fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have hW : ∀ {s₀'' s : State} (C : OneCtx s₀'' 3 (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rdx).toNat (s₀.gpr .r8).toNat (stackArg s₀ 0).toNat),
      s₀''.gpr .rsi = s₀.gpr .rsi → (s₀''.gpr .rdx).toNat = (s₀.gpr .rdx).toNat →
      (s₀''.gpr .r8).toNat = (s₀.gpr .r8).toNat →
      s₀''.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s₀ 1 →
      OneEntry s₀'' (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rcx) (s₀.gpr .r9) (stackArg s₀ 0).toNat s →
      WP isa (.seq (oneAad v.callees) (.seq oneCrypt (oneTag v.callees 0))) s
        (TagAt (s₀.gpr .rdi) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) (s₀.gpr .rsp) .rsp 16
          (stackArg s₀ 1)) :=
    fun C h₁ h₂ h₃ hT E => WP.mono (sealRun_ok v C E h₁ h₂ h₃) fun _ ⟨he, hrd, hwr, _, f, _⟩ => ⟨he, by
      rw [he.rsp, f.readW (r := ⟨s₀.gpr .rsp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dA _ (.inl fun _ h => h)
        · exact dA _ (.inr (.inl fun _ h => h))
        · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT], by
      rw [he.rsp, hrd, hwr]; exact C.args 1 (by decide)⟩
  have m := rel_wp (sealRun_rel v C C' rfl rfl rfl q₂.symm (by rw [q₃]) (by rw [q₅]))
    (fun _ _ h => h.2) (fun _ h => hW C rfl rfl rfl hT₁ h) (fun _ h => hW C' q₂.symm (by rw [q₃]) (by rw [q₅]) hT₂ h)
  exact RelCT.seq m (tagOut_rel (b := .rsp) (d := 16) (by simp) ⟨_, by taint_decide⟩ (fun _ _ h => h.2))

theorem seal_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.sealX86_64.pre Proof.Sm4Gcm.sealX86_64.pub («seal» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => seal_rel v hp hp' hq

end VG.Proof.Sm4Gcm.X86_64

end

end

/-! ### `Sm4Gcm.X86_64.Open`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. A tag length `tagLenOk` does
not allow gives 0. Any other: `J₀` and the additional data (AES-GCM's
`oneAad`), the tag of the ciphertext (`oneTag 112`), the received tag, read
from `tag`, padded (AES-GCM's `recv`) and compared (its `cmp 112`), and if
they match the data decrypted (`oneCrypt`); if not, the data stays as it was:
GCM-AD (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm tagLenOk recv cmp uO tlO auxO oneAad restore)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH gctr inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk SavedAt blockAt_frame bytesAt_frame exit_ok ret_kept
  covers_left padded_eq length_bytesAt recv_ok cmp_ok tagLenOk_ok bytesAt_take eval_e WP.run oneR and_self_beq)

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `OneEntry`, after code that writes only the tag length's slot. -/
theorem OneEntry.keep {s₀ s s' : State} {A D : Addr} {n : Nat} (E : OneEntry s₀ Ctx W SP A D n s)
    (hg : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneEntry s₀ Ctx W SP A D n s' := by
  obtain kp : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (by omega_arith) h' (by decide)) (by decide)
  refine ⟨E.env.keep (fun r hr => ?_) hrd hwr, by rw [kp 232 (.inr (by decide)) (by decide)]; exact E.aad,
    by rw [kp 184 (.inl (by decide)) (by decide)]; exact E.alen, by rw [kp 200 (.inl (by decide)) (by decide)]; exact E.dat,
    by rw [kp 208 (.inl (by decide)) (by decide)]; exact E.len, by rw [kp 192 (.inl (by decide)) (by decide)]; exact E.tlen,
    by rw [hg _ (by simp)]; exact E.r12, by rw [hg _ (by simp)]; exact E.rbp, by rw [hg _ (by simp)]; exact E.rsp,
    E.saved.frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)),
    E.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩), hrd.trans E.rd, hwr.trans E.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by simp)

end

/-- The entry of `open`, and the tag length kept at `W + 224`. -/
theorem openEntry_ok {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .rcx = A)
    (hD : s.gpr .r9 = D) (hn : (stackArg s 0).toNat = n) (hW : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = W) :
    WP isa (.block (oneEntry 32 ++ ([.mov .rbx (.mem (at_ .rsp 24)), .store (at_ .r15 tlO) .rbx] : List Instr))) s
      fun s₁ => OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = stackArg s 2 ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s 2 ∧ Frame [oneR W] s.mem s₁.mem := by
  have L := C.lay
  obtain a₄ := C.args 3 (by decide)
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW a₄) fun s₁ E => ?_)
  obtain a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [E.rd, E.wr]; exact C.args 2 (by decide)
  obtain ht : s₁.mem.readW (SP + BitVec.ofNat 64 24) 64 = stackArg s 2 := by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain hs : Region.Sub ⟨SP + BitVec.ofNat 64 24, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 4⟩ := by
        rw [show (24 : Nat) = 8 + 16 by rfl, ← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
        exact Offset.sub_base _ (by decide)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    rfl
  obtain w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 24)),
      .store (at_ .r15 tlO) .rbx] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 2 ∧ (∀ r, r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 2) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [E.rsp, E.env.r15, a₃, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, ht]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, ht]
    all_goals rfl
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₂, run₂, E.keep L (fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hrd₂ hwr₂ f₂, hbx₂,
    by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  exact E.frame.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- A region disjoint from what `open` writes before it compares the tags,
but for the data: `W` and the stack below `SP`. -/
def OutWS (W SP : Addr) (X : Region) : Prop :=
  ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub (below SP stkN) → X.Disjoint r

/-- A region disjoint from `W`, the data and the stack below `SP`. -/
def OutWDS (W D SP : Addr) (n : Nat) (X : Region) : Prop :=
  ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP stkN) → X.Disjoint r

theorem OutWDS.ws {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) : OutWS W SP X :=
  fun r hr => h r (hr.elim .inl fun h => .inr (.inr h))

theorem OutWS.tagFrame {W SP : Addr} {X : Region} (h : OutWS W SP X) {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Lay.wSub ho))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr fun _ h => h)

theorem ite_ofNat (p : Prop) [Decidable p] :
    (if p then 1 else 0 : BitVec 64) = BitVec.ofNat 64 (if p then 1 else 0) := by split <;> rfl

/-- After the comparison, from `s`: `k` is 1 if the tag of the ciphertext
matches the received one, and 0 if not, in ZF and at `W + 216`; the counter
block kept, and the first one (after `J₀ = J`) at the state's start. -/
structure OpenMid (Ctx W SP : Addr) (J : Block) (k : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  frame : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cb : blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
  zf : s'.zf = some (decide (k = 0))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k
  j : blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 J

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The tag of the ciphertext (`x`, absorbed, then the `n` bytes at `D`, of `N`
in all), compared with the received one. -/
theorem openCheck_ok {t : Nat} {D : Addr} {n N al : Nat} {H J : Block}
    {x : List Byte} (hx16 : x.length % 16 = 0) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hN₁ : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hCD : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (habs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x)
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J) {Tp : Addr}
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = Tp) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : OutWS W SP ⟨Tp, t⟩)
    (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 16, 8⟩) :
    WP isa (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv
      (.seq (cmp uO)
        (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))) s
      (OpenMid Ctx W SP J (if (toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
          zeros (padLen (x ++ bytesAt s.mem D n).length))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx J)).take t = bytesAt s.mem Tp t then 1 else 0) s) := by
  have La := L.lay
  have hlt := hd.lt
  -- The tag.
  refine WP.seq (WP.mono (oneTag_ok v L (o := 112) (al := al) (.inr rfl) hx16 he hH hdat hlen hN₁ hN hal hd hDW hCD)
    fun s₃ ⟨he₃, f₃, hrd₃, hwr₃, hcb₃, hj₃, hq⟩ => ?_)
  obtain hT₃ := hq habs
  rw [hj] at hT₃
  generalize hT : toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
    zeros (padLen (x ++ bytesAt s.mem D n).length)))) [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx J) = T
    at hT₃ ⊢
  obtain f₃' := wFrame_one (D := D) (n := n) (.inr rfl) f₃
  obtain kp₃ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => f₃'.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd')
      (by decide)
  obtain hTp₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t :=
    bytesAt_frame f₃ (oT.tagFrame (o := 112) (by decide)) (by omega_arith)
  obtain hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 16) 64 = Tp := by
    rw [f₃.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (oA.tagFrame (o := 112) (by decide))
      (by decide), hTa]
  obtain htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [kp₃ 224 (.inr ⟨by decide, by decide⟩)]; exact htl
  obtain q₁ := he₃.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain q₂ : InRegions (s₃.rd ++ s₃.wr) (SP + BitVec.ofNat 64 16) 8 := by rw [hrd₃, hwr₃]; exact hTar
  obtain ⟨s₄, run₄, hbx₄, hsi₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 16))] s₃ = some s₄ ∧ s₄.gpr .rbx = BitVec.ofNat 64 t ∧ s₄.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by xrun [he₃.r15, he₃.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₃]
    · simp [gpr_setReg, hTa₃]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)) hrd₄ hwr₄
  -- The received tag, padded.
  refine WP.seq (WP.mono (AesGcm.X86_64.WP.with_rdwr (recv_ok he₄ hbx₄ h1 h16 hsi₄
    (by rw [hrd₄, hrd₃, hwr₄, hwr₃]; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₅ ⟨⟨he₅, hr₅, f₅, hbx₅⟩, hrd₅, hwr₅⟩ => ?_)
  rw [hbx₄] at hbx₅
  refine WP.seq (WP.mono (AesGcm.X86_64.WP.with_rdwr
    (cmp_ok La (by decide) (o := 112) (.inr rfl) he₅ hbx₅ h1 h16 (length_bytesAt _ _ _) hr₅))
    fun s₆ ⟨⟨he₆, hax₆, f₆⟩, hrd₆, hwr₆⟩ => ?_)
  obtain d256 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact La.w_w (.inl (by decide)) (by decide) (by decide)
  obtain hU : bytesAt s₅.mem (W + BitVec.ofNat 64 112) t = T.take t := by
    rw [bytesAt_take _ _ h16, bytesAt_frame f₅ d256 (by decide), hm₄, hT₃]
  rw [hU, hm₄, hTp₃, ite_ofNat] at hax₆
  generalize hk : (if T.take t = bytesAt s.mem Tp t then 1 else 0) = k at hax₆
  obtain hk1 : k < 2 ^ 64 := by rw [← hk]; split <;> decide
  -- The result kept at `W + 216`.
  obtain w₇ := he₆.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₇, run₇, hz₇, hg₇, hm₇, hrd₇, hwr₇⟩ : ∃ s₇, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₆ = some s₇ ∧ s₇.zf = some (decide (k = 0)) ∧ (∀ r, s₇.gpr r = s₆.gpr r) ∧
      s₇.mem = s₆.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    refine ⟨_, by xrun [he₆.r15, w₇], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₆, mem_setReg]
      exact congrArg some (and_self_beq hk1)
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₆]
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  obtain he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇ := he₆.keep (fun r _ => hg₇ r) hrd₇ hwr₇
  obtain g₇ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩]
      s₃.mem s₇.mem := by
    obtain g₅ := f₅.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    obtain g₆ := f₆.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    rw [hm₄] at g₅
    rw [hm₇]
    exact (g₅.trans g₆).writeW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  obtain f₇ : Frame (wFrame W SP) s₃.mem s₇.mem := g₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_wFrame (.inr (.inl ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  obtain F₇ : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s₇.mem := f₃.trans (wFrame_cons f₇)
  obtain hcb₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
      rcases hr with rfl | rfl | rfl <;> exact La.w_w (.inl (by decide)) (by decide) (by decide)), hcb₃]
  obtain hj₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = inc32 J := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact La.w_w (.inl (by decide)) (by decide) (by decide)), hj₃, hj]
  obtain hrd₇' : s₇.rd = s.rd := hrd₇.trans (hrd₆.trans (hrd₅.trans (hrd₄.trans hrd₃)))
  obtain hwr₇' : s₇.wr = s.wr := hwr₇.trans (hwr₆.trans (hwr₅.trans (hwr₄.trans hwr₃)))
  obtain hax₇ : s₇.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [hm₇, Mem.readW_writeW_self64]
  subst hk hT
  exact ⟨he₇, F₇, hrd₇', hwr₇', hcb₇, hz₇, hax₇, hj₇⟩

omit v in
/-- After the comparison: the data decrypted if the tags match (`k ≠ 0`), and
the result. -/
theorem openEnd_ok {n k : Nat} {D : Addr} {J : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n)
    (hz : s.zf = some (decide (k = 0))) (hax : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hcb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J) :
    WP isa (.seq (.ite .e (.block []) oneCrypt) (.block [.mov .rax (.mem (at_ .r15 auxO))])) s
      fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (oneFrame W D SP n) s.mem s'.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rax = BitVec.ofNat 64 k ∧
        bytesAt s'.mem D n = if k = 0 then bytesAt s.mem D n
          else xorKs (ciphOf s.mem Ctx) (inc32 J) 0 (bytesAt s.mem D n) := by
  have La := L.lay
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧
      Frame (oneFrame W D SP n) s.mem s₈.mem ∧ s₈.rd = s.rd ∧ s₈.wr = s.wr ∧
      s₈.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      bytesAt s₈.mem D n = if k = 0 then bytesAt s.mem D n
        else xorKs (ciphOf s.mem Ctx) (inc32 J) 0 (bytesAt s.mem D n))
    (WP.ite (decide (k = 0)) (eval_e hz) (fun ht => ?_) (fun hf => ?_)) fun s₈ h₈ => ?_)
  · -- The tags differ: the data as it was.
    obtain h0 : k = 0 := by simpa using ht
    exact WP.block_nil ⟨he, Frame.refl _ _, rfl, rfl, hax, by simp only [h0, ↓reduceIte]⟩
  · -- The tags match: the data decrypted.
    obtain h0 : k ≠ 0 := by simpa using hf
    refine WP.mono (oneCrypt_ok L (icb := inc32 J) (P := 0) rfl he hdat hlen hd)
      fun s₈ ⟨cr, rd₈, wr₈⟩ => ⟨cr.env, crFrame_one cr.frame, rd₈, wr₈, ?_, ?_⟩
    · rw [cr.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), hax]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.dw.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact (La.st_w (a := 48) (n := 32) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.kw.sub_right (Lay.wSub (by decide))).symm
    · simp only [h0, ↓reduceIte]
      exact cr.out (Proof.Gcm.ctr_zero _ _ _ _ hcb)
  obtain ⟨he₈, f₈, hrd₈, hwr₈, hax₈, hD₈⟩ := h₈
  obtain q₉ := he₈.perm.wR (show 216 + 8 ≤ 2560 by decide)
  refine WP.run (Q := fun s₉ => s₉.gpr .rax = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rax → s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr)
    ⟨_, by xrun [he₈.r15, q₉], by simp [gpr_setReg, hax₈], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
    fun s₉ ⟨hax₉, hg₉, hm₉, hrd₉, hwr₉⟩ => ?_
  exact ⟨he₈.keep (fun r hr => hg₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₉ hwr₉, by rw [hm₉]; exact f₈,
    by rw [hrd₉, hrd₈], by rw [hwr₉, hwr₈], hax₉, by rw [hm₉]; exact hD₈⟩

end

/-- What `open` returns and leaves in the data, as `openResult` says. -/
abbrev OpenRes (ciph : Block → Block) (H : Block) (t : Nat) (iv c a tag : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop :=
  match Spec.Gcm.openResult ciph H t iv c a tag with
  | some pt => s.gpr .rax = 1 ∧ bytesAt s.mem D n = pt
  | none => s.gpr .rax = 0 ∧ bytesAt s.mem D n = c

/-- What `open` leaves before the exit, for a tag length it allows. -/
abbrev OpenOkPost (s : State) (Ctx W SP Np A D T : Addr) (nl al n t : Nat) (s₅ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ ∧ SavedAt s₅.mem W s ∧ s₅.mem.readW SP 64 = s.mem.readW SP 64 ∧
    OpenRes (ctxCiph s.mem Ctx) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem D n)
      (bytesAt s.mem A al) (bytesAt s.mem T t) D n s₅

/-- `open`'s body for a tag length it allows, after the entry: `oneAad`, the
tags compared, and the data decrypted if they match. -/
theorem openOk_ok (v : GcmImpl) {s s₂ : State}
    {Ctx W SP Np A D T : Addr} {nl al n t : Nat} (C : OneCtx s 4 Ctx W SP Np A D nl al n)
    (E : OneEntry s Ctx W SP A D n s₂)
    (hNp : s.gpr .rsi = Np) (hnl : (s.gpr .rdx).toNat = nl) (hal : (s.gpr .r8).toNat = al)
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTr : Covers [⟨T, t⟩] (s.rd ++ s.wr)) (oT : OutWDS W D SP n ⟨T, t⟩)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩)
    (htl : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (hok' : Spec.Gcm.tagLenOk t = true) :
    WP isa (.seq (oneAad v.callees) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (.block []) oneCrypt)
        (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))) s₂
      (OpenOkPost s Ctx W SP Np A D T nl al n t) := by
  have L := C.lay
  have La := L.lay
  have hlt := C.data.dw.ok.lt
  unfold OpenOkPost
  obtain hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
    omega_arith
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₃ M => ?_)
  generalize hH : ctxH s.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s.mem A al = a at M ⊢
  obtain hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain hal' : a.length = al := by rw [← ha, length_bytesAt]
  obtain htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), htl]
  obtain hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 16) 64 = T := by
    rw [M.frame.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oA _ (.inl fun _ h => h)
      · exact oA _ (.inr (.inr fun _ h => h))) (by decide), hTa]
  obtain hx16 : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain hd₃ : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s₃ D n := C.data.of_eq M.rd M.wr
  refine AesGcm.X86_64.WP.seq5 (openCheck_ok v L (al := al) hx16 M.env M.hH M.dat M.len M.tlen hlt hal₃ htl₃
    hb.1 hb.2 hd₃.dw.ok C.dE C.data.dw.ctx M.abs M.j0 hTa₃ (by rw [M.rd, M.wr]; exact hTar)
    (by rw [M.rd, M.wr]; exact hTr) oT.ws oA.ws) fun s₄ O => ?_
  rw [padded_eq] at O
  generalize hk : (if (toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s₃.mem D n))))
    [ofBytes (lensBlock al n)] ^^^ ciphOf s₃.mem Ctx (Spec.Gcm.j0 H iv))).take t = bytesAt s₃.mem T t then 1 else 0) = k
    at O
  obtain fO := wFrame_one (D := D) (n := n) (.inr rfl) O.frame
  obtain kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => fO.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd')
      (by decide)
  obtain dO : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.stk.symm
  obtain hp₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D n := bytesAt_frame O.frame dO (by omega_arith)
  obtain dC : ∀ r ∈ oneFrame W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact La.cw'.sub_right (Region.sub_prefix (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact C.data.dw.ctx
    · exact L.kc.symm
  obtain hc₄ : ciphOf s₄.mem Ctx = ciphOf s₃.mem Ctx := ciph_frame fO dC
  refine WP.mono (openEnd_ok L (k := k) (J := Spec.Gcm.j0 H iv) O.env
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact M.dat) (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact M.len)
    (C.data.of_eq (O.rd.trans M.rd) (O.wr.trans M.wr)) O.zf O.aux (by rw [O.cb]; exact M.cb))
    fun s₅ ⟨he₅, f₅, _, _, hax₅, hD₅⟩ => ?_
  rw [hc₄, hp₄] at hD₅
  -- From the entry to `s₃`.
  obtain dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP stkN).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  obtain hc₃ : ciphOf s₃.mem Ctx = ctxCiph s.mem Ctx := ciph_frame M.frame (fun r hr => dM _ _ La.cw' L.kc r hr)
  obtain hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.stk) (by omega_arith)
  obtain hw₃ : bytesAt s₃.mem T t = bytesAt s.mem T t := bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact oT _ (.inl fun _ h => h)
    · exact oT _ (.inr (.inr fun _ h => h))) (by omega_arith)
  obtain dRet : ∀ r ∈ oneFrame W D SP n, (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.rW.sub_right (Region.sub_prefix (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rD
    · exact ret_stk SP
  refine ⟨he₅, (M.saved.frame fO (saved_oneFrame L C.dE)).frame f₅ (saved_oneFrame L C.dE), ?_, ?_⟩
  · rw [ret_kept f₅ dRet, ret_kept fO dRet, ret_kept M.frame (fun r hr => ?_)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact C.rW
    · exact ret_stk SP
  · rw [hc₃, hp₃, hw₃] at hk
    rw [hc₃, hp₃, ← Proof.Gcm.gctr_eq] at hD₅
    subst hk
    simp only [OpenRes, Spec.Gcm.openResult, hok', ↓reduceIte, Spec.Gcm.decryptWith,
      Proof.Gcm.fullTag_eq, length_bytesAt, hal']
    by_cases e : List.take t (toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
        [ofBytes (lensBlock al n)] ^^^ ctxCiph s.mem Ctx (Spec.Gcm.j0 H iv))) = bytesAt s.mem T t
    · simp only [e, ↓reduceIte, Nat.one_ne_zero] at hD₅ hax₅ ⊢; exact ⟨hax₅, hD₅⟩
    · simp only [e, ↓reduceIte] at hD₅ hax₅ ⊢; exact ⟨hax₅, hD₅⟩

/-- `vg_sm4_gcm_open`. -/
theorem open_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.openX86_64.pre s) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.openX86_64.post s s' := by
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s 3 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  obtain hTar := C.args 1 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hnl : (s.gpr .rdx).toNat = nl at *
  generalize hA : s.gpr .rcx = A at *
  generalize hal : (s.gpr .r8).toNat = al at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  generalize hT : stackArg s 1 = T at *
  generalize hW : stackArg s 3 = W at *
  have L := C.lay
  refine WP.seq (WP.mono (openEntry_ok C hCtx hSP hA hD hn hW') fun s₁ ⟨E, hbx₁, htl₁, fE⟩ => ?_)
  generalize ht : (stackArg s 2).toNat = t at hTr d_td d_tw t_t ⊢
  obtain oT : OutWDS W D SP n ⟨T, t⟩ := fun r hr =>
    hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  obtain oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩ := fun r hr => arg16_disj (by decide) C.dA C.dAD hr
  obtain hbx₁' : s₁.gpr .rbx = BitVec.ofNat 64 t := by rw [hbx₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain htl₁' : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [htl₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok s₁ hbx₁' (ht ▸ (stackArg s 2).isLt)) fun s₂ ⟨hz₂, k₂⟩ => ?_)
  obtain E₂ : OneEntry s Ctx W SP A D n s₂ := E.keep L (fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k₂.rd k₂.wr (by rw [k₂.mem]; exact Frame.refl _ _)
  obtain dR : ∀ r ∈ [oneR W], (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
  obtain dDR : ∀ r ∈ [oneR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (Q := OpenOkPost s Ctx W SP Np A D T nl al n t)
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₂) (fun hbad => ?_) (fun hok => ?_)) fun s₅ h₅ => ?_)
  · -- A length `tagLenOk` does not allow.
    obtain hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₅ => s₅.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₅.gpr r = s₂.gpr r) ∧ s₅.mem = s₂.mem ∧
        s₅.rd = s₂.rd ∧ s₅.wr = s₂.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₅ ⟨hax, hg₅, hm₅, hrd₅, hwr₅⟩ => ?_
    refine ⟨E₂.env.keep (fun r hr => hg₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅, by rw [hm₅]; exact E₂.saved, ?_, ?_⟩
    · rw [hm₅, k₂.mem, ret_kept fE dR]
    · simp only [OpenRes, Spec.Gcm.openResult, hbad', Bool.false_eq_true, ↓reduceIte]
      exact ⟨hax, by rw [hm₅, k₂.mem, bytesAt_frame fE dDR (by omega_arith)]⟩
  · -- An allowed length.
    exact openOk_ok v C E₂ hNp hnl hal hTa hTar hTr oT oA (by rw [k₂.mem]; exact htl₁') (by simpa using hok)
  obtain ⟨he₅, hsv₅, hret₅, hres⟩ := h₅
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret₅]))
    fun s' ⟨hg, hm, hax⟩ => ⟨hg, ?_⟩
  simp only [Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, ht]
  simp only [OpenRes] at hres
  split
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_open` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OpenCT.lean`): the first branch is on the tag length
(public); then both runs go through `oneAad` and `oneTag` with the same
public data, as in `seal`, and copy and compare the tags without a branch
(the taint analysis). The second branch is on the comparison, which `open`
may leak: correctness says it is whether `openResult` succeeds
(`openPre_ok`), the same in both runs by `pub`; then both runs decrypt the
data (`oneCrypt`) or leave it.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm oneAad tagLenOk recv cmp uO tlO auxO restore)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ghashFrom ghash blocks ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (lensBlock padded)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env rel_regs rel_taint rel_wp rel_ite_e rel_env rel_reassoc_inner
  EnvAgree EnvAgree.regs env_agree fn_rel₂ ct_of_rel tagLenOk_ok bytesAt_frame padded_eq length_bytesAt
  leak_bool)

/-- `a; (b; (c; (d; (e; (f; g)))))`, related as `(a; (b; (c; (d; (e; f))))); g`. -/
theorem rel_reassoc6 {P Q : State → State → Prop} {a b c d e f g : Prog isa}
    (hr : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d (.seq e f))))) g) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ e₁ => cases e₁ with | seq x₁ e₁ => cases e₁ with | seq f₁ g₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ e₂ => cases e₂ with | seq x₂ e₂ => cases e₂ with | seq f₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq x₁ f₁))))) g₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq x₂ f₂))))) g₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- What `open`'s entry leaves, for a tag length `t`. -/
abbrev OpenIn (s₀ : State) (Ctx W SP A D : Addr) (n t : Nat) (s : State) : Prop :=
  OneEntry s₀ Ctx W SP A D n s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t

/-- The address `T` of the received tag, in the argument at `[SP + 16]`. -/
abbrev ArgT (SP T : Addr) (s : State) : Prop := s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T

/-- `ArgT`, and the argument may be read. -/
abbrev ArgR (SP T : Addr) (s : State) : Prop :=
  ArgT SP T s ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneAad` keeps `OneS`, the tag length, and the address of the received tag. -/
theorem aadTl_ok {s₀ s : State} {Np A D T : Addr} {nl al n t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hT : ArgT SP T s₀) (h : OpenIn s₀ Ctx W SP A D n t s) :
    WP isa (oneAad v.callees) s fun s' => OneS Ctx W SP A al D n s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP T s' :=
  WP.mono (oneMid_ok v C h.1 hNp hnl hal) fun _ Mi => by
    have La := L.lay
    refine ⟨(h.1.aadPre C hNp hnl hal).1.frame L Mi.env (Mi.rd.trans h.1.rd.symm) (Mi.wr.trans h.1.wr.symm)
      C.dE (wFrame_one (.inl rfl) (wFrame_cons Mi.fr)), ?_, ?_, by rw [Mi.rd, Mi.wr]; exact C.args 1 (by decide)⟩
    · rw [Mi.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact La.w_w (.inr (by decide)) (by decide) (by decide)
        · exact La.w_w (.inr (by decide)) (by decide) (by decide)
        · exact La.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), h.2.2]
    · rw [ArgT, Mi.frame.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact arg16_disj (by decide) C.dA C.dAD (.inl fun _ h => h)
        · exact arg16_disj (by decide) C.dA C.dAD (.inr (.inr fun _ h => h))) (by decide), hT]

/-- `oneTag 112` keeps `OneS` and the tag length. -/
theorem tagTl_ok {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr} {s : State} (hN : n < 2 ^ 64)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 16, 8⟩)
    (h : OneS Ctx W SP A al D n s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s) :
    WP isa (oneTag v.callees uO) s fun s' => OneS Ctx W SP A al D n s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s' :=
  WP.mono (oneTag_ok v L (o := 112) (.inr rfl) (x := []) (by decide) h.1.env rfl h.1.dat h.1.len h.1.tlen hN
    h.1.alen h.1.dD.dw.ok hDW h.1.dD.dw.ctx) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := D) (n := n) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hDW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hDW (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [ArgT, f.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _)
        (oA.tagFrame (o := 112) (by decide)) (by decide), h.2.2.1], by rw [hrd, hwr]; exact h.2.2.2⟩

omit L in
/-- The tag length loaded into `rbx`, and the address of the received tag into `rsi`. -/
theorem loadTl_ok {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr} {s : State}
    (h : OneS Ctx W SP A al D n s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))]) s fun s' =>
      OneS Ctx W SP A al D n s' ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rsi = Tp := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have r₂ := h.2.2.2
  obtain ⟨s₁, run₁, hbx, hsi, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 16))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, h.1.env.rsp, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.2.2.1]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm hrd hwr, hbx, hsi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

omit L in
/-- The result loaded from `W + 216`. -/
theorem loadAux_ok {s : State} (h : Env Ctx (W + BitVec.ofNat 64 16) W SP s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 auxO))]) s (Env Ctx (W + BitVec.ofNat 64 16) W SP) := by
  have r₁ := h.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 auxO))] s = some s₁ ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.r15, r₁], ?_, ?_, ?_⟩
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hrd hwr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

end

/-- From the entry, for an allowed tag length: ZF says whether
`openResult` fails. -/
theorem openPre_ok (v : GcmImpl) {s s₁ : State} {Ctx W SP Np A D Tp : Addr} {nl al n t : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (h : OpenIn s Ctx W SP A D n t s₁)
    (hNp : s.gpr .rsi = Np) (hnl : (s.gpr .rdx).toNat = nl) (hal : (s.gpr .r8).toNat = al)
    (hok : Spec.Gcm.tagLenOk t = true) (hT : ArgT SP Tp s)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : OutWDS W D SP n ⟨Tp, t⟩) :
    WP isa (.seq (oneAad v.callees) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))) s₁
      fun s' => OneS Ctx W SP A al D n s' ∧
        s'.zf = some (!(Spec.Gcm.openResult (ctxCiph s.mem Ctx) (ctxH s.mem Ctx) t
          (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem Tp t)).isSome) := by
  have L := C.lay
  have La := L.lay
  have E := h.1
  have hS := (E.aadPre C hNp hnl hal).1
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega_using [hok]
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₃ Mi => ?_)
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [Mi.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [Mi.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), h.2.2]
  have hd₃ := C.data.of_eq Mi.rd Mi.wr
  have hS₃ : OneS Ctx W SP A al D n s₃ := hS.frame L Mi.env (Mi.rd.trans E.rd.symm) (Mi.wr.trans E.wr.symm) C.dE
    (wFrame_one (.inl rfl) (wFrame_cons Mi.fr))
  have oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩ := fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 16) 64 = Tp := by
    rw [Mi.frame.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oA _ (.inl fun _ h => h)
      · exact oA _ (.inr (.inr fun _ h => h))) (by decide), hT]
  have hx16 : (bytesAt s.mem A al ++ Spec.Gcm.zeros (Spec.Gcm.padLen (bytesAt s.mem A al).length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.mono (openCheck_ok v L (al := al) hx16 Mi.env Mi.hH Mi.dat Mi.len Mi.tlen hlt hal₃ htl₃
    hb.1 hb.2 hd₃.dw.ok C.dE C.data.dw.ctx Mi.abs Mi.j0 hTa₃ (by rw [Mi.rd, Mi.wr]; exact C.args 1 (by decide))
    (by rw [Mi.rd, Mi.wr]; exact hTr) oT.ws oA.ws) fun s' O => ⟨hS₃.frame L O.env O.rd O.wr C.dE
      (wFrame_one (.inr rfl) O.frame), ?_⟩
  -- From the entry to `s₃`.
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP stkN).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₃ : ciphOf s₃.mem Ctx = ctxCiph s.mem Ctx := ciph_frame Mi.frame (fun r hr => dM _ _ La.cw' L.kc r hr)
  have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
    bytesAt_frame Mi.frame (dM _ _ C.dE C.data.stk) (by omega_using [hlt])
  have hw₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t := bytesAt_frame Mi.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact oT _ (.inl fun _ h => h)
    · exact oT _ (.inr (.inr fun _ h => h))) (by omega_using [hb])
  have hz := O.zf
  rw [padded_eq, hc₃, hp₃, hw₃] at hz
  rw [hz]
  simp only [Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- From the entry to the comparison, for an allowed tag length. -/
theorem openPre_rel {s₀ s₀' : State} {Np A D Tp : Addr} {nl al n t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hNp' : s₀'.gpr .rsi = Np) (hnl' : (s₀'.gpr .rdx).toNat = nl) (hal' : (s₀'.gpr .r8).toNat = al)
    (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀') :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq (oneAad v.callees) (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
        (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))
      fun _ _ => True := by
  have hDW := C.dE
  have hlt := C.data.dw.ok.lt
  have oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩ := fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have a := rel_wp ((oneAad_rel v L hDW (Np := Np) (nl := nl)).mono
      (P' := fun (s₁ s₂ : State) => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (fun _ _ h => ⟨h.1.1.aadPre C hNp hnl hal, h.2.1.aadPre C' hNp' hnl' hal'⟩) fun _ _ _ => trivial)
    (fun _ _ h => h) (fun _ h => aadTl_ok v L C hNp hnl hal hT h) (fun _ h => aadTl_ok v L C' hNp' hnl' hal' hT' h)
  have b := rel_wp ((oneTag_rel v L (.inr rfl) hDW).mono (P' := fun (s₁ s₂ : State) =>
        (OneS Ctx W SP A al D n s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₁) ∧
        (OneS Ctx W SP A al D n s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₂))
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => tagTl_ok v L hlt hDW oA.ws h) (fun _ h => tagTl_ok v L hlt hDW oA.ws h)
  have c := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP A al D n s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₁) ∧
      (OneS Ctx W SP A al D n s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₂))
      [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env ⟨h.2.1.1, h.2.2.1⟩) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => loadTl_ok h) (fun _ h => loadTl_ok h)
  have d := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp) ∧
      (OneS Ctx W SP A al D n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t ∧ s₂.gpr .rsi = Tp))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩)
    (RelCT.seq (b.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩) (RelCT.seq c d))

omit v in
/-- After the comparison: the data decrypted if the tags match, and the
result loaded. -/
theorem openPost_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat} {b₁ b₂ : Bool} (hb : b₁ = b₂)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => True ∧ (OneS Ctx W SP A al D n s₁ ∧ s₁.zf = some b₁) ∧
        (OneS Ctx W SP A al D n s₂ ∧ s₂.zf = some b₂))
      (.seq (.ite .e (.block []) oneCrypt) (.block [.mov .rax (.mem (at_ .r15 auxO))]))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have e := (oneCrypt_rel L (A := A) (al := al) hDW).mono
    (P' := fun (s₁ s₂ : State) => (True ∧ (OneS Ctx W SP A al D n s₁ ∧ s₁.zf = some b₁) ∧
        (OneS Ctx W SP A al D n s₂ ∧ s₂.zf = some b₂)) ∧ s₁.zf = some false)
    (Q' := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => ⟨h.1.env, h.2.env⟩
  have f := rel_wp (rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun _ h => loadAux_ok h) (fun _ h => loadAux_ok h)
  exact RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, hb])
    (RelCT.block_nil fun _ _ h => ⟨h.1.2.1.1.env, h.1.2.2.1.env⟩) e)
    (f.mono (fun _ _ h => h) fun _ _ h => h.2)

/-- After the entry: the tag length checked, then, if it is allowed, `mid`. -/
theorem openBody_relOf {s₀ s₀' : State} {A D : Addr} {n t : Nat} {mid : Prog isa} (ht : t < 2 ^ 64)
    (hrel : Spec.Gcm.tagLenOk t = true →
      RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂) mid
        fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) :
    RelCT isa (fun s₁ s₂ => True ∧ OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq tagLenOk (.ite .e (.block [.mov32 .rax (imm 0)]) mid))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have hK : ∀ {s₀ s : State}, OpenIn s₀ Ctx W SP A D n t s → WP isa tagLenOk s fun s' =>
      OpenIn s₀ Ctx W SP A D n t s' ∧ s'.zf = some (!Spec.Gcm.tagLenOk t) := fun h =>
    WP.mono (tagLenOk_ok _ h.2.1 ht) fun _ ⟨hz, k⟩ =>
      ⟨⟨h.1.keep L (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k.rd k.wr
          (by rw [k.mem]; exact Frame.refl _ _), by rw [k.gpr _ (by decide), h.2.1], by rw [k.mem]; exact h.2.2⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun (s₁ s₂ : State) => True ∧ OpenIn s₀ Ctx W SP A D n t s₁ ∧
      OpenIn s₀' Ctx W SP A D n t s₂) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun _ h => hK h) (fun _ h => hK h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length `tagLenOk` does not allow.
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.env, h.1.2.2.1.1.env⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.env h.1.2.2.1.1.env)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    exact (hrel hok).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h

end

/-- For an allowed tag length: `oneAad`, the tags compared, and the data
decrypted if they match. -/
theorem openOk_rel (v : GcmImpl) {s₀ s₀' : State} {Ctx W SP Np A D Tp : Addr} {nl al n t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hNp' : s₀'.gpr .rsi = Np) (hnl' : (s₀'.gpr .rdx).toNat = nl) (hal' : (s₀'.gpr .r8).toNat = al)
    (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr)) (hTr' : Covers [⟨Tp, t⟩] (s₀'.rd ++ s₀'.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome)
    (hok : Spec.Gcm.tagLenOk t = true) :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq (oneAad v.callees)
        (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
        (.seq recv
        (.seq (cmp uO)
        (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
        (.seq (.ite .e (.block []) oneCrypt)
          (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  refine rel_reassoc6 (RelCT.seq ?_ (openPost_rel L (A := A) (al := al) (congrArg (!·) hres) C.dE))
  exact rel_wp ((openPre_rel v L C C' hNp hnl hal hNp' hnl' hal' hT hT').mono
      (fun _ _ h => h) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => openPre_ok v C h hNp hnl hal hok hT hTr oT)
    (fun _ h => openPre_ok v C' h hNp' hnl' hal' hok hT' hTr' oT)

theorem open_rel (v : GcmImpl) {s₀ s₀' : State}
    (hp : Proof.Sm4Gcm.openX86_64.pre s₀) (hp' : Proof.Sm4Gcm.openX86_64.pre s₀')
    (hq : Proof.Sm4Gcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp
  obtain ⟨C', hTr', -, -, -⟩ := OneCtx.ofOpen hp'
  have L := C.lay
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩, hres⟩ := hq
  simp only [Proof.Sm4Gcm.openLeak, Proof.Sm4Gcm.arg] at hres
  have hres := leak_bool hres
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide)
  simp only [Proof.Sm4Gcm.arg] at a₀ a₁ a₂ a₃
  have ha₃ := C.args 3 (by decide); have ha₃' := C'.args 3 (by decide)
  have hw32 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 32) 64 := a₃
  have hT₁ : ArgT (s₀.gpr .rsp) (stackArg s₀ 1) s₀ := rfl
  have hT₂ : ArgT (s₀.gpr .rsp) (stackArg s₀ 1) s₀' := by rw [ArgT, q₇, a₁]; rfl
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₃] at C'
  rw [← a₁, ← a₂] at hTr'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← a₀, ← a₁, ← a₂] at hres
  generalize ht : (stackArg s₀ 2).toNat = t at hres hTr hTr' d_td d_tw t_t
  have oT : OutWDS (stackArg s₀ 3) (s₀.gpr .r9) (s₀.gpr .rsp) (stackArg s₀ 0).toNat ⟨stackArg s₀ 1, t⟩ :=
    fun r hr => hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have hE : ∀ {s : State} (C : OneCtx s 4 (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rsi) (s₀.gpr .rcx)
      (s₀.gpr .r9) (s₀.gpr .rdx).toNat (s₀.gpr .r8).toNat (stackArg s₀ 0).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .rcx = s₀.gpr .rcx →
      s.gpr .r9 = s₀.gpr .r9 → (stackArg s 0).toNat = (stackArg s₀ 0).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 → stackArg s 2 = stackArg s₀ 2 →
      WP isa (.block (oneEntry 32 ++ [.mov .rbx (.mem (at_ .rsp 24)), .store (at_ .r15 tlO) .rbx])) s
        (OpenIn s (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rcx) (s₀.gpr .r9) (stackArg s₀ 0).toNat t) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => WP.mono (openEntry_ok C h₁ h₂ h₃ h₄ h₅ h₆) fun _ ⟨E, hbx, htl, _⟩ =>
      ⟨E, by rw [hbx, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [htl, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl rfl
  have hE₂ := hE C' q₁.symm q₇.symm q₄.symm q₆.symm (by rw [a₀]) (by rw [q₇, a₃]; rfl) a₂.symm
  rw [oneEntry] at hE₁ hE₂
  simp only [List.append_assoc] at hE₁ hE₂
  rw [«open», oneEntry]
  simp only [List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 3 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 3) (SP := s₀.gpr .rsp) (k := 32) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩) hw32 ha₃ ha₃' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  exact openBody_relOf L (by rw [← ht]; exact (stackArg s₀ 2).isLt) fun hok =>
    openOk_rel v C C' rfl rfl rfl q₂.symm (by rw [← q₃]) (by rw [← q₅]) hT₁ hT₂ hTr hTr' oT hres hok

theorem open_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.openX86_64.pre Proof.Sm4Gcm.openX86_64.pub («open» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => open_rel v hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
