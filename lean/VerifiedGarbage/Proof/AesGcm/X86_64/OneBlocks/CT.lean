module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
meta import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import Lean.Level
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import Lean.Level
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesGcm.X86_64.J0
meta import VerifiedGarbage.Proof.AesGcm.X86_64.J0

/-! ### `AesGcm.X86_64.OneCT`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.J0CT`, which this module and modules that import it used -/

section

/-!
# AES-GCM on x86-64: `j0` in two runs

Untrusted: everything here is checked by Lean. Two runs of `j0` for nonces
at the same address, of the same length, leak the same: the branch is on the
length, and the GHASH of a nonce of any other length is `absorbPad` and
`lens` (`absorbPad_rel`, `lens_rel`), with the length kept at
`W + 216` between them.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N gs : Nat} [G : GhFits v N gs] (L : Lay Ctx St W SP N)
include G L

/-- The nonce's length is kept at `W + 216`. -/
def AuxN (Ctx St W SP : Addr) (n : Nat) (s : State) (N : Nat := 2560) : Prop :=
  Env Ctx St W SP s N ∧ s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

omit G in
theorem j0hashA_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In Ctx St W SP H Np n s N)
    (hN : 224 ≤ N := by decide) :
    WP isa (.block [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax, .store (at_ .r14 8) .rax,
      .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)]) s fun s₁ =>
      (∃ H', AbsIn Ctx St W SP 0 H' [] Np n s₁ N) ∧ AuxN Ctx St W SP n s₁ N := by
  have he := h.env
  have h14 := he.r14; have h15 := he.r15
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have wa := he.perm.wW (show 216 + 8 ≤ N from (Lay.leN hN)) L.nlt
  obtain ⟨s₁, run₁, hm₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax,
      .store (at_ .r14 8) .rax, .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h14, h15, z₀, z₁, wa], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, h.rbp, Mem.readW_writeW_self64]
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  have he₁ : Env Ctx St W SP s₁ N := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨s₁, run₁, ⟨_, he₁, by rw [hg₁ _ (by decide) (by decide), h.r12],
    by rw [hg₁ _ (by decide) (by decide), h.rbp], by rw [hbx₁]; rfl, h.data.of_eq hrd₁ hwr₁, rfl⟩, he₁, hm₁⟩

omit G in
theorem auxLens_ok {n : Nat} {s : State} (h : AuxN Ctx St W SP n s N)
    (hN : 224 ≤ N := by decide) :
    WP isa (.block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))]) s fun s₁ =>
      Env Ctx St W SP s₁ N ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n := by
  have ra := h.1.perm.wR (show 216 + 8 ≤ N from (Lay.leN hN)) L.nlt
  obtain ⟨s₁, run₁, hbx, hbp, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov32 .rbx (imm 0),
      .mov .rbp (.mem (at_ .r15 auxO))] s = some s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.r15, ra], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, h.2]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hrd hwr, hbx, hbp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- `J₀` of a nonce of any length but 12, for nonces at the same address, of
the same length. -/
theorem j0hash_rel {H₁ H₂ : Block} {Np : Addr} {n : Nat} (hN : 224 ≤ N := by decide) :
    RelCT isa (fun s₁ s₂ => J0In Ctx St W SP H₁ Np n s₁ N ∧ J0In Ctx St W SP H₂ Np n s₂ N) (j0hash v.callees)
      fun _ _ => True := by
  by_cases hlt : n < 2 ^ 64
  swap
  · exact RelCT.of_false fun _ _ h => hlt h.1.data.lt
  -- After `absorbPad`, the length is still kept.
  have hA : ∀ s, (∃ H', AbsIn Ctx St W SP 0 H' [] Np n s N) ∧ AuxN Ctx St W SP n s N →
      WP isa (absorbPad v.callees 0) s (AuxN Ctx St W SP n · N) := fun s ⟨⟨_, h⟩, ha⟩ =>
    WP.mono (absorbPad_ok v L (.inl rfl) h rfl) fun _ o => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact ⟨o.env, by
        rw [ft.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (aux_tFrame L hN G.fit) (by decide),
          fa.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (aux_absFrame L hN G.fit) (by decide),
          ha.2]⟩
  have r₀ := rel_wp (rel_taint (P := fun s₁ s₂ => J0In Ctx St W SP H₁ Np n s₁ N ∧ J0In Ctx St W SP H₂ Np n s₂ N)
      [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [h.1.r12, h.2.r12]
        · rw [h.1.rbp, h.2.rbp]
        · rw [h.1.env.r13, h.2.env.r13]
        · rw [h.1.env.r14, h.2.env.r14]
        · rw [h.1.env.r15, h.2.env.r15]
        · rw [h.1.env.rsp, h.2.env.rsp]) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => j0hashA_ok L h hN) (fun s h => j0hashA_ok L h hN)
  let PA : State → State → Prop := fun s₁ s₂ => True ∧
    ((∃ H', AbsIn Ctx St W SP 0 H' [] Np n s₁ N) ∧ AuxN Ctx St W SP n s₁ N) ∧
    ((∃ H', AbsIn Ctx St W SP 0 H' [] Np n s₂ N) ∧ AuxN Ctx St W SP n s₂ N)
  have a₁ : RelCT isa PA (absorbPad v.callees 0) fun _ _ => True :=
    (RelCT.exists_ fun H₁' => RelCT.exists_ fun H₂' =>
      absorbPad_rel v L (.inl rfl) (H₁ := H₁') (H₂ := H₂') (x₁ := []) (x₂ := []) (D := Np) (n := n) rfl rfl).mono
      (fun s₁ s₂ (h : PA s₁ s₂) => by
        obtain ⟨_, ⟨⟨H₁', h₁⟩, _⟩, ⟨⟨H₂', h₂⟩, _⟩⟩ := h; exact ⟨H₁', H₂', h₁, h₂⟩) fun _ _ h => h
  have r₁ := rel_wp a₁ (fun _ _ h => h.2) hA hA
  have r₄ := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ AuxN Ctx St W SP n s₁ N ∧ AuxN Ctx St W SP n s₂ N)
      (c := .block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))])
      [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1.1, h.2.2.1, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun s h => auxLens_ok L h hN) (fun s h => auxLens_ok L h hN)
  have r₅ := (lens_rel v L (yo := 0) (.inl rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (Env Ctx St W SP s₁ N ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧ s₁.gpr .rbp = BitVec.ofNat 64 n) ∧
      (Env Ctx St W SP s₂ N ∧ s₂.gpr .rbx = BitVec.ofNat 64 0 ∧ s₂.gpr .rbp = BitVec.ofNat 64 n))
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) fun _ _ h => h
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₄ r₅))

/-- `j0`, for nonces at the same address, of the same length. -/
theorem j0_rel {H₁ H₂ : Block} {Np : Addr} {n : Nat} (hN : 224 ≤ N := by decide) :
    RelCT isa (fun s₁ s₂ => J0In Ctx St W SP H₁ Np n s₁ N ∧ J0In Ctx St W SP H₂ Np n s₂ N) (j0 v.callees)
      fun _ _ => True := by
  have hag : ∀ s₁ s₂, J0In Ctx St W SP H₁ Np n s₁ N ∧ J0In Ctx St W SP H₂ Np n s₂ N →
      ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := fun _ _ h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.env.r13, h.2.env.r13]
    · rw [h.1.env.r14, h.2.env.r14]
    · rw [h.1.env.r15, h.2.env.r15]
    · rw [h.1.env.rsp, h.2.env.rsp]
  have hC : ∀ {H : Block} (s : State), J0In Ctx St W SP H Np n s N →
      WP isa (.block [.alu .cmp .rbp (imm 12)]) s (fun s₁ => J0In Ctx St W SP H Np n s₁ N ∧
        s₁.zf = some (decide (n = 12))) := fun s h => by
    have hlt := h.data.lt
    obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .rbp (imm 12)] s = some s₁ ∧
        s₁.zf = some (decide (n = 12)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [], ?_, by rfl, by rfl, by rfl, by rfl⟩
      rw [zf_arithFlags, h.rbp]
      exact congrArg some (sub_beq hlt (by decide))
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hm₁]; exact h.hH,
      by rw [hg₁]; exact h.r12, by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁⟩, hzf⟩
  have c := rel_wp (rel_regs [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hC s h) (fun s h => hC s h)
  let P₀ : State → State → Prop := fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (J0In Ctx St W SP H₁ Np n s₁ N ∧ s₁.zf = some (decide (n = 12))) ∧
      (J0In Ctx St W SP H₂ Np n s₂ N ∧ s₂.zf = some (decide (n = 12)))
  refine RelCT.seq c (RelCT.seq (R := fun s₁ s₂ => Env Ctx St W SP s₁ N ∧ Env Ctx St W SP s₂ N)
    (rel_ite_e (P := P₀) (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_) ?_)
  · let P₁ : State → State → Prop := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (J0In Ctx St W SP H₁ Np n s₁ N ∧ s₁.zf = some (decide (n = 12))) ∧
      (J0In Ctx St W SP H₂ Np n s₂ N ∧ s₂.zf = some (decide (n = 12)))) ∧ s₁.zf = some true
    have ht : RelCT isa P₁ (.block j012) fun _ _ => True :=
      rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp] (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩)
        ⟨_, by taint_decide⟩
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.env, h.1.2.2.1.env⟩) ht).mono (fun _ _ h => h)
      fun _ _ h => h.2
  · by_cases h12 : n = 12
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [h12] at this
    let P₂ : State → State → Prop := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (J0In Ctx St W SP H₁ Np n s₁ N ∧ s₁.zf = some (decide (n = 12))) ∧
      (J0In Ctx St W SP H₂ Np n s₂ N ∧ s₂.zf = some (decide (n = 12)))) ∧ s₁.zf = some false
    have hj : RelCT isa P₂ (j0hash v.callees) fun _ _ => True :=
      (j0hash_rel v L hN).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
    exact (rel_wp hj (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (G₁ := (Env Ctx St W SP · N)) (G₂ := (Env Ctx St W SP · N))
      (fun s h => WP.mono (j0hash_ok v L h h12 hN) fun _ m => m.env)
      (fun s h => WP.mono (j0hash_ok v L h h12 hN) fun _ m => m.env)).mono (fun _ _ h => h) fun _ _ h => h.2
  · exact rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩)
      ⟨_, by taint_decide⟩

end

end VG.Proof.AesGcm.X86_64

end

end

/-! ### `AesGcm.X86_64.CryptCT`, which this module and modules that import it used -/

section

/-!
# AES-GCM on x86-64: `crypt` in two runs

Untrusted: everything here is checked by Lean. Two runs of `crypt` over
data at the same address, of the same length, after the same number of
bytes modulo 16, with the same number of rounds, leak the same: the code
between the calls of `vg_aes_ctr32` is checked by the taint analysis, from
the registers `CrIn` and `CrMid` fix, and each call has the same arguments
in both runs.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem CrMid.agree {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat}
    {s₁ s₂ : State} (h₁ : CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁) (h₂ : CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) :
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
theorem cryptWhole_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂)
      (cryptWhole v.callees) fun _ _ => True := by
  let Sp : State → Prop := fun s₁ => Env Ctx St W SP s₁ ∧ DataW Ctx St W SP s₁ D n ∧ j ≤ n ∧
    RoundsAt s₁.mem W R ∧ s₁.gpr .rcx = D + BitVec.ofNat 64 j ∧ s₁.gpr .r8 = BitVec.ofNat 64 ((n - j) / 16)
  obtain hS : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State), CrMid Ctx St W SP R icb P D n m j s →
      WP isa (.block (splitWhole .rcx .r8 ++ [.alu .test .r8 (.reg .r8)])) s Sp := fun s h => by
    obtain ⟨s₁, run₁, hcx, h8, -, -, -, hg₁, hm₁, hrd₁, hwr₁⟩ :=
      wholeSplit_ok .rcx .r8 (.inr ⟨rfl, rfl⟩) h.data.ok.lt h.le h.r12 h.rbp
    refine WP.of_runBlock ⟨s₁, run₁, h.env.keep (fun r hr => ?_) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁, h.le,
      by rw [hm₁]; exact h.rounds, hcx, h8⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain a := rel_wp (rel_regs (P := fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧
      CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂) [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1 h.2) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hS s h) (fun s h => hS s h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  let Ar : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R ((n - j) / 16)
  obtain hA : ∀ s, Sp s → WP isa (.block ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++
      ptr .rdx .r14 48 ++ ptr .r9 .r15 scrO)) s Ar := fun s ⟨he, hd, hj, hR, hcx, h8⟩ => by
    obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, -, hrd₂, hwr₂⟩ := ctrArgs_ok he hR
    obtain he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    exact WP.of_runBlock ⟨s₂, run₂, he₂, cwCall_of L he₂ (hd.of_eq hrd₂ hwr₂) hj (by omega_using []) hR.2 hdi hsi hdx
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), hcx])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h8]) h9⟩
  obtain b := rel_wp (rel_taint (P := fun s₁ s₂ => ((True ∧ Sp s₁ ∧ Sp s₂) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1.2.1.1, h.1.2.2.1, fun _ h => by cases h⟩)
    ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) hA hA
  refine (RelCT.seq b (ctr_rel v.ctr fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩)).mono
    (fun _ _ h => ⟨⟨trivial, h.1.2.1, h.1.2.2⟩, h.2⟩) fun _ _ h => h
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

/-- The arguments of `cryptTail`'s call of `vg_aes_ctr32`. -/
theorem ctTailArgs_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP R icb P D n m₀ j s) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) s fun s₂ =>
      Env Ctx St W SP s₂ ∧
      CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 ∧
      s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j) ∧ s₂.gpr .rbx = s.gpr .rbx := by
  have he := h.env
  obtain h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  obtain r₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  obtain w₁ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  obtain w₂ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s = some s₂ ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = St + BitVec.ofNat 64 64 ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hR := h.rounds.1
    obtain hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (St + BitVec.ofNat 64 64) x).writeW
        (St + BitVec.ofNat 64 72) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
      intro m x y
      rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 72) (n := 8) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
        Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 64) (n := 8) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    refine ⟨_, by xrun [h13, h14, h15, w₁, w₂, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg, hsep, hR]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  refine ⟨he₂, ?_, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    h.r12], by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp],
    hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  refine ⟨hdi, hsi, hdx, hcx, h8, h9, h.rounds.2, by have := L.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [this],
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    L.st_st (.inl (by decide)) (by decide) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact L.stk_w (by decide)
  · refine covers_cons ?_ (covers_cons (covers_left (he₂.perm.stC (by decide))) (covers_cons
      (covers_left (he₂.perm.stC (by decide))) (covers_left (he₂.perm.wC (by decide)))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega_using [hc']⟩
  · exact covers_cons (he₂.perm.stC (by decide)) (covers_cons (he₂.perm.stC (by decide))
      (he₂.perm.wC (by decide)))

/-- The last bytes, with a new keystream block, read at the same `Q` in `rbx`
in both runs out of place (`to`). -/
theorem cryptTailG_rel (to : Bool) {Q : Addr} {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat}
    {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => (CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ (to = true → s₁.gpr .rbx = Q)) ∧
        CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂ ∧ (to = true → s₂.gpr .rbx = Q))
      (cryptTailG v.callees to) fun _ _ => True := by
  obtain hT : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State),
      CrMid Ctx St W SP R icb P D n m j s ∧ (to = true → s.gpr .rbx = Q) →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) s
        (fun s' => CrMid Ctx St W SP R icb P D n m j s' ∧ (to = true → s'.gpr .rbx = Q)) := fun s ⟨h, hb⟩ => by
    obtain ⟨s₁, run₁, -, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (by have := h.data.ok.lt; omega_using [this])
    refine WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.le, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds, fun hc => by rw [hm₁]; exact h.ctr hc,
      fun hc => by rw [hm₁]; exact h.done hc, by rw [hm₁]; exact h.rest, h.whole, by rw [hm₁]; exact h.frame⟩,
      fun ht => by rw [hg₁]; exact hb ht⟩
  obtain t := rel_wp (rel_regs (P := fun s₁ s₂ => (CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧
      (to = true → s₁.gpr .rbx = Q)) ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂ ∧ (to = true → s₂.gpr .rbx = Q))
      [.r12, .rbp, .r13, .r14, .r15, .rsp] [] true
    (fun _ _ h => CrMid.agree h.1.1 h.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)
  refine RelCT.seq t (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The arguments of the call, and what it keeps.
  let G : State → Prop := fun s₂ => Env Ctx St W SP s₂ ∧
    CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 ∧
    s₂.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₂.gpr .rbp = BitVec.ofNat 64 (n - j) ∧ (to = true → s₂.gpr .rbx = Q)
  let K : State → Prop := fun s₃ => Env Ctx St W SP s₃ ∧
    s₃.gpr .r12 = D + BitVec.ofNat 64 j ∧ s₃.gpr .rbp = BitVec.ofNat 64 (n - j) ∧ (to = true → s₃.gpr .rbx = Q)
  obtain hA : ∀ {icb : Block} {P : Nat} {m : Mem} (s : State),
      CrMid Ctx St W SP R icb P D n m j s ∧ (to = true → s.gpr .rbx = Q) →
      WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
        .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
        ptr .rcx .r14 64 ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) s G := fun s ⟨h, hb⟩ =>
    WP.mono (ctTailArgs_ok L h) fun _ ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, fun ht => by rw [e]; exact hb ht⟩
  obtain a := rel_wp (rel_taint (P := fun s₁ s₂ => ((((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ (to = true → s₁.gpr .rbx = Q)) ∧
      CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂ ∧ (to = true → s₂.gpr .rbx = Q)) ∧ s₁.zf = some false))
    [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => CrMid.agree h.1.2.1.1 h.1.2.2.1 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1, h.1.2.2⟩) (G₁ := G) (G₂ := G) (fun s h => hA s h) (fun s h => hA s h)
  obtain hK : ∀ s, G s → WP isa (.call v.ctr.callee.name v.ctr.callee.code) s K := fun s ⟨he, hc, h12, hbp, hbx⟩ =>
    WP.mono (ctr_call v.ctr hc) fun _ g => ⟨he.of_saved g.saved g.rd g.wr,
      by rw [g.saved _ (by decide), h12], by rw [g.saved _ (by decide), hbp],
      fun ht => by rw [g.saved _ (by decide), hbx ht]⟩
  obtain c := rel_wp (ctr_rel v.ctr (P := fun s₁ s₂ => True ∧ G s₁ ∧ G s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, _, h.2.1.2.1, h.2.2.2.1, by rw [h.2.1.1.rsp, h.2.2.1.rsp]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hK hK
  obtain hag : ∀ s₁ s₂, True ∧ K s₁ ∧ K s₂ → ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
    fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2.1, h.2.2.2.2.1]
      · rw [h.2.1.1.r13, h.2.2.1.r13]
      · rw [h.2.1.1.r14, h.2.2.1.r14]
      · rw [h.2.1.1.r15, h.2.2.1.r15]
      · rw [h.2.1.1.rsp, h.2.2.1.rsp]
  obtain d : RelCT isa (fun s₁ s₂ => True ∧ K s₁ ∧ K s₂)
      (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r14 64 ++
        ([.mov .rcx (.reg .rbp)] : List Instr))) (xorLoopG to)) fun _ _ => True := by
    cases to
    · exact rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp] hag ⟨_, by taint_decide⟩
    · exact rel_taint [.r12, .rbp, .r13, .r14, .r15, .rsp, .rbx] (fun s₁ s₂ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with hr | hr | hr | hr | hr | hr | rfl
        · exact hag _ _ h r (by simp [hr])
        · exact hag _ _ h r (by simp [hr])
        · exact hag _ _ h r (by simp [hr])
        · exact hag _ _ h r (by simp [hr])
        · exact hag _ _ h r (by simp [hr])
        · exact hag _ _ h r (by simp [hr])
        · rw [h.2.1.2.2.2 rfl, h.2.2.2.2.2 rfl]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq c d)

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} {m₁ m₂ : Mem} {j : Nat} :
    RelCT isa (fun s₁ s₂ => CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂)
      (cryptTail v.callees) fun _ _ => True :=
  (cryptTailG_rel v L false (Q := 0)).mono (fun _ _ h => ⟨⟨h.1, nofun⟩, h.2, nofun⟩) fun _ _ h => h

/-- `crypt`, over data at the same address, of the same length, after the
same number of bytes modulo 16, with the same number of rounds. -/
theorem crypt_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} (hP : P₁ % 16 = P₂ % 16) :
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP R icb₂ P₂ D n s₂)
      (crypt v.callees) fun _ _ => True := by
  obtain hag : ∀ s₁ s₂, CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP R icb₂ P₂ D n s₂ →
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
  obtain hT : ∀ {r : Reg} {icb : Block} {P : Nat} {k : Nat} (s : State), CrIn Ctx St W SP R icb P D n s →
      s.gpr r = BitVec.ofNat 64 k → k < 2 ^ 64 →
      WP isa (.block [.alu .test r (.reg r)]) s (fun s' => CrIn Ctx St W SP R icb P D n s' ∧
        s'.zf = some (decide (k = 0))) := fun s h hk hk' => by
    obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s _ hk hk'
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, by rw [hg₁]; exact h.r12,
      by rw [hg₁]; exact h.rbp, by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds⟩, hz⟩
  obtain t₁ := rel_wp (rel_regs (P := fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧
      CrIn Ctx St W SP R icb₂ P₂ D n s₂) absRegs [] true hag ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (fun s h => hT (r := .rbp) s h h.rbp h.data.ok.lt)
    (fun s h => hT (r := .rbp) s h h.rbp h.data.ok.lt)
  refine RelCT.seq t₁ (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hn0] at this
  obtain hr₁ := Nat.mod_lt P₁ (show 16 > 0 by decide)
  obtain hr₂ := Nat.mod_lt P₂ (show 16 > 0 by decide)
  obtain t₂ := rel_wp (rel_regs (P := fun s₁ s₂ => (((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
      (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (n = 0))) ∧
      CrIn Ctx St W SP R icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (n = 0))) ∧ s₁.zf = some false)
      absRegs [] true (fun _ _ h => hag _ _ ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun s h => hT (r := .rbx) s h h.rbx (by omega_using []))
    (fun s h => hT (r := .rbx) s h h.rbx (by omega_using []))
  obtain i₂ : RelCT isa (fun s₁ s₂ => ((∀ r ∈ ([] : List Reg), s₁.gpr r = s₂.gpr r) ∧
        (true = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
        (CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ s₁.zf = some (decide (P₁ % 16 = 0))) ∧
        CrIn Ctx St W SP R icb₂ P₂ D n s₂ ∧ s₂.zf = some (decide (P₂ % 16 = 0)))
      (.ite .e (.block []) cryptHead) fun s₁ s₂ => ∃ j, ∃ m₁ m₂ : Mem,
        CrMid Ctx St W SP R icb₁ P₁ D n m₁ j s₁ ∧ CrMid Ctx St W SP R icb₂ P₂ D n m₂ j s₂ := by
    refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_
    · by_cases ho : P₁ % 16 = 0
      swap
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine RelCT.block_nil fun s₁ s₂ h => ⟨0, s₁.mem, s₂.mem, ?_, ?_⟩
      · have h₂ := h.1.2.1.1
        exact ⟨h₂.env, by omega_using [], by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
          h₂.rounds, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by simp,
          .inr (by omega_using [ho]), Frame.refl _ _⟩
      · have h₂ := h.1.2.2.1
        exact ⟨h₂.env, by omega_using [], by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
          h₂.rounds, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by simp,
          .inr (by omega_using [hP, ho]), Frame.refl _ _⟩
    · by_cases ho : P₁ % 16 = 0
      · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [ho] at this
      refine (rel_wp ((rel_taint absRegs (P := fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧
          CrIn Ctx St W SP R icb₂ P₂ D n s₂) hag ⟨_, by taint_decide⟩).mono ?_ fun _ _ h => h) ?_
        (G₁ := fun s => ∃ m, CrMid Ctx St W SP R icb₁ P₁ D n m (min (16 - P₁ % 16) n) s)
        (G₂ := fun s => ∃ m, CrMid Ctx St W SP R icb₂ P₂ D n m (min (16 - P₂ % 16) n) s)
        (fun s h => WP.mono (cryptHead_ok h hn0 ho) fun _ h => ⟨_, h⟩)
        (fun s h => WP.mono (cryptHead_ok h hn0 (by omega_using [hP, ho])) fun _ h => ⟨_, h⟩)).mono (fun _ _ h => h)
        fun _ _ ⟨_, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ => ⟨_, m₁, m₂, h₁, by rw [hP]; exact h₂⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · exact fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  refine RelCT.seq t₂ (RelCT.seq i₂ ?_)
  refine RelCT.exists_ fun j => RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  obtain hw := rel_wp (cryptWhole_rel v L (R := R) (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := j)) (fun _ _ h => h)
    (fun s h => cryptWhole_ok v L h (h.ciph L)) (fun s h => cryptWhole_ok v L h (h.ciph L))
  exact RelCT.seq hw ((cryptTail_rel v L).mono (fun _ _ h => h.2) fun _ _ h => h)

/-- `cryptAl`, for data at the same address, of the same length, from the
start of a keystream block. -/
theorem cryptAl_rel {R : Nat} {icb₁ icb₂ : Block} {P₁ P₂ : Nat} {D : Addr} {n : Nat} (hP₁ : P₁ % 16 = 0)
    (hP₂ : P₂ % 16 = 0) :
    RelCT isa (fun s₁ s₂ => CrIn Ctx St W SP R icb₁ P₁ D n s₁ ∧ CrIn Ctx St W SP R icb₂ P₂ D n s₂)
      (cryptAl v.callees) fun _ _ => True := by
  suffices k : RelCT isa (fun s₁ s₂ => ∃ m₁ m₂ : Mem, CrMid Ctx St W SP R icb₁ P₁ D n m₁ 0 s₁ ∧
      CrMid Ctx St W SP R icb₂ P₂ D n m₂ 0 s₂) (cryptAl v.callees) fun _ _ => True from
    k.mono (fun s₁ s₂ h => ⟨s₁.mem, s₂.mem, h.1.mid hP₁, h.2.mid hP₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  obtain hw := rel_wp (cryptWhole_rel v L (R := R) (icb₁ := icb₁) (icb₂ := icb₂) (P₁ := P₁) (P₂ := P₂) (D := D)
      (n := n) (m₁ := m₁) (m₂ := m₂) (j := 0)) (fun _ _ h => h)
    (fun s h => cryptWhole_ok v L h (h.ciph L)) (fun s h => cryptWhole_ok v L h (h.ciph L))
  exact RelCT.seq hw ((cryptTail_rel v L).mono (fun _ _ h => h.2) fun _ _ h => h)

end

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM on x86-64: the pieces of `seal` and `open` in two runs

Untrusted: everything here is checked by Lean. What stays in `W` between
the pieces (`OneS`: the rounds, the additional data's address and length,
the data's address and length) is the same in both runs, so each piece
(`oneAad`, `oneCrypt`, `oneTag`) leaks the same, by the fragments'
relations.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- What stays in `W` and the buffers between the pieces of `seal` and `open`. -/
structure OneS (M : Gcm.X86_64.Stitch.CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  dA : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  dD : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  /-- The total length, once `oneBlocks` has kept it. -/
  tlen : ∀ N, T = some N → s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N
  ext : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : Gcm.X86_64.Stitch.CtxMode}
include L

theorem OneS.frame {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s s' : State}
    (h : OneS M Ctx W SP R A al D n T s) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (oneFrame W D SP n) s.mem s'.mem) : OneS M Ctx W SP R A al D n T s' := by
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  exact ⟨he, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad, by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact h.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact h.len,
    h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr, fun N hN => by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact h.tlen N hN,
    h.ext.keep hrd hwr hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h.ext.cw.sub_right (Region.sub_prefix (by decide))
      · exact h.ext.cw.sub_right (Lay.wSub (by decide))
      · exact h.ext.cw.sub_right (Lay.wSub (by decide))
      · exact h.ext.cd
      · exact (h.ext.ct.sub_left (below_sub (by decide) (by decide))).symm)⟩

omit L in
theorem OneS.keep {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s s' : State}
    (h : OneS M Ctx W SP R A al D n T s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OneS M Ctx W SP R A al D n T s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.rounds, by rw [hm]; exact h.aad, by rw [hm]; exact h.alen,
    by rw [hm]; exact h.dat, by rw [hm]; exact h.len, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr,
    fun N hN => by rw [hm]; exact h.tlen N hN, h.ext.of_eq hrd hwr hm⟩

omit L in
/-- Two slots of `W` loaded, and a constant. -/
theorem load2_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s : State}
    (h : OneS M Ctx W SP R A al D n T s) {o₁ o₂ : Nat} {P : Addr} {k : Nat}
    (h₁ : s.mem.readW (W + BitVec.ofNat 64 o₁) 64 = P) (h₂ : s.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 k)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₁) 8) (q₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₂) 8) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)]) s
      fun s₁ => OneS M Ctx W SP R A al D n T s₁ ∧ s₁.gpr .r12 = P ∧ s₁.gpr .rbp = BitVec.ofNat 64 k ∧
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

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : Gcm.X86_64.Stitch.CtxMode}
include L

omit L in
theorem w_one {D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wFrame W SP) m m') : Frame (oneFrame W D SP n) m m' :=
  wFrame_one (o := 0) (.inl rfl) (wFrame_cons h)

/-- Two runs in `OneS` for the same parameters. -/
abbrev OneS₂ (M : Gcm.X86_64.Stitch.CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat) (s₁ s₂ : State) :
    Prop :=
  OneS M Ctx W SP R A al D n T s₁ ∧ OneS M Ctx W SP R A al D n T s₂

omit L in
theorem OneS₂.env {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s₁ s₂ : State}
    (h : OneS₂ M Ctx W SP R A al D n T s₁ s₂) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
  env_agree h.1.env h.2.env

/-- The additional data, absorbed and padded. -/
theorem aadRest_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ M Ctx W SP R A al D n T)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)])
      (absorbPad v.callees 16)) (OneS₂ M Ctx W SP R A al D n T) := by
  have hL : ∀ s, OneS M Ctx W SP R A al D n T s → WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS M Ctx W SP R A al D n T s₁ ∧
      s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.aad h.alen (h.env.perm.wR (show 232 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 184 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS M Ctx W SP R A al D n T s ∧ s.gpr .r12 = A ∧
    s.gpr .rbp = BitVec.ofNat 64 al ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] A al s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dA, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorbPad v.callees 16) s (OneS M Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (absorbPad_ok v L (.inr rfl) (ai s h) rfl)) fun _ ⟨o, hrd, hwr⟩ => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact h.1.frame L o.env hrd hwr hDW (w_one ((absFrame_one fa).trans (tFrame_one ft)))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := A) (n := al) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `J₀` of the nonce, and the additional data. -/
theorem oneAad_rel {R : Nat} {Np A : Addr} {nl al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => (OneS M Ctx W SP R A al D n T s₁ ∧ s₁.gpr .r12 = Np ∧ s₁.gpr .rbp = BitVec.ofNat 64 nl ∧
        DataOk (W + BitVec.ofNat 64 16) W SP s₁ Np nl) ∧ (OneS M Ctx W SP R A al D n T s₂ ∧ s₂.gpr .r12 = Np ∧
        s₂.gpr .rbp = BitVec.ofNat 64 nl ∧ DataOk (W + BitVec.ofNat 64 16) W SP s₂ Np nl))
      (oneAad v.callees) (OneS₂ M Ctx W SP R A al D n T) := by
  have ji : ∀ s, (OneS M Ctx W SP R A al D n T s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) →
      J0In Ctx (W + BitVec.ofNat 64 16) W SP (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) Np nl s :=
    fun s h => ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩
  have hJ : ∀ s, (OneS M Ctx W SP R A al D n T s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) → WP isa (j0 v.callees) s (OneS M Ctx W SP R A al D n T) :=
    fun s h => WP.mono (WP.with_rdwr (j0_ok v L (ji s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (w_one (j0Frame_one o.frame))
  have a := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      j0_rel v L (H₁ := H₁) (H₂ := H₂) (Np := Np) (n := nl)).mono
      (fun _ _ h => ⟨_, _, ji _ h.1, ji _ h.2⟩) fun _ _ h => h) (fun _ _ h => h) hJ hJ
  exact RelCT.seq a ((aadRest_rel v L hDW).mono (fun _ _ h => h.2) fun _ _ h => h)

/-- The data encrypted or decrypted. -/
theorem oneCrypt_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ M Ctx W SP R A al D n T) (oneCrypt v.callees) (OneS₂ M Ctx W SP R A al D n T) := by
  have hL : ∀ s, OneS M Ctx W SP R A al D n T s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS M Ctx W SP R A al D n T s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let CI : State → Prop := fun s => OneS M Ctx W SP R A al D n T s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ci : ∀ s, CI s → CrIn Ctx (W + BitVec.ofNat 64 16) W SP R 0 0 D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD, h.1.rounds⟩
  have hC : ∀ s, CI s → WP isa (cryptAl v.callees) s (OneS M Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (cryptAl_ok v L (ci s h) rfl)) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (crFrame_one o.frame)
  have b := rel_wp ((cryptAl_rel v L (R := R) (icb₁ := 0) (icb₂ := 0) (P₁ := 0) (P₂ := 0) (D := D) (n := n) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ CI s₁ ∧ CI s₂) (fun _ _ h => ⟨ci _ h.2.1, ci _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hC hC
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- What `oneTag` needs of the state in each run: what `OneS` says but of
the data, which it only reads, the `n` bytes kept at `W + 200`, of `N` in
all. -/
structure OneT (Ctx W SP : Addr) (R al : Nat) (D : Addr) (n N : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  dD : DataOk (W + BitVec.ofNat 64 16) W SP s D n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N

omit L in
theorem OneS.oneT {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n N : Nat} {s : State}
    (h : OneS M Ctx W SP R A al D n (some N) s) : OneT Ctx W SP R al D n N s :=
  ⟨h.env, h.rounds, h.alen, h.dat, h.len, h.dD.ok, h.tlen N rfl⟩

theorem OneT.frame {R al : Nat} {D : Addr} {n N : Nat} {s s' : State} (h : OneT Ctx W SP R al D n N s)
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hf : Frame (oneFrame W D SP n) s.mem s'.mem) :
    OneT Ctx W SP R al D n N s' := by
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  exact ⟨he, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen, by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact h.dat,
    by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact h.len, h.dD.of_eq hrd hwr,
    by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact h.tlen⟩

omit L in
theorem OneT.keep {R al : Nat} {D : Addr} {n N : Nat} {s s' : State} (h : OneT Ctx W SP R al D n N s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OneT Ctx W SP R al D n N s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.rounds, by rw [hm]; exact h.alen, by rw [hm]; exact h.dat,
    by rw [hm]; exact h.len, h.dD.of_eq hrd hwr, by rw [hm]; exact h.tlen⟩

omit L in
/-- `load2_ok` in `OneT`. -/
theorem load2T_ok {R al : Nat} {D : Addr} {n N : Nat} {s : State}
    (h : OneT Ctx W SP R al D n N s) {o₁ o₂ : Nat} {P : Addr} {k : Nat}
    (h₁ : s.mem.readW (W + BitVec.ofNat 64 o₁) 64 = P) (h₂ : s.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 k)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₁) 8) (q₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₂) 8) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)]) s
      fun s₁ => OneT Ctx W SP R al D n N s₁ ∧ s₁.gpr .r12 = P ∧ s₁.gpr .rbp = BitVec.ofNat 64 k ∧
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

/-- The tag of the data (as ciphertext) into `W + o`, in two runs in `OneT`
for the same parameters: the data only read, wherever it is (in place, or
out of place at `src`). -/
theorem oneTag_relT {R al : Nat} {D : Addr} {n N : Nat} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => OneT Ctx W SP R al D n N s₁ ∧ OneT Ctx W SP R al D n N s₂) (oneTag v.callees o)
      fun _ _ => True := by
  have hL : ∀ s, OneT Ctx W SP R al D n N s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneT Ctx W SP R al D n N s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2T_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.env h.2.env) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneT Ctx W SP R al D n N s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorbPad v.callees 16) s (OneT Ctx W SP R al D n N) := fun s h =>
    WP.mono (WP.with_rdwr (absorbPad_ok v L (.inr rfl) (ai s h) rfl)) fun _ ⟨o, hrd, hwr⟩ => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact h.1.frame L o.env hrd hwr hDW (w_one ((absFrame_one fa).trans (tFrame_one ft)))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := D) (n := n) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  -- The lengths, for `tag`.
  have hT : ∀ s, OneT Ctx W SP R al D n N s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))]) s fun s₁ => OneT Ctx W SP R al D n N s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 N := fun s h => by
    have q₁ := h.env.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have q₂ := h.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
    have h15 := h.env.r15
    obtain ⟨s₁, run₁, hbx, hbp, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧
        s₁.gpr .rbp = BitVec.ofNat 64 N ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h.alen]
      · simp [gpr_setReg, h.tlen]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx, hbp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ (OneT Ctx W SP R al D n N s₁ ∧ OneT Ctx W SP R al D n N s₂)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.2.1.env h.2.2.env) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hT hT
  have t := (tag_rel v L (by decide) (TagCall.base v) (R := R) ho).mono (P' := fun (s₁ s₂ : State) => True ∧
      (OneT Ctx W SP R al D n N s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 N) ∧
      (OneT Ctx W SP R al D n N s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 al ∧ s₂.gpr .rbp = BitVec.ofNat 64 N))
    (fun _ _ h => ⟨⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩, h.2.1.1.rounds, h.2.2.1.rounds⟩) fun _ _ h => h
  exact RelCT.seq a (RelCT.seq b (RelCT.seq e t))

/-- The tag of the data (as ciphertext) into `W + o`, in two runs in `OneS`. -/
theorem oneTag_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {N : Nat} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ M Ctx W SP R A al D n (some N)) (oneTag v.callees o) fun _ _ => True :=
  (oneTag_relT v L (R := R) (al := al) (N := N) ho hDW).mono (fun _ _ h => ⟨h.1.oneT, h.2.oneT⟩) fun _ _ h => h

end

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM on x86-64: `oneBlocks` in two runs

Untrusted: everything here is checked by Lean. Both runs keep the same
length, branch the same way on it, and call `vg_aes_gcm_encrypt_blocks` or
`_decrypt_blocks` with the same arguments (`oneBlocks_rel`), so they leak
the same; after it, what stays in `W` is the data left and its length, and
the total length (`oneBlocks_oneS`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- The blocks of `oneBlocks`. -/
abbrev obB1 : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rax, .shift .shr .rax 4, .alu .test .rax (.reg .rax)]
abbrev obB2 : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
    ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++ ptr .rax .r15 bScrO
abbrev obB3 : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx,
    .alu .sub .rax (.reg .rcx), .alu .add .rax (.mem (at_ .r15 dataO)), .store (at_ .r15 dataO) .rax]

theorem oneBlocks_eq (f : Fn) : oneBlocks f = .seq (.block obB1) (.ite .e (.block [])
    (.seq (.block obB2) (.seq (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) (.block obB3)))) := rfl

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : Gcm.X86_64.Stitch.CtxMode}
include L

/-- The length kept, and the arguments of the call when there are whole blocks. -/
theorem ob12_ok {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) :
    WP isa (.block obB1) s fun s₁ => s₁.zf = some (decide (n / 16 = 0)) ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      (n / 16 ≠ 0 → WP isa (.block obB2) s₁ (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16))) := by
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, -, -, -, -, -, -, f192⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.mono (ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine ⟨z₁, he₁, fun hz => ?_⟩
  have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
  have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
  refine WP.mono (ob2_ok he₁ hR₁ hd₁) fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) rd₂ wr₂
  exact ⟨he₂, h.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁), by omega_using [], h.t_c, h.t_w, h.t_d, h.sp24, a1, a2, a3, a4,
    a5, by rw [a6, r₁], a7, h.rounds.2, h.t_w.sub_right (Lay.wSub (by decide)),
    h.ext.keep (rd₂.trans rd₁) (wr₂.trans wr₁) (by rw [m₂, m₁]; exact f192) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ext.cw.sub_right (Lay.wSub (by decide)))⟩

/-- `oneBlocks` of a function whose frame (`hf`, `hw`) leaks the same in two
runs with the same arguments. -/
theorem oneBlocks_rel (f : Fn) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat)
    (hf : RelCT isa (fun s₁ s₂ => ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₁ ∧ ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂)
      (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) fun _ _ => True)
    (hw : ∀ s, ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s
        fun s' => ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    RelCT isa (OneS₂ M Ctx W SP R A al D n T) (oneBlocks f) fun _ _ => True := by
  have pre : ∀ s, OneS M Ctx W SP R A al D n T s → ObPre M Ctx W SP R D n s := fun s h =>
    ⟨h.env, h.rounds, h.dat, h.len, h.dD, t_c, t_w, t_d, sp24, h.ext⟩
  let G₁ : State → Prop := fun s₁ => s₁.zf = some (decide (n / 16 = 0)) ∧
    Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ (n / 16 ≠ 0 → WP isa (.block obB2) s₁ (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16)))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (G₁ := G₁) (G₂ := G₁) (fun s h => ob12_ok L (pre s h)) (fun s h => ob12_ok L (pre s h))
  have t := rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some true) (c := .block [])
    [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block obB2) s (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16)) :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some false) (c := .block obB2)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨⟨h.1.2.1, h.2⟩, ⟨h.1.2.2, by rw [h.1.2.2.1, ← h.1.2.1.1, h.2]⟩⟩) hw₂ hw₂
  let G₃ : State → Prop := fun s => s.gpr .r13 = Ctx ∧ s.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s.gpr .r15 = W ∧
    s.gpr .rsp = SP
  have hw₃ : ∀ s, ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s G₃ := fun s h =>
    WP.mono (hw s h) fun _ hc => ⟨by rw [hc .r13 (by decide)]; exact h.env.r13,
      by rw [hc .r14 (by decide)]; exact h.env.r14, by rw [hc .r15 (by decide)]; exact h.env.r15,
      by rw [hc .rsp (by decide)]; exact h.env.rsp⟩
  have c := rel_wp (hf.mono (P' := fun s₁ s₂ => True ∧ ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₁ ∧
      ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂) (fun _ _ h => h.2) fun _ _ h => h) (fun _ _ h => h.2) hw₃ hw₃
  have d := rel_taint (P := fun s₁ s₂ => True ∧ G₃ s₁ ∧ G₃ s₂) (c := .block obB3) [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      obtain ⟨-, ⟨a₁, b₁, c₁, d₁⟩, ⟨a₂, b₂, c₂, d₂⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [d₁, d₂]) ⟨_, by taint_decide⟩
  rw [oneBlocks_eq]
  exact RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.1, h.2.2.1]) t (RelCT.seq b (RelCT.seq c d)))

omit L in
/-- The key context after `seal`'s or `open`'s pieces up to the tag, for the
data left. -/
theorem CtxExt.oneB {D : Addr} {n k : Nat} (hk : k ≤ n) {s s' : State}
    (h : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame (oneFrameB W D SP n) s.mem s'.mem) :
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 k) (n - k) s' :=
  (h.keep hrd hwr hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.cw.sub_right (Region.sub_prefix (by decide))
    · exact h.cw.sub_right (Lay.wSub (by decide))
    · exact h.cw.sub_right (Lay.wSub (by decide))
    · exact h.cd
    · exact h.ct.symm).sub (Offset.sub_base D (by omega_using [hk]))

omit L in
/-- The key context after `oneBlocks`, for the data left. -/
theorem CtxExt.obPost {D : Addr} {n : Nat} {s s' : State} (h : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s)
    (P : ObPost Ctx W SP D n s s') :
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) s' :=
  (h.keep P.rd P.wr P.frame fun r hr => by
    simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.cw.sub_right (Lay.wSub (by decide))
    · exact h.cs.sub_right (Lay.stSub (by decide))
    · exact h.cs.sub_right (Lay.stSub (by decide))
    · exact h.cd.sub_right (Region.sub_prefix (by omega_using []))
    · exact h.cw.sub_right (Lay.wSub (by decide))
    · exact h.ct.symm).sub (Offset.sub_base D (by omega_using []))

/-- What stays in `W` after `oneBlocks`. -/
theorem ObPost.oneS {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) {s s' : State} (h : OneS M Ctx W SP R A al D n T s)
    (P : ObPost Ctx W SP D n s s') :
    OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s' := by
  have fB := obFrame_B P.frame
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => fB.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L h.dD.ok.w t_w hd) (by decide)
  exact ⟨P.env, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad, by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    P.dat, by rw [P.len]; congr 1; omega_using [], h.dA.of_eq P.rd P.wr, (h.dD.of_eq P.rd P.wr).drop (by omega_using []),
    fun N hN => by cases hN; exact P.tlen, h.ext.obPost P⟩

/-- After `oneBlocks`, what stays in `W`: the data left, its length and the
total length. -/
theorem oneBlocks_oneS (f : Fn) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat)
    (hw : ∀ s, ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s fun s' =>
        (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame (obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s'.mem)
    {s : State} (h : OneS M Ctx W SP R A al D n T s) :
    WP isa (oneBlocks f) s (OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  exact WP.mono (oneBlocks_core L f (Out := fun _ _ => True) ⟨h.env, h.rounds, h.dat, h.len, h.dD, t_c, t_w, t_d, sp24, h.ext⟩
    (fun s₂ hi => WP.mono (hw s₂ hi) fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d, trivial⟩) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)) fun s' ⟨P, _⟩ => ObPost.oneS L t_w h P

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem obFrameE_rel {R : Nat} {D : Addr} {n q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn M Ctx St W SP R D n q s₁ ∧ ObIn M Ctx St W SP R D n q s₂)
      (.frame (.push [.rax]) (.call B.enc.name B.enc.code) (.pop .rax 1)) fun _ _ => True :=
  RelCT.frame (fun _ _ h => by rw [h.1.env.rsp, h.2.env.rsp]) (blkE_rel B fun _ _ ⟨s₁, s₂, hp, ha, hb⟩ =>
    ⟨_, _, _, _, _, _, _, ha ▸ ObIn.call L hp.1, hb ▸ ObIn.call L hp.2,
      by rw [ha, hb, pushed_rsp, pushed_rsp, hp.1.env.rsp, hp.2.env.rsp]⟩)

theorem obFrameD_rel {R : Nat} {D : Addr} {n q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn M Ctx St W SP R D n q s₁ ∧ ObIn M Ctx St W SP R D n q s₂)
      (.frame (.push [.rax]) (.call B.dec.name B.dec.code) (.pop .rax 1)) fun _ _ => True :=
  RelCT.frame (fun _ _ h => by rw [h.1.env.rsp, h.2.env.rsp]) (blkD_rel B fun _ _ ⟨s₁, s₂, hp, ha, hb⟩ =>
    ⟨_, _, _, _, _, _, _, ha ▸ ObIn.call L hp.1, hb ▸ ObIn.call L hp.2,
      by rw [ha, hb, pushed_rsp, pushed_rsp, hp.1.env.rsp, hp.2.env.rsp]⟩)

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneBlocks` encrypting, in two runs: after it, what stays in `W`. -/
theorem oneBlocksE_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat) :
    RelCT isa (OneS₂ M Ctx W SP R A al D n T) (oneBlocks B.enc)
      (OneS₂ M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  have hw := fun s => oneBlocks_oneS L B.enc (R := R) (A := A) (al := al) (T := T) t_c t_w t_d sp24
    (fun s h => WP.mono (obFrameE_ok L B h) fun _ o => ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1⟩) (s := s)
  exact (rel_wp (oneBlocks_rel L B.enc t_c t_w t_d sp24 (obFrameE_rel B L)
    (fun s h => WP.mono (obFrameE_ok L B h) fun _ o => o.1)) (fun _ _ h => h) hw hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- `oneBlocks` decrypting, in two runs: after it, what stays in `W`. -/
theorem oneBlocksD_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat) :
    RelCT isa (OneS₂ M Ctx W SP R A al D n T) (oneBlocks B.dec)
      (OneS₂ M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  have hw := fun s => oneBlocks_oneS L B.dec (R := R) (A := A) (al := al) (T := T) t_c t_w t_d sp24
    (fun s h => WP.mono (obFrameD_ok L B h) fun _ o => ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1⟩) (s := s)
  exact (rel_wp (oneBlocks_rel L B.dec t_c t_w t_d sp24 (obFrameD_rel B L)
    (fun s h => WP.mono (obFrameD_ok L B h) fun _ o => o.1)) (fun _ _ h => h) hw hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

end

end VG.Proof.AesGcm.X86_64
