import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
import VerifiedGarbage.Proof.AesOcb.X86_64.Whole

/-!
# AES-OCB on x86-64: the whole blocks are constant time

Untrusted: everything here is checked by Lean. Each pass passes the taint
analysis from the public slots and the number of blocks in `r13`
(`rel_taintC`); the call of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` between them has the same arguments in both runs
(`callBlocks_rel`). A pass keeps the public arguments, whatever the offsets
and the checksum (`pass_one`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- The checksums of a pass, from `c₀`. -/
def ckRec (c₀ : Block) (f : Nat → Block → Block) : Nat → Block
  | 0 => c₀
  | i + 1 => f i (ckRec c₀ f i)

/-- A pass keeps the public arguments, the table and the registers it does
not use. -/
theorem pass_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hmn : 16 * m ≤ n) {body : List Instr}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} (hB : BodyOk body fB fC)
    {t : State} (o : One K W SP R N A D nl n tl t) (hD : DBuf K W SP t D (16 * m)) (hm0 : 0 < m)
    {l : Block} (hT : ∃ M, Tbl W l M t.mem ∧ m ≤ M)
    (hbx : t.gpr .rbx = D) (hbp : t.gpr .rbp = BitVec.ofNat 64 1) (h12 : t.gpr .r12 = BitVec.ofNat 64 m) :
    WP isa (pass body) t fun t' => One K W SP R N A D nl n tl t' ∧ (∃ M, Tbl W l M t'.mem ∧ m ≤ M) ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → t'.gpr r = t.gpr r := by
  let O0 := blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  let X := fun k => blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k))
  let ckF := ckRec (blockAtMem t.mem (W + BitVec.ofNat 64 ckO)) fun i c => fC c (X i) (offAt O0 l (i + 1))
  refine WP.mono (pass_ok hB (ckF := ckF) (O0 := O0) (fun i _ => rfl) ⟨L, hD, hT⟩ o.env hm0 hbx hbp h12 rfl rfl)
    fun t' P => ⟨?_, ?_, P.gpr⟩
  · refine o.step L hDW P.env P.wr (P.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, by simp, Region.sub_prefix hmn⟩
  · obtain ⟨M, T, hM⟩ := hT
    exact ⟨M, T.frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.wT_w (by decide)
      · exact L.wT_w (by decide)
      · exact hD.w.symm.sub_left (Lay.wSub (by decide)), hM⟩

/-- What the whole blocks need of a run, and what their first pass keeps:
the public arguments, the number of blocks in `r13`, the table and the
data. -/
def WRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl m : Nat) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m ∧
    (∃ l M, Tbl W l M s.mem ∧ m ≤ M) ∧ DBuf K W SP s D n

/-- The first pass. -/
theorem wholeA_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    {body : List Instr} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
    (hB : BodyOk body fB fC) {s : State} (h : WRun K W SP R N A D nl n tl m s) :
    WP isa (.seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass body)) s
      (WRun K W SP R N A D nl n tl m) := by
  obtain ⟨o, h13, ⟨l, M, T, hM⟩, hD⟩ := h
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := o.env.perm.wR (by decide)
  have hdata := o.sl.data
  obtain ⟨s₁, run₁, rbx₁, r12₁, rbp₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] s = some s₁ ∧
      s₁.gpr .rbx = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 m ∧ s₁.gpr .rbp = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by orun [o.env.r15, r₁, hdata], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13]
    · simp only [gpr_setReg, ite_true, sext1]
    · simp only [gpr_setReg, h1, h2, h3, ite_false]
    all_goals rfl
  have E₁ : Env K W SP s₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  have o₁ : One K W SP R N A D nl n tl s₁ := ⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩
  have hD₁ : DBuf K W SP s₁ D n := hD.of_eq rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (pass_one L hDW hmn hB o₁ (hD₁.take' hmn) hm0 (l := l) ⟨M, by rw [m₁]; exact T, hM⟩ rbx₁ rbp₁ r12₁)
    fun t ⟨o', hT', g'⟩ => ⟨o', ?_, ⟨l, hT'⟩, hD₁.of_one o'⟩
  rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₁ _ (by decide) (by decide) (by decide), h13]

/-- Both runs with the number of blocks in `r13`. -/
theorem both_r13 {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl m : Nat} {s₁ s₂ : State}
    (o₁ : One K W SP R N A D nl n tl s₁) (o₂ : One K W SP R N A D nl n tl s₂)
    (h₁ : s₁.gpr .r13 = BitVec.ofNat 64 m) (h₂ : s₂.gpr .r13 = BitVec.ofNat 64 m) :
    Both K W SP R N A D nl n tl [.r13] [] s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂], fun _ h => (nomatch h)⟩

/-- `whole f pre post` in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    {pre post : List Instr} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
    (hB : BodyOk pre fB fC)
    (hc₁ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass pre)) hc).isSome = true)
    (hc₂ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block (copy16 o0O ofsO ++ [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])) (pass post)) hc).isSome
        = true)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → WRun K W SP R N A D nl n tl m s₁ ∧ WRun K W SP R N A D nl n tl m s₂) :
    RelCT isa P (whole b pre post) fun _ _ => True := by
  unfold whole
  have a := (rel_taintC [.r13] [] hDW hn (fun s₁ s₂ h => both_r13 (hP s₁ s₂ h).1.1 (hP s₁ s₂ h).2.1
    (hP s₁ s₂ h).1.2.1 (hP s₁ s₂ h).2.2.1) hc₁).wp
    (F₁ := WRun K W SP R N A D nl n tl m) (F₂ := WRun K W SP R N A D nl n tl m)
    fun s₁ s₂ h => ⟨wholeA_one L hDW hmn hm0 hB (hP s₁ s₂ h).1, wholeA_one L hDW hmn hm0 hB (hP s₁ s₂ h).2⟩
  have args : ∀ {s : State}, WRun K W SP R N A D nl n tl m s → ArgsOk [ld .rdx .r15 dataO, mvr .rcx .r13] s D m :=
    fun h => dataArgs_ok h.1.env.r15 h.1.sl.data h.2.1 (h.1.env.perm.wR (by decide))
  have call : ∀ s, WRun K W SP R N A D nl n tl m s →
      WP isa (callBlocks b [ld .rdx .r15 dataO, mvr .rcx .r13]) s fun s' =>
        One K W SP R N A D nl n tl s' ∧ s'.gpr .r13 = BitVec.ofNat 64 m := fun s h =>
    WP.mono (callBlocks_ok ok nosp depth L h.1.env hR h.1.sl.rounds (args h) (dstD (h.2.2.2.take' hmn)))
      fun s' Q => by
      refine ⟨h.1.step L hDW (h.1.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_),
        by rw [Q.saved _ (by decide), h.2.1]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, Region.sub_prefix hmn⟩
      · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
      · rw [h.1.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have bb := (callBlocks_rel ok ct L hR hDW hn [.r13] [] (args := [ld .rdx .r15 dataO, mvr .rcx .r13])
    ⟨_, by taint_decide⟩ (D' := D) (k := m)
    (P := fun s₁ s₂ => True ∧ WRun K W SP R N A D nl n tl m s₁ ∧ WRun K W SP R N A D nl n tl m s₂) fun s₁ s₂ h =>
      ⟨both_r13 h.2.1.1 h.2.2.1 h.2.1.2.1 h.2.2.2.1, args h.2.1, args h.2.2, dstD (h.2.1.2.2.2.take' hmn),
        dstD (h.2.2.2.2.2.take' hmn)⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m)
    fun s₁ s₂ h => ⟨call s₁ h.2.1, call s₂ h.2.2⟩
  have c := rel_taintC [.r13] [] hDW hn (fun s₁ s₂ (h : True ∧ (One K W SP R N A D nl n tl s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 m) ∧ (One K W SP R N A D nl n tl s₂ ∧ s₂.gpr .r13 = BitVec.ofNat 64 m)) =>
    both_r13 h.2.1.1 h.2.2.1 h.2.1.2 h.2.2.2) hc₂
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq a (RelCT.seq bb c))

end VG.Proof.AesOcb.X86_64
