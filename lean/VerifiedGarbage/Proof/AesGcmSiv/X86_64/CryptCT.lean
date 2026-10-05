import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-GCM-SIV on x86-64: relating two runs, the tag and counter mode

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree and those slots, public (`sivT`, `both_agree`);
what correctness says about each run is added with `RelCT.wp`.
-/

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[200, 248)` public. -/
def sivT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 3816], bases := [(.r15, 1, 0)],
    slots := [(1, 200, 48)] }

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D al n s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 3816⟩]

/-- Two runs with the same public arguments, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  o₁ : One K W SP R N A D al n s₁
  o₂ : One K W SP R N A D al n s₂
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} {v : BitVec 64} (h₁ : m₁.readW a 64 = v) (h₂ : m₂.readW a 64 = v)
    {j : Nat} (hj : j < 8) : m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  have e : bytesAt m₁ a 8 = bytesAt m₂ a 8 := by rw [← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, h₁, h₂]
  have := congrArg (fun l => l.getD j 0) e
  simpa only [Proof.Cmac.getD_bytesAt _ _ hj] using this

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D al n rs s₁ s₂) : X86_64.Taint.Agree (sivT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 3816⟩] → X86_64.Taint.Wf (sivT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 3816 ≤ 2 ^ 64; decide
    · simp only [sivT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.o₁.wr, h.o₂.wr], wf h.o₁.env h.o₁.wr,
    wf h.o₂.env h.o₂.wr, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.o₁.env.r13, h.o₂.env.r13]
      · rw [h.o₁.env.r15, h.o₂.env.r15]
      · rw [h.o₁.env.rsp, h.o₂.env.rsp]
  · simp only [sivT, List.mem_singleton] at hsl; subst hsl; simp [sivT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 3816⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
      fun s hw => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [add_ofNat_assoc, ← e]
    simp only [sivT, List.mem_singleton] at hsl; subst hsl
    rw [hb s₁ h.o₁.wr, hb s₂ h.o₂.wr]
    simp only at hk₁ hk₂
    have S₁ := h.o₁.sl
    have S₂ := h.o₂.sl
    have key : ∀ d, d ∈ [200, 208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
        s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
      rw [hw d (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact word_byte S₁.rounds S₂.rounds (by omega)
      · exact word_byte S₁.nonce S₂.nonce (by omega)
      · exact word_byte S₁.aad S₂.aad (by omega)
      · exact word_byte S₁.alen S₂.alen (by omega)
      · exact word_byte S₁.data S₂.data (by omega)
      · exact word_byte S₁.len S₂.len (by omega)
    have hq : (k - 200) / 8 = 0 ∨ (k - 200) / 8 = 1 ∨ (k - 200) / 8 = 2 ∨ (k - 200) / 8 = 3 ∨
        (k - 200) / 8 = 4 ∨ (k - 200) / 8 = 5 := by omega
    exact key (200 + 8 * ((k - 200) / 8)) (by
      rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)

/-- Code the taint analysis checks from `sivT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, (taint.check (sivT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (sivT rs) (fun s₁ s₂ h => both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `sivT rs`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, ((taint.check (sivT rs) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (both_agree hDW hn (hP _ _ hp)) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

theorem eval_e_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .e s₁ = isa.eval .e s₂ := h
theorem eval_ne_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .ne s₁ = isa.eval .ne s₂ := by
  show s₁.zf.map _ = s₂.zf.map _; rw [h]
theorem eval_b_eq {s₁ s₂ : State} (h : s₁.cf = s₂.cf) : isa.eval .b s₁ = isa.eval .b s₂ := h

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.AesGcmSiv.X86_64

/-!
## The tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The code around each call of
`vg_aes_ctr32` passes the taint analysis from the public slots and the
registers both runs agree on (`rel_taintC`); each call has the same
arguments in both runs, by correctness.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall ctr_rel ctr_call)

/-! ## The tag -/

theorem tagCall_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (O : One K W SP R N A D al n t) {o : Nat} (ho : o = 0 ∨ o = 128) :
    WP isa (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 o)) t fun t₁ =>
      CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 1768) R 1 ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := tagArgs_ok L O.env O.sl ho
  have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have dO : (⟨W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  exact WP.of_runBlock ⟨t₁, run₁, cargs L E₁ hR (keyS L E₁.perm) (c := 112) (by decide)
    (srcW L E₁.perm (t := o) (k := 16 * 1) (by omega)) dO (L.w_w (.inr (by omega)) (by decide) (by omega))
    (E₁.perm.wC (by omega)) rdi rsi rdx rcx r8 r9, E₁.rsp⟩

theorem tagArgs_check {o : Nat} (ho : o = 0 ∨ o = 128) :
    ∃ hc, (taint.check (sivT []) (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++
      ptr .rcx .r15 o)) hc).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {o : Nat}
    (ho : o = 0 ∨ o = 128) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Both K W SP R N A D al n [] t₁ t₂) :
    RelCT isa P (tag v.callees o) fun _ _ => True := by
  have a := (rel_taintC [] hDW hn hP (tagArgs_check ho)).wp
    (F₁ := fun (t₁ : State) => CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 1768) R 1 ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 1768) R 1 ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨tagCall_wp L hR (hP _ _ h).o₁ ho, tagCall_wp L hR (hP _ _ h).o₂ ho⟩
  exact RelCT.seq a (ctr_rel v.ctr fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

/-! ## Counter mode's whole blocks -/

/-- The end of a block: the counter incremented, the pointer and the count. -/
theorem blkEnd_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {D : Addr} {b j : Nat} (hj : j < b)
    (hb : b < 2 ^ 60) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)) (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) :
    ∃ t' : State, runBlock isa [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
        .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] t = some t' ∧
      Frame [⟨W + BitVec.ofNat 64 96, 4⟩] t.mem t'.mem ∧ t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 1)) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (b - (j + 1)) ∧ t'.zf = some (decide (b - (j + 1) = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have c₀ := E.perm.wR (show 96 + 4 ≤ 3816 by decide)
  have c₁ := E.perm.wW (show 96 + 4 ≤ 3816 by decide)
  refine ⟨_, by srun [h15, c₀, c₁, h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_arithFlags, gpr_setReg, mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg,
    wr_arithFlags, wr_setReg, zf_arithFlags, zf_setReg, ite_true, ite_false, reduceCtorEq]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [add_ofNat_assoc, show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [Proof.AesGcm.X86_64.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

/-- A run of counter mode before block `j`. -/
structure CInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n b : Nat) (j : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t D n
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (n % 16)

theorem CInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n b : Nat} {j : Nat} {t₁ t₂ : State}
    (h₁ : CInv K W SP R N A D al n b j t₁) (h₂ : CInv K W SP R N A D al n b j t₂) :
    Both K W SP R N A D al n [.r12, .rbx, .rbp] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r12, h₂.r12]
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]⟩

/-- A block, after its arguments: the call's, and the run's. -/
def BlkArgs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n b : Nat) (j : Nat) (t : State) : Prop :=
  CtrCall t (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (D + BitVec.ofNat 64 (16 * j))
    (W + BitVec.ofNat 64 1768) R 1 ∧ t.gpr .rsp = SP ∧ CInv K W SP R N A D al n b j t

theorem blkArgs_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n b : Nat}
    (hb : 16 * b ≤ n) {j : Nat} (hj : j < b) {t : State} (I : CInv K W SP R N A D al n b j t) :
    WP isa (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr))) t
      (BlkArgs K W SP R N A D al n b j) := by
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := blkArgs_ok L I.one.env I.one.sl I.r12
  have E₁ : Env K W SP t₁ := I.one.env.of_saved hg₁ hrd₁ hwr₁
  have hn := I.buf.lt
  have hD₁ := I.buf.of_eq hrd₁ hwr₁
  have hQ : Buf K W SP t₁ (D + BitVec.ofNat 64 (16 * j)) (16 * 1) := hD₁.slice (by omega)
  have hDw : Covers [⟨D, n⟩] t₁.wr := by rw [hwr₁, I.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)
  refine WP.of_runBlock ⟨t₁, run₁, cargs L E₁ hR (keyS L E₁.perm) (c := 112) (by decide) (srcBuf hQ)
    (hQ.w.sub_right (Lay.wSub (by decide))) (hQ.w.sub_right (Lay.wSub (show 248 + 240 ≤ 3816 by decide))).symm
    (Proof.AesGcm.X86_64.covers_off hDw (by omega) hn) rdi rsi rdx rcx r8 r9, E₁.rsp,
    ⟨⟨E₁, by rw [hm₁]; exact I.one.sl.of_frame (Proof.Cmac.frame_store2 _ _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      hwr₁.trans I.one.wr⟩, hD₁, by rw [hg₁ _ (by decide), I.r12], by rw [hg₁ _ (by decide), I.rbx],
      by rw [hg₁ _ (by decide), I.rbp]⟩⟩

theorem blkCalled_wp (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n b : Nat}
    (hb : 16 * b ≤ n) {j : Nat} (hj : j < b) {t : State} (h : BlkArgs K W SP R N A D al n b j t) :
    WP isa (.call v.ctr.callee.name v.ctr.callee.code) t (CInv K W SP R N A D al n b j) := by
  obtain ⟨cc, hsp, I⟩ := h
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨I.one.env.of_saved P.saved P.rd P.wr, I.one.sl.of_frame fc (fun q hq => ?_), P.wr.trans I.one.wr⟩,
    I.buf.of_eq P.rd P.wr, by rw [P.saved _ (by decide), I.r12], by rw [P.saved _ (by decide), I.rbx],
    by rw [P.saved _ (by decide), I.rbp]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact ((I.buf.w.sub_left (Offset.sub_base D (show 16 * j + 16 * 1 ≤ n by omega))).sub_right
      (Lay.wSub (by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem blkEnd_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n b : Nat} (hb : 16 * b ≤ n)
    {j : Nat} (hj : j < b) {t : State} (I : CInv K W SP R N A D al n b j t) :
    WP isa (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
        .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]) t fun t' =>
      CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)) := by
  have hn := I.buf.lt
  obtain ⟨t', run', f', r12', rbx', zf', hg', hrd', hwr'⟩ := blkEnd_ok I.one.env hj (by omega) I.r12 I.rbx
  exact WP.of_runBlock ⟨t', run', ⟨⟨I.one.env.keep (fun r hr => hg' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd' hwr',
    I.one.sl.of_frame f' (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    hwr'.trans I.one.wr⟩, I.buf.of_eq hrd' hwr', r12', rbx', by rw [hg' _ (by simp), I.rbp]⟩, zf'⟩

theorem blkArgs_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkEnd_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
      .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A block of counter mode, in two runs before the same block. -/
theorem blk_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) {j : Nat}
    (hj : j < b) :
    RelCT isa (fun t₁ t₂ => CInv K W SP R N A D al n b j t₁ ∧ CInv K W SP R N A D al n b j t₂) (cryptBlock v.callees)
      fun t₁ t₂ => (CInv K W SP R N A D al n b (j + 1) t₁ ∧ t₁.zf = some (decide (b - (j + 1) = 0))) ∧
        (CInv K W SP R N A D al n b (j + 1) t₂ ∧ t₂.zf = some (decide (b - (j + 1) = 0))) := by
  have r₁ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) blkArgs_check).wp
    (F₁ := BlkArgs K W SP R N A D al n b j) (F₂ := BlkArgs K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨blkArgs_wp L hR hb hj h.1, blkArgs_wp L hR hb hj h.2⟩
  have r₂ := (ctr_rel v.ctr (P := fun t₁ t₂ => True ∧ BlkArgs K W SP R N A D al n b j t₁ ∧
      BlkArgs K W SP R N A D al n b j t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := CInv K W SP R N A D al n b j) (F₂ := CInv K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨blkCalled_wp v L hb hj h.2.1, blkCalled_wp v L hb hj h.2.2⟩
  have r₃ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => True ∧ CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) blkEnd_check).wp
    (F₁ := fun (t' : State) => CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)))
    (F₂ := fun (t' : State) => CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)))
    fun t₁ t₂ h => ⟨blkEnd_wp L hb hj h.2.1, blkEnd_wp L hb hj h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- The whole blocks of counter mode, in two runs. -/
theorem blks_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) (hb1 : 1 ≤ b) :
    RelCT isa (fun t₁ t₂ => CInv K W SP R N A D al n b 0 t₁ ∧ CInv K W SP R N A D al n b 0 t₂)
      (.loop (cryptBlock v.callees) .ne)
      fun t₁ t₂ => CInv K W SP R N A D al n b b t₁ ∧ CInv K W SP R N A D al n b b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ j, m = b - j ∧ j < b ∧ CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) (fun m => ?_) (b - 0)).mono (fun t₁ t₂ h => ⟨0, rfl, hb1, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hj : j < b
  · by_cases hm : m = b - j
    · subst hm
      refine (blk_rel v L hR hDW hn hb hj).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : j + 1 = b := by simp at hc; omega
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : b - (j + 1) ≠ 0 := by simpa using hc
        exact ⟨b - (j + 1), by omega, j + 1, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hj h.2.1

/-! ## The last bytes, and the whole of counter mode -/

theorem tail2_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 bO ++ ([.mov .rcx (.reg .rbp)] : List Instr)))
      xorLoop) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The tag's code leaves a run with the public arguments, and the registers. -/
theorem tag_cinv (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b j : Nat} {t : State} (I : CInv K W SP R N A D al n b j t) :
    WP isa (tag v.callees 128) t (CInv K W SP R N A D al n b j) :=
  WP.mono (tag_ok v L hR I.one.env I.one.sl (o := 128) (by decide)) fun t' T =>
    ⟨⟨T.env, I.one.sl.of_frame T.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm), T.wr.trans I.one.wr⟩,
      I.buf.of_eq T.rd T.wr, by rw [T.saved _ (by decide), I.r12], by rw [T.saved _ (by decide), I.rbx],
      by rw [T.saved _ (by decide), I.rbp]⟩

/-- The last bytes, in two runs. -/
theorem tail_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b j : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) :
    RelCT isa (fun t₁ t₂ => CInv K W SP R N A D al n b j t₁ ∧ CInv K W SP R N A D al n b j t₂) (cryptTail v.callees)
      fun _ _ => True := by
  refine RelCT.assoc ?_
  show RelCT isa _ (.seq (tag v.callees 128) _) _
  have r₁ := (tag_rel v L hR hDW hn (o := 128) (by decide)
    (P := fun t₁ t₂ => CInv K W SP R N A D al n b j t₁ ∧ CInv K W SP R N A D al n b j t₂)
    fun t₁ t₂ h => ⟨h.1.one, h.2.one, fun _ h => nomatch h⟩).wp
    (F₁ := CInv K W SP R N A D al n b j) (F₂ := CInv K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨tag_cinv v L hR h.1, tag_cinv v L hR h.2⟩
  exact RelCT.seq r₁ (rel_taintC [.r12, .rbx, .rbp] hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) tail2_check)

/-- The start of `crypt`, in a run. -/
theorem head_cinv {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (O : One K W SP R N A D al n t) (hD : Buf K W SP t D n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
        .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) t fun t₁ =>
      CInv K W SP R N A D al n (n / 16) 0 t₁ ∧ t₁.zf = some (decide (n / 16 = 0)) := by
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hbx₁, hzf₁, hg₁, hrd₁, hwr₁⟩ := cryptHead_ok L O.env O.sl hD
  refine WP.of_runBlock ⟨t₁, run₁, ⟨⟨O.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁,
    by rw [hm₁]; exact O.sl.of_frame (Proof.Cmac.frame_store2 _ _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    hwr₁.trans O.wr⟩, hD.of_eq hrd₁ hwr₁, by rw [h12₁, Nat.mul_zero, BitVec.add_zero], by rw [hbx₁, Nat.sub_zero],
    hbp₁⟩, hzf₁⟩

theorem head_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
        .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp]) (.block [.alu .test .rbp (.reg .rbp)]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem test_cinv {K W SP : Addr} {R : Nat} {N A D : Addr} {al n b j : Nat} {t : State}
    (I : CInv K W SP R N A D al n b j t) :
    WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
      CInv K W SP R N A D al n b j t' ∧ t'.zf = some (decide (n % 16 = 0)) := by
  have hn := I.buf.lt
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · exact ⟨⟨I.one.env.keep (fun _ _ => by simp only [gpr_arithFlags]) rfl rfl, I.one.sl, I.one.wr⟩, I.buf.of_eq rfl rfl,
      by simp only [gpr_arithFlags, I.r12], by simp only [gpr_arithFlags, I.rbx], by simp only [gpr_arithFlags, I.rbp]⟩
  · simp only [zf_arithFlags, I.rbp]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (One K W SP R N A D al n t₁ ∧ Buf K W SP t₁ D n) ∧
      (One K W SP R N A D al n t₂ ∧ Buf K W SP t₂ D n)) :
    RelCT isa P (crypt v.callees) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.1, (hP _ _ h).2.1, fun _ h => nomatch h⟩)
    head_check).wp
    (F₁ := fun (t₁ : State) => CInv K W SP R N A D al n (n / 16) 0 t₁ ∧ t₁.zf = some (decide (n / 16 = 0)))
    (F₂ := fun (t₁ : State) => CInv K W SP R N A D al n (n / 16) 0 t₁ ∧ t₁.zf = some (decide (n / 16 = 0)))
    fun t₁ t₂ h => ⟨head_cinv L (hP _ _ h).1.1 (hP _ _ h).1.2, head_cinv L (hP _ _ h).2.1 (hP _ _ h).2.2⟩
  have r₂ : RelCT isa (fun t₁ t₂ => True ∧ (CInv K W SP R N A D al n (n / 16) 0 t₁ ∧
        t₁.zf = some (decide (n / 16 = 0))) ∧ (CInv K W SP R N A D al n (n / 16) 0 t₂ ∧
        t₂.zf = some (decide (n / 16 = 0))))
      (.ite .e (.block []) (.loop (cryptBlock v.callees) .ne))
      fun t₁ t₂ => CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧ CInv K W SP R N A D al n (n / 16) (n / 16) t₂ := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) ?_ ?_
    · refine RelCT.block_nil fun t₁ t₂ h => ?_
      have h0 : n / 16 = 0 := by have := h.2; rw [eval_e h.1.2.1.2] at this; simpa using this
      have a := h.1.2.1.1
      have b := h.1.2.2.1
      rw [h0] at a b ⊢
      exact ⟨a, b⟩
    · by_cases h0 : n / 16 = 0
      · refine RelCT.of_false fun t₁ t₂ h => ?_
        have := h.2
        rw [eval_e h.1.2.1.2] at this
        simp [h0] at this
      · exact (blks_rel v L hR hDW hn (b := n / 16) (by omega) (by omega)).mono
          (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
  have r₃ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧
      CInv K W SP R N A D al n (n / 16) (n / 16) t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) test_check).wp
    (F₁ := fun (t : State) => CInv K W SP R N A D al n (n / 16) (n / 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    (F₂ := fun (t : State) => CInv K W SP R N A D al n (n / 16) (n / 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    fun t₁ t₂ h => ⟨test_cinv h.1, test_cinv h.2⟩
  have r₄ : RelCT isa (fun t₁ t₂ => True ∧ (CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧
        t₁.zf = some (decide (n % 16 = 0))) ∧ (CInv K W SP R N A D al n (n / 16) (n / 16) t₂ ∧
        t₂.zf = some (decide (n % 16 = 0))))
      (.ite .e (.block []) (cryptTail v.callees)) fun _ _ => True :=
    RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial)
      ((tail_rel v L hR hDW hn).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ _ => trivial)
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

end VG.Proof.AesGcmSiv.X86_64
