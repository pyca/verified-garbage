import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinishCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. The only branch is on the
tag length (`tagLenOk`, checked by the taint analysis); the received tag is
read from the same address (`r9`), the tag is computed from the same lengths
and number of rounds (`finTag_rel`), and the comparison has no branch.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- The lengths and rounds kept, and the tag length at `W + 224`. -/
def VerS (Ctx St W SP : Addr) (R : Nat) (aL tL tl : BitVec 64) (s : State) : Prop :=
  FinS Ctx St W SP R aL tL s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- What `verify` has before checking a received tag of length `t` at `Tp`. -/
def VerT (R : Nat) (aL tL : BitVec 64) (t : Nat) (Tp : Addr) (s : State) : Prop :=
  VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧ s.gpr .rsi = Tp ∧
    Covers [⟨Tp, t⟩] (s.rd ++ s.wr)

omit L in
theorem VerT.keep {R : Nat} {aL tL : BitVec 64} {t : Nat} {Tp : Addr} {s s' : State}
    (h : VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s) (k : Keeps s s') :
    VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s' :=
  ⟨⟨h.1.1.keep (fun r hr => k.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) k.mem k.rd k.wr, by rw [k.mem]; exact h.1.2⟩,
    by rw [k.gpr _ (by decide), h.2.1], by rw [k.gpr _ (by decide), h.2.2.1], by rw [k.rd, k.wr]; exact h.2.2.2⟩

/-- The tag computed and compared, for an allowed length `t`. -/
theorem verifyCheck_rel {R t : Nat} (h1 : 1 ≤ t) (h16 : t ≤ 16) {aL tL : BitVec 64} {Tp : Addr}
    (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₁ ∧
        VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₂)
      (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0))))
      fun _ _ => True := by
  -- `recv` keeps the lengths.
  have hR : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s →
      WP isa recv s (VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t)) := fun s ⟨⟨h, ht⟩, hbx, hsi, hTr⟩ =>
    WP.mono (recv_ok h.1 hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide)))) fun s' ⟨he', _, f, _⟩ => by
      have d : ∀ d, 176 ≤ d → d + 8 ≤ 256 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide)
      exact ⟨⟨he', rounds_frame f (d 176 (by decide) (by decide)) h.2.1,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 184 (by decide) (by decide)) (by decide), h.2.2.1],
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 192 (by decide) (by decide)) (by decide), h.2.2.2]⟩,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 224 (by decide) (by decide)) (by decide), ht]⟩
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₁ ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R aL tL t Tp s₂) ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
      (fun _ _ h => EnvAgree.regs ⟨h.1.1.1.1, h.2.1.1.1, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hR hR
  -- `finTag` keeps the tag length.
  have hT : ∀ s, VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s → WP isa (finTag v.callees 0) s fun s' =>
      Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := fun s ⟨h, ht⟩ =>
    WP.mono (finTag_ok v L (.inl rfl) h.1 h.2.1 h.2.2.1 h.2.2.2
      (x := List.replicate ((if tL = 0 then aL.toNat else tL.toNat) % 16) 0) (by simp)) fun _ ⟨he', _, f, _⟩ =>
      ⟨he', by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.st_w (a := 0) (n := 32) (d := 224) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · simpa using L.w_w (a := 224) (n := 8) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w (by decide)).symm) (by decide), ht]⟩
  have b := rel_wp ((finTag_rel v L (R := R) (aL := aL) (tL := tL) (.inl rfl)).mono
      (P' := fun s₁ s₂ => True ∧ VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₁ ∧
        VerS Ctx St W SP R aL tL (BitVec.ofNat 64 t) s₂) (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hT hT
  -- The tag length, and the comparison.
  have hL : ∀ s, (Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) →
      WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO))]) s fun s' => Env Ctx St W SP s' ∧
        s'.gpr .rbx = BitVec.ofNat 64 t := fun s ⟨he, ht⟩ => by
    have r₁ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
    obtain ⟨s₁, run₁, hbx, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s = some s₁ ∧
        s₁.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [he.r15, r₁], ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, ht]
      · intro r a; simp [gpr_setReg, a]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => ?_) hrd hwr, hbx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ (Env Ctx St W SP s₁ ∧
      s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧ (Env Ctx St W SP s₂ ∧
      s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.2.1.1 h.2.2.1) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hL hL
  have d := rel_taint (P := fun s₁ s₂ => True ∧ (Env Ctx St W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
      (Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t)) (c := cmp 0) ([.rbx] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c d))

end

theorem streamVerify_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamVerifyX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamVerifyX86_64.pre s₀') (hq : Proof.AesGcm.streamVerifyX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamVerify v.callees) fun _ _ => True := by
  obtain ⟨L, hperm, ha, hta, dA, hTr, dTW, -, -, -, hR⟩ := ver_lay hp
  obtain ⟨L', hperm', ha', hta', dA', hTr', -, -, -, -, hR'⟩ := ver_lay hp'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq
  simp only [Proof.AesGcm.arg] at q₈ q₉
  have hw16 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 16) 64 := q₉
  -- What the entry leaves in each run.
  let I : State → State → Prop := fun s₀ s => VerS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
      (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) (stackArg s₀ 0) s ∧ s.gpr .rbx = stackArg s₀ 0 ∧
    s.gpr .rsi = s₀.gpr .r9 ∧ Covers [⟨s₀.gpr .r9, (stackArg s₀ 0).toNat⟩] (s.rd ++ s.wr)
  have hE : ∀ {s : State}, Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) →
      Perm (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) s → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 →
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 →
      (⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨stackArg s 1, 2560⟩ →
      Covers [⟨s.gpr .r9, (stackArg s 0).toNat⟩] (s.rd ++ s.wr) →
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) →
      WP isa (.block (finEntry 16 ++ ([.mov .rbx (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rbx,
        .mov .rsi (.reg .r9)] : List Instr))) s (I s) := fun L hperm ha hta dA hTr hR =>
    WP.mono (verifyEntry_ok L rfl rfl rfl rfl ha hta dA hperm hR) fun _ e =>
      ⟨⟨⟨e.env, e.rounds, e.alen, e.tlen⟩, e.tl⟩, e.rbx, e.rsi, by rw [e.rd, e.wr]; exact hTr⟩
  have hE₁ := hE L hperm ha hta dA hTr hR
  have hE₂ := hE L' hperm' ha' hta' dA' hTr' hR'
  simp only [I] at hE₁ hE₂
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  rw [finEntry, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [streamVerify, finEntry, List.append_assoc, List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1)
    (SP := s₀.gpr .rsp) (k := 16) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp) ⟨_, by taint_decide⟩
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    hw16 ha ha' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rdx = St at *
  generalize stackArg s₀ 1 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r9 = Tp at *
  generalize (s₀.gpr .rsi).toNat = R at *
  generalize htl : stackArg s₀ 0 = tl at *
  generalize ht : tl.toNat = t at *
  have htl' : tl = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  subst htl'
  -- The tag length.
  let A : State → Prop := fun s => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s ∧
    s.zf = some (!Spec.Gcm.tagLenOk t)
  have hK : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s →
      WP isa tagLenOk s A := fun s h =>
    WP.mono (tagLenOk_ok s h.2.1 (by rw [← ht]; exact (BitVec.ofNat 64 t).isLt)) fun s' ⟨hz, k⟩ => ⟨h.keep k, hz⟩
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => True ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s₁ ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s₂)
      ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.1.1, h.2.2.1.1.1,
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hK hK
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length §5.2.1.2 does not allow (`rax` is 0).
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.1.1, h.1.2.2.1.1.1.1⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.1.1 h.1.2.2.1.1.1.1)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
      omega
    have hc : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) R (s₀.gpr .rcx) (s₀.gpr .r8) t Tp s →
        WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
          (Env Ctx St W SP) := fun s ⟨⟨h, hm⟩, hbx, hsi, hTr⟩ =>
      WP.mono (verifyCheck_ok v L h.1 h.2.1 h.2.2.1 h.2.2.2 hm hbx hb.1 hb.2 hsi hTr dTW
        (x := List.replicate ((if s₀.gpr .r8 = 0 then (s₀.gpr .rcx).toNat else (s₀.gpr .r8).toNat) % 16) 0)
        (by simp)) fun _ h => h.1
    exact (rel_wp ((verifyCheck_rel v L hb.1 hb.2 dTW).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) hc hc).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamVerifyX86_64.pre Proof.AesGcm.streamVerifyX86_64.pub
      (streamVerify v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamVerify_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
