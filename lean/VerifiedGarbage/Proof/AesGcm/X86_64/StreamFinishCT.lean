import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_finish` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
compute the tag from the same lengths and number of rounds (`finTag_rel`),
and copy it to the same address, kept in `W` (`finishEntry_ok`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

theorem fin_lay {s : State} (hp : Proof.AesGcm.finPre s) :
    Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 0) (s.gpr .rsp) ∧ Perm (s.gpr .rdi) (s.gpr .rdx) (stackArg s 0) s ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) := by
  simp only [Proof.AesGcm.finPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, -, -, -, -, -, k_c, k_s, -, k_w, wc, ws, -, ww, hR⟩ := hp
  exact ⟨Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w,
    ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩,
    by rw [hrd]; exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Region.contains_self _ _⟩, hR⟩

theorem finishEntry_fin {s : State} (hp : Proof.AesGcm.finPre s) :
    WP isa (.block (finEntry 8 ++ ([.store (at_ .r15 tagPO) .r9] : List Instr))) s fun s' =>
      FinS (s.gpr .rdi) (s.gpr .rdx) (stackArg s 0) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) s' ∧
        s'.mem.readW (stackArg s 0 + BitVec.ofNat 64 200) 64 = s.gpr .r9 := by
  obtain ⟨L, hperm, ha, hR⟩ := fin_lay hp
  exact WP.mono (finishEntry_ok L rfl rfl rfl rfl rfl ha hperm hR) fun _ ⟨e, h⟩ =>
    ⟨⟨e.env, e.rounds, e.alen, e.tlen⟩, h⟩

theorem streamFinish_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamFinishX86_64.pre s₀') (hq : Proof.AesGcm.streamFinishX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamFinish v.callees) fun _ _ => True := by
  obtain ⟨L, -, ha₁, -⟩ := fin_lay hp
  obtain ⟨-, -, ha₂, -⟩ := fin_lay hp'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq
  simp only [Proof.AesGcm.arg] at q₈
  have hw8 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 8) 64 :=
    q₈
  have hE₂ := finishEntry_fin hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  have hE₁ := finishEntry_fin hp
  rw [finEntry, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [streamFinish, finEntry, List.append_assoc, List.append_assoc]
  refine fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 0) (SP := s₀.gpr .rsp) (k := 8)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp) ⟨_, by taint_decide⟩ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    hw8 ha₁ ha₂ ⟨_, by taint_decide⟩ hE₁ hE₂ ?_
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rdx = St at *
  generalize stackArg s₀ 0 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r9 = T at *
  have hw : ∀ s, FinS Ctx St W SP (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) s ∧
      s.mem.readW (W + BitVec.ofNat 64 200) 64 = T → WP isa (finTag v.callees 0) s fun s' =>
        Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 200) 64 = T :=
    fun s h => WP.mono (finTag_ok v L (.inl rfl) h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
      (x := List.replicate ((if s₀.gpr .r8 = 0 then (s₀.gpr .rcx).toNat else (s₀.gpr .r8).toNat) % 16) 0)
      (by simp)) fun _ ⟨he, _, f, _⟩ => ⟨he, by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w (by decide)).symm) (by decide), h.2]⟩
  have a := rel_wp ((finTag_rel v L (R := (s₀.gpr .rsi).toNat) (aL := s₀.gpr .rcx) (tL := s₀.gpr .r8) (.inl rfl)).mono
      (P' := fun (s₁ s₂ : State) => True ∧ (FinS Ctx St W SP (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) s₁ ∧
        s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = T) ∧ (FinS Ctx St W SP (s₀.gpr .rsi).toNat (s₀.gpr .rcx)
          (s₀.gpr .r8) s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T))
      (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h) (fun _ _ h => h.2) hw hw
  -- The address of `tag`, loaded from `W + 200`, is the same in both runs.
  have tg : ∀ s, Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = T →
      TagAt Ctx St W SP .r15 200 T s := fun s ⟨he, hT⟩ =>
    ⟨he, by rw [he.r15]; exact hT, by rw [he.r15]; exact he.perm.wR (show 200 + 8 ≤ 2560 by decide)⟩
  exact RelCT.seq a ((tagOut_rel (b := .r15) (d := 200) (by simp) ⟨_, by taint_decide⟩
    (fun _ _ h => ⟨tg _ h.2.1, tg _ h.2.2⟩)).mono (fun _ _ h => h) fun _ _ h => h)

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamFinishX86_64.pre Proof.AesGcm.streamFinishX86_64.pub
      (streamFinish v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamFinish_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
