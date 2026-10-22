module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamVerify
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinTag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State

/-!
# SM4-GCM on x86-64: `stream_finish` and `stream_verify` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/StreamFinishCT.lean`, `StreamVerifyCT.lean`): after the
entry, both runs compute the tag from the same lengths (`finTag_rel`);
`finish` copies it to the same address, kept in `W`, and `verify` branches
only on the tag length, reads the received tag from the same address and
compares without a branch.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ tagLenOk recv cmp tlO tagPO)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm Keeps rel_regs rel_taint rel_wp rel_ite_e rel_env
  rel_reassoc_inner EnvAgree EnvAgree.regs env_agree covers_of_mem TagAt tagOut_rel fn_rel fn_rel₂ ct_of_rel
  recv_ok tagLenOk_ok)

theorem fin_lay {s : State} (hp : Proof.Sm4Gcm.finPre s) :
    Lay4 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) ∧ Perm (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) s := by
  simp only [Proof.Sm4Gcm.finPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_cs, -, d_cw, d_sw, -, -, -, -, -, k_c, k_s, -, k_w, wc, ws, -, ww, hsp⟩ := hp
  exact ⟨Lay4.of wc ws ww d_cs d_cw d_sw hsp k_c k_s k_w,
    ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩⟩

theorem finishEntry_fin {s : State} (hp : Proof.Sm4Gcm.finPre s) :
    WP isa (.block (finEntry .r9 ++ ([.store (at_ .r15 tagPO) .r8] : List Instr))) s fun s' =>
      FinS (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) s' ∧
        s'.mem.readW (s.gpr .r9 + BitVec.ofNat 64 200) 64 = s.gpr .r8 := by
  obtain ⟨L, hperm⟩ := fin_lay hp
  exact WP.mono (finishEntry_ok L rfl rfl rfl rfl rfl hperm) fun _ ⟨e, h⟩ => ⟨⟨e.env, e.alen, e.tlen⟩, h⟩

theorem streamFinish_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.Sm4Gcm.streamFinishX86_64.pre s₀)
    (hp' : Proof.Sm4Gcm.streamFinishX86_64.pre s₀') (hq : Proof.Sm4Gcm.streamFinishX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamFinish v.callees) fun _ _ => True := by
  obtain ⟨L, -⟩ := fin_lay hp
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have hE₂ := finishEntry_fin hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇] at hE₂
  have hE₁ := finishEntry_fin hp
  refine fn_rel (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := s₀.gpr .r9) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    ⟨_, by taint_decide⟩ hE₁ hE₂ ?_
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rsi = St at *
  generalize s₀.gpr .r9 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r8 = T at *
  have hw : ∀ s, FinS Ctx St W SP (s₀.gpr .rdx) (s₀.gpr .rcx) s ∧
      s.mem.readW (W + BitVec.ofNat 64 200) 64 = T → WP isa (finTag v.callees 0) s fun s' =>
        Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 200) 64 = T :=
    fun s h => WP.mono (finTag_ok v L (.inl rfl) h.1.1 h.1.2.1 h.1.2.2
      (x := List.replicate ((if s₀.gpr .rcx = 0 then (s₀.gpr .rdx).toNat else (s₀.gpr .rcx).toNat) % 16) 0)
      (by simp)) fun _ ⟨he, f, _⟩ => ⟨he, by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.lay.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide)
              (.inr ⟨by decide, by decide⟩)).symm
          · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), h.2]⟩
  have a := rel_wp ((finTag_rel v L (aL := s₀.gpr .rdx) (tL := s₀.gpr .rcx) (.inl rfl)).mono
      (P' := fun (s₁ s₂ : State) => True ∧ (FinS Ctx St W SP (s₀.gpr .rdx) (s₀.gpr .rcx) s₁ ∧
        s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = T) ∧ (FinS Ctx St W SP (s₀.gpr .rdx) (s₀.gpr .rcx) s₂ ∧
          s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T))
      (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h) (fun _ _ h => h.2) hw hw
  -- The address of `tag`, loaded from `W + 200`, is the same in both runs.
  have tg : ∀ s, Env Ctx St W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = T →
      TagAt Ctx St W SP .r15 200 T s := fun s ⟨he, hT⟩ =>
    ⟨he, by rw [he.r15]; exact hT, by rw [he.r15]; exact he.perm.wR (show 200 + 8 ≤ 2560 by decide)⟩
  exact RelCT.seq a ((tagOut_rel (b := .r15) (d := 200) (by simp) ⟨_, by taint_decide⟩
    (fun _ _ h => ⟨tg _ h.2.1, tg _ h.2.2⟩)).mono (fun _ _ h => h) fun _ _ h => h)

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamFinishX86_64.pre Proof.Sm4Gcm.streamFinishX86_64.pub
      (streamFinish v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamFinish_rel v hp hp' hq

/-- The lengths kept, and the tag length at `W + 224`. -/
def VerS (Ctx St W SP : Addr) (aL tL tl : BitVec 64) (s : State) : Prop :=
  FinS Ctx St W SP aL tL s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

/-- What `verify` has before checking a received tag of length `t` at `Tp`. -/
def VerT (aL tL : BitVec 64) (t : Nat) (Tp : Addr) (s : State) : Prop :=
  VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧ s.gpr .rsi = Tp ∧
    Covers [⟨Tp, t⟩] (s.rd ++ s.wr)

omit L in
theorem VerT.keep {aL tL : BitVec 64} {t : Nat} {Tp : Addr} {s s' : State}
    (h : VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s) (k : Keeps s s') :
    VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s' :=
  ⟨⟨h.1.1.keep (fun r hr => k.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) k.mem k.rd k.wr, by rw [k.mem]; exact h.1.2⟩,
    by rw [k.gpr _ (by decide), h.2.1], by rw [k.gpr _ (by decide), h.2.2.1], by rw [k.rd, k.wr]; exact h.2.2.2⟩

/-- The tag computed and compared, for an allowed length `t`. -/
theorem verifyCheck_rel {t : Nat} (h1 : 1 ≤ t) (h16 : t ≤ 16) {aL tL : BitVec 64} {Tp : Addr}
    (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₁ ∧
        VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₂)
      (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0))))
      fun _ _ => True := by
  have La := L.lay
  -- `recv` keeps the lengths.
  have hR : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s →
      WP isa recv s (VerS Ctx St W SP aL tL (BitVec.ofNat 64 t)) := fun s ⟨⟨h, ht⟩, hbx, hsi, hTr⟩ =>
    WP.mono (recv_ok h.1 hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide)))) fun s' ⟨he', _, f, _⟩ => by
      have d : ∀ d, 176 ≤ d → d + 8 ≤ 256 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact La.w_w (.inl (by omega)) (by omega) (by decide)
      exact ⟨⟨he',
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 184 (by decide) (by decide)) (by decide), h.2.1],
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 192 (by decide) (by decide)) (by decide), h.2.2]⟩,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 224 (by decide) (by decide)) (by decide), ht]⟩
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₁ ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₂) ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
      (fun _ _ h => EnvAgree.regs ⟨h.1.1.1.1, h.2.1.1.1, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hR hR
  -- `finTag` keeps the tag length.
  have hT : ∀ s, VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s → WP isa (finTag v.callees 0) s fun s' =>
      Env Ctx St W SP s' ∧ s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := fun s ⟨h, ht⟩ =>
    WP.mono (finTag_ok v L (.inl rfl) h.1 h.2.1 h.2.2
      (x := List.replicate ((if tL = 0 then aL.toNat else tL.toNat) % 16) 0) (by simp)) fun _ ⟨he', f, _⟩ =>
      ⟨he', by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (La.st_w (a := 0) (n := 32) (d := 224) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact La.w_w (.inr (by decide)) (by decide) (by decide)
          · simpa using La.w_w (a := 224) (n := 8) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
          · exact La.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), ht]⟩
  have b := rel_wp ((finTag_rel v L (aL := aL) (tL := tL) (.inl rfl)).mono
      (P' := fun s₁ s₂ => True ∧ VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s₁ ∧
        VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s₂) (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h)
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

theorem streamVerify_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.Sm4Gcm.streamVerifyX86_64.pre s₀)
    (hp' : Proof.Sm4Gcm.streamVerifyX86_64.pre s₀') (hq : Proof.Sm4Gcm.streamVerifyX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamVerify v.callees) fun _ _ => True := by
  obtain ⟨L, hperm, ha, hTr, dTW, -, -, -⟩ := ver_lay hp
  obtain ⟨L', hperm', ha', hTr', -, -, -, -⟩ := ver_lay hp'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq
  simp only [Proof.Sm4Gcm.arg] at q₈
  have hw8 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 8) 64 := q₈
  -- What the entry leaves in each run.
  let I : State → State → Prop := fun s₀ s => VerS (s₀.gpr .rdi) (s₀.gpr .rsi) (stackArg s₀ 0) (s₀.gpr .rsp)
      (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) s ∧ s.gpr .rbx = s₀.gpr .r9 ∧
    s.gpr .rsi = s₀.gpr .r8 ∧ Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] (s.rd ++ s.wr)
  have hE : ∀ {s : State}, Lay4 (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) →
      Perm (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) s → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 →
      Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr) →
      WP isa (.block (([.mov .rax (.mem (at_ .rsp 8))] : List Instr) ++ (finEntry .rax ++
        ([.mov .rbx (.reg .r9), .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r8)] : List Instr)))) s (I s) :=
    fun L hperm ha hTr => by
      rw [← List.append_assoc]
      exact WP.mono (verifyEntry_ok L rfl rfl rfl rfl ha hperm) fun _ e =>
        ⟨⟨⟨e.env, e.alen, e.tlen⟩, e.tl⟩, e.rbx, e.rsi, by rw [e.rd, e.wr]; exact hTr⟩
  have hE₁ := hE L hperm ha hTr
  have hE₂ := hE L' hperm' ha' hTr'
  simp only [I] at hE₁ hE₂
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  rw [streamVerify, List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := stackArg s₀ 0)
    (SP := s₀.gpr .rsp) (k := 8) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp) ⟨_, by taint_decide⟩
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    hw8 ha ha' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rsi = St at *
  generalize stackArg s₀ 0 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r8 = Tp at *
  generalize htl : s₀.gpr .r9 = tl at *
  generalize ht : tl.toNat = t at *
  have htl' : tl = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  subst htl'
  -- The tag length.
  let A : State → Prop := fun s => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s ∧
    s.zf = some (!Spec.Gcm.tagLenOk t)
  have hK : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s →
      WP isa tagLenOk s A := fun s h =>
    WP.mono (tagLenOk_ok s h.2.1 (by rw [← ht]; exact (BitVec.ofNat 64 t).isLt)) fun s' ⟨hz, k⟩ => ⟨h.keep k, hz⟩
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => True ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s₁ ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s₂)
      ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.1.1, h.2.2.1.1.1,
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hK hK
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length `tagLenOk` does not allow (`rax` is 0).
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.1.1, h.1.2.2.1.1.1.1⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.1.1 h.1.2.2.1.1.1.1)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      omega
    have hc : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s →
        WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
          (Env Ctx St W SP) := fun s ⟨⟨h, hm⟩, hbx, hsi, hTr⟩ =>
      WP.mono (verifyCheck_ok v L h.1 h.2.1 h.2.2 hm hbx hb.1 hb.2 hsi hTr dTW
        (x := List.replicate ((if s₀.gpr .rcx = 0 then (s₀.gpr .rdx).toNat else (s₀.gpr .rcx).toNat) % 16) 0)
        (by simp)) fun _ h => h.1
    exact (rel_wp ((verifyCheck_rel v L hb.1 hb.2 dTW).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) hc hc).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamVerifyX86_64.pre Proof.Sm4Gcm.streamVerifyX86_64.pub
      (streamVerify v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamVerify_rel v hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
