module

public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextS
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextS
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM on x86-64: `streamTextS` is constant time

Untrusted: everything here is checked by Lean. As `StreamCryptCT.lean` for
`streamText`: `flushS_rel`, `startS_rel`, `streamTextS_rel` and
`streamS_rel` are `flush_rel`, `start_rel`, `streamText_rel` and
`stream_rel` with the additional data padded in the state.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)

theorem gh1Check_r14_64 {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : Gh1Check yo .r14 64 := by
  rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N gs : Nat} [G : GhFits v N gs] (L : Lay Ctx St W SP N) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include G L hyo

/-- `flushS yo`, with the same number of buffered bytes. -/
theorem flushS_rel : RelCT isa (EnvAgree Ctx St W SP [.rbx] · · N) (flushS v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_regs ([.rbx] ++ [.r13, .r14, .r15, .rsp]) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) true
      (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine rel_reassoc2 (RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => h.1.2) (rel_taint ([.rbx] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.1.1.1) ⟨_, by taint_decide⟩))
    ?_)
  refine (ghash1_rel v L hyo .r14 64 (.inl rfl) (by decide) (P := St + BitVec.ofNat 64 64)
    (L.st_st (.inl (by omega_using [hyo])) (by omega_using [hyo]) (by decide)) (L.st_gh G.fit (by decide))
    (L.stk_st (by decide)) (gh1Check_r14_64 hyo) (F₁ := (Env Ctx St W SP · N)) (F₂ := (Env Ctx St W SP · N))
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s N := hs.elim id id
  exact ⟨he, by rw [he.r14], covers_left (he.perm.stC (by decide))⟩

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N : Nat} (L : Lay Ctx St W SP N)
include L

/-- The additional data padded if there is no text yet, in both runs. -/
theorem startS_rel {aL P : Nat} (hP : P < 2 ^ 64) {F : State → Prop} (hF : ∀ s, F s → Env Ctx St W SP s N ∧
      s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P ∧
      s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) {gs : Nat} [GhFits v N gs]
    (hN : 200 ≤ N := by decide) (hNl : N < 2 ^ 64 := by decide) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) fun _ _ => True := by
  let G : State → Prop := fun s' => s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' N ∧
    s'.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  have g : ∀ s, F s → WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s G :=
    fun s h => WP.mono (tl_ok hP (hF s h).1 (hF s h).2.1 hN hNl) fun s' ⟨z, e, m⟩ => ⟨z, e, by rw [m]; exact (hF s h).2.2⟩
  have a := rel_both (rel_envT (F := F) [] (fun s h => (hF s h).1) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g g
  have b := rel_both (rel_envT (F := fun s => G s ∧ s.zf = some true) [] (fun _ h => h.1.2.1)
      (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
    (fun s h => al_ok h.1.2.1 h.1.2.2 hN hNl) (fun s h => al_ok h.1.2.1 h.1.2.2 hN hNl)
  have c := (flushS_rel v L (yo := 16) (.inr rfl)).mono (P' := fun (s₁ s₂ : State) =>
      (s₁.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₁ N) ∧
      (s₂.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₂ N))
    (fun _ _ h => ⟨h.1.2, h.2.2, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]⟩) fun _ _ h => h
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) ?_ (RelCT.block_nil fun _ _ _ => trivial))
  unfold firstFlushS
  exact (RelCT.seq b c).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩) fun _ _ h => h

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R aL P₀ : Nat} {D : Addr} {n : Nat}

include L in
/-- `streamTextS` in two runs, with the same data and lengths. -/
theorem streamTextS_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TPre M Ctx St W SP R aL P₀ D n s₁ ∧ TPre M Ctx St W SP R aL P₀ D n s₂)
      (streamTextS (v.withBlk B) enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  generalize hk : headLen P₀ n = k
  have hkw := headLen_whole P₀ n
  have hkn := headLen_le P₀ n
  rw [hk] at hkw hkn
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre M Ctx St W SP R aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, TPre M Ctx St W SP R aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbp h.rbp h.data.ok.lt
    exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r _ => by rw [hg]) hrd hwr, h.data.of_eq hrd hwr,
      by rw [hg]; exact h.rbp, hm ▸ h.alen, hm ▸ h.tlen, hm ▸ h.dat, hm ▸ h.len, by rw [hm]; exact h.K, h.hP, by rw [hrd, hwr]; exact h.cov⟩, hz⟩
  have a := rel_both (rel_envT (F := TPre M Ctx St W SP R aL P₀ D n) [.rbp] (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  -- The start.
  let F₀ : State → Prop := fun s => T1 s ∧ s.zf = some false
  let G₂ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₂ : ∀ s, F₀ s → WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s G₂ := fun s h => by
    have t := h.1.1
    refine WP.mono (startS_ok v t.K enc (Hyp := False) (icb := 0) t.env rfl t.data t.cov (a := List.replicate aL 0)
      (c₀ := List.replicate P₀ 0) (by simpa using t.hP) (by simpa using t.alen) (by simpa using t.tlen)
      False.elim False.elim) fun s' ⟨I, sl⟩ => ?_
    simp only [List.length_replicate] at I
    refine ⟨⟨_, _, _, _, t.K, ?_, I⟩, by rw [sl 200 (by decide) (by decide)]; exact t.dat,
      by rw [sl 208 (by decide) (by decide)]; exact t.len, by rw [sl 192 (by decide) (by decide)]; exact t.tlen⟩
    have := Proof.Gcm.length_pad_mod aL
    simp only [List.length_append, List.length_replicate, Proof.Gcm.length_zeros]; omega_arith
  have b := rel_both (startS_rel v L (aL := aL) (F := F₀) hP (fun s h => ⟨h.1.1.env, h.1.1.tlen, h.1.1.alen⟩))
    g₂ g₂
  -- The data loaded.
  let G₃ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₃ : ∀ s, G₂ s → WP isa (.block streamLoad) s G₃ := fun s h => by
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok h.1.env h.2.1 h.2.2.1 h.2.2.2
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, h.1.regs (load_env hg) hm hrd hwr, h12, hbp, hbx, hm ▸ h.2.1, hm ▸ h.2.2.1,
      hm ▸ h.2.2.2⟩
  have c := rel_both (rel_envT (F := G₂) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₃ g₃
  -- Fewer than 256 bytes, or more.
  have g₃s : ∀ s, G₃ s → WP isa (.block streamSmall) s fun s' => G₃ s' ∧ s'.cf = some (decide (n < 256)) :=
    fun s h => by
      obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
      have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
      obtain ⟨s', run, hcf, hg, hm, hrd, hwr⟩ := small_ok s hbp hlt
      exact WP.of_runBlock ⟨s', run, ⟨hs.regs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hm hrd hwr,
        by rw [hg .r12 (by decide)]; exact h12, by rw [hg .rbp (by decide)]; exact hbp,
        by rw [hg .rbx (by decide)]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hcf⟩
  have cs := rel_both (rel_envT (F := G₃) [.rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₃s g₃s
  have pp : ∀ s, G₃ s → PartPre M Ctx St W SP R P₀ enc D n 0 n s := fun s h =>
    ⟨h.1, by omega_arith, by simp [h.2.1], h.2.2.1, by rw [h.2.2.2.1, Nat.add_zero], by rw [h.2.2.2.2.1]; simp,
      h.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2, Nat.add_zero]⟩
  have gsm : ∀ s, PartPre M Ctx St W SP R P₀ enc D n 0 n s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  -- The head's length.
  let G₄ : State → Prop := fun s => PartPre M Ctx St W SP R P₀ enc D n 0 k s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₄ : ∀ s, G₃ s → WP isa streamHead s G₄ := fun s h => by
    obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    refine WP.mono (sHead_ok hs.env hlt hbx hbp) fun s' ⟨hbp', hg, hl, ha, f, hrd, hwr⟩ => ?_
    rw [hk] at hbp' hl
    have rd : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide)
    refine ⟨⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (by decide) (by decide) f,
      by omega_arith, by simp [hg .r12 (by decide) (by decide), h12], hbp',
      by rw [hg .rbx (by decide) (by decide), hbx, Nat.add_zero], by rw [rd 200 (by decide) (by decide), hdat]; simp, hl,
      by rw [rd 192 (by decide) (by decide), htl, Nat.add_zero]⟩, ha⟩
  have d := rel_both (rel_envT (F := G₃) [.rbx, .rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₄ g₄
  -- The head.
  let G₅ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n k s ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀ ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₅ : n ≠ 0 → ∀ s, G₄ s → WP isa (headPart v.callees enc) s G₅ := fun hn s h => by
    obtain ⟨hp, ha⟩ := h
    have ⟨_, _, _, _, _, hdat, hlen, htl⟩ := hp
    subst hk
    refine WP.mono (si_head v enc hp hn) fun s' ⟨hs, sl⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.zero_add] at hs; exact hs
    · rw [sl 208 (by decide) (by decide)]; exact hlen
    · rw [sl 200 (by decide) (by decide), hdat]; simp
    · rw [sl 192 (by decide) (by decide), htl, Nat.add_zero]
    · rw [sl 216 (by decide) (by decide)]; exact ha
  -- Whether the text so far left a block partial: the head, by `cryptHead` and `absorbHead`, if so.
  let T₄ : State → Prop := fun s => G₄ s ∧ s.zf = some (decide (P₀ % 16 = 0))
  have g₄t : ∀ s, G₄ s → WP isa (.block [.alu .test .rbx (.reg .rbx)]) s T₄ := fun s h => by
    obtain ⟨⟨hs, hk', h12, hbp, hbx, hdat, hlen, htl⟩, ha⟩ := h
    have hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbx hbx (by omega_arith)
    rw [Nat.add_zero] at hz
    exact WP.of_runBlock ⟨s', run, ⟨⟨hs.regs (fun r _ => by rw [hg]) hm hrd hwr, hk', by rw [hg]; exact h12,
      by rw [hg]; exact hbp, by rw [hg]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hm ▸ ha⟩, hz⟩
  have e₁ := rel_both (rel_envT (F := G₄) [.rbx] (fun _ h => h.1.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.2.2.1, h₂.1.2.2.2.2.1]) ⟨_, by taint_decide⟩) g₄t g₄t
  have e : n ≠ 0 → RelCT isa (fun s₁ s₂ => G₄ s₁ ∧ G₄ s₂) (headPart v.callees enc) fun s₁ s₂ => G₅ s₁ ∧ G₅ s₂ :=
    fun hn => by
    refine rel_both (RelCT.seq e₁ (rel_ite_e (fun _ _ h => h.1.2.trans h.2.2.symm)
      (RelCT.block_nil fun _ _ _ => trivial) ?_)) (g₅ hn) (g₅ hn)
    by_cases hz : P₀ % 16 = 0
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hz] at this
    have e' : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, hz]
    rw [hk] at e'
    exact (headPart_rel v L enc (k := k) (by omega_arith) hz (by omega_arith)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩)
      fun _ _ h => h
  -- Past the head.
  have g₆ : ∀ s, G₅ s → WP isa (.block streamNext) s (BPre M Ctx St W SP R P₀ enc D n k) := fun s h => by
    obtain ⟨hs, hl, hdat, htl, ha⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    exact WP.mono (next_ok hs.env hkn hlt hl hdat htl ha) fun s' ⟨hg, d', t', l', f, hrd, hwr⟩ =>
      ⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (Nat.le_refl _)
        (by decide) f, d', l', t'⟩
  have f := rel_both (rel_envT (F := G₅) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₆ g₆
  -- The whole blocks.
  let G₇ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - k) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (k + 16 * ((n - k) / 16)))
  have g₇ : ∀ s, BPre M Ctx St W SP R P₀ enc D n k s → WP isa (streamBlocks (if enc then B.enc
      else B.dec)) s G₇ := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := hs
    exact WP.mono (blocks_ok B K enc I hx hdat hlen htl (fun hq => hkw.resolve_left (by omega_arith)))
      fun s' ⟨I', d', l', t'⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, d', l', t'⟩
  have g := rel_both (blocks_rel B L enc) g₇ g₇
  -- The rest.
  have g₈ : ∀ s, G₇ s → WP isa (.block streamLoad) s
      (PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16)) := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok hs.env hdat hlen htl
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, hs.regs (load_env hg) hm hrd hwr, by omega_arith, h12, hbp, hbx, hm ▸ hdat,
      hm ▸ hlen, hm ▸ htl⟩
  have i := rel_both (rel_envT (F := G₇) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₈ g₈
  have g₉ : ∀ s, PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16) s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  have j := rel_both (part_rel v L enc) g₉ g₉
  simp only [streamTextS]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelCT.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  by_cases hs : n < 256
  · -- All of it is the rest.
    refine rel_reassoc2 ((RelCT.seq b (RelCT.seq c (RelCT.seq cs (RelCT.seq
      (RelCT.ite (M := isa) (c := .b) (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm)
        (RelCT.block_nil fun _ _ h => ⟨pp _ h.1.1.1, pp _ h.1.2.1⟩)
        (RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hs] at this))
      (rel_both (part_rel v L enc (j := 0) (k := n)) gsm gsm))))).mono
      (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)
  · -- The head and the whole blocks first.
    refine rel_reassoc2 ((RelCT.seq b (RelCT.seq c (RelCT.seq cs (RelCT.seq
      (RelCT.ite (M := isa) (c := .b) (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm)
        (RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hs] at this)
        ((RelCT.seq d (RelCT.seq (e (by omega_arith)) (RelCT.seq f (RelCT.seq g i)))).mono
          (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))
      j)))).mono
      (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)

end

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem streamS_rel (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (enc : Bool) {s₀ s₀' : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s₀) (hok : M.ok s₀.mem (s₀.gpr .rdi))
    (hp' : Proof.AesGcm.streamCryptPre M.len s₀') (hok' : M.ok s₀'.mem (s₀'.gpr .rdi))
    (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) fun _ _ => True := by
  have L := (CryptCtx.of hp M.ge).lay
  have hE₂ := cryptEntry_tpre hp' hok'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := cryptEntry_tpre hp hok
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₉
    (CryptCtx.of hp M.ge).args.2 (CryptCtx.of hp' M.ge).args.2 ⟨_, by taint_decide⟩ hE₁ hE₂
    ((streamTextS_rel v B L enc (s₀.gpr .r8).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

theorem streamEncryptSM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.streamEncryptX86_64M M).pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncryptS (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => streamS_rel v B true hp.1 hp.2 hp'.1 hp'.2 hq

theorem streamDecryptSM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.streamDecryptX86_64M M).pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecryptS (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => streamS_rel v B false hp.1 hp.2 hp'.1 hp'.2 hq

end VG.Proof.AesGcm.X86_64
