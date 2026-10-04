import VerifiedGarbage.Proof.AesCcm.X86_64.MacCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt

/-!
# AES-CCM on x86-64: counter mode is constant time

Untrusted: everything here is checked by Lean. Both runs go through the same
chunks: the number of blocks of each, `k`, depends only on the length and
the blocks done (`chunk_ok`), and it is kept at `W + 216`, which the taint
analysis then takes as public (`ccmTk`) for the end of the chunk; the calls
of `vg_aes_ctr32` have the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The taint of `ccmT rs`, with `k` at `W + 216` public too. -/
def ccmTk (rs : List Reg) : X86_64.Taint.T :=
  { ccmT rs with slots := [(1, 160, 56), (1, 232, 8), (1, 216, 8)] }

theorem both_agree_k {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D nl al n tl rs s₁ s₂) {v : BitVec 64}
    (hk₁ : s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = v) (hk₂ : s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = v) :
    X86_64.Taint.Agree (ccmTk rs) s₁ s₂ := by
  have a := both_agree hDW hn h
  refine ⟨a.rf, a.wr, a.wf₁, a.wf₂, fun sl hsl => ?_, fun sl hsl k hk₁' hk₂' => ?_, a.lo⟩
  · simp only [ccmTk, ccmT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl | rfl <;> simp [ccmTk, ccmT]
  · simp only [ccmTk, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl | rfl
    · exact a.slots _ (List.Mem.head _) k hk₁' hk₂'
    · exact a.slots _ (List.Mem.tail _ (List.Mem.head _)) k hk₁' hk₂'
    · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
        fun s hw => by simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ,
          List.getD_cons_zero]
      simp only at hk₁' hk₂'
      rw [hb s₁ h.wr₁, hb s₂ h.wr₂, show W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 216 + BitVec.ofNat 64 (k - 216)
        by rw [add_ofNat_assoc, show 216 + (k - 216) = k by omega]]
      exact word_byte hk₁ hk₂ (by omega)

/-- Code the taint analysis checks from `ccmTk rs`, leaving the flags public. -/
theorem rel_flagsCk {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl rs s₁ s₂ ∧ ∃ v,
      s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = v ∧ s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = v)
    (hc : ∃ hc, ((taint.check (ccmTk rs) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hb, v, h₁, h₂⟩ := hP _ _ hp
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (both_agree_k hDW hn hb h₁ h₂) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

/-- The number of blocks of the chunk after `b`. -/
def chunkK (n b : Nat) : Nat := min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32)

/-- A chunk up to its call: the arguments. -/
theorem chunkPre_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b : Nat} {t : State} (I : CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)])
      (.seq (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))
      (.block ([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] ++ ctrAt ++
        [.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++
        ptr .r9 .r15 scrO)))) t fun t₅ =>
      CtrCall t₅ K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R
        (chunkK n b) ∧ Env K W SP t₅ ∧ t₅.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (chunkK n b) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine WP.assoc (WP.seq (WP.mono (kSel_ok I.rbx I.r14 (by omega)) fun t₂ ⟨hm₂, hr8₂, hg₂, hrd₂, hwr₂⟩ => ?_))
  have hk1 : 1 ≤ chunkK n b := by unfold chunkK; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + chunkK n b ≤ n / 16 := by unfold chunkK; omega
  obtain ⟨t₅, run₅, f₅, _, hkO₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ :=
    setup_ok C I hb hm₂ hr8₂ hg₂ hrd₂ hwr₂
  have E₅ : Env K W SP t₅ := I.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₅ hwr₅
  have hS := (C.buf.of_eq (hrd₅.trans I.rd) (hwr₅.trans I.wr)).slice (a := 16 * b) (k := 16 * chunkK n b) (by omega)
  have hqc : (⟨D + BitVec.ofNat 64 (16 * b), 16 * chunkK n b⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    hS.w.sub_right (Lay.wSub (by decide))
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * b), 16 * chunkK n b⟩ :=
    C.dk.sub_right (Offset.sub_base D (by omega))
  have hqw : Covers [⟨D + BitVec.ofNat 64 (16 * b), 16 * chunkK n b⟩] t₅.wr := by
    rw [hwr₅, I.wr]; exact covers_off C.dw (by omega) hn64
  exact WP.of_runBlock ⟨t₅, run₅, cargs L E₅ C.rounds (c := 64) (by decide) (srcBuf hS) hqc hqk hqw
    hdi hsi hdx hcx hr8 hr9, E₅, hkO₅, hg₅, hrd₅, hwr₅, f₅⟩

theorem chunkPre_check : ∃ hc, (taint.check (ccmT [.rbx, .r12, .r14])
    (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)])
      (.seq (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))
      (.block ([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] ++ ctrAt ++
        [.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++
        ptr .r9 .r15 scrO)))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ hc, ((taint.check (ccmTk [.rbx, .r12, .r14])
    (.block [.mov .rax (.mem (at_ .r15 kO)), .alu .sub .rbx (.reg .rax), .alu .add .r14 (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .r12 (.reg .rax), .alu .test .rbx (.reg .rbx)]) hc).map (·.flags)) = some true := ⟨_, by taint_decide⟩

/-- A run after `b` blocks of counter mode, from `σ`. -/
theorem CtrInv.one {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {nonce : List Byte} {σ t : State}
    {b : Nat} (C : CtrCtx K W SP σ R nonce D n) (O : One K W SP R N A D nl al n tl σ)
    (I : CtrInv K W SP σ R nonce D n b t) : One K W SP R N A D nl al n tl t :=
  ⟨I.env, slots_mut C.lay C.buf.w (I.frame.sub (ctrR_mut W SP D n)) O.sl, I.wr.trans O.wr⟩

/-- What the call of a chunk is given, in a run from `σ`. -/
def ChunkArgs (K W SP : Addr) (R : Nat) (D : Addr) (n b : Nat) (σ t : State) : Prop :=
  CtrCall t K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R (chunkK n b) ∧
    Env K W SP t ∧ t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (chunkK n b) ∧
    t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) ∧ t.gpr .r12 = D + BitVec.ofNat 64 (16 * b) ∧
    t.gpr .r14 = BitVec.ofNat 64 (1 + b) ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧ Frame (ctrR W SP D n) σ.mem t.mem

/-- What the call of a chunk leaves, in a run from `σ`. -/
def ChunkCalled (K W SP : Addr) (D : Addr) (n b : Nat) (σ t : State) : Prop :=
  Env K W SP t ∧ t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (chunkK n b) ∧
    t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) ∧ t.gpr .r12 = D + BitVec.ofNat 64 (16 * b) ∧
    t.gpr .r14 = BitVec.ofNat 64 (1 + b) ∧ t.wr = σ.wr ∧ Frame (ctrR W SP D n) σ.mem t.mem

theorem chunkArgs_ok {K W SP : Addr} {σ : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP σ R nonce D n) {b : Nat} {t : State} (I : CtrInv K W SP σ R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)])
      (.seq (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))
      (.block ([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] ++ ctrAt ++
        [.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++
        ptr .r9 .r15 scrO)))) t (ChunkArgs K W SP R D n b σ) :=
  WP.mono (chunkPre_ok C I hb) fun _ ⟨cc, E, k, g, rd, wr, f⟩ =>
    ⟨cc, E, k, by rw [g _ (by simp), I.rbx], by rw [g _ (by simp), I.r12], by rw [g _ (by simp), I.r14],
      by rw [rd, I.rd], by rw [wr, I.wr], I.frame.trans (f.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩)⟩

theorem chunkCalled_ok (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {D : Addr} {n b : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hkb : 16 * b + 16 * chunkK n b ≤ n) {σ t : State}
    (h : ChunkArgs K W SP R D n b σ t) :
    WP isa (.call v.callee.name v.callee.code) t (ChunkCalled K W SP D n b σ) := by
  obtain ⟨cc, E, k, h₁, h₂, h₃, _, wr, f⟩ := h
  refine WP.mono (ctr_call v cc) fun t' p => ⟨E.of_saved p.saved p.rd p.wr, ?_, by rw [p.saved _ (by decide), h₁],
    by rw [p.saved _ (by decide), h₂], by rw [p.saved _ (by decide), h₃], by rw [p.wr, wr], ?_⟩
  · have hDs : Region.Sub ⟨D + BitVec.ofNat 64 (16 * b), 16 * chunkK n b⟩ ⟨D, n⟩ := Offset.sub_base D hkb
    rw [p.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((hDW.sub_left hDs).sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E.rsp]; exact ((L.stk_w' (by decide)).sub_left (below8_sub _)).symm) (by decide), k]
  · have fc := p.frame
    rw [E.rsp] at fc
    exact f.trans (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D hkb⟩
      · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below SP 16, by simp, below8_sub SP⟩)

/-- A chunk, in two runs (from `σ₁` and `σ₂`) that have done the same blocks. -/
theorem chunk_rel (v : Ctr32Impl) {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {σ₁ σ₂ : State}
    {nonce₁ nonce₂ : List Byte} (C₁ : CtrCtx K W SP σ₁ R nonce₁ D n) (C₂ : CtrCtx K W SP σ₂ R nonce₂ D n)
    (O₁ : One K W SP R N A D nl al n tl σ₁) (O₂ : One K W SP R N A D nl al n tl σ₂) {b : Nat} (hb : b < n / 16) :
    RelCT isa (fun t₁ t₂ => CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧ CtrInv K W SP σ₂ R nonce₂ D n b t₂)
      (ctrChunk v.callee) fun t₁ t₂ => t₁.zf = t₂.zf := by
  have L := C₁.lay
  have hDW := C₁.buf.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt C₁.buf.lt
  have hkb : 16 * b + 16 * chunkK n b ≤ n := by unfold chunkK; omega
  have hreg : ∀ {t₁ t₂ : State}, t₁.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) → t₂.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) →
      t₁.gpr .r12 = D + BitVec.ofNat 64 (16 * b) → t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * b) →
      t₁.gpr .r14 = BitVec.ofNat 64 (1 + b) → t₂.gpr .r14 = BitVec.ofNat 64 (1 + b) →
      ∀ r ∈ [Reg.rbx, .r12, .r14], t₁.gpr r = t₂.gpr r := fun a₁ a₂ b₁ b₂ c₁ c₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [b₁, b₂]
    · rw [c₁, c₂]
  have r₁ := (rel_taintC [.rbx, .r12, .r14] hDW hn (fun t₁ t₂ (h : CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧
      CtrInv K W SP σ₂ R nonce₂ D n b t₂) =>
    Both.of (h.1.one C₁ O₁) (h.2.one C₂ O₂) (hreg h.1.rbx h.2.rbx h.1.r12 h.2.r12 h.1.r14 h.2.r14))
    chunkPre_check).wp (F₁ := ChunkArgs K W SP R D n b σ₁) (F₂ := ChunkArgs K W SP R D n b σ₂)
    fun t₁ t₂ h => ⟨chunkArgs_ok C₁ h.1 hb, chunkArgs_ok C₂ h.2 hb⟩
  have r₂ := (ctr_rel v (P := fun t₁ t₂ => True ∧ ChunkArgs K W SP R D n b σ₁ t₁ ∧ ChunkArgs K W SP R D n b σ₂ t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1.rsp, h.2.2.2.1.rsp]⟩).wp
    (F₁ := ChunkCalled K W SP D n b σ₁) (F₂ := ChunkCalled K W SP D n b σ₂)
    fun t₁ t₂ h => ⟨chunkCalled_ok v L hDW hkb h.2.1, chunkCalled_ok v L hDW hkb h.2.2⟩
  have r₃ := rel_flagsCk (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun t₁ t₂ => True ∧ ChunkCalled K W SP D n b σ₁ t₁ ∧ ChunkCalled K W SP D n b σ₂ t₂)
    [.rbx, .r12, .r14] hDW hn (fun t₁ t₂ ⟨_, ⟨E₁, k₁, a₁, b₁, c₁, w₁, f₁⟩, ⟨E₂, k₂, a₂, b₂, c₂, w₂, f₂⟩⟩ =>
      ⟨Both.of ⟨E₁, slots_mut L hDW (f₁.sub (ctrR_mut W SP D n)) O₁.sl, w₁.trans O₁.wr⟩
        ⟨E₂, slots_mut L hDW (f₂.sub (ctrR_mut W SP D n)) O₂.sl, w₂.trans O₂.wr⟩ (hreg a₁ a₂ b₁ b₂ c₁ c₂),
        _, k₁, k₂⟩) chunkEnd_check
  exact rel_assoc3 (RelCT.seq r₁ (RelCT.seq r₂ (r₃.mono (fun _ _ h => h) fun _ _ h => h.2)))

end VG.Proof.AesCcm.X86_64
