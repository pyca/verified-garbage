import VerifiedGarbage.Proof.AesGcm.X86_64.StreamRun
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. Both runs take the same
pieces of `streamText` (`streamText_rel`): the branches are on the length
of the data and of the text so far, the same in both; `crypt`, `absorb`,
`flush` and the call of the whole blocks are on data at the same address,
of the same length (`part_rel`, `blocks_rel`, `start_rel`); between them,
each run keeps `SInv` (with no hypotheses: `SI`), from the correctness
proofs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)

/-- Two runs, each with what it satisfies after `c`. -/
theorem rel_both {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True) (hw₁ : ∀ s, F₁ s → WP isa c s G₁)
    (hw₂ : ∀ s, F₂ s → WP isa c s G₂) : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp h (fun _ _ h => h) hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code whose leakage depends only on the registers `rs` and the
environment's. -/
theorem rel_envT {Ctx St W SP : Addr} {F : State → Prop} {c : Prog isa} (rs : List Reg)
    (hF : ∀ s, F s → Env Ctx St W SP s) (hag : ∀ s₁ s₂, F s₁ → F s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (rs ++ ([.r13, .r14, .r15, .rsp] : List Reg))) c hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) c fun _ _ => True :=
  rel_taint (rs ++ [.r13, .r14, .r15, .rsp]) (fun s₁ s₂ h r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hag _ _ h.1 h.2 r hr
    · exact env_agree (hF _ h.1) (hF _ h.2) r hr) hc

/-- One run between the pieces of `streamText`: `SInv`, with no hypotheses. -/
def SI (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j : Nat) (s : State) : Prop :=
  ∃ H icb x₀ m₀, SCtx Ctx St W SP R H D n m₀ ∧ x₀.length % 16 = P₀ % 16 ∧
    SInv False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s

section
variable {Ctx St W SP : Addr} {R P₀ : Nat} {enc : Bool} {D : Addr} {n : Nat}

theorem SI.env {j : Nat} {s : State} (h : SI Ctx St W SP R P₀ enc D n j s) : Env Ctx St W SP s :=
  let ⟨_, _, _, _, _, _, I⟩ := h; I.env

/-- What a piece does to `SInv`, to `SI`. -/
theorem SI.lift {j j' : Nat} {s : State} {c : Prog isa} {G : State → Prop} (h : SI Ctx St W SP R P₀ enc D n j s)
    (hw : ∀ {H icb x₀ m₀}, SCtx Ctx St W SP R H D n m₀ → x₀.length % 16 = P₀ % 16 →
      SInv False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s →
      WP isa c s fun s' => SInv False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j' s' ∧ G s') :
    WP isa c s fun s' => SI Ctx St W SP R P₀ enc D n j' s' ∧ G s' := by
  obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := h
  exact WP.mono (hw K hx I) fun s' ⟨I', g⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, g⟩

theorem SI.regs {j : Nat} {s s' : State} (h : SI Ctx St W SP R P₀ enc D n j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : SI Ctx St W SP R P₀ enc D n j s' :=
  let ⟨H, icb, x₀, m₀, K, hx, I⟩ := h; ⟨H, icb, x₀, m₀, K, hx, I.regs hg hm hrd hwr⟩

theorem SI.slots {j : Nat} {s s' : State} (h : SI Ctx St W SP R P₀ enc D n j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    {d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] s.mem s'.mem) :
    SI Ctx St W SP R P₀ enc D n j s' :=
  let ⟨H, icb, x₀, m₀, K, hx, I⟩ := h; ⟨H, icb, x₀, m₀, K, hx, I.slots K hg hrd hwr h₁ h₂ hf⟩

end

/-! ## A part of the data -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {R P₀ : Nat} {D : Addr} {n : Nat}
include L

/-- Before `part`: what `part_ok` needs. -/
def PartPre (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j k : Nat) (s : State) : Prop :=
  SI Ctx St W SP R P₀ enc D n j s ∧ j + k ≤ n ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧
    s.gpr .rbp = BitVec.ofNat 64 k ∧ s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- Between `crypt` and `absorb`, in either order. -/
def PartMid (Ctx St W SP : Addr) (R P₀ : Nat) (D : Addr) (j k : Nat) (s : State) : Prop :=
  Env Ctx St W SP s ∧ RoundsAt s.mem W R ∧ DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

omit L in
theorem PartPre.mid {enc : Bool} {j k : Nat} {s : State} (h : PartPre Ctx St W SP R P₀ enc D n j k s) :
    PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) := by
  obtain ⟨⟨H, icb, x₀, m₀, K, hx, I⟩, hk, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  exact ⟨⟨I.env, I.rounds K, (I.data.drop I.le).take (by have := I.le; omega), hdat, hlen, htl⟩, h12, hbp, hbx⟩

omit L in
theorem PartMid.crIn {j k : Nat} {s : State}
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    CrIn Ctx St W SP R 0 (P₀ + j) (D + BitVec.ofNat 64 j) k s :=
  ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.1, h.1.2.1⟩

omit L in
theorem PartMid.absIn {j k : Nat} {s : State}
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    AbsIn Ctx St W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (List.replicate (P₀ + j) 0)
      (D + BitVec.ofNat 64 j) k s :=
  ⟨h.1.1, h.2.1, h.2.2.1, by rw [List.length_replicate]; exact h.2.2.2, h.1.2.2.1.ok, rfl⟩

omit L in
/-- The data reloaded. -/
theorem partMid_load {j k : Nat} {s : State} (h : PartMid Ctx St W SP R P₀ D j k s) :
    WP isa (.block streamLoad) s fun s' => PartMid Ctx St W SP R P₀ D j k s' ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 j ∧ s'.gpr .rbp = BitVec.ofNat 64 k ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) := by
  obtain ⟨he, hR, hd, hdat, hlen, htl⟩ := h
  obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok he hdat hlen htl
  rw [toNat_mod16] at hbx
  exact WP.of_runBlock ⟨s', run, ⟨he.keep (load_env hg) hrd hwr, hm ▸ hR, hd.of_eq hrd hwr, hm ▸ hdat, hm ▸ hlen,
    hm ▸ htl⟩, h12, hbp, hbx⟩

/-- After `crypt`. -/
theorem partMid_crypt {j k : Nat} {s : State}
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    WP isa (crypt v.callees) s (PartMid Ctx St W SP R P₀ D j k) := by
  have hd := h.1.2.2.1
  refine WP.mono (WP.with_rdwr (crypt_ok v L (PartMid.crIn h))) fun s' ⟨co, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hd.ok h₁ (by omega))
      (by decide)
  exact ⟨co.env, co.rounds, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2.2⟩

/-- After `absorb`. -/
theorem partMid_absorb {j k : Nat} {s : State}
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    WP isa (absorb v.callees 16) s (PartMid Ctx St W SP R P₀ D j k) := by
  have hd := h.1.2.2.1
  refine WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) (PartMid.absIn h))) fun s' ⟨ao, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega))
      (by decide)
  exact ⟨ao.env, rounds_frame ao.frame (slot_absFrame L (by decide) (by decide)) h.1.2.1, hd.of_eq hrd hwr,
    by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2.2⟩

/-- `crypt` and `absorb` over the same part of the data in both runs. -/
theorem part_rel (enc : Bool) {j k : Nat} :
    RelCT isa (fun s₁ s₂ => PartPre Ctx St W SP R P₀ enc D n j k s₁ ∧ PartPre Ctx St W SP R P₀ enc D n j k s₂)
      (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
        else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) fun _ _ => True := by
  let M : State → Prop := fun s => PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧
    s.gpr .rbp = BitVec.ofNat 64 k ∧ s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)
  have cr : RelCT isa (fun s₁ s₂ => M s₁ ∧ M s₂) (crypt v.callees) fun _ _ => True :=
    (crypt_rel v L (icb₁ := 0) (icb₂ := 0) rfl).mono (fun _ _ h => ⟨PartMid.crIn h.1, PartMid.crIn h.2⟩)
      fun _ _ h => h
  have ab : RelCT isa (fun s₁ s₂ => M s₁ ∧ M s₂) (absorb v.callees 16) fun _ _ => True :=
    (RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => absorb_rel v L (yo := 16) (.inr rfl) (H₁ := H₁) (H₂ := H₂)
      (x₁ := List.replicate (P₀ + j) 0) (x₂ := List.replicate (P₀ + j) 0) rfl).mono
      (fun _ _ h => ⟨_, _, PartMid.absIn h.1, PartMid.absIn h.2⟩) fun _ _ h => h
  have ld := rel_both (rel_envT (F := PartMid Ctx St W SP R P₀ D j k) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => partMid_load h) (fun _ h => partMid_load h)
  cases enc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (RelCT.seq (rel_both ab (fun _ h => partMid_absorb v L h) (fun _ h => partMid_absorb v L h))
      (RelCT.seq ld cr)).mono (fun _ _ h => ⟨h.1.mid, h.2.mid⟩) fun _ _ h => h
  · simp only [↓reduceIte]
    exact (RelCT.seq (rel_both cr (fun _ h => partMid_crypt v L h) (fun _ h => partMid_crypt v L h))
      (RelCT.seq ld ab)).mono (fun _ _ h => ⟨h.1.mid, h.2.mid⟩) fun _ _ h => h

end

/-! ## The whole blocks -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {R P₀ : Nat} {D : Addr} {n : Nat}
include L

theorem callBlocks_rel (enc : Bool) {D' : Addr} {n' q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn Ctx St W SP R D' n' q s₁ ∧ ObIn Ctx St W SP R D' n' q s₂)
      (.frame (.push [.rax]) (.call (if enc then v.callees.enc else v.callees.dec).name
        (if enc then v.callees.enc else v.callees.dec).code) (.pop .rax 1)) fun _ _ => True := by
  cases enc
  · exact obFrameD_rel v L
  · exact obFrameE_rel v L

/-- Before `streamBlocks`: what `blocks_ok` needs. -/
def BPre (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j : Nat) (s : State) : Prop :=
  SI Ctx St W SP R P₀ enc D n j s ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- `streamBlocks`, with the same number of whole blocks, at the same
address, in both runs. -/
theorem blocks_rel (enc : Bool) {j : Nat} :
    RelCT isa (fun s₁ s₂ => BPre Ctx St W SP R P₀ enc D n j s₁ ∧ BPre Ctx St W SP R P₀ enc D n j s₂)
      (streamBlocks (if enc then v.callees.enc else v.callees.dec)) fun _ _ => True := by
  -- After the number of whole blocks: what the call's arguments need.
  let G₁ : State → Prop := fun s => s.zf = some (decide ((n - j) / 16 = 0)) ∧ Env Ctx St W SP s ∧
    ((n - j) / 16 ≠ 0 → WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s (ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16)))
  have g₁ : ∀ s, BPre Ctx St W SP R P₀ enc D n j s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),
      .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) s G₁ := fun s h => by
    obtain ⟨⟨H, icb, x₀, m₀, K, hx, I⟩, hdat, hlen, htl⟩ := h
    have hlt := I.data.ok.lt
    have hj := I.le
    refine WP.mono (sb1_ok (L := n - j) (by omega) I.env hlen) fun s₁ ⟨r₁, z₁, g, m₁, rd₁, wr₁⟩ => ⟨z₁, ?_, fun hz => ?_⟩
    · exact I.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd₁ wr₁
    have he₁ : Env Ctx St W SP s₁ := I.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd₁ wr₁
    refine WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ (m₁ ▸ I.rounds K) (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    exact ⟨he₂, (I.data.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁), by omega, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s⟩
  have a := rel_both (rel_envT (F := BPre Ctx St W SP R P₀ enc D n j) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) g₁ g₁
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s (ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16)) :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := rel_both (rel_envT (F := fun s => G₁ s ∧ s.zf = some false) [] (fun _ h => h.1.2.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩) hw₂ hw₂
  have hw₃ : ∀ s, ObIn Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16) s →
      WP isa (.frame (.push [.rax]) (.call (if enc then v.callees.enc else v.callees.dec).name
        (if enc then v.callees.enc else v.callees.dec).code) (.pop .rax 1)) s (Env Ctx St W SP) := fun s h =>
    WP.mono (callBlocks_ok v L enc h) fun _ o => h.env.of_saved o.1 o.2.1 o.2.2.1
  have c := rel_both (callBlocks_rel v L enc) hw₃ hw₃
  have d := rel_envT (F := Env Ctx St W SP) (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax),
      .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx),
      .mov .rcx (.mem (at_ .r15 dataO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 dataO) .rcx,
      .mov .rcx (.mem (at_ .r15 tlenO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 tlenO) .rcx])
    [] (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩
  unfold streamBlocks
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  exact (RelCT.seq b (RelCT.seq c d)).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩)
    fun _ _ h => h

end

/-! ## The start -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
/-- Whether there is text yet. -/
theorem tl_ok {P : Nat} (hP : P < 2 ^ 64) {s : State} (he : Env Ctx St W SP s)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s fun s' =>
      s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' ∧ s'.mem = s.mem := by
  have r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (P = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  exact WP.of_runBlock ⟨s₂, run₂, hz₂, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂, hm₂⟩

omit L in
/-- The length of the additional data modulo 16. -/
theorem al_ok {aL : Nat} {s : State} (he : Env Ctx St W SP s)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s' := by
  have r₃ := he.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hand := and15 (BitVec.ofNat 64 aL)
  rw [imm_eq (by decide), toNat_mod16] at hand
  obtain ⟨s₃, run₃, hbx₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hal, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  exact WP.of_runBlock ⟨s₃, run₃, hbx₃, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃⟩

/-- The additional data padded if there is no text yet, in both runs. -/
theorem start_rel {aL P : Nat} (hP : P < 2 ^ 64) {F : State → Prop} (hF : ∀ s, F s → Env Ctx St W SP s ∧
      s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P ∧
      s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) fun _ _ => True := by
  let G : State → Prop := fun s' => s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' ∧
    s'.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  have g : ∀ s, F s → WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s G :=
    fun s h => WP.mono (tl_ok hP (hF s h).1 (hF s h).2.1) fun s' ⟨z, e, m⟩ => ⟨z, e, by rw [m]; exact (hF s h).2.2⟩
  have a := rel_both (rel_envT (F := F) [] (fun s h => (hF s h).1) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g g
  have b := rel_both (rel_envT (F := fun s => G s ∧ s.zf = some true) [] (fun _ h => h.1.2.1)
      (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
    (fun s h => al_ok h.1.2.1 h.1.2.2) (fun s h => al_ok h.1.2.1 h.1.2.2)
  have c := (flush_rel v L (yo := 16) (.inr rfl)).mono (P' := fun (s₁ s₂ : State) =>
      (s₁.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₁) ∧
      (s₂.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₂))
    (fun _ _ h => ⟨h.1.2, h.2.2, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]⟩) fun _ _ h => h
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) ?_ (RelCT.block_nil fun _ _ _ => trivial))
  unfold firstFlush
  exact (RelCT.seq b c).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩) fun _ _ h => h

end

/-! ## All of `streamText` -/

/-- Before `streamText`: what the entry leaves, in each run. -/
structure TPre (Ctx St W SP : Addr) (R aL P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW Ctx St W SP s D n
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  K : SCtx Ctx St W SP R (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) D n s.mem
  hP : P₀ < 2 ^ 64

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {R aL P₀ : Nat} {D : Addr} {n : Nat}

/-- What `part_ok` does to `PartPre`. -/
theorem si_part (enc : Bool) {j k : Nat} {s : State} (h : PartPre Ctx St W SP R P₀ enc D n j k s) :
    WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
      else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s fun s' =>
      SI Ctx St W SP R P₀ enc D n (j + k) s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  let ⟨hs, hk, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  hs.lift fun K hx I => part_ok v K enc I hx hk h12 hbp hbx hdat hlen htl

include L in
/-- `streamText` in two runs, with the same data and lengths. -/
theorem streamText_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TPre Ctx St W SP R aL P₀ D n s₁ ∧ TPre Ctx St W SP R aL P₀ D n s₂)
      (streamText v.callees enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  generalize hk : headLen P₀ n = k
  have hkw := headLen_whole P₀ n
  have hkn := headLen_le P₀ n
  rw [hk] at hkw hkn
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre Ctx St W SP R aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, TPre Ctx St W SP R aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbp h.rbp h.data.ok.lt
    exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r _ => by rw [hg]) hrd hwr, h.data.of_eq hrd hwr,
      by rw [hg]; exact h.rbp, hm ▸ h.alen, hm ▸ h.tlen, hm ▸ h.dat, hm ▸ h.len, by rw [hm]; exact h.K, h.hP⟩, hz⟩
  have a := rel_both (rel_envT (F := TPre Ctx St W SP R aL P₀ D n) [.rbp] (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  -- The start.
  let F₀ : State → Prop := fun s => T1 s ∧ s.zf = some false
  let G₂ : State → Prop := fun s => SI Ctx St W SP R P₀ enc D n 0 s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₂ : ∀ s, F₀ s → WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s G₂ := fun s h => by
    have t := h.1.1
    refine WP.mono (start_ok v t.K enc (Hyp := False) (icb := 0) t.env rfl t.data (a := List.replicate aL 0)
      (c₀ := List.replicate P₀ 0) (by simpa using t.hP) (by simpa using t.alen) (by simpa using t.tlen)
      False.elim False.elim) fun s' ⟨I, sl⟩ => ?_
    simp only [List.length_replicate] at I
    refine ⟨⟨_, _, _, _, t.K, ?_, I⟩, by rw [sl 200 (by decide) (by decide)]; exact t.dat,
      by rw [sl 208 (by decide) (by decide)]; exact t.len, by rw [sl 192 (by decide) (by decide)]; exact t.tlen⟩
    have := Proof.Gcm.length_pad_mod aL
    simp only [List.length_append, List.length_replicate, Proof.Gcm.length_zeros]; omega
  have b := rel_both (start_rel v L (aL := aL) (F := F₀) hP (fun s h => ⟨h.1.1.env, h.1.1.tlen, h.1.1.alen⟩))
    g₂ g₂
  -- The data loaded.
  let G₃ : State → Prop := fun s => SI Ctx St W SP R P₀ enc D n 0 s ∧ s.gpr .r12 = D ∧
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
  have pp : ∀ s, G₃ s → PartPre Ctx St W SP R P₀ enc D n 0 n s := fun s h =>
    ⟨h.1, by omega, by simp [h.2.1], h.2.2.1, by rw [h.2.2.2.1, Nat.add_zero], by rw [h.2.2.2.2.1]; simp,
      h.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2, Nat.add_zero]⟩
  have gsm : ∀ s, PartPre Ctx St W SP R P₀ enc D n 0 n s →
      WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
        else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  have sm := (rel_both (part_rel v L enc (j := 0) (k := n)) gsm gsm).mono (P' := fun (s₁ s₂ : State) =>
    ((G₃ s₁ ∧ s₁.cf = some (decide (n < 256))) ∧ (G₃ s₂ ∧ s₂.cf = some (decide (n < 256)))) ∧
      isa.eval .b s₁ = some true) (fun _ _ h => ⟨pp _ h.1.1.1, pp _ h.1.2.1⟩) fun _ _ h => h
  -- The head's length.
  let G₄ : State → Prop := fun s => PartPre Ctx St W SP R P₀ enc D n 0 k s ∧
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
        exact L.w_w (.inl (by omega)) (by omega) (by decide)) (by decide)
    refine ⟨⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (by decide) (by decide) f,
      by omega, by simp [hg .r12 (by decide) (by decide), h12], hbp',
      by rw [hg .rbx (by decide) (by decide), hbx, Nat.add_zero], by rw [rd 200 (by decide) (by decide), hdat]; simp, hl,
      by rw [rd 192 (by decide) (by decide), htl, Nat.add_zero]⟩, ha⟩
  have d := rel_both (rel_envT (F := G₃) [.rbx, .rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₄ g₄
  -- The head.
  let G₅ : State → Prop := fun s => SI Ctx St W SP R P₀ enc D n k s ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀ ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₅ : ∀ s, G₄ s → WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
      else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s G₅ := fun s h => by
    obtain ⟨hp, ha⟩ := h
    have ⟨_, _, _, _, _, hdat, hlen, htl⟩ := hp
    refine WP.mono (si_part v enc hp) fun s' ⟨hs, sl⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.zero_add] at hs; exact hs
    · rw [sl 208 (by decide) (by decide)]; exact hlen
    · rw [sl 200 (by decide) (by decide), hdat]; simp
    · rw [sl 192 (by decide) (by decide), htl, Nat.add_zero]
    · rw [sl 216 (by decide) (by decide)]; exact ha
  have e := rel_both ((part_rel v L enc (j := 0) (k := k)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) g₅ g₅
  -- Past the head.
  have g₆ : ∀ s, G₅ s → WP isa (.block streamNext) s (BPre Ctx St W SP R P₀ enc D n k) := fun s h => by
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
  let G₇ : State → Prop := fun s => SI Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - k) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (k + 16 * ((n - k) / 16)))
  have g₇ : ∀ s, BPre Ctx St W SP R P₀ enc D n k s → WP isa (streamBlocks (if enc then v.callees.enc
      else v.callees.dec)) s G₇ := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := hs
    exact WP.mono (blocks_ok v K enc I hx hdat hlen htl (fun hq => hkw.resolve_left (by omega)))
      fun s' ⟨I', d', l', t'⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, d', l', t'⟩
  have g := rel_both (blocks_rel v L enc) g₇ g₇
  -- The rest.
  have g₈ : ∀ s, G₇ s → WP isa (.block streamLoad) s
      (PartPre Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16)) := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok hs.env hdat hlen htl
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, hs.regs (load_env hg) hm hrd hwr, by omega, h12, hbp, hbx, hm ▸ hdat,
      hm ▸ hlen, hm ▸ htl⟩
  have i := rel_both (rel_envT (F := G₇) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₈ g₈
  have g₉ : ∀ s, PartPre Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16) s →
      WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
        else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  have j := rel_both (part_rel v L enc) g₉ g₉
  simp only [streamText]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelCT.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  have big := (RelCT.seq d (RelCT.seq e (RelCT.seq f (RelCT.seq g (RelCT.seq i j))))).mono
    (P' := fun (s₁ s₂ : State) => ((G₃ s₁ ∧ s₁.cf = some (decide (n < 256))) ∧ (G₃ s₂ ∧ s₂.cf = some (decide (n < 256)))) ∧
      isa.eval .b s₁ = some false) (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  refine rel_reassoc2 ((RelCT.seq b (RelCT.seq c (RelCT.seq cs
    (RelCT.ite (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm) sm big)))).mono
    (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)

end

/-! ## The functions -/

/-- After the entry, what `streamText` needs. -/
theorem cryptEntry_tpre {s : State} (hp : Proof.AesGcm.streamCryptPre s) :
    WP isa (.block cryptEntry) s (TPre (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r8).toNat (s.gpr .r9) (stackArg s 0).toNat) := by
  have C := CryptCtx.of hp
  refine WP.mono (cryptEntry_ok rfl rfl rfl rfl rfl rfl C.perm C.ww C.args C.dA C.rounds) fun s₁ E => ?_
  exact ⟨E.env, C.data.of_eq E.rd E.wr, E.rbp, by rw [E.alen, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.tlen, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    ⟨C.lay, E.rounds, rfl, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24⟩, (s.gpr .r8).isLt⟩

theorem stream_pub {s₀ s₀' : State} (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem stream_rel (v : GcmImpl) (enc : Bool) {s₀ s₀' : State} (hp : Proof.AesGcm.streamCryptPre s₀)
    (hp' : Proof.AesGcm.streamCryptPre s₀') (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block restore))) fun _ _ => True := by
  have L := (CryptCtx.of hp).lay
  have hE₂ := cryptEntry_tpre hp'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := cryptEntry_tpre hp
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₉
    (CryptCtx.of hp).args.2 (CryptCtx.of hp').args.2 ⟨_, by taint_decide⟩ hE₁ hE₂
    ((streamText_rel v L enc (s₀.gpr .r8).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamEncryptX86_64.pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v true hp hp' hq

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamDecryptX86_64.pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v false hp hp' hq

end VG.Proof.AesGcm.X86_64
