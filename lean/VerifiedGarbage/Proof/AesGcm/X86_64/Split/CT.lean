module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.FinCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.FinCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM `seal_split` on x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: `prefix`'s blocks are
checked by the taint analysis from `W` (and the pointers they address), its
branches are on the number of whole blocks and of bytes left of `src_len`,
which is public, and its call gets the same public arguments in both runs
(`prefix_ct`); `body` runs `oneBlocks` and the end as `seal` does, a word
lower (`body_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn step skip_rel copy_check)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

theorem preTest_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.preTest) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem preArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15]) (.block SealSplit.preArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem copyArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.copyArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem rest_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.rest) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem fixTlen_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.fixTlen) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## `prefix`, in each run -/

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ : State} (h : PP M Ctx W SP D S R n sl σ)
include h

/-- After `preTest`. -/
def G₁ (Ctx W SP : Addr) (sl : Nat) (σ s : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ s.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧
    s.zf = some (decide (sl / 16 = 0)) ∧ s.mem = σ.mem ∧ s.rd = σ.rd ∧ s.wr = σ.wr

/-- After `preArgs`. -/
def G₂ (Ctx W SP D S : Addr) (R sl : Nat) (σ s : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ s.gpr .rdi = Ctx ∧ s.gpr .rsi = BitVec.ofNat 64 R ∧
    s.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48 ∧
    s.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16 ∧ s.gpr .r8 = S ∧
    s.gpr .r9 = BitVec.ofNat 64 (sl / 16) ∧ s.gpr .r10 = BitVec.ofNat 64 (sl / 16) ∧ s.gpr .r11 = D ∧
    s.gpr .rax = W + BitVec.ofNat 64 448 ∧ s.mem = σ.mem ∧ s.rd = σ.rd ∧ s.wr = σ.wr

/-- After `copyArgs`. -/
def G₃ (Ctx W SP D S : Addr) (R sl : Nat) (σ s : State) : Prop :=
  Mid2 Ctx W SP D S R sl σ s ∧ s.gpr .rcx = BitVec.ofNat 64 (sl % 16) ∧
    s.gpr .rsi = S + BitVec.ofNat 64 (16 * (sl / 16)) ∧ s.gpr .rdi = D + BitVec.ofNat 64 (16 * (sl / 16)) ∧
    s.zf = some (decide (sl % 16 = 0))

/-- After the bytes left copied: what the end needs. -/
def G₄ (Ctx W SP : Addr) (σ s : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ s.rd = σ.rd ∧ s.wr = σ.wr

theorem g₁_wp : WP isa (.block SealSplit.preTest) σ (G₁ Ctx W SP sl σ) := by
  have := h.sl_le; have := h.data.ok.lt
  refine WP.mono (pre1_ok (sl := sl) (by omega) h.env h.slen) fun s₁ ⟨ax₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  exact ⟨h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁, ax₁, zf₁, m₁, rd₁, wr₁⟩

theorem g₂_wp {s : State} (g : G₁ Ctx W SP sl σ s) : WP isa (.block SealSplit.preArgs) s (G₂ Ctx W SP D S R sl σ) := by
  obtain ⟨he, ax, -, m, rd, wr⟩ := g
  refine WP.mono (pre2_ok (R := R) (D := D) (S := S) he (by rw [m]; exact h.rounds) (by rw [m]; exact h.dat)
    (by rw [m]; exact h.src)) fun s₂ ⟨di, si, dx, cx, r8, r9, r10, r11, a, g₂, m₂, rd₂, wr₂⟩ => ?_
  exact ⟨he.keep g₂ rd₂ wr₂, di, si, dx, cx, r8, by rw [r9, ax], by rw [r10, ax], r11, a, m₂.trans m, rd₂.trans rd,
    wr₂.trans wr⟩

omit h in
theorem mid2_zero {s : State} (g : G₁ Ctx W SP sl σ s) (h0 : sl / 16 = 0) : Mid2 Ctx W SP D S R sl σ s := by
  obtain ⟨he, -, -, m, rd, wr⟩ := g
  refine ⟨he, rd, wr, by rw [m]; exact Frame.refl _ _, ?_, ?_, ?_⟩
  · rw [h0, m]; rfl
  · rw [h0, m]; rfl
  · rw [h0, m]; rfl

theorem mid2_call_wp (T : BlkToFn M) {s : State} (g : G₂ Ctx W SP D S R sl σ s) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) s
      (Mid2 Ctx W SP D S R sl σ) := by
  obtain ⟨he, di, si, dx, cx, r8, r9, r10, r11, ax, m, rd, wr⟩ := g
  refine WP.mono (preCall_ok h T (q := sl / 16) (by omega) he.rsp rd wr m di si dx cx r8 r9 r10 r11 ax)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans rd, wr₃.trans wr, by rw [m] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

theorem g₃_wp {s : State} (H : Mid2 Ctx W SP D S R sl σ s) :
    WP isa (.block SealSplit.copyArgs) s (G₃ Ctx W SP D S R sl σ) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s.mem.readW (W + BitVec.ofNat 64 d) 64 = σ.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => H.frame.readW (Region.contains_self _ _) (slot_disj h (q := sl / 16) (by omega) h₁ h₂) (by decide)
  refine WP.mono (pre3_ok (D := D) (S := S) (sl := sl) (by omega) H.env (by rw [kp 200 (by decide) (by decide)]; exact h.dat)
    (by rw [kp 224 (by decide) (by decide)]; exact h.src) (by rw [kp 192 (by decide) (by decide)]; exact h.slen))
    fun s₃ ⟨cx₃, si₃, di₃, zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  exact ⟨⟨H.env.keep g₃ rd₃ wr₃, rd₃.trans H.rd, wr₃.trans H.wr, by rw [m₃]; exact H.frame, by rw [m₃]; exact H.blocks,
    by rw [m₃]; exact H.ctr, by rw [m₃]; exact H.y⟩, cx₃, si₃, di₃, zf₃⟩

theorem g₄_copy_wp (h0 : sl % 16 ≠ 0) {s : State} (g : G₃ Ctx W SP D S R sl σ s) :
    WP isa copyLoop s (G₄ Ctx W SP σ) := by
  obtain ⟨H, cx₃, si₃, di₃, -⟩ := g
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have e1 : 16 * (sl / 16) + sl % 16 ≤ sl := by omega
  have e2 : 16 * (sl / 16) + sl % 16 ≤ n := by omega
  have sl64 : sl < 2 ^ 64 := by omega
  have c1 : Covers [⟨S + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] (s.rd ++ s.wr) := by
    rw [H.rd, H.wr]; exact covers_off' h.srcCov e1 sl64
  have c2 : Covers [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] s.wr := by
    rw [H.wr]; exact covers_off' h.data.wr e2 hn
  have hlp : LoopPre s (S + BitVec.ofNat 64 (16 * (sl / 16))) (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) :=
    ⟨si₃, di₃, cx₃, by omega, by omega, c1, c2,
      (h.sD.sub_left (Offset.sub_base S (by omega))).sub_right (Offset.sub_base D (by omega))⟩
  refine WP.mono (copyLoop_ok s hlp) fun s₄ ⟨_, g₄, rd₄, wr₄⟩ => ⟨H.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) rd₄ wr₄,
    rd₄.trans H.rd, wr₄.trans H.wr⟩

omit h in
/-- `rest` runs from any state with the environment. -/
theorem rest_runs {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) :
    WP isa (.block SealSplit.rest) s fun _ => True := by
  have r192 := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r208 := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have r200 := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have w216 := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have w208 := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have w200 := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  unfold SealSplit.rest
  exact WP.of_runBlock ⟨_, by xrun [he.r15, r192, r208, r200, w216, w208, w200], trivial⟩

end

/-! ## `prefix`, in two runs -/

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP M Ctx W SP D S R n sl σ) (h' : PP M Ctx W SP D S R n sl σ')
include h h'

/-- The call of `vg_aes_gcm_encrypt_blocks_to`, in two runs: the same public
arguments. -/
theorem call_rel (T : BlkToFn M) :
    RelCT isa (fun s₁ s₂ => G₂ Ctx W SP D S R sl σ s₁ ∧ G₂ Ctx W SP D S R sl σ' s₂)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq : 16 * (sl / 16) ≤ sl := Nat.mul_div_le _ _
  refine RelCT.frame (fun _ _ g => by rw [g.1.1.rsp, g.2.1.rsp])
    (RelCT.callEx (k := Proof.AesGcm.encryptBlocksToX86_64M M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, ⟨g₁, g₂⟩, rfl, rfl⟩ := hab
  obtain ⟨he₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, r11₁, ax₁, m₁, rd₁, wr₁⟩ := g₁
  obtain ⟨he₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, m₂, rd₂, wr₂⟩ := g₂
  obtain ⟨p₁, cr₁, cw₁, gU₁, hU₁, a0₁, a1₁, a2₁⟩ :=
    callIn h hq he₁.rsp rd₁ wr₁ m₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ r11₁ ax₁
  obtain ⟨p₂, cr₂, cw₂, gU₂, hU₂, a0₂, a1₂, a2₂⟩ :=
    callIn h' hq he₂.rsp rd₂ wr₂ m₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ r11₂ ax₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, cr₁, cw₁, cr₂, cw₂, by rw [pushed_rsp, pushed_rsp, he₁.rsp, he₂.rsp]⟩
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPub, Proof.AesGcm.arg, callU] at *
  simp only [gU₁ _ (by decide : Reg.rdi ≠ .rsp), gU₁ _ (by decide : Reg.rsi ≠ .rsp),
    gU₁ _ (by decide : Reg.rdx ≠ .rsp), gU₁ _ (by decide : Reg.rcx ≠ .rsp), gU₁ _ (by decide : Reg.r8 ≠ .rsp),
    gU₁ _ (by decide : Reg.r9 ≠ .rsp), gU₂ _ (by decide : Reg.rdi ≠ .rsp), gU₂ _ (by decide : Reg.rsi ≠ .rsp),
    gU₂ _ (by decide : Reg.rdx ≠ .rsp), gU₂ _ (by decide : Reg.rcx ≠ .rsp), gU₂ _ (by decide : Reg.r8 ≠ .rsp),
    gU₂ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂, hU₁, hU₂,
    a0₁, a0₂, a1₁, a1₂, a2₁, a2₂, and_self]

/-- `prefix`, in two runs. -/
theorem prefix_ct (T : BlkToFn M) :
    RelCT isa (fun a b => a = σ ∧ b = σ') (SealSplit.prefix T.fn) fun _ _ => True := by
  have r15 : ∀ {s₁ s₂ : State}, Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ → Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ →
      ∀ r ∈ [Reg.r15], s₁.gpr r = s₂.gpr r := fun e₁ e₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁.r15, e₂.r15]
  unfold SealSplit.prefix
  refine RelCT.seq (step [.r15] preTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := G₁ Ctx W SP sl σ) (G₂ := G₁ Ctx W SP sl σ')
    (fun _ _ g => by obtain ⟨rfl, rfl⟩ := g; exact r15 h.env h'.env) (fun _ _ g => g)
    (fun _ hs => by rw [hs]; exact g₁_wp h) (fun _ hs => by rw [hs]; exact g₁_wp h')) ?_
  refine RelCT.seq (R := fun a b => Mid2 Ctx W SP D S R sl σ a ∧ Mid2 Ctx W SP D S R sl σ' b)
    (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.2.1, g.2.2.2.1]) ?_ ?_) ?_
  · refine StreamTo.RelCT.of_imp (sl / 16 = 0) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.2.2.1] at e; simpa using e) fun h0 => ?_
    exact skip_rel fun _ _ g => ⟨mid2_zero g.1.1 h0, mid2_zero g.1.2 h0⟩
  · refine RelCT.seq (step [.r13, .r14, .r15] preArgs_check (F₁ := G₁ Ctx W SP sl σ) (F₂ := G₁ Ctx W SP sl σ')
      (fun _ _ g r hr => by
        have e₁ := g.1.1.1; have e₂ := g.1.2.1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e₁.r13, e₂.r13]
        · rw [e₁.r14, e₂.r14]
        · rw [e₁.r15, e₂.r15])
      (fun _ _ g => g.1) (fun _ g => g₂_wp h g) (fun _ g => g₂_wp h' g)) ?_
    exact (rel_wp (call_rel h h' T) (fun _ _ g => g) (fun _ g => mid2_call_wp h T g)
      (fun _ g => mid2_call_wp h' T g)).mono (fun _ _ g => g) fun _ _ g => g.2
  refine RelCT.seq (step [.r15] copyArgs_check (F₁ := Mid2 Ctx W SP D S R sl σ) (F₂ := Mid2 Ctx W SP D S R sl σ')
    (fun _ _ g => r15 g.1.env g.2.env) (fun _ _ g => g) (fun _ g => g₃_wp h g) (fun _ g => g₃_wp h' g)) ?_
  refine RelCT.seq (R := fun a b => G₄ Ctx W SP σ a ∧ G₄ Ctx W SP σ' b)
    (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.2.2.2, g.2.2.2.2.2]) ?_ ?_) ?_
  · exact skip_rel fun _ _ g => ⟨⟨g.1.1.1.env, g.1.1.1.rd, g.1.1.1.wr⟩, ⟨g.1.2.1.env, g.1.2.1.rd, g.1.2.1.wr⟩⟩
  · refine StreamTo.RelCT.of_imp (sl % 16 ≠ 0) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.2.2.2.2] at e; simpa using e) fun h0 => ?_
    refine step [.rsi, .rdi, .rcx] copy_check (F₁ := G₃ Ctx W SP D S R sl σ) (F₂ := G₃ Ctx W SP D S R sl σ')
      (fun _ _ g r hr => ?_) (fun _ _ g => g.1) (fun _ g => g₄_copy_wp h h0 g) (fun _ g => g₄_copy_wp h' h0 g)
    obtain ⟨⟨-, cx₁, si₁, di₁, -⟩, ⟨-, cx₂, si₂, di₂, -⟩⟩ := g.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [si₁, si₂]
    · rw [di₁, di₂]
    · rw [cx₁, cx₂]
  exact (step [.r15] rest_check (F₁ := G₄ Ctx W SP σ) (F₂ := G₄ Ctx W SP σ') (fun _ _ g => r15 g.1.1 g.2.1)
    (fun _ _ g => g) (fun _ g => rest_runs g.1) (fun _ g => rest_runs g.1)).mono (fun _ _ g => g) fun _ _ _ => trivial

end

/-! ## `body`, in two runs -/

section
variable {M : CtxMode} {Ctx W SP A D : Addr} {R al n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
  (kw : (below SP 56).Disjoint ⟨W, 2560⟩) (kd : (below SP 56).Disjoint ⟨D, n⟩)
  (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (ka : (below SP 56).Disjoint ⟨A, al⟩) (sp : 56 ≤ SP.toNat)
include L kw kd kM ka sp

omit L in
/-- What `oneBlocks` needs, a word lower. -/
theorem oneS_pushed {T : Option Nat} {s : State} (h : OneS M Ctx W SP R A al D n T s) :
    OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al D n T (pushed [Reg.rax] s) := by
  obtain ⟨f₀, -⟩ := push_frame h.env (by omega)
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have one : ∀ {r : Region}, (below SP 56).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  have rW : ∀ d, d + 8 ≤ 2560 →
      (pushed [Reg.rax] s).mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₀.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (one (kw.sub_right (Lay.wSub hd))) (by decide)
  have b := below8_sub (SP := SP) (k := 8) (by decide)
  exact ⟨env_pushed h.env, ⟨by rw [rW 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [rW 232 (by decide)]; exact h.aad, by rw [rW 184 (by decide)]; exact h.alen,
    by rw [rW 200 (by decide)]; exact h.dat, by rw [rW 208 (by decide)]; exact h.len,
    ⟨by rw [pushed_rd, pushed_wr]; exact covers_ins h.dA.rd, h.dA.lt, h.dA.wrap, h.dA.st, h.dA.w, ka.sub_left b⟩,
    ⟨⟨by rw [pushed_rd, pushed_wr]; exact covers_ins h.dD.ok.rd, h.dD.ok.lt, h.dD.ok.wrap, h.dD.ok.st, h.dD.ok.w,
      kd.sub_left b⟩, by rw [pushed_wr]; exact covers_tail h.dD.wr, h.dD.ctx⟩,
    fun N hN => by rw [rW 192 (by decide)]; exact h.tlen N hN,
    ⟨h.ext.w, h.ext.cs, h.ext.cw, h.ext.cd, kM.sub_left (below8_sub (by decide)),
      by rw [pushed_rd, pushed_wr]; exact covers_ins h.ext.cov, M.frame f₀ (one kM) h.ext.w h.ext.ok⟩⟩

omit L kd kM ka sp in
/-- What is at `auxO`, after the push. -/
theorem aux_pushed {N : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (sp8 : 8 ≤ SP.toNat)
    (h : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) :
    (pushed [Reg.rax] s).mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N := by
  obtain ⟨f₀, -⟩ := push_frame he sp8
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  rw [f₀.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((kw.sub_left b8).sub_right (Lay.wSub (by decide))).symm) (by decide), h]

/-- `body`, in two runs, from states holding the total length `N` at `auxO`. -/
theorem body_ct (B : BlkFn M) {fin : Prog isa} (hfin : FinRel M fin) {N : Nat} :
    RelCT isa (fun s₁ s₂ =>
        (OneS M Ctx W SP R A al D n none s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) ∧
        (OneS M Ctx W SP R A al D n none s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N))
      (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1))
      fun _ _ => True := by
  have kc : (below SP 56).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix M.ge)
  have L' := lay_pushed L kc kw
  have sub : ∀ {k : Nat}, k + 8 ≤ 56 → Region.Sub (below (SP - BitVec.ofNat 64 8) k) (below SP 56) :=
    fun hk => below8_sub hk
  have t_c := kc.sub_left (sub (k := 24) (by decide))
  have t_w := kw.sub_left (sub (k := 24) (by decide))
  have t_d := kd.sub_left (sub (k := 24) (by decide))
  have sp24 : 24 ≤ (SP - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have bl := oneBlocksE_rel B L' (R := R) (A := A) (al := al) (D := D) (n := n) (T := none) t_c t_w t_d sp24
  have hw : ∀ s, OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al D n none s ∧
      s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N →
      WP isa (oneBlocks B.enc) s fun s' =>
        OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
          (some n) s' ∧ s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N :=
    fun s g => oneBlocks_aux L' B t_c t_w t_d sp24 g.1 g.2
  refine StreamTo.RelCT.of_imp ((R = 10 ∨ R = 12 ∨ R = 14) ∧ (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩ ∧ n < 2 ^ 64)
    (fun _ _ g => ⟨g.1.1.rounds.2, g.1.1.dD.ok.w, g.1.1.dD.ok.lt⟩) fun ⟨hR, hDW, hn⟩ => ?_
  have pre : ∀ s, OneS M Ctx W SP R A al D n none s ∧ s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N →
      OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al D n none (pushed [Reg.rax] s) ∧
        (pushed [Reg.rax] s).mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N :=
    fun s g => ⟨oneS_pushed kw kd kM ka sp g.1, aux_pushed kw g.1.env (by omega) g.2⟩
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ g => by rw [g.1.1.env.rsp, g.2.1.env.rsp]) ?_
  refine RelCT.seq (rel_wp (bl.mono (fun _ _ g => by
      obtain ⟨s₁, s₂, ⟨g₁, g₂⟩, rfl, rfl⟩ := g
      exact ⟨(pre _ g₁).1, (pre _ g₂).1⟩) fun _ _ g => g) (fun _ _ g => by
      obtain ⟨s₁, s₂, ⟨g₁, g₂⟩, rfl, rfl⟩ := g
      exact ⟨pre _ g₁, pre _ g₂⟩) hw hw) ?_
  refine RelCT.seq (step [.r15] fixTlen_check
    (fun _ _ g r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [g.2.1.1.env.r15, g.2.2.1.env.r15])
    (fun _ _ g => g.2) (fun _ g => fixTlen_oneS L' g.1 g.2) (fun _ g => fixTlen_oneS L' g.1 g.2)) ?_
  exact hfin L' hR (by omega) (hDW.sub_left (Offset.sub_base D (by omega)))

end

/-- What constant time needs of `seal_split`'s code after `prefix`: what
`body_ct` says of `SealSplit.body`. -/
def BodyRel (M : CtxMode) (body : Prog isa) : Prop :=
  ∀ {Ctx W SP A D : Addr} {R al n : Nat}, Lay Ctx (W + BitVec.ofNat 64 16) W SP →
    (below SP 56).Disjoint ⟨W, 2560⟩ → (below SP 56).Disjoint ⟨D, n⟩ → (below SP 56).Disjoint ⟨Ctx, M.len⟩ →
    (below SP 56).Disjoint ⟨A, al⟩ → 56 ≤ SP.toNat → ∀ {N : Nat},
    RelCT isa (fun s₁ s₂ =>
        (OneS M Ctx W SP R A al D n none s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) ∧
        (OneS M Ctx W SP R A al D n none s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N))
      body fun _ _ => True

theorem bodyRel_body {M : CtxMode} (B : BlkFn M) {fin : Prog isa} (hfin : FinRel M fin) :
    BodyRel M (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)) :=
  fun L kw kd kM ka sp _ => body_ct L kw kd kM ka sp B hfin

/-! ## After the entry, in two runs -/

/-- Related pairs of states, one pair at a time. -/
theorem rel_each {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ a b, P a b → RelCT isa (fun x y => x = a ∧ y = b) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- What `body` needs, after code that leaves `PPostG` for `q` blocks. -/
theorem oneS_afterG {M : CtxMode} {Ctx W SP A D S : Addr} {R al n sl q : Nat} {σ s : State}
    (O : OneS M Ctx W SP R A al D n none σ) (h : PP M Ctx W SP D S R n sl σ)
    (Q : PPostG Ctx W SP D S R n sl q σ s) :
    OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * q)) (n - 16 * q) none s := by
  have L := h.lay
  have hq := Q.le
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 200) ∨ (224 ≤ d ∧ d + 8 ≤ 448) →
      s.mem.readW (W + BitVec.ofNat 64 d) 64 = σ.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    Q.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (pp_wG L h.data.ok.w h.kw (.inr hd)) (by decide)
  exact ⟨Q.env, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact O.rounds.1, O.rounds.2⟩,
    by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact O.aad, by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact O.alen,
    Q.dat, Q.len, O.dA.of_eq Q.rd Q.wr, (O.dD.of_eq Q.rd Q.wr).drop hq, (fun _ e => nomatch e),
    (O.ext.keep Q.rd Q.wr Q.frame (pp_outG O.ext.cw O.ext.cd h.kM.symm)).sub (Offset.sub_base D (by omega))⟩

/-- What constant time needs of the code before `body`: from states `prefix`
could start from, with the same public values, the same pieces. -/
def PreRel (M : CtxMode) (pre : Prog isa) : Prop :=
  ∀ {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}, PP M Ctx W SP D S R n sl σ → PP M Ctx W SP D S R n sl σ' →
    RelCT isa (fun a b => a = σ ∧ b = σ') pre fun _ _ => True

theorem prefixRel {M : CtxMode} (T : BlkToFn M) : PreRel M (SealSplit.prefix T.fn) :=
  fun h h' => prefix_ct h h' T

/-- What constant time needs of `seal_split`'s code `mid` after the entry. -/
def MidRel (M : CtxMode) (mid : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat},
    SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl → SplitCtx s₀' Ctx W SP Np A D S T' nl al n sl →
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀' →
    (below SP 56).Disjoint ⟨Ctx, M.len⟩ →
    s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R →
    s₀'.gpr .rdx = Np → (s₀'.gpr .rcx).toNat = nl → (s₀'.gpr .r9).toNat = al → (s₀'.gpr .rsi).toNat = R →
    RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂) mid
      fun _ _ => True

/-- What `body` needs of the additional data's code: what `oneAad` leaves. -/
theorem oneS_ofMid {M : CtxMode} {s₀ s₁ s₂ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    {H : Block} {iv a : List Byte} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R) (M₂ : OneMid s₀ Ctx W SP D n H iv a s₁.mem s₂) :
    OneS M Ctx W SP R A al D n none s₂ :=
  (E.toOneEntry.aadPre C.toOneCtx X hNp hnl hal hR).1.frame C.lay M₂.env (M₂.rd.trans E.rd.symm)
    (M₂.wr.trans E.wr.symm) C.dE (wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₂.fr))

/-- After the entry, `seal_split` up to the tag at `W`, in two runs: additional
data `aadP` that leaves what `oneAad` does (`OneMid`) and takes the same
branches in both, code `pre` that encrypts the first `qf n sl` whole blocks
(`PreOk`, `PreRel`), and `body`. -/
theorem splitRun_rel_of_pre {M : CtxMode} {pre : Prog isa} {qf : Nat → Nat → Nat} (hpre : PreOk M pre qf)
    (hrel : PreRel M pre) (hq : ∀ n sl, sl ≤ n → 16 * qf n sl ≤ n) {body : Prog isa}
    (hbody : BodyRel M body) {aadP : Prog isa} {s₀ s₀' : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (C' : SplitCtx s₀' Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R)
    (ha : RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂) aadP
      fun _ _ => True)
    (hm : ∀ s, SEntry s₀ Ctx W SP A D S n sl s → WP isa aadP s
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem))
    (hm' : ∀ s, SEntry s₀' Ctx W SP A D S n sl s → WP isa aadP s
      (OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) s.mem)) :
    RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (.seq aadP (.seq pre body)) fun _ _ => True := by
  have L := C.lay
  have hsl := C.sl_le
  have hw : ∀ {s₀ : State} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl)
      (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀), s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R →
      (∀ s, SEntry s₀ Ctx W SP A D S n sl s → WP isa aadP s
        (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem)) →
      ∀ s, SEntry s₀ Ctx W SP A D S n sl s →
      WP isa aadP s fun t => OneS M Ctx W SP R A al D n none t ∧ PP M Ctx W SP D S R n sl t :=
    fun C X hNp hnl hal hR hm s E => WP.mono (hm s E) fun _ M₂ =>
      ⟨oneS_ofMid C X E hNp hnl hal hR M₂, PP.ofMid C X kM hR M₂ (mid_slots C E M₂).1 (mid_slots C E M₂).2⟩
  refine RelCT.seq (rel_wp ha (fun _ _ g => g) (hw C X hNp hnl hal hR hm) (hw C' X' hNp' hnl' hal' hR' hm')) ?_
  have sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * qf n sl), n - 16 * qf n sl⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by have := hq n sl hsl; omega)
  let G : State → Prop := fun a =>
    OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * qf n sl)) (n - 16 * qf n sl) none a ∧
      a.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  refine RelCT.seq (R := fun a b => G a ∧ G b)
    (rel_each fun σ σ' g => ?_) (hbody L C.kw (C.kd.sub_right sD') kM C.ka C.sp56 (N := n))
  obtain ⟨-, ⟨O, P⟩, O', P'⟩ := g
  exact (rel_wp (hrel P P') (F₁ := (· = σ)) (F₂ := (· = σ')) (fun _ _ g => g) (G₁ := G) (G₂ := G)
    (fun _ hs => by rw [hs]; exact WP.mono (hpre P) fun _ Q => ⟨oneS_afterG O P Q, Q.aux⟩)
    (fun _ hs => by rw [hs]; exact WP.mono (hpre P') fun _ Q => ⟨oneS_afterG O' P' Q, Q.aux⟩)).mono
    (fun _ _ g => g) fun _ _ g => g.2

/-- After the entry, `seal_split` up to the tag at `W`, in two runs: additional
data `aadP` that leaves what `oneAad` does (`OneMid`) and takes the same
branches in both, `prefix` and `body`. -/
theorem splitRun_rel_of_midB {M : CtxMode} (T : BlkToFn M) {body : Prog isa}
    (hbody : BodyRel M body) {aadP : Prog isa} {s₀ s₀' : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (C' : SplitCtx s₀' Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R)
    (ha : RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂) aadP
      fun _ _ => True)
    (hm : ∀ s, SEntry s₀ Ctx W SP A D S n sl s → WP isa aadP s
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem))
    (hm' : ∀ s, SEntry s₀' Ctx W SP A D S n sl s → WP isa aadP s
      (OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) s.mem)) :
    RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (.seq aadP (.seq (SealSplit.prefix T.fn) body)) fun _ _ => True :=
  splitRun_rel_of_pre (prefixOk T) (prefixRel T) (fun _ _ h => by omega) hbody C C' X X' kM hNp hnl hal hR hNp' hnl'
    hal' hR' ha hm hm'

/-- `splitRun_rel_of_midB` with `SealSplit.body`. -/
theorem splitRun_rel_of_mid (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa}
    (hfr : FinRel M fin) {aadP : Prog isa} {s₀ s₀' : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (C' : SplitCtx s₀' Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R)
    (ha : RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂) aadP
      fun _ _ => True)
    (hm : ∀ s, SEntry s₀ Ctx W SP A D S n sl s → WP isa aadP s
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem))
    (hm' : ∀ s, SEntry s₀' Ctx W SP A D S n sl s → WP isa aadP s
      (OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) s.mem)) :
    RelCT isa (fun s₁ s₂ => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (.seq aadP (.seq (SealSplit.prefix T.fn) (SealSplit.body (v.withBlk B) fin))) fun _ _ => True :=
  splitRun_rel_of_midB T (bodyRel_body B hfr) C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR' ha hm hm'

/-- After the entry, `seal_split` up to the tag at `W`, in two runs. -/
theorem splitRun_rel (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa} (hfr : FinRel M fin) :
    MidRel M (SealSplit.run (v.withBlk B) T.fn fin) := by
  intro s₀ s₀' Ctx W SP Np A D S T' nl al n sl R C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR'
  have L := C.lay
  have a := (oneAad_rel v L C.dE (T := none) (R := R) (Np := Np) (nl := nl)).mono
    (P' := fun (s₁ s₂ : State) => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
    (fun _ _ g => ⟨g.1.toOneEntry.aadPre C.toOneCtx X hNp hnl hal hR,
      g.2.toOneEntry.aadPre C'.toOneCtx X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial
  exact splitRun_rel_of_mid v B T hfr C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR' a
    (fun s E => oneMid_ok v C.toOneCtx E.toOneEntry hNp hnl hal)
    (fun s E => oneMid_ok v C'.toOneCtx E.toOneEntry hNp' hnl' hal')

/-- After the entry, `seal_split` up to the tag copied to `tag`, in two runs. -/
theorem splitTag_rel {M : CtxMode} {mid : Prog isa} (hmid : MidOk M mid) (hrel : MidRel M mid) {s₀ s₀' : State}
    {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (C' : SplitCtx s₀' Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R)
    (hT : s₀.mem.readW (SP + BitVec.ofNat 64 40) 64 = T') (hT' : s₀'.mem.readW (SP + BitVec.ofNat 64 40) 64 = T') :
    RelCT isa (fun s₁ s₂ => True ∧ SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (.seq mid (.block (tagOut (at_ .rsp 40))))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have hW : ∀ {s₀'' : State} (C : SplitCtx s₀'' Ctx W SP Np A D S T' nl al n sl)
      (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀''), s₀''.gpr .rdx = Np →
      (s₀''.gpr .rcx).toNat = nl → (s₀''.gpr .r9).toNat = al → s₀''.mem.readW (SP + BitVec.ofNat 64 40) 64 = T' →
      ∀ s, SEntry s₀'' Ctx W SP A D S n sl s → WP isa mid s (TagAt Ctx (W + BitVec.ofNat 64 16) W SP .rsp 40 T') := by
    intro s₀'' C X h₁ h₂ h₃ hT s E
    have dA : ∀ r ∈ [(⟨W, 2560⟩ : Region), ⟨D, n⟩, below SP 56],
        (⟨SP + BitVec.ofNat 64 40, 8⟩ : Region).Disjoint r := by
      have hs : Region.Sub ⟨SP + BitVec.ofNat 64 40, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 6⟩ := by
        rw [show (40 : Nat) = 8 + 32 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact C.dA.sub_left hs
      · exact C.dAD.sub_left hs
      · exact Offset.disjoint_below SP (n := 56) (d := 40) (k := 8) (by decide)
    exact WP.mono (hmid C X kM E h₁ h₂ h₃) fun _ ⟨he, hrd, hwr, _, f, _⟩ => ⟨he, by
      rw [he.rsp, f.readW (r := ⟨SP + BitVec.ofNat 64 40, 8⟩) (Region.contains_self _ _) dA (by decide), hT], by
      rw [he.rsp, hrd, hwr]; exact C.args 4 (by decide)⟩
  have m := rel_wp ((hrel C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR').mono
      (P' := fun s₁ s₂ => True ∧ SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (fun _ _ g => g.2) fun _ _ g => g)
    (fun _ _ g => g.2) (hW C X hNp hnl hal hT) (hW C' X' hNp' hnl' hal' hT')
  exact RelCT.seq m (tagOut_rel (b := .rsp) (d := 40) (by simp) ⟨_, by taint_decide⟩ (fun _ _ g => g.2))

/-- `e; (m; (t; r))`, related as `e; ((m; t); r)`. -/
theorem rel_reassoc_split {P Q : State → State → Prop} {e m t r : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq m t) r)) Q) : RelCT isa P (.seq e (.seq m (.seq t r))) Q := by
  intro s₁ s₂ u₁ u₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq m₁ e₁ => cases e₁ with | seq t₁ r₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq m₂ e₂ => cases e₂ with | seq t₂ r₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq m₁ t₁) r₁)) (.seq x₂ (.seq (.seq m₂ t₂) r₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `vg_aes_gcm_seal_split`, in two runs from states with the same public
arguments. -/
theorem sealSplitM_rel {M : CtxMode} {mid : Prog isa} (hmid : MidOk M mid) (hrel : MidRel M mid) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.sealSplitX86_64M M).pre s₀) (hp' : (Proof.AesGcm.sealSplitX86_64M M).pre s₀')
    (hq : (Proof.AesGcm.sealSplitX86_64M M).pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (SealSplit.«seal» mid) fun _ _ => True := by
  obtain ⟨X, kM⟩ := CtxExt.ofSplit hp.1 hp.2
  obtain ⟨X', -⟩ := CtxExt.ofSplit hp'.1 hp'.2
  have C := SplitCtx.of hp.1 M.ge
  have C' := SplitCtx.of hp'.1 M.ge
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩ := hq'
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide); have a₄ := qa 4 (by decide); have a₅ := qa 5 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃ a₄ a₅
  have ha₅ := C.args 5 (by decide)
  have ha₅' := C'.args 5 (by decide)
  have hw48 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 48) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 48) 64 := a₅
  have hT₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s₀ 4 := rfl
  have hT₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s₀ 4 := by rw [q₇, a₄]; rfl
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₂, ← a₃, ← a₄, ← a₅] at C'
  rw [← q₁, ← q₇, ← a₂, ← a₃, ← a₅] at X'
  have e : SealSplit.entry = ([.mov .rax (.mem (at_ .rsp 48))] : List Instr) ++ SealSplit.entry.tail := rfl
  have hE₁ : WP isa (.block (([.mov .rax (.mem (at_ .rsp 48))] : List Instr) ++ SealSplit.entry.tail)) s₀
      (SEntry s₀ (s₀.gpr .rdi) (stackArg s₀ 5) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 2) (stackArg s₀ 0)
        (stackArg s₀ 3).toNat (stackArg s₀ 1).toNat) := by
    rw [← e]; exact entry_ok C rfl rfl rfl rfl rfl rfl rfl rfl
  have hE₂ : WP isa (.block (([.mov .rax (.mem (at_ .rsp 48))] : List Instr) ++ SealSplit.entry.tail)) s₀'
      (SEntry s₀' (s₀.gpr .rdi) (stackArg s₀ 5) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 2) (stackArg s₀ 0)
        (stackArg s₀ 3).toNat (stackArg s₀ 1).toNat) := by
    rw [← e]
    exact entry_ok C' q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) a₂.symm (by rw [a₃]) (by rw [q₇, a₅]; rfl)
  unfold SealSplit.«seal»
  rw [e]
  exact rel_reassoc_split (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 5 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 5) (SP := s₀.gpr .rsp) (k := 48) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub hq) hw48 ha₅ ha₅' ⟨_, by taint_decide⟩ hE₁ hE₂
    (splitTag_rel hmid hrel C C' X X' kM rfl rfl rfl rfl q₃.symm (by rw [q₄]) (by rw [q₆]) (by rw [q₂]) hT₁ hT₂))

theorem sealSplitM_ct {M : CtxMode} {mid : Prog isa} (hmid : MidOk M mid) (hrel : MidRel M mid) :
    ConstantTime isa (Proof.AesGcm.sealSplitX86_64M M).pre (Proof.AesGcm.sealSplitX86_64M M).pub
      (SealSplit.«seal» mid) :=
  ct_of_rel fun _ _ hp hp' hq => sealSplitM_rel hmid hrel hp hp' hq

end VG.Proof.AesGcm.X86_64.Split
