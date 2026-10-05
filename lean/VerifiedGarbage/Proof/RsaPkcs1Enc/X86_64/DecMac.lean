import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecHash

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: one HMAC

`HMAC-SHA256(K, X)` for a 32-byte key `K` in `scratch` and data `X`, to
`scratch + d`: HMAC's `init` with `K` and the streaming `update` with `X`
(`mac_front`), then HMAC's `finalize` (`mac_fin`). They change `scratch`
only below `sMsg` (HMAC's states and working space) and at `d` (`KeepHi`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- The bytes of `scratch` from `sMsg` on, but in the ranges `lo`, are those of `m`. -/
def KeepHi (s : State) (lo : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ a n, sMsg ≤ a → a + n ≤ scrBytes → (∀ p ∈ lo, a + n ≤ p.1 ∨ p.1 + p.2 ≤ a) →
    Spec.Rsa.bytesAt m' (scA s a) n = Spec.Rsa.bytesAt m (scA s a) n

theorem KeepHi.refl (s : State) (lo : List (Nat × Nat)) (m : Mem) : KeepHi s lo m m := fun _ _ _ _ _ => rfl

theorem KeepHi.trans {s : State} {lo lo' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : KeepHi s lo m₁ m₂)
    (h₂ : KeepHi s lo' m₂ m₃) : KeepHi s (lo ++ lo') m₁ m₃ := fun a n h₀ ha hl =>
  (h₂ a n h₀ ha fun p hp => hl p (List.mem_append_right _ hp)).trans
    (h₁ a n h₀ ha fun p hp => hl p (List.mem_append_left _ hp))

theorem KeepHi.mono {s : State} {lo lo' : List (Nat × Nat)} {m m' : Mem} (h : KeepHi s lo m m')
    (hs : ∀ p ∈ lo, p ∈ lo') : KeepHi s lo' m m' := fun a n h₀ ha hl => h a n h₀ ha fun p hp => hl p (hs p hp)

theorem KeepHi.eq {s : State} {lo : List (Nat × Nat)} {m m' : Mem} (h : m' = m) : KeepHi s lo m m' :=
  fun _ _ _ _ _ => by rw [h]

/-- Writes in `scratch` below `sMsg` or in the ranges `lo`, and below the
frame, keep the rest of `scratch`. -/
theorem keepHi_of_frame {s : State} (hp : DPre s) {lo : List (Nat × Nat)} {ws : List Region} {n : Nat}
    (hn : n ≤ 8 + privStack) {m m' : Mem} (hf : Frame (ws ++ [below (fb s) n]) m m')
    (hw : ∀ r ∈ ws, ∃ a k, r = ⟨scA s a, k⟩ ∧ a + k ≤ scrBytes ∧ (a + k ≤ sMsg ∨ (a, k) ∈ lo)) :
    KeepHi s lo m m' := fun a k h₀ ha hl => by
  refine bytes_keep hf (fun r hr => ?_) (by unfold scrBytes at ha; omega)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨b, j, rfl, hb, hb'⟩ := hw r hr
    refine scD ?_ ha hb
    rcases hb' with hb' | hb'
    · exact .inr (by omega)
    · exact hl _ hb'
  · rw [List.mem_singleton.mp hr]; exact (stkD hp hn ha).symm

/-- The words of the frame are those of `m`. -/
def FrmKeep (s : State) (m m' : Mem) : Prop :=
  ∀ d, d + 8 ≤ frameBytes → word m' (fb s) d = word m (fb s) d

theorem FrmKeep.trans {s : State} {m₁ m₂ m₃ : Mem} (h₁ : FrmKeep s m₁ m₂) (h₂ : FrmKeep s m₂ m₃) :
    FrmKeep s m₁ m₃ := fun d hd => (h₂ d hd).trans (h₁ d hd)

theorem FrmKeep.eq {s : State} {m m' : Mem} (h : m' = m) : FrmKeep s m m' := fun _ _ => by rw [h]

/-- Writes in `scratch` and below the frame keep the frame. -/
theorem frmKeep_of_frame {s : State} (hp : DPre s) {lo : List (Nat × Nat)} {ws : List Region} {n : Nat}
    (hn : n ≤ 8 + privStack) {m m' : Mem} (hf : Frame (ws ++ [below (fb s) n]) m m')
    (hw : ∀ r ∈ ws, ∃ a k, r = ⟨scA s a, k⟩ ∧ a + k ≤ scrBytes ∧ (a + k ≤ sMsg ∨ (a, k) ∈ lo)) :
    FrmKeep s m m' := fun d hd => by
  have hF := fb_toNat hp
  obtain ⟨h1, _⟩ := scr_len hp
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨b, j, rfl, hb, -⟩ := hw r hr
    exact (hp.dKs.sub_left (frame_sub s hd)).sub_right (sub_trans (scSub hb) (Region.sub_prefix h1))
  · rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_below (fb s) (by unfold frameBytes privStack at *; omega)

/-- After HMAC's `init` with `K` and the streaming `update` with `X`, from `t₀`. -/
structure MacMid (v : Compress) (s : State) (R : BitVec 64) (EM K X : List Byte) (t₀ t : State) : Prop where
  ctx : Ctx s R EM t
  inner : (OK v).SH.Repr t.mem (scA s 0) (Spec.Hmac.xorPad (Spec.Hmac.blockKey (OK v).SH.H K) Spec.Hmac.ipad ++ X)
  outer : (OK v).SH.Repr t.mem (scA s sOuter) (Spec.Hmac.xorPad (Spec.Hmac.blockKey (OK v).SH.H K) Spec.Hmac.opad)
  keep : KeepHi s [] t₀.mem t.mem
  frm : FrmKeep s t₀.mem t.mem

theorem macInitArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {kOff : Nat} (hk : kOff < 2 ^ 31) :
    WP isa (.block (macInitArgs kOff)) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = scA s sOuter ∧ t'.gpr .rdx = scA s kOff ∧ t'.gpr .rcx = BitVec.ofNat 64 32 ∧
      t'.gpr .r8 = scA s sWork := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block (macInitArgs kOff)) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = scA s sOuter ∧ t'.gpr .rdx = scA s kOff ∧
    t'.gpr .rcx = BitVec.ofNat 64 32 ∧ t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [macInitArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hc.slots.sScr, scA_zero, sx (d := sOuter) (by decide), sx hk, sx (d := sWork) (by decide)]

theorem blockKey_len (K : List Byte) (hK : K.length = 32) : (Spec.Hmac.blockKey (OK v).SH.H K).length = 64 := by
  rw [sh_hash]
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, hK, show ¬ (64 < 32) by decide, ↓reduceIte, List.length_append,
    List.length_replicate]

theorem mac_front {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t₀ : State} (hc : Ctx s R EM t₀)
    {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes) {updA : List Instr} {da : Addr} {L : Nat}
    (hupd : ∀ t, Ctx s R EM t → WP isa (.block updA) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = BitVec.ofNat 64 64 ∧ t'.gpr .rdx = da ∧ (t'.gpr .rcx).toNat = L ∧
      t'.gpr .r8 = scA s sWork)
    (hdc : Covers [⟨da, L⟩] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)))
    (hdd : ∀ a n, a + n ≤ sMsg → Region.Disjoint ⟨da, L⟩ ⟨scA s a, n⟩)
    (hds : (below (fb s) 24).Disjoint ⟨da, L⟩) (hL : L ≤ 2 ^ 64)
    {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t, MacMid v s R EM (Spec.Rsa.bytesAt t₀.mem (scA s kOff) 32) (Spec.Rsa.bytesAt t₀.mem da L) t₀ t →
      WP isa rest t Q) :
    WP isa (.seq (.block (macInitArgs kOff)) (.seq (.call (HH v).hmacInitN (HH v).hmacInit)
      (.seq (.block updA) (.seq (.call (HH v).updN (HH v).updC) rest)))) t₀ Q := by
  obtain ⟨hS, hW, -, hB, hSs, -, -, hWb⟩ := sizes v
  refine WP.seq (WP.mono (macInitArgs_run hp hc (by unfold scrBytes at hk2; omega))
    fun t₁ ⟨hc₁, hm₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁⟩ => ?_)
  have cw₁ : Covers [⟨scA s 0, 96⟩, ⟨scA s sOuter, 96⟩, ⟨scA s sWork, 832⟩] t₁.wr :=
    (scCov hp hc₁ (by decide)).cons ((scCov hp hc₁ (by decide)).cons ((scCov hp hc₁ (by decide)).cons Covers.nil))
  refine WP.seq (Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call (OK v) (hI v) (hIsp v) (hId v) (kl := 32)
    { rdi := hdi₁, rsi := hsi₁, rdx := hdx₁, rcx := by rw [hcx₁]; rfl, r8 := h8₁, klB := by rw [hB]; decide
      cr := Covers.right (scCov hp hc₁ hk2)
      cw := by rw [hS, hW]; exact cw₁
      i_o := by rw [hS]; exact scD (.inl (by decide)) (by decide) (by decide)
      i_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      o_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      k_i := by rw [hS]; exact scD (.inr (by unfold sMsg at hk1; omega)) hk2 (by decide)
      k_o := by rw [hS]; exact scD (.inr (by unfold sMsg sOuter at *; omega)) hk2 (by decide)
      k_s := by rw [hW]; exact scD (.inr (by unfold sMsg sWork at *; omega)) hk2 (by decide)
      stk_i := by rw [below_rsp hc₁, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc₁, hS]; exact stkD hp (by decide) (by decide)
      stk_k := by rw [below_rsp hc₁]; exact stkD hp (by decide) hk2
      stk_s := by rw [below_rsp hc₁, hW]; exact stkD hp (by decide) (by decide)
      scnw := by
        rw [hW]; obtain ⟨h1, h2⟩ := scr_len hp
        simp only [scA, off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold scrBytes at h1; unfold sWork; omega }
    fun t₂ hrd₂ hwr₂ hcs₂ hf₂ hi₂ ho₂ => ?_)
  rw [hS, hW, below_rsp hc₁] at hf₂
  rw [hm₁] at hi₂ ho₂
  have hws₂ : ∀ r ∈ [(⟨scA s 0, 96⟩ : Region), ⟨scA s sOuter, 96⟩, ⟨scA s sWork, 8 * 104⟩],
      ∃ a k, r = ⟨scA s a, k⟩ ∧ a + k ≤ scrBytes ∧ (a + k ≤ sMsg ∨ (a, k) ∈ ([] : List (Nat × Nat))) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, 96, rfl, by decide, .inl (by decide)⟩
    · exact ⟨sOuter, 96, rfl, by decide, .inl (by decide)⟩
    · exact ⟨sWork, 8 * 104, rfl, by decide, .inl (by decide)⟩
  have hc₂ : Ctx s R EM t₂ := hc₁.step hp hrd₂ hwr₂ (hcs₂ .rsp (by decide)) hf₂ fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨a, k, rfl, hk, -⟩ := hws₂ r hr; exact scS hk
    · rw [List.mem_singleton.mp hr]; exact belowS hp (n := 24) (by decide)
  have kp₂ : KeepHi s [] t₀.mem t₂.mem :=
    ((KeepHi.eq (lo := []) hm₁).trans (keepHi_of_frame (lo := []) hp (by decide) hf₂ hws₂)).mono
      fun _ h => absurd h (by simp)
  have hX₂ : Spec.Rsa.bytesAt t₂.mem da L = Spec.Rsa.bytesAt t₀.mem da L := by
    rw [← hm₁]
    refine bytes_keep hf₂ (fun r hr => ?_) hL
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨a, k, rfl, hk, hk'⟩ := hws₂ r hr
      exact hdd a k (by simpa using hk')
    · rw [List.mem_singleton.mp hr]; exact hds.symm
  refine WP.seq (WP.mono (hupd t₂ hc₂) fun t₃ ⟨hc₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃⟩ => ?_)
  have hdc₃ : Covers [⟨da, L⟩] (t₃.rd ++ t₃.wr) := by rw [hc₃.rd, hc₃.wr]; exact hdc
  refine WP.seq (Proof.Pbkdf2.Md.X86_64.Calls.upd_call (OK v).stream (len := L)
    { rdi := hdi₃, rdx := hdx₃, rcx := hcx₃, r8 := h8₃, cd := hdc₃
      cw := by rw [hSs, hWb]; exact Covers.pair (scCov hp hc₃ (by decide)) (scCov hp hc₃ (by decide))
      st_sc := by rw [hSs, hWb]; exact scD (.inl (by decide)) (by decide) (by decide)
      d_st := by rw [hSs]; exact hdd 0 96 (by decide)
      d_sc := by rw [hWb]; exact hdd sWork 608 (by decide)
      stk_st := by rw [below_rsp hc₃, hSs]; exact stkD hp (by decide) (by decide)
      stk_d := by rw [below_rsp hc₃]; exact hds.sub_left (VG.X86_64.below_sub (by decide) (by decide))
      stk_sc := by rw [below_rsp hc₃, hWb]; exact stkD hp (by decide) (by decide) } hL
    fun t₄ a₄ hu₄ => ?_)
  rw [hSs, hWb] at a₄
  have hws₄ : ∀ r ∈ [(⟨scA s 0, 96⟩ : Region), ⟨scA s sWork, 608⟩],
      ∃ a k, r = ⟨scA s a, k⟩ ∧ a + k ≤ scrBytes ∧ (a + k ≤ sMsg ∨ (a, k) ∈ ([] : List (Nat × Nat))) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 96, rfl, by decide, .inl (by decide)⟩
    · exact ⟨sWork, 608, rfl, by decide, .inl (by decide)⟩
  have hf₄ : Frame ([(⟨scA s 0, 96⟩ : Region), ⟨scA s sWork, 608⟩] ++ [below (fb s) 16]) t₃.mem t₄.mem := by
    have := a₄.frame; rwa [below_rsp hc₃] at this
  have hc₄ : Ctx s R EM t₄ := hc₃.after hp a₄ fun r hr => by
    obtain ⟨a, k, rfl, hk, -⟩ := hws₄ r hr; exact scS hk
  have hk₂ : 32 ≤ 64 := by decide
  have hlen : (Spec.Hmac.xorPad (Spec.Hmac.blockKey (OK v).SH.H (Spec.Rsa.bytesAt t₀.mem (scA s kOff) 32)) Spec.Hmac.ipad).length = 64 := by
    rw [show ∀ k : List Byte, (Spec.Hmac.xorPad k Spec.Hmac.ipad).length = k.length from
      fun k => List.length_map _]
    exact blockKey_len _ (blen _ _ _)
  have hi₃ : (OK v).stream.SH.Repr t₃.mem (scA s 0)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey (OK v).SH.H (Spec.Rsa.bytesAt t₀.mem (scA s kOff) 32)) Spec.Hmac.ipad) := by
    rw [hm₃]; exact hi₂
  have hr₄ := hu₄ _ hi₃ (by rw [hsi₃, hlen])
  refine hrest t₄ ⟨hc₄, ?_, ?_, ((kp₂.trans (KeepHi.eq (lo := []) hm₃) |>.trans
    (keepHi_of_frame (lo := []) (n := 16) hp (by decide) hf₄ hws₄)).mono
    fun _ h => absurd h (by simp)), ((FrmKeep.eq hm₁).trans (frmKeep_of_frame (lo := []) hp (by decide) hf₂ hws₂)).trans
      ((FrmKeep.eq hm₃).trans (frmKeep_of_frame (lo := []) (n := 16) hp (by decide) hf₄ hws₄))⟩
  · have e : Spec.Sha256.bytesAt t₃.mem da L = Spec.Rsa.bytesAt t₀.mem da L := by
      rw [show Spec.Sha256.bytesAt t₃.mem da L = Spec.Rsa.bytesAt t₃.mem da L from rfl, hm₃, hX₂]
    rw [e] at hr₄; exact hr₄
  · refine (OK v).stream.repr t₂.mem t₄.mem (scA s sOuter) (scA s sOuter) _ (fun i hi => ?_) ho₂
    have hb := Frame.bytes (R := ⟨scA s sOuter, 96⟩) hf₄ (fun r hr => ?_) (show 96 ≤ 2 ^ 64 by decide) (i := i) (by rw [hSs] at hi; exact hi)
    · rw [hb, hm₃]
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact scD (.inr (by decide)) (by decide) (by decide)
        · exact scD (.inl (by decide)) (by decide) (by decide)
      · rw [List.mem_singleton.mp hr]; exact (stkD hp (by decide) (by decide)).symm


theorem mac_fin {s : State} (hp : DPre s) {R : BitVec 64} {EM K X : List Byte} {t₀ t : State}
    (h : MacMid v s R EM K X t₀ t) {dOff : Nat} (hd1 : sMsg ≤ dOff) (hd2 : dOff + 32 ≤ scrBytes) (hK : K.length = 32)
    (hdi : t.gpr .rdi = scA s 0) (hsi : t.gpr .rsi = scA s sOuter)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 (64 + X.length)) (hcx : t.gpr .rcx = scA s dOff)
    (h8 : t.gpr .r8 = scA s sWork) (hX : X.length < 2 ^ 63) :
    WP isa (.call (HH v).hmacFinN (HH v).hmacFin) t fun t' => Ctx s R EM t' ∧
      Spec.Rsa.bytesAt t'.mem (scA s dOff) 32 = Spec.Hmac.hmac Spec.Hmac.sha256 K X ∧
      KeepHi s [(dOff, 32)] t₀.mem t'.mem ∧ FrmKeep s t₀.mem t'.mem := by
  obtain ⟨hS, hW, hD, hB, -, -, -, -⟩ := sizes v
  have hc := h.ctx
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s dOff, 32⟩, ⟨scA s sWork, 832⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc hd2).cons ((scCov hp hc (by decide)).cons Covers.nil))
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call (OK v) (hF v) (hFsp v) (hFd v)
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := hcx, r8 := h8
      cr := by rw [hS]; exact Covers.right (scCov hp hc (by decide))
      cw := by rw [hS, hD, hW]; exact cw
      i_u := by rw [hS]; exact scD (.inl (by decide)) (by decide) (by decide)
      i_o := by rw [hS, hD]; exact scD (.inl (by unfold sMsg at hd1; omega)) (by decide) hd2
      i_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      u_o := by rw [hS, hD]; exact scD (.inl (by unfold sMsg sOuter at *; omega)) (by decide) hd2
      u_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      o_s := by rw [hD, hW]; exact scD (.inr (by unfold sMsg sWork at *; omega)) hd2 (by decide)
      stk_i := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_u := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hD]; exact stkD hp (by decide) hd2
      stk_s := by rw [below_rsp hc, hW]; exact stkD hp (by decide) (by decide)
      scnw := by
        rw [hW]; obtain ⟨h1, h2⟩ := scr_len hp
        simp only [scA, off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold scrBytes at h1; unfold sWork; omega }
    fun t' hrd hwr hcs hf hmac => ?_
  rw [hS, hD, hW, below_rsp hc] at hf
  have hws : ∀ r ∈ [(⟨scA s 0, 96⟩ : Region), ⟨scA s dOff, 32⟩, ⟨scA s sWork, 8 * 104⟩],
      ∃ a k, r = ⟨scA s a, k⟩ ∧ a + k ≤ scrBytes ∧ (a + k ≤ sMsg ∨ (a, k) ∈ [(dOff, 32)]) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, 96, rfl, by decide, .inl (by decide)⟩
    · exact ⟨dOff, 32, rfl, hd2, .inr (List.mem_singleton_self _)⟩
    · exact ⟨sWork, 8 * 104, rfl, by decide, .inl (by decide)⟩
  have hc' : Ctx s R EM t' := hc.step hp hrd hwr (hcs .rsp (by decide)) hf fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨a, k, rfl, hk, -⟩ := hws r hr; exact scS hk
    · rw [List.mem_singleton.mp hr]; exact belowS hp (n := 24) (by decide)
  have hk0 : (Spec.Hmac.blockKey (OK v).SH.H K).length = 64 := blockKey_len K hK
  have := hmac (Spec.Hmac.blockKey (OK v).SH.H K) X (by rw [hk0, hB]) (by rw [hk0]; omega) h.inner
    (by rw [hB]) h.outer
  rw [hD] at this
  refine ⟨hc', this, ((h.keep.trans (keepHi_of_frame hp (by decide) hf hws)).mono fun p hp => ?_),
    h.frm.trans (frmKeep_of_frame hp (by decide) hf hws)⟩
  simpa using hp

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
