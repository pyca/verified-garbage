module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PreG
public import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.Gcm.StreamTo

/-!
# AES-GCM `seal_split` on x86-64: from the entry to the tag at `W`

Untrusted: everything here is checked by Lean. After the entry, `J₀` and the
additional data (`oneMid_ok`), `prefix` (`prefix_ok`) and `body` (`body_ok`)
leave the plaintext `src[0..sl] ‖ dst[sl..len]` encrypted at `dst` and the
tag at `W`, of the additional data and the ciphertext with the lengths block
of `len` (`splitRun_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 ghash blocks ofBytes toBytes zeros
  padLen gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

theorem padLen_mod {n : Nat} (h : n % 16 = 0) : padLen n = 0 := by simp [padLen, h]

/-- Whole blocks after the padded additional data are text. -/
theorem padded_whole {a A c d : List Byte} (hA : a ++ zeros (padLen a.length) = A) (hAl : A.length % 16 = 0)
    (hc : c.length % 16 = 0) : padded (A ++ c) d = padded a (c ++ d) := by
  have z0 : padLen (A ++ c).length = 0 := padLen_mod (by simp only [List.length_append]; omega)
  have zA : padLen A.length = 0 := padLen_mod hAl
  unfold padded Spec.Gcm.ghashInput
  by_cases hd : d = []
  · subst hd
    by_cases hc0 : c = []
    · subst hc0
      simp only [List.append_nil, ↓reduceIte, hA, zA]
      simp [zeros]
    · simp only [List.append_nil, ↓reduceIte, hc0, hA]
  · have hcd : c ++ d ≠ [] := by simp [hd]
    simp only [hd, hcd, ↓reduceIte, hA, z0]
    simp [zeros, List.append_assoc]

/-- The keystream from the counter block `q` blocks on, from any byte. -/
theorem xorKs_shift' (ciph : Block → Block) (icb : Block) (q k : Nat) (d : List Byte) :
    xorKs ciph icb (16 * q + k) d = xorKs ciph (Nat.repeat inc32 q icb) k d := by
  simp only [xorKs]
  refine List.map_congr_left fun i _ => ?_
  simp only [Proof.Gcm.ksByte]
  rw [show (16 * q + k + i) / 16 = (k + i) / 16 + q by omega, show (16 * q + k + i) % 16 = (k + i) % 16 by omega,
    Proof.Gcm.repeat_add]

/-- A region apart from `W`, the data from byte `k` on and the 56 bytes below
`SP` is apart from what `body` writes. -/
theorem sf_out {W D SP : Addr} {n : Nat} {X : Region} (xw : X.Disjoint ⟨W, 2560⟩) (xd : X.Disjoint ⟨D, n⟩)
    (xs : X.Disjoint (below SP 56)) : ∀ r ∈ splitFrame W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact xw.sub_right (Region.sub_prefix (by decide))
  · exact xw.sub_right (Lay.wSub (by decide))
  · exact xw.sub_right (Lay.wSub (by decide))
  · exact xd
  · exact xs

theorem saved_sf {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {D : Addr} {n : Nat}
    (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (kw : (below SP 56).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ splitFrame W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (kw.sub_right (Lay.wSub (by decide))).symm

/-- `src` and `src_len`, kept at `tlO` and `tlenO` through `oneAad`. -/
theorem mid_slots {s₀ s₁ s₂ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat} {H : Block}
    {iv a : List Byte} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (M₂ : OneMid s₀ Ctx W SP D n H iv a s₁.mem s₂) :
    s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = S ∧ s₂.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl := by
  have f₂ : Frame (oneFrame W D SP n) s₁.mem s₂.mem := wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₂.fr)
  have k₂ : ∀ d, d = 192 ∨ d = 224 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame C.lay C.dE (by rcases hd with rfl | rfl <;> decide)) (by decide)
  exact ⟨by rw [k₂ 224 (.inr rfl)]; exact E.src, by rw [k₂ 192 (.inl rfl)]; exact E.slen⟩

/-- What `prefix` needs, after `J₀` and the additional data. -/
theorem PP.ofMid {M : CtxMode} {s₀ s₂ : State} {mE : Mem} {Ctx W SP Np A D S T' : Addr} {nl al n sl R : Nat}
    {H : Block} {iv a : List Byte} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩)
    (hR : (s₀.gpr .rsi).toNat = R) (M₂ : OneMid s₀ Ctx W SP D n H iv a mE s₂)
    (hS : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hsl : s₂.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) : PP M Ctx W SP D S R n sl s₂ := by
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  exact ⟨M₂.env, C.lay, hR ▸ M₂.rounds, M₂.dat, M₂.len, hS, hsl, C.data.of_eq M₂.rd M₂.wr,
    by rw [M₂.rd, M₂.wr]; exact C.src, C.sW, C.sD, C.sWrap, C.sl_le, C.kw, C.kd, C.ks, kM, C.sp56,
    X.keep M₂.rd M₂.wr M₂.frame (dM X.cw (X.ct.sub_left (below_sub (by decide) (by decide))))⟩

/-- What `seal_split` leaves at the tag at `W`, after the entry: what
`sealRun_ok` does, for the plaintext of `sl` bytes at `S` and the rest at
`D`. -/
abbrev SplitRunPost (s₀ : State) (Ctx W SP Np A D S : Addr) (nl al n sl : Nat) (s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
    SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 56] s₀.mem s₄.mem ∧
    bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat)
      (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))
      (bytesAt s₀.mem S sl ++ (bytesAt s₀.mem D n).drop sl) ∧
    bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))

/-- What `seal_split`'s code `mid` after the entry must do: leave what
`SplitRunPost` says. -/
def MidOk (M : CtxMode) (mid : Prog isa) : Prop :=
  ∀ {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat},
    SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ →
    (below SP 56).Disjoint ⟨Ctx, M.len⟩ → SEntry s₀ Ctx W SP A D S n sl s₁ →
    s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al →
    WP isa mid s₁ (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl)

/-- After the entry, `seal_split` up to the tag at `W`: additional data
`aadP` that leaves what `oneAad` does (`OneMid`), code `pre` that encrypts
the first whole blocks of the plaintext (`PreOk`), and `body`. -/
theorem splitRun_of_pre {M : CtxMode} {pre : Prog isa} {qf : Nat → Nat → Nat} (hpre : PreOk M pre qf) {body : Prog isa}
    (hbody : BodyOk M body) {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq pre body)) s₁ (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) := by
  unfold SplitRunPost
  have L := C.lay
  have hsl := C.sl_le
  have hn := C.data.ok.lt
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono ha fun s₂ M₂ => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M₂ ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M₂ ⊢
  generalize ha : bytesAt s₀.mem A al = a at M₂ ⊢
  have hRo : RoundsAt s₂.mem W R := hR ▸ M₂.rounds
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  obtain ⟨hS₂, hsl₂⟩ := mid_slots C E M₂
  have P : PP M Ctx W SP D S R n sl s₂ := PP.ofMid C X kM hR M₂ hS₂ hsl₂
  have X₂ := P.ext
  refine WP.seq (WP.mono (hpre P) fun s₃ Q => ?_)
  generalize qf n sl = q at Q
  have fQ := Q.frame
  have rd₃ : s₃.rd = s₀.rd := Q.rd.trans M₂.rd
  have wr₃ : s₃.wr = s₀.wr := Q.wr.trans M₂.wr
  have hq := Q.le
  have wsl : ∀ d, 128 ≤ d → d + 8 ≤ 200 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    fQ.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (pp_wG L C.dE C.kw (.inr (.inl ⟨h₁, h₂⟩))) (by decide)
  have sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * q), n - 16 * q⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by omega)
  have X₃ : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 (16 * q))
      (n - 16 * q) s₃ := (X₂.keep Q.rd Q.wr fQ (pp_outG X.cw X.cd kM.symm)).sub sD'
  have s240 : Region.Sub ⟨Ctx + BitVec.ofNat 64 240, 16⟩ ⟨Ctx, M.len⟩ := Offset.sub_base Ctx (by have := M.ge; omega)
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fQ (pp_outG (X.cw.sub_left s240) (X.cd.sub_left s240) (kM.symm.sub_left s240)), M₂.hH]
  have hcb₃ : blockAt s₃.mem (cbA W) = Nat.repeat inc32 q (inc32 (Spec.Gcm.j0 H iv)) := by
    rw [Q.ctr]; exact congrArg _ M₂.cb
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [wsl 184 (by decide) (by decide), M₂.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hy₃ : blockAt s₃.mem (yA W) = ghashFrom H (blockAt s₂.mem (yA W))
      (blocks (bytesAt s₃.mem D (16 * q))) := by
    rw [Q.y, ← Proof.Gcm.blocksAt_eq, ctxH_eq, M₂.hH]
  have hAl : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hC1l : (bytesAt s₃.mem D (16 * q)).length % 16 = 0 := by rw [length_bytesAt]; omega
  have habs₃ := Proof.Gcm.absorb_whole M₂.abs hAl hC1l hy₃
  have ez : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q) ++
      zeros (padLen (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q)).length) =
      a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q) := by
    have h3 : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * q)).length % 16 = 0 := by
      rw [List.length_append]; omega
    rw [padLen_mod h3]; simp [zeros]
  rw [← ez] at habs₃
  have hR₃ : RoundsAt s₃.mem W R := ⟨by rw [wsl 176 (by decide) (by decide)]; exact hRo.1, hRo.2⟩
  refine WP.mono (hbody L (R := R) (al := al) (N := n) Q.env hR₃ Q.dat Q.len ((C.data.of_eq rd₃ wr₃).drop hq) C.kw (C.kd.sub_right sD') kM C.sp56 X₃ hH₃
    hcb₃ hal₃ habs₃ Q.aux (by have := C.data.ok.lt; omega)) fun s₄ ⟨e₄, rd₄, wr₄, f₄, hC₄, hT₄⟩ => ?_
  -- The cipher, kept.
  have kc : (below SP 56).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix M.ge)
  have hc₂ : ciphOf s₂.mem Ctx R = ciphOf s₀.mem Ctx R := ciph_frame M₂.frame (dM L.cw' L.kc) hR'
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s₀.mem Ctx R :=
    (ciph_frame fQ (pp_outG L.cw' C.data.ctx kc.symm) hR').trans hc₂
  -- The plaintext, kept by `aadP`.
  have hpt : splitPt s₂.mem D S n sl = splitPt s₀.mem D S n sl := by
    simp only [splitPt]
    rw [bytesAt_frame M₂.frame (dM C.sW (C.ks.sub_left b8)) (by omega),
      bytesAt_frame M₂.frame (dM C.dE C.data.ok.stk) (by omega)]
  have hC1 : bytesAt s₃.mem D (16 * q) =
      xorKs (ciphOf s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) 0 ((splitPt s₀.mem D S n sl).take (16 * q)) := by
    rw [Q.enc, hc₂, hpt, M₂.cb]
  have hC1₄ : bytesAt s₄.mem D (16 * q) = bytesAt s₃.mem D (16 * q) :=
    bytesAt_frame f₄ (sf_out (C.dE.sub_left (Region.sub_prefix hq)) (Offset.base_disjoint D (Nat.le_refl _) (by omega))
      ((C.kd.sub_right (Region.sub_prefix hq)).symm)) (by omega)
  have hD₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D (16 * q) ++
      bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * q)) (n - 16 * q) := by
    have e := bytesAt_add s₄.mem D (16 * q) (n - 16 * q)
    rw [Nat.add_sub_cancel' hq] at e
    rw [e, hC1₄]
  have hJ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [blockAt_frame fQ (pp_wG L C.dE C.kw (d := 16) (k := 16) (.inl (by decide)))]; exact M₂.j0
  refine ⟨e₄, rd₄.trans rd₃, wr₄.trans wr₃, (M₂.saved.frame fQ (pp_wG L C.dE C.kw (d := 128) (k := 48)
    (.inr (.inl ⟨Nat.le_refl _, by decide⟩)))).frame f₄ (saved_sf L (C.dE.sub_left sD') C.kw), ?_, ?_, ?_⟩
  · refine (M₂.frame.sub fun r hr => ?_).trans ((fQ.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨below SP 56, by simp, b8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun a hc => st_w a (cb_sub a hc)⟩
      · exact ⟨_, List.mem_cons_self .., fun a hc => st_w a (y_sub a hc)⟩
      · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., sc_w⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨⟨D, n⟩, by simp, sD'⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
  · rw [hD₄, hC₄, hc₃, hC1, Q.tail, hpt, Proof.Gcm.gctr_eq, ← xorKs_shift' _ _ q 0, Nat.add_zero]
    have e := Proof.Gcm.xorKs_append (ciphOf s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) 0
      ((splitPt s₀.mem D S n sl).take (16 * q)) ((splitPt s₀.mem D S n sl).drop (16 * q))
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by simp only [List.length_append, List.length_drop, length_bytesAt]; omega), Nat.zero_add] at e
    exact e.symm
  · rw [hT₄, hc₃, hJ, padded_whole rfl hAl hC1l, ← hD₄]
    rfl

/-- After the entry, `seal_split` up to the tag at `W`: additional data
`aadP` that leaves what `oneAad` does (`OneMid`), `prefix` and `body`. -/
theorem splitRun_of_midB {M : CtxMode} (T : BlkToFn M) {body : Prog isa}
    (hbody : BodyOk M body) {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq (SealSplit.prefix T.fn) body)) s₁
      (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) :=
  splitRun_of_pre (prefixOk T) hbody C X kM E hal ha

/-- `splitRun_of_midB` with `SealSplit.body`. -/
theorem splitRun_of_mid (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa}
    (hfin : FinOk M fin) {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (E : SEntry s₀ Ctx W SP A D S n sl s₁)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq (SealSplit.prefix T.fn) (SealSplit.body (v.withBlk B) fin))) s₁
      (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) :=
  splitRun_of_midB T (bodyOk_body B hfin) C X kM E hal ha

/-- After the entry, `seal_split` up to the tag at `W`: `oneAad`, `prefix` and
`body`. -/
theorem splitRun_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa} (hfin : FinOk M fin) :
    MidOk M (SealSplit.run (v.withBlk B) T.fn fin) := by
  intro s₀ s₁ Ctx W SP Np A D S T' nl al n sl C X kM E hNp hnl hal
  exact splitRun_of_mid v B T hfin C X kM E hal (oneMid_ok v C.toOneCtx E.toOneEntry hNp hnl hal)

/-- The key context, from `seal_split`'s precondition, and the 56 bytes below
the stack pointer apart from it. -/
theorem CtxExt.ofSplit {M : CtxMode} {s : State} (hp : Proof.AesGcm.splitPre M.len s)
    (hok : M.ok s.mem (s.gpr .rdi)) :
    CtxExt M (s.gpr .rdi) (stackArg s 5 + BitVec.ofNat 64 16) (stackArg s 5) (s.gpr .rsp) (stackArg s 2)
      (stackArg s 3).toNat s ∧ (below (s.gpr .rsp) 56).Disjoint ⟨s.gpr .rdi, M.len⟩ := by
  simp only [Proof.AesGcm.splitPre, Proof.AesGcm.stk56, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, -, d_cd, d_cw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t_c, -, -, -, -, -, wc, -⟩ := hp
  exact ⟨⟨wc, d_cw.sub_right (Lay.wSub (by decide)), d_cw, d_cd, t_c.sub_left (below_sub (by decide) (by decide)),
    by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)), hok⟩, t_c⟩

/-- `x; (a; (b; (c; (d; e))))` from `x; ((a; (b; c)); (d; e))`. -/
theorem WP.reassoc_split {x a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq x (.seq (.seq a (.seq b c)) (.seq d e))) s Q) :
    WP isa (.seq x (.seq a (.seq b (.seq c (.seq d e))))) s Q := by
  obtain ⟨t, s', ex, q⟩ := h
  cases ex with | seq ex ex₁ => cases ex₁ with | seq ex₁ ex₂ => cases ex₁ with | seq ea ex₁ => cases ex₁ with
    | seq eb ec => exact ⟨_, _, .seq ex (.seq ea (.seq eb (.seq ec ex₂))), q⟩

/-- `vg_aes_gcm_seal_split`, for a key context of kind `M`. -/
theorem sealSplitM_wp {M : CtxMode} {mid : Prog isa} (hmid : MidOk M mid) {s : State}
    (hp : (Proof.AesGcm.sealSplitX86_64M M).pre s) :
    WP isa (SealSplit.«seal» mid) s fun s' =>
      gprPreserved s s' ∧ (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  obtain ⟨X, kM⟩ := CtxExt.ofSplit hp.1 hp.2
  have C := SplitCtx.of hp.1 M.ge
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 48) 64 = stackArg s 5 := rfl
  have hT' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := rfl
  have hta := C.args 4 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rdx = Np at *
  generalize hnl : (s.gpr .rcx).toNat = nl at *
  generalize hA : s.gpr .r8 = A at *
  generalize hal : (s.gpr .r9).toNat = al at *
  generalize hS : stackArg s 0 = S at *
  generalize hsl : (stackArg s 1).toNat = sl at *
  generalize hD : stackArg s 2 = D at *
  generalize hn : (stackArg s 3).toNat = n at *
  generalize hT : stackArg s 4 = T' at *
  generalize hW : stackArg s 5 = W at *
  have L := C.lay
  unfold SealSplit.«seal»
  refine WP.seq (WP.mono (entry_ok C hCtx hSP hA hS hsl hD hn hW') fun s₁ E => ?_)
  refine WP.seq (WP.mono (hmid C X kM E hNp hnl hal)
    fun s₄ ⟨he₄, hrd₄, hwr₄, hsv₄, f₄, hC, hT₄⟩ => WP.seq ?_)
  -- The tag copied to `tag`.
  have dA : ∀ r ∈ [(⟨W, 2560⟩ : Region), ⟨D, n⟩, below SP 56], (⟨SP + BitVec.ofNat 64 40, 8⟩ : Region).Disjoint r := by
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 40, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 6⟩ := by
      rw [show (40 : Nat) = 8 + 32 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact C.dA.sub_left hs
    · exact C.dAD.sub_left hs
    · exact Offset.disjoint_below SP (n := 56) (d := 40) (k := 8) (by decide)
  have hT₄' : s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 40) 64 = T' := by
    rw [he₄.rsp, f₄.readW (r := ⟨SP + BitVec.ofNat 64 40, 8⟩) (Region.contains_self _ _) dA (by decide), hT']
  obtain ⟨s₅, run₅, hb₅, f₅, hg₅, hrd₅, hwr₅⟩ := tagOut_ok (b := .rsp) (d := 40) he₄.r15 hT₄'
    (by rw [he₄.rsp, hrd₄, hwr₄]; exact hta) he₄.perm.w (by rw [hwr₄]; exact C.tag)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have hsv₅ : SavedAt s₅.mem W s := hsv₄.frame f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (C.tW.sub_right (Lay.wSub (by decide))).symm
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₅ (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact C.rW
      · exact C.rD
      · exact Offset.base_disjoint_below SP (n := 56) (k := 8) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact C.rT
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun _ => ?_⟩
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.tD.symm) (by have := C.data.ok.lt; omega)
  simp only [Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hS, hsl, hD, hn, hT, Spec.Gcm.encryptWith, hm, hb₅, hT₄, hd₅, hC,
    Proof.Gcm.fullTag_eq, Proof.Gcm.length_gctr]
  simp only [List.length_append, List.length_drop, length_bytesAt]
  rw [Nat.add_sub_cancel' C.sl_le]
  simp only [Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.AesGcm.X86_64.Split
