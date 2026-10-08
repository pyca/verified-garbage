import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain

/-!
# `vg_rsa_check_crt_key` on x86-64: constant time of `main`

`reduceTop` from `KK` (`reduceTopK_ct`): its header loads from `rdi`, the
rest from the registers they pin, which are public (`w'` and `c` from the
lengths); then `main` as `vg_rsa_check_key`'s (`ckMain_ct`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- After `reduceTop`'s first block: `KK`, and the copy's registers. -/
def RT1 (fl fc : KPub → Nat) (p : KPub) (t : State) : Prop :=
  KK p t ∧ RegsAre [(.rdi, p.B), (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)), (.r13, BitVec.ofNat 64 (fc p)),
    (.rsi, off p.B (slot p.w aAcc + 8 * fc p)), (.rbx, kb p aR)] t

/-- After the copy. -/
def RT2 (fl fc : KPub → Nat) (p : KPub) (t : State) : Prop :=
  KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) ∧ t.gpr .r13 = BitVec.ofNat 64 (fc p)

/-- `reduceTop sl top` from `KK`, for the length `fl p` in slot `sl` and the
`c = fc p` that `top` computes. -/
theorem reduceTopK_ct {sl : Nat} {top : List Instr} (fl fc : KPub → Nat) (hsl : sl < 32) (hsl' : sl ≠ sMask)
    (hL : ∀ p s, KS p s → word s.mem p.B (8 * sl) = BitVec.ofNat 64 (fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    (hfc : ∀ p s, KS p s → fc p + (fl p + 7) / 8 ≤ 2 * p.w + 4)
    (htop : ∀ p t, KK p t → WP isa (.block top) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 (fc p) ∧
      t'.mem = t.mem ∧ Keep [.r13] t t')
    (hok : ∀ p s, KK p s → WP isa (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sl top)) s (KK p))
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Impl.Rsa.X86_64.CheckCrtKey.lenWords sl ++ top ++
      ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
        .mov .rbx (.mem (hdr (sArr aR)))] : List Instr))) hc₁).isSome = true) :
    RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sl top)) (Two KK) := by
  refine kk_ct ?_ hok
  simp only [Impl.Rsa.X86_64.CheckCrtKey.reduceTop, seqs]
  refine RelCT.seq ((zeroArrK_ct (j := aR) (by decide) (by decide) (by decide) (by taint_decide)).mono
    (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h) ?_
  refine RelCT.seq (two_piece (Ψ := RT1 fl fc) [.rdi] pins_kk hT fun p s h => ?_) ?_
  · obtain ⟨hdi, hl, -, hb'⟩ := h.lds
    obtain ⟨s₀, minv, N, c, hs⟩ := h
    obtain ⟨hLs, hL1, hLw⟩ := hL p s₀ hs
    rw [← c.hdr sl hsl hsl'] at hLs
    have := c.w2
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) ∧ t.mem = s.mem)
      (by xrun [Impl.Rsa.X86_64.CheckCrtKey.lenWords, State.ea, hdr, hdi, hdrOff, hl sl hsl, hLs,
        shr3_w (fl p) (by omega)]) rfl) fun s₂ ⟨⟨h12₂, hm₂⟩, k₂⟩ => ?_
    have hK₂ : KK p s₂ := KK.keep ⟨s₀, minv, N, c, hs⟩ hm₂ (k₂.mono (by decide))
    refine WP.mono (htop p s₂ hK₂) fun s₃ ⟨h13₃, hm₃, k₃⟩ => ?_
    have hK₃ : KK p s₃ := KK.keep hK₂ hm₃ (k₃.mono (by decide))
    obtain ⟨hdi₃, hl₃, -, hb₃⟩ := hK₃.lds
    have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) := (k₃.gpr (by decide)).trans h12₂
    refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off p.B (slot p.w aAcc + 8 * fc p) ∧
        t.gpr .rbx = kb p aR ∧ t.mem = s₃.mem)
      (by
        xrun [State.ea, hdr, hdi₃, hdrOff, h13₃, hl₃ (sArr aAcc) (by decide), hl₃ (sArr aR) (by decide),
          hb₃ aAcc (by decide), hb₃ aR (by decide)]
        rw [eight_add]; exact off_off p.B _ _) rfl) fun t ⟨⟨a, b, hm⟩, k⟩ => ?_
    exact ⟨KK.keep hK₃ hm (k.mono (by decide)), regsAre_cons ((k.gpr (by decide)).trans hdi₃)
      (regsAre_cons ((k.gpr (by decide)).trans h12₃)
      (regsAre_cons ((k.gpr (by decide)).trans h13₃) (regsAre_cons a (regsAre_cons b regsAre_nil))))⟩
  refine RelCT.seq (R := Two (RT2 fl fc)) (two_post (two_taint [.rdi, .r12, .r13, .rsi, .rbx]
    (pins_regsAre (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)), (.r13, BitVec.ofNat 64 (fc p)),
      (.rsi, off p.B (slot p.w aAcc + 8 * fc p)), (.rbx, kb p aR)]) (fun _ => rfl) fun _ _ h => h.2)
    (by taint_decide)) fun p s h => ?_) ?_
  · obtain ⟨⟨s₀, minv, N, c, hs⟩, hr⟩ := h
    obtain ⟨hL', hL1, hLw⟩ := hL p s₀ hs
    have hn := c.good.scr.nowrap
    have hZ := c.hZ
    have := c.w2
    have := hfc p s₀ hs
    have eAcc : slot p.w aAcc = 256 + 16 * (p.w + 2) := by unfold slot hdrBytes aAcc; omega
    have eR : slot p.w aR = 256 + 48 * (p.w + 2) := by unfold slot hdrBytes aR; omega
    have e8 : slot p.w 8 = 256 + 64 * (p.w + 2) := by unfold slot hdrBytes; omega
    have hsi : s.gpr .rsi = off p.B (slot p.w aAcc + 8 * fc p) := hr (.rsi, off p.B (slot p.w aAcc + 8 * fc p)) (by simp)
    have hbx : s.gpr .rbx = off p.B (slot p.w aR) := hr (.rbx, kb p aR) (by simp)
    have h12 : s.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) := hr (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)) (by simp)
    have h13 : s.gpr .r13 = BitVec.ofNat 64 (fc p) := hr (.r13, BitVec.ofNat 64 (fc p)) (by simp)
    refine WP.mono (copyWords_ok hsi hbx h12 (by omega) (by omega) (by omega)
      (fun i hi => c.good.scr.ld (by omega)) (fun i hi => c.good.scr.st (by omega))
      (fun i hi b hb => by rw [ofs_off p.B (by omega)]; omega)) fun t ⟨_, _, ho, k⟩ => ?_
    have ha : Arrays p.B p.w [aR] s.mem t.mem :=
      Arrays.of_outside (j := aR) (by simp) ho (Nat.le_refl _) (by omega)
    exact ⟨⟨s₀, minv, N, c.arr ha (by decide) (by decide) (by decide) (k.mono (by decide)), hs⟩,
      (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h13⟩
  refine hdr_ct (Φ := RT2 fl fc) (pins_of (fun p _ => p.B) fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi)
    (rs := [.rbx, .r10, .r8, .r12, .rsi, .r9, .r13]) (fun p => [(.rbx, kb p aR), (.r10, kb p aM),
      (.r8, kb p aX), (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)), (.rsi, kb p aT), (.r9, kb p aAcc),
      (.r13, BitVec.ofNat 64 (fc p))]) (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
  obtain ⟨hdi, hl, -, hb'⟩ := h.1.lds
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .rsi, .r9] (Q := fun t => t.gpr .rbx = kb p aR ∧
      t.gpr .r10 = kb p aM ∧ t.gpr .r8 = kb p aX ∧ t.gpr .rsi = kb p aT ∧ t.gpr .r9 = kb p aAcc)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr aR) (by decide), hl (sArr aM) (by decide),
      hl (sArr aX) (by decide), hl (sArr aT) (by decide), hl (sArr aAcc) (by decide), hb' aR (by decide),
      hb' aM (by decide), hb' aX (by decide), hb' aT (by decide), hb' aAcc (by decide)]) rfl)
    fun t ⟨⟨a, b, c, d, e⟩, k⟩ => ?_
  exact regsAre_cons a (regsAre_cons b (regsAre_cons c (regsAre_cons ((k.gpr (by decide)).trans h.2.1)
    (regsAre_cons d (regsAre_cons e (regsAre_cons ((k.gpr (by decide)).trans h.2.2) regsAre_nil))))))

theorem ckModChecks_ct {sX sXlen sDX : Nat} (hsXl : sXlen < 32) (nXl : sXlen ≠ sMask) (fl : KPub → Nat)
    (hX : ∀ p s, KS p s → word s.mem p.B (8 * sXlen) = BitVec.ofNat 64 (fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    (hM : RelCT isa (Two KK) (seqs (loadNum aM sX sXlen)) (Two KK))
    (hDX : RelCT isa (Two KK) (seqs (loadNum aX sDX sXlen)) (Two KK))
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Impl.Rsa.X86_64.CheckCrtKey.lenWords sXlen ++
      Impl.Rsa.X86_64.CheckCrtKey.topE ++
      ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
        .mov .rbx (.mem (hdr (sArr aR)))] : List Instr))) hc₁).isSome = true)
    :
    RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.modChecks sX sXlen sDX)) (Two KK) := by
  unfold Impl.Rsa.X86_64.CheckCrtKey.modChecks
  have hR : RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sXlen
      Impl.Rsa.X86_64.CheckCrtKey.topE)) (Two KK) :=
    reduceTopK_ct fl (fun _ => 1) hsXl nXl hX (fun p s h => by have := (hX p s h).2.2; omega) (fun _ t _ => topE_ok t)
      (fun p s h => by
        obtain ⟨s₀, minv, N, c, hs⟩ := h
        obtain ⟨a, c1, c2⟩ := hX p s₀ hs
        have := c.w2
        exact WP.mono (reduceTopK c (Nx := p.w + 2) hsXl nXl a c1 c2 (fun t _ _ => topE_ok t) (Nat.le_refl _) (by omega)
          (by omega)) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩) hT
  refine kk_app (by simp [loadNum]) (by simp [eqOne])
    (kk_app (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
    (kk_app (by simp [loadNum]) (by simp [mulE]) (kk_app (by simp [loadNum]) (by simp [ltMask])
    (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [decM]) hM decMK_ct) hDX) ltXM) mulEK_ct) hR) eqOneK_ct

theorem topQK_ok {p : KPub} {t : State} (h : KK p t) :
    WP isa (.block Impl.Rsa.X86_64.CheckCrtKey.topQ) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 ((p.ql + 7) / 8) ∧
      t'.mem = t.mem ∧ Keep [.r13] t t' := by
  obtain ⟨s₀, minv, N, c, hs⟩ := h
  have := c.w2
  have := hs.ql2
  exact topQ_ok c.good c.hZ (by rw [c.hdr sQlen (by decide) (by decide)]; exact hs.hQl) (by omega)

theorem reduceTopQK_ct : RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sPlen
    Impl.Rsa.X86_64.CheckCrtKey.topQ)) (Two KK) :=
  reduceTopK_ct (·.pl) (fun p => (p.ql + 7) / 8) (by decide) (by decide) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩)
    (fun _ _ h => by have := h.pl2; have := h.ql2; omega) (fun _ _ h => topQK_ok h)
    (fun p s h => by
      obtain ⟨s₀, minv, N, c, hs⟩ := h
      have := c.w2
      have := hs.ql2
      have := hs.pl2
      have := hs.ql1
      have hq : ∀ t : State, (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) →
          word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql := fun t hh => by
        rw [hh _ (by decide), c.hdr sQlen (by decide) (by decide)]; exact hs.hQl
      exact WP.mono (reduceTopK c (Nx := 2 * p.w + 2) (by decide) (by decide) hs.hPl hs.pl1 hs.pl2
        (fun t hg hh => topQ_ok hg c.hZ (hq t hh) (by omega)) (by omega) (by omega) (by omega))
        fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩) (by taint_decide)

/-- `main` is constant time from `M0`. -/
theorem ckMain_ct : RelCT isa (Two M0) Impl.Rsa.X86_64.CheckCrtKey.main fun _ _ => True := by
  rw [crtMain_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq setupK_ct
    (RelCT.mono (P := Two KK) ?_ (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a.kp, h₁, h₂⟩) fun _ _ h => h))
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (RelCT.seq (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulXRK_ct) eqCheckK_ct) ?_)
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (RelCT.seq
    (ckModChecks_ct (by decide) (by decide) (·.pl) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩) ld_PM ld_DP
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (by simp [loadNum])
    (RelCT.seq (ckModChecks_ct (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql1, h.ql2⟩) ld_QM ld_DQ
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum])
      (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
      (kk_app (by simp [loadNum]) (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) (kk_app (by simp [loadNum]) (by simp [ltMask])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulXRK_ct) reduceTopQK_ct)
      eqOneK_ct)
    ?_)
  exact outK_ct

end VG.Proof.Rsa.X86_64.Key
