import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs

/-!
# RSA with the CRT on AArch64: setting up the primes

`primesSetup`, from the modulus' workspace: the workspaces of `p` and `q`
after it, `p` and `qInv` into `p`'s, and `q` into `q`'s
(`primesSetup_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- Entering a prime's workspace from the modulus'. -/
theorem SubCtx.mk' {t : State} {B : Addr} {Z o w wx : Nat} {minvN minv : BitVec 64}
    (hs : Scr t B Z) (hH : Hdr t.mem B w minvN) (hws : WsAt t.mem B o wx minv) (h0 : t.gpr .x0 = off B o)
    (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) : SubCtx t B Z o w wx minv :=
  ⟨hs, h0, hws.hdr, hws.link, hH.hw, hH.harr, hlo, hhi⟩

theorem SubCtx.ws {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv) :
    WsAt t.mem B o wx minv :=
  ⟨h.hdr, h.link⟩

/-- `primesSetup`: the primes' workspaces, `p` and `qInv` into `p`'s (arrays
`aN` and `aChunk`), and `q` into `q`'s. -/
theorem primesSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {pl ql : Nat} {pp qp ip : Addr}
    {pb qb ib : List Byte} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw30 : w < 2 ^ 28)
    (hZ : offQ w pl + slot (wsWords ql) 8 + tabBytes (wsWords ql) ≤ Z)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (hpp : word s.mem B (8 * sP) = pp) (hqp : word s.mem B (8 * sQ) = qp) (hip : word s.mem B (8 * sQinv) = ip)
    (hpb : Src s B Z pp pb) (hqb : Src s B Z qp qb) (hib : Src s B Z ip ib)
    (hpbl : pb.length = pl) (hqbl : qb.length = ql) (hibl : ib.length = pl)
    (hpl1 : 1 ≤ pl) (hpl2 : pl < 8 * w) (hql1 : 1 ≤ ql) (hql2 : ql < 8 * w) :
    WP isa (seqs primesSetup) s fun t => Good t B Z w minv ∧
      word t.mem B (8 * sWsP) = off B (offP w) ∧ word t.mem B (8 * sWsQ) = off B (offQ w pl) ∧
      (∃ mp, WsAt t.mem B (offP w) (wsWords pl) mp) ∧ (∃ mq, WsAt t.mem B (offQ w pl) (wsWords ql) mq) ∧
      wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = Spec.Rsa.os2ip pb ∧
      wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = Spec.Rsa.os2ip ib ∧
      wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Spec.Rsa.os2ip qb ∧
      Frm B [(8 * sWsP, 8), (8 * sWsQ, 8), (offP w, slot (wsWords pl) 8 + tabBytes (wsWords pl) + slot (wsWords ql) 8)]
        s.mem t.mem ∧
      Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hs := hg.scr
  have hpw := wsWords_le hpl2 (by omega)
  have hqw := wsWords_le hql2 (by omega)
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  unfold offQ at hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold primesSetup
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `p`'s workspace.
  refine WP.seq ?_
  rw [show mov .x5 .x0 :: wsEnd = [mov .x5 .x0] ++ wsEnd from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = B ∧ t.mem = s.mem) (by brun [hg.x0]) (by decide)
    (by decide) (by decide +kernel)) fun s₁ ⟨⟨hdx₁, hm₁⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  refine WP.mono (wsEnd_ok (wx := w) hs₁ hdx₁ (by rw [hm₁]; exact hg.hdr.hw) (by omega)
    (by rw [hm₁]; exact hg.hdr.harr _ (by decide)) (by omega)) fun s₂ ⟨⟨hax₂, _, hm₂⟩, k₂⟩ => ?_
  have k02 := k₁.trans k₂
  have hm02 : s₂.mem = s.mem := hm₂.trans hm₁
  refine WP.seq ?_
  refine WP.mono (wsNew_ok (o := offP w) (len := pl) (hs.congr k02.wr) ((k02.gpr .x0 (by decide)).trans hg.x0) hax₂
    (by decide) (by decide) (by decide) (by rw [hm02]; exact hpl) (by omega) (by unfold offP; omega)
    (by unfold offP; omega)) fun s₃ ⟨hWsP₃, hlP₃, hwP₃, haP₃, hdi₃, f₃, k₃⟩ => ?_
  have hs₃ := hs.congr (k02.trans k₃).wr
  have hb₃ : ∀ i < 32, i ≠ sWsP → word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hne => by
    rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; unfold sWsP sFn at hne ⊢; omega
      · simp only; unfold offP; omega) (by omega), hm02]
  -- `q`'s workspace.
  refine WP.seq ?_
  rw [show ldh .x5 sWsP :: wsEndT = [ldh .x5 sWsP] ++ wsEndT from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off B (offP w) ∧ t.mem = s₃.mem)
    (by brun [hdi₃, hdr_enc (show sWsP < 32 by decide), hs₃.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hWsP₃])
    (by decide) (by decide) (by decide +kernel))
    fun s₄ ⟨⟨hdx₄, hm₄⟩, k₄⟩ => ?_
  refine WP.mono (wsEndT_ok (wx := wsWords pl) ((hs.congr ((k02.trans k₃).trans k₄).wr).sub
    (o := offP w) (n := slot (wsWords pl) 8) (by unfold offP; omega) (by omega)) hdx₄
    (by rw [hm₄]; exact hwP₃) (by omega) (by rw [hm₄]; exact haP₃ _ (by decide)) (Nat.le_refl _))
    fun s₅ ⟨⟨hax₅, hm₅⟩, k₅⟩ => ?_
  rw [off_off] at hax₅
  have k05 := ((k02.trans k₃).trans k₄).trans k₅
  have hm35 : s₅.mem = s₃.mem := hm₅.trans hm₄
  refine WP.seq ?_
  refine WP.mono (wsNew_ok (o := offQ w pl) (len := ql) (hs.congr k05.wr) ((k05.gpr .x0 (by decide)).trans hg.x0)
    (by rw [hax₅]; exact congrArg (off B) (by unfold offQ offP; omega)) (by decide) (by decide) (by decide)
    (by rw [hm35, hb₃ _ (by decide) (by decide)]; exact hql) (by omega) (by unfold offQ; omega)
    (by unfold offQ; omega)) fun s₆ ⟨hWsQ₆, hlQ₆, hwQ₆, haQ₆, hdi₆, f₆, k₆⟩ => ?_
  have k06 := k05.trans k₆
  have hs₆ := hs.congr k06.wr
  have hoq : offP w + 256 ≤ offQ w pl := by unfold offP offQ; omega
  have f36 : Frm B [(8 * sWsQ, 8), (offP w + 256, slot (wsWords pl) 8 + tabBytes (wsWords pl) - 256 +
      slot (wsWords ql) 8)] s₃.mem s₆.mem := by
    rw [← hm35]
    refine f₆.widen fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨(offP w + 256, slot (wsWords pl) 8 + tabBytes (wsWords pl) - 256 + slot (wsWords ql) 8), by simp,
        hoq, ?_⟩
      show offQ w pl + 8 * 17 ≤ offP w + 256 + (slot (wsWords pl) 8 + tabBytes (wsWords pl) - 256 + slot (wsWords ql) 8)
      unfold offQ offP; omega
  -- Into `p`'s workspace.
  refine WP.seq ?_
  have hWsP₆ : word s₆.mem B (8 * sWsP) = off B (offP w) := by
    rw [f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inl (show 8 * sWsP + 8 ≤ offQ w pl by unfold offQ; unfold sWsP sFn; omega)) (by unfold sWsP sFn; omega), hm35]
    exact hWsP₃
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B (offP w) ∧ t.mem = s₆.mem)
    (by brun [enterP, hdi₆, hdr_enc (show sWsP < 32 by decide), hs₆.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega),
      hWsP₆]) (by decide) (by decide) (by decide +kernel))
    fun s₇ ⟨⟨hdi₇, hm₇⟩, k₇⟩ => ?_
  have k07 := k06.trans k₇
  have hs₇ := hs.congr k07.wr
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  -- The modulus' header and `p`'s, as `wsNew` left them.
  have hb₆ : ∀ i < 32, i ≠ sWsP → i ≠ sWsQ → word s₇.mem B (8 * i) = word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₇, f36.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * i + 8 ≤ 8 * sWsQ ∨ 8 * sWsQ + 8 ≤ 8 * i
        unfold sWsQ sFn at h2 ⊢; omega
      · exact Or.inl (show 8 * i + 8 ≤ offP w + 256 by unfold offP; omega)) (by omega)]
    exact hb₃ i hi h1
  have hp₆ : ∀ i < 32, word s₇.mem (off B (offP w)) (8 * i) = word s₃.mem (off B (offP w)) (8 * i) := fun i hi => by
    rw [hm₇, word_off, word_off, f36.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (show 8 * sWsQ + 8 ≤ offP w + 8 * i by unfold offP sWsQ sFn; omega)
      · exact Or.inl (show offP w + 8 * i + 8 ≤ offP w + 256 by omega)) (by unfold offP; omega)]
  have hHn₇ : Hdr s₇.mem B w minv :=
    ⟨(hb₆ _ (by decide) (by decide) (by decide)).trans hg.hdr.hw,
      (hb₆ _ (by decide) (by decide) (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₆ _ (by unfold sArr; omega) (by unfold sArr sWsP sFn; omega)
        (by unfold sArr sWsQ sFn; omega)).trans (hg.hdr.harr j hj)⟩
  have hWp₇ : WsAt s₇.mem B (offP w) (wsWords pl) (word s₇.mem (off B (offP w)) (8 * sMinv)) :=
    ⟨hdr_any ((hp₆ _ (by decide)).trans hwP₃) fun j hj => (hp₆ _ (by unfold sArr; omega)).trans (haP₃ j hj),
      (hp₆ _ (by decide)).trans hlP₃⟩
  have hcP₇ := SubCtx.mk' hs₇ hHn₇ hWp₇ hdi₇ (by unfold offP; omega) (by unfold offP; omega)
  have i07 : InScr B Z s.mem s₇.mem := by
    have a := InScr.of_frm (Z := Z) f₃ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * sWsP + 8 ≤ Z; unfold sWsP sFn; omega
      · show offP w + 8 * 17 ≤ Z; unfold offP; omega)
    have b := InScr.of_frm (Z := Z) f₆ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * sWsQ + 8 ≤ Z; unfold sWsQ sFn; omega
      · show offQ w pl + 8 * 17 ≤ Z; unfold offQ; omega)
    rw [hm02] at a
    rw [hm35] at b
    rw [hm₇]; exact a.trans b
  refine wp_seqs_append (by simp [loadArr]) (by simp [loadArr]) ?_
  refine WP.mono (primeLoad_ok hcP₇ hwp2 (wsWords_le hpl2 (by omega)) (by omega) (j := Public.aN) (by decide)
    (sp := sP) (sl := sPlen) (by decide) (by decide) (by rw [hb₆ _ (by decide) (by decide) (by decide)]; exact hpp)
    (by rw [hb₆ _ (by decide) (by decide) (by decide), hpbl]; exact hpl) (hpb.congrK i07 k07) (by omega)
    (by omega) (by unfold wsWords; omega)) fun s₈ ⟨hcP₈, hpv₈, ho₈, k₈⟩ => ?_
  have hPZ : offP w + slot (wsWords pl) 8 + tabBytes (wsWords pl) ≤ Z := by unfold offP; omega
  have hQZ : offQ w pl + slot (wsWords ql) 8 + tabBytes (wsWords ql) ≤ Z := by unfold offQ; omega
  have fl8 : Frm B [(offP w + 256, slot (wsWords pl) 8 - 256)] s₇.mem s₈.mem :=
    Frm.of_load ho₈ (by decide) (by omega) (by simp)
  have hb₈ : ∀ i < 32, word s₈.mem B (8 * i) = word s₇.mem B (8 * i) := fun i hi =>
    fl8.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ offP w + 256 by unfold offP; omega)) (by omega)
  have i78 : InScr B Z s₇.mem s₈.mem := InScr.of_frm fl8 fun r hr => by
    rw [List.mem_singleton.mp hr]; show offP w + 256 + (slot (wsWords pl) 8 - 256) ≤ Z; omega
  refine wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (primeLoad_ok hcP₈ hwp2 (wsWords_le hpl2 (by omega)) (by omega) (j := aChunk) (by decide)
    (sp := sQinv) (sl := sPlen) (by decide) (by decide)
    (by rw [hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide)]; exact hip)
    (by rw [hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide), hibl]; exact hpl)
    (hib.congrK (i07.trans i78) (k07.trans k₈)) (by omega) (by omega) (by unfold wsWords; omega))
    fun s₉ ⟨hcP₉, hcv₉, ho₉, k₉⟩ => ?_
  have fl9 : Frm B [(offP w + 256, slot (wsWords pl) 8 - 256)] s₈.mem s₉.mem :=
    Frm.of_load ho₉ (by decide) (by omega) (by simp)
  have hb₉ : ∀ i < 32, word s₉.mem B (8 * i) = word s₈.mem B (8 * i) := fun i hi =>
    fl9.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ offP w + 256 by unfold offP; omega)) (by omega)
  have i89 : InScr B Z s₈.mem s₉.mem := InScr.of_frm fl9 fun r hr => by
    rw [List.mem_singleton.mp hr]; show offP w + 256 + (slot (wsWords pl) 8 - 256) ≤ Z; omega
  have hq₉ : ∀ i < 32, word s₉.mem (off B (offQ w pl)) (8 * i) = word s₇.mem (off B (offQ w pl)) (8 * i) :=
    fun i hi => by
      rw [word_off, word_off, (fl8.trans fl9).word_eq (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Or.inr (show offP w + 256 + (slot (wsWords pl) 8 - 256) ≤ offQ w pl + 8 * i by
          unfold offQ offP; omega)) (by unfold offQ; omega)]
  -- Into `q`'s workspace.
  have hWsQ₉ : word s₉.mem B (8 * sWsQ) = off B (offQ w pl) := by
    rw [hb₉ _ (by decide), hb₈ _ (by decide), hm₇]; exact hWsQ₆
  refine WP.seq ?_
  have hl₉ : ∀ i < 32, InRegions (s₉.rd ++ s₉.wr) (off B (8 * i)) 8 := fun i hi => hcP₉.scr.ld (by omega)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B (offQ w pl) ∧ t.mem = s₉.mem)
    (by brun [leave, enterQ, hcP₉.x0, hdr_enc (show sLink < 32 by decide), hdr_enc (show sWsQ < 32 by decide),
      hcP₉.ld' (show sLink < 32 by decide), hcP₉.link', hl₉ sWsQ (by decide), hWsQ₉])
    (by decide) (by decide) (by decide +kernel))
    fun s₁₀ ⟨⟨hdi₁₀, hm₁₀⟩, k₁₀⟩ => ?_
  have k010 := ((k07.trans k₈).trans k₉).trans k₁₀
  have hs₁₀ := hs.congr k010.wr
  have hHn₁₀ : Hdr s₁₀.mem B w minv := by
    rw [hm₁₀]
    exact ⟨(hb₉ _ (by decide)).trans ((hb₈ _ (by decide)).trans hHn₇.hw),
      (hb₉ _ (by decide)).trans ((hb₈ _ (by decide)).trans hHn₇.hminv),
      fun j hj => (hb₉ _ (by unfold sArr; omega)).trans ((hb₈ _ (by unfold sArr; omega)).trans (hHn₇.harr j hj))⟩
  have hqs₇ : ∀ i < 32, word s₇.mem (off B (offQ w pl)) (8 * i) = word s₆.mem (off B (offQ w pl)) (8 * i) :=
    fun i _ => by rw [hm₇]
  have hWq₁₀ : WsAt s₁₀.mem B (offQ w pl) (wsWords ql) (word s₁₀.mem (off B (offQ w pl)) (8 * sMinv)) := by
    rw [hm₁₀]
    exact ⟨hdr_any ((hq₉ _ (by decide)).trans ((hqs₇ _ (by decide)).trans hwQ₆))
      fun j hj => (hq₉ _ (by unfold sArr; omega)).trans ((hqs₇ _ (by unfold sArr; omega)).trans (haQ₆ j hj)),
      (hq₉ _ (by decide)).trans ((hqs₇ _ (by decide)).trans hlQ₆)⟩
  have hcQ₁₀ := SubCtx.mk' hs₁₀ hHn₁₀ hWq₁₀ hdi₁₀ (by unfold offQ; omega) hQZ
  refine wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (primeLoad_ok hcQ₁₀ hwq2 (wsWords_le hql2 (by omega)) (by omega) (j := Public.aN) (by decide)
    (sp := sQ) (sl := sQlen) (by decide) (by decide)
    (by rw [hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide)]; exact hqp)
    (by rw [hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide), hqbl]; exact hql)
    (hqb.congrK ((i07.trans i78).trans (by rw [hm₁₀]; exact i89)) k010) (by omega) (by omega)
    (by unfold wsWords; omega)) fun s₁₁ ⟨hcQ₁₁, hqv₁₁, ho₁₁, k₁₁⟩ => ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₁₁.mem)
    (by brun [leave, hcQ₁₁.x0, hdr_enc (show sLink < 32 by decide), hcQ₁₁.ld' (show sLink < 32 by decide),
      hcQ₁₁.link']) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have fl11 : Frm B [(offQ w pl + 256, slot (wsWords ql) 8 - 256)] s₁₀.mem t.mem := by
    rw [hm]; exact Frm.of_load ho₁₁ (by decide) (by omega) (by simp)
  have hbt : ∀ i < 32, word t.mem B (8 * i) = word s₁₀.mem B (8 * i) := fun i hi =>
    fl11.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ offQ w pl + 256 by unfold offQ; omega))
      (by omega)
  have hpt : ∀ i < 17, word t.mem (off B (offP w)) (8 * i) = word s₇.mem (off B (offP w)) (8 * i) := fun i hi => by
    rw [word_off, word_off, fl11.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show offP w + 8 * i + 8 ≤ offQ w pl + 256 by unfold offQ offP; omega)) (by unfold offP; omega),
      hm₁₀, (fl8.trans fl9).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show offP w + 8 * i + 8 ≤ offP w + 256 by omega))
      (by unfold offP; omega)]
  have hqt : ∀ i < 17, word t.mem (off B (offQ w pl)) (8 * i) = word s₁₀.mem (off B (offQ w pl)) (8 * i) :=
    fun i hi => by
      rw [word_off, word_off, fl11.word_eq (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Or.inl (show offQ w pl + 8 * i + 8 ≤ offQ w pl + 256 by omega))
        (by unfold offQ; omega)]
  have kall := ((k010.trans k₁₁).trans k')
  refine ⟨⟨hs.congr kall.wr, hdi, ?_⟩, ?_, ?_, ⟨_, hWp₇.of_words hpt⟩, ⟨_, hWq₁₀.of_words hqt⟩, ?_, ?_, ?_, ?_,
    ⟨fun r hr => ?_, kall.rd, kall.wr, kall.sp, kall.vcs⟩⟩
  · exact ⟨(hbt _ (by decide)).trans hHn₁₀.hw, (hbt _ (by decide)).trans hHn₁₀.hminv,
      fun j hj => (hbt _ (by unfold sArr; omega)).trans (hHn₁₀.harr j hj)⟩
  · rw [hbt _ (by decide), hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hm₇]; exact hWsP₆
  · rw [hbt _ (by decide), hm₁₀]; exact hWsQ₉
  · have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide)
    have := slot_sep (w := wsWords pl) (show Public.aN ≠ aChunk by decide)
    rw [wv_off, fl11.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show offP w + slot (wsWords pl) Public.aN + 8 * wsWords pl ≤ offQ w pl + 256 by
        unfold offQ offP; omega)) (by unfold offP; omega), hm₁₀, ← wv_off,
      ho₉.wv (by omega) (by omega)]
    exact hpv₈
  · have := slot_le (w := wsWords pl) (show aChunk < 8 by decide)
    rw [wv_off, fl11.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show offP w + slot (wsWords pl) aChunk + 8 * wsWords pl ≤ offQ w pl + 256 by
        unfold offQ offP; omega)) (by unfold offP; omega), hm₁₀, ← wv_off]
    exact hcv₉
  · rw [hm]; exact hqv₁₁
  · have f02 : Frm B [(8 * sWsP, 8), (offP w, 8 * 17)] s.mem s₃.mem := by rw [← hm02]; exact f₃
    have f36' : Frm B [(8 * sWsQ, 8), (offQ w pl, 8 * 17)] s₃.mem s₆.mem := by rw [← hm35]; exact f₆
    have f710 : Frm B [(offP w + 256, slot (wsWords pl) 8 - 256)] s₆.mem s₁₀.mem := by
      rw [hm₁₀, ← hm₇]; exact fl8.trans fl9
    refine (((f02.append f36').append f710).append fl11).widen fun r hr => ?_
    have hP : (offP w, slot (wsWords pl) 8 + tabBytes (wsWords pl) + slot (wsWords ql) 8) ∈
        [(8 * sWsP, 8), (8 * sWsQ, 8), (offP w, slot (wsWords pl) 8 + tabBytes (wsWords pl) + slot (wsWords ql) 8)] := by
      simp
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hP, Nat.le_refl _, show offP w + 8 * 17 ≤ _ by omega⟩
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hP, show offP w ≤ offQ w pl by unfold offQ offP; omega,
        show offQ w pl + 8 * 17 ≤ _ by unfold offQ offP; omega⟩
    · exact ⟨_, hP, show offP w ≤ offP w + 256 by omega, show offP w + 256 + _ ≤ _ by omega⟩
    · exact ⟨_, hP, show offP w ≤ offQ w pl + 256 by unfold offQ offP; omega,
        show offQ w pl + 256 + _ ≤ _ by unfold offQ offP; omega⟩
  · by_cases h : r = .x0
    · subst h; rw [hdi, hg.x0]
    · exact kall.gpr r (by revert hr h; cases r <;> decide)

end VG.Proof.Bignum.AArch64
