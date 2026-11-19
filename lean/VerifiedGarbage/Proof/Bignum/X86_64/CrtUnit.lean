module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import Aesop.BuiltinRules

/-! ### `Bignum.X86_64.CrtSetup`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on x86-64: setting up the primes

`primesSetup`, from the modulus' workspace: the workspaces of `p` and `q`
after it, `p` and `qInv` into `p`'s, and `q` into `q`'s
(`primesSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Entering a prime's workspace from the modulus'. -/
theorem SubCtx.mk' {t : State} {B : Addr} {Z o w wx : Nat} {minvN minv : BitVec 64}
    (hs : Scr t B Z) (hH : Hdr t.mem B w minvN) (hws : WsAt t.mem B o wx minv) (hdi : t.gpr .rdi = off B o)
    (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) : SubCtx t B Z o w wx minv :=
  ⟨hs, hdi, hws.hdr, hws.link, hH.hw, hH.harr, hlo, hhi⟩

theorem SubCtx.ws {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv) :
    WsAt t.mem B o wx minv :=
  ⟨h.hdr, h.link⟩

/-- `primesSetup`: the primes' workspaces, `p` and `qInv` into `p`'s (arrays
`aN` and `aChunk`), and `q` into `q`'s. -/
theorem primesSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {pl ql : Nat} {pp qp ip : Addr}
    {pb qb ib : List Byte} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw30 : w < 2 ^ 28)
    (hZ : offQ w pl + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z)
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
      Frm B [(8 * sWsP, 8), (8 * sWsQ, 8), (offP w, slot (wsWords pl) 8 + wsTab (wsWords pl) + slot (wsWords ql) 8)]
        s.mem t.mem ∧
      Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hs := hg.scr
  obtain hpw := wsWords_le hpl2 (by omega_using [hw])
  obtain hqw := wsWords_le hql2 (by omega_using [hw])
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  obtain hTP := tabBytes_le_wsTab (wsWords pl)
  obtain hTQ := tabBytes_le_wsTab (wsWords ql)
  unfold offQ at hZ
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hQ8, hi])
  unfold primesSetup
  simp only [List.append_assoc]
  -- `p`'s workspace.
  refine wp_seqs_append (by simp) (by simp) ?_
  show WP isa (.block (_ ++ wsEnd)) s _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = B ∧ t.mem = s.mem) (by xrun [hg.rdi]) rfl)
    fun s₁ ⟨⟨hdx₁, hm₁⟩, k₁⟩ => ?_
  obtain hs₁ := hs.congr k₁.2.2
  refine WP.mono (wsEnd_ok (wx := w) hs₁ hdx₁ (by rw [hm₁]; exact hg.hdr.hw) (by rw [hm₁]; exact hg.hdr.harr _ (by decide))
    (by omega_using [hZ])) fun s₂ ⟨hax₂, hm₂, k₂⟩ => ?_
  obtain k02 := k₁.trans k₂
  obtain hm02 : s₂.mem = s.mem := hm₂.trans hm₁
  refine wp_seqs_append (by simp [wsNew]) (by simp) ?_
  refine WP.mono (wsNew_ok (o := offP w) (len := pl) (hs.congr k02.2.2) ((k02.gpr (by decide)).trans hg.rdi) hax₂
    (by decide) (by decide) (by decide) (by rw [hm02]; exact hpl) (by omega_using [hw30, hpl2]) (by unfold offP; omega_using [h8])
    (by unfold offP; omega_using [hZ])) fun s₃ ⟨hWsP₃, hlP₃, hwP₃, haP₃, hdi₃, f₃, k₃⟩ => ?_
  obtain hs₃ := hs.congr (k02.trans k₃).2.2
  obtain hb₃ : ∀ i < 32, i ≠ sWsP → word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hne => by
    rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; unfold sWsP sFn at hne ⊢; omega_using [hne]
      · simp only; unfold offP; omega_using [h8, hi]) (by omega_using [hi]), hm02]
  -- `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp) ?_
  show WP isa (.block (_ ++ wsEndT)) s₃ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = off B (offP w) ∧ t.mem = s₃.mem)
    (by xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega_using [hZ, hQ8]), hWsP₃]) rfl)
    fun s₄ ⟨⟨hdx₄, hm₄⟩, k₄⟩ => ?_
  refine WP.mono (wsEndT_ok (wx := wsWords pl) ((hs.congr ((k02.trans k₃).trans k₄).2.2).sub
    (o := offP w) (n := slot (wsWords pl) 8) (by unfold offP; omega_using [hZ]) (by omega_using [hP8])) hdx₄
    (by rw [hm₄]; exact hwP₃) (by rw [hm₄]; exact haP₃ _ (by decide)) (Nat.le_refl _))
    fun s₅ ⟨hax₅, hm₅, k₅⟩ => ?_
  rw [off_off] at hax₅
  obtain k05 := ((k02.trans k₃).trans k₄).trans k₅
  obtain hm35 : s₅.mem = s₃.mem := hm₅.trans hm₄
  refine wp_seqs_append (by simp [wsNew]) (by simp) ?_
  refine WP.mono (wsNew_ok (o := offQ w pl) (len := ql) (hs.congr k05.2.2) ((k05.gpr (by decide)).trans hg.rdi)
    (by rw [hax₅]; exact congrArg (off B) (by unfold offQ offP; omega_using [])) (by decide) (by decide) (by decide)
    (by rw [hm35, hb₃ _ (by decide) (by decide)]; exact hql) (by omega_using [hw30, hql2]) (by unfold offQ; omega_using [hP8])
    (by unfold offQ; omega_using [hZ])) fun s₆ ⟨hWsQ₆, hlQ₆, hwQ₆, haQ₆, hdi₆, f₆, k₆⟩ => ?_
  obtain k06 := k05.trans k₆
  obtain hs₆ := hs.congr k06.2.2
  obtain hoq : offP w + 256 ≤ offQ w pl := by unfold offP offQ; omega_using [hP8]
  obtain f36 : Frm B [(8 * sWsQ, 8), (offP w + 256, slot (wsWords pl) 8 + wsTab (wsWords pl) - 256 +
      slot (wsWords ql) 8)] s₃.mem s₆.mem := by
    rw [← hm35]
    refine f₆.widen fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨(offP w + 256, slot (wsWords pl) 8 + wsTab (wsWords pl) - 256 + slot (wsWords ql) 8), by simp,
        hoq, ?_⟩
      show offQ w pl + 8 * 17 ≤ offP w + 256 + (slot (wsWords pl) 8 + wsTab (wsWords pl) - 256 + slot (wsWords ql) 8)
      unfold offQ offP; omega_using [hQ8]
  -- Into `p`'s workspace.
  refine wp_seqs_append (by simp) (by simp [loadArr]) ?_
  obtain hWsP₆ : word s₆.mem B (8 * sWsP) = off B (offP w) := by
    rw [f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inl (show 8 * sWsP + 8 ≤ offQ w pl by unfold offQ; unfold sWsP sFn; omega_using [hP8]))
      (by unfold sWsP sFn; omega_using []), hm35]
    exact hWsP₃
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B (offP w) ∧ t.mem = s₆.mem)
    (by xrun [enterP, State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega_using [hZ, hQ8]), hWsP₆]) rfl)
    fun s₇ ⟨⟨hdi₇, hm₇⟩, k₇⟩ => ?_
  obtain k07 := k06.trans k₇
  obtain hs₇ := hs.congr k07.2.2
  obtain hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_using []
  obtain hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  -- The modulus' header and `p`'s, as `wsNew` left them.
  obtain hb₆ : ∀ i < 32, i ≠ sWsP → i ≠ sWsQ → word s₇.mem B (8 * i) = word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₇, f36.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * i + 8 ≤ 8 * sWsQ ∨ 8 * sWsQ + 8 ≤ 8 * i
        unfold sWsQ sFn at h2 ⊢; omega_using [h2]
      · exact Or.inl (show 8 * i + 8 ≤ offP w + 256 by unfold offP; omega_using [hi])) (by omega_using [hi])]
    exact hb₃ i hi h1
  obtain hp₆ : ∀ i < 32, word s₇.mem (off B (offP w)) (8 * i) = word s₃.mem (off B (offP w)) (8 * i) := fun i hi => by
    rw [hm₇, word_off, word_off, f36.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (show 8 * sWsQ + 8 ≤ offP w + 8 * i by unfold offP sWsQ sFn; omega_using [h8])
      · exact Or.inl (show offP w + 8 * i + 8 ≤ offP w + 256 by omega_using [hi])) (by unfold offP; omega_using [hZ, hn, hQ8, hi])]
  obtain hHn₇ : Hdr s₇.mem B w minv :=
    ⟨(hb₆ _ (by decide) (by decide) (by decide)).trans hg.hdr.hw,
      (hb₆ _ (by decide) (by decide) (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₆ _ (by unfold sArr; omega_using [hj]) (by unfold sArr sWsP sFn; omega_using [hj])
        (by unfold sArr sWsQ sFn; omega_using [hj])).trans (hg.hdr.harr j hj)⟩
  obtain hWp₇ : WsAt s₇.mem B (offP w) (wsWords pl) (word s₇.mem (off B (offP w)) (8 * sMinv)) :=
    ⟨hdr_any ((hp₆ _ (by decide)).trans hwP₃) fun j hj => (hp₆ _ (by unfold sArr; omega_using [hj])).trans (haP₃ j hj),
      (hp₆ _ (by decide)).trans hlP₃⟩
  obtain hcP₇ := SubCtx.mk' hs₇ hHn₇ hWp₇ hdi₇ (by unfold offP; omega_using []) (by unfold offP; omega_using [hZ, hTP])
  obtain i07 : InScr B Z s.mem s₇.mem := by
    obtain a := InScr.of_frm (Z := Z) f₃ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * sWsP + 8 ≤ Z; unfold sWsP sFn; omega_using [hZ, hQ8]
      · show offP w + 8 * 17 ≤ Z; unfold offP; omega_using [hZ, hQ8])
    obtain b := InScr.of_frm (Z := Z) f₆ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * sWsQ + 8 ≤ Z; unfold sWsQ sFn; omega_using [hZ, hQ8]
      · show offQ w pl + 8 * 17 ≤ Z; unfold offQ; omega_using [hZ, hQ8])
    rw [hm02] at a
    rw [hm35] at b
    rw [hm₇]; exact a.trans b
  refine wp_seqs_append (by simp [loadArr]) (by simp [loadArr]) ?_
  refine WP.mono (primeLoad_ok hcP₇ hwp2 (wsWords_le hpl2 (by omega_using [hqw, hwq2])) (by omega_using [hw30]) (j := Public.aN) (by decide)
    (sp := sP) (sl := sPlen) (by decide) (by decide) (by rw [hb₆ _ (by decide) (by decide) (by decide)]; exact hpp)
    (by rw [hb₆ _ (by decide) (by decide) (by decide), hpbl]; exact hpl) (hpb.congrK i07 k07) (by omega_using [hpbl, hpl1])
    (by omega_using [hw30, hpbl, hpl2]) (by unfold wsWords; omega_using [hpbl])) fun s₈ ⟨hcP₈, hpv₈, ho₈, k₈⟩ => ?_
  obtain hPZ : offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) ≤ Z := by unfold offP; omega_using [hZ]
  obtain hQZ : offQ w pl + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z := by unfold offQ; omega_using [hZ]
  obtain fl8 : Frm B [(offP w + 256, slot (wsWords pl) 8 - 256)] s₇.mem s₈.mem :=
    Frm.of_load ho₈ (by decide) (by omega_using [hn, hPZ]) (by simp)
  obtain hb₈ : ∀ i < 32, word s₈.mem B (8 * i) = word s₇.mem B (8 * i) := fun i hi =>
    fl8.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ offP w + 256 by unfold offP; omega_using [hi])) (by omega_using [hi])
  obtain i78 : InScr B Z s₇.mem s₈.mem := InScr.of_frm fl8 fun r hr => by
    rw [List.mem_singleton.mp hr]; show offP w + 256 + (slot (wsWords pl) 8 - 256) ≤ Z; omega_using [hoq, hPZ, hQZ]
  refine wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (primeLoad_ok hcP₈ hwp2 (wsWords_le hpl2 (by omega_using [hqw, hwq2])) (by omega_using [hw30]) (j := aChunk) (by decide)
    (sp := sQinv) (sl := sPlen) (by decide) (by decide)
    (by rw [hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide)]; exact hip)
    (by rw [hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide), hibl]; exact hpl)
    (hib.congrK (i07.trans i78) (k07.trans k₈)) (by omega_using [hibl, hpl1]) (by omega_using [hw30, hibl, hpl2]) (by unfold wsWords; omega_using [hibl]))
    fun s₉ ⟨hcP₉, hcv₉, ho₉, k₉⟩ => ?_
  obtain fl9 : Frm B [(offP w + 256, slot (wsWords pl) 8 - 256)] s₈.mem s₉.mem :=
    Frm.of_load ho₉ (by decide) (by omega_using [hn, hPZ]) (by simp)
  obtain hb₉ : ∀ i < 32, word s₉.mem B (8 * i) = word s₈.mem B (8 * i) := fun i hi =>
    fl9.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ offP w + 256 by unfold offP; omega_using [hi])) (by omega_using [hi])
  obtain i89 : InScr B Z s₈.mem s₉.mem := InScr.of_frm fl9 fun r hr => by
    rw [List.mem_singleton.mp hr]; show offP w + 256 + (slot (wsWords pl) 8 - 256) ≤ Z; omega_using [hoq, hPZ, hQZ]
  obtain hq₉ : ∀ i < 32, word s₉.mem (off B (offQ w pl)) (8 * i) = word s₇.mem (off B (offQ w pl)) (8 * i) :=
    fun i hi => by
      rw [word_off, word_off, (fl8.trans fl9).word_eq (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Or.inr (show offP w + 256 + (slot (wsWords pl) 8 - 256) ≤ offQ w pl + 8 * i by
          unfold offQ offP; omega_using [hP8])) (by unfold offQ; omega_using [hZ, hn, hQ8, hi])]
  -- Into `q`'s workspace.
  obtain hWsQ₉ : word s₉.mem B (8 * sWsQ) = off B (offQ w pl) := by
    rw [hb₉ _ (by decide), hb₈ _ (by decide), hm₇]; exact hWsQ₆
  refine wp_seqs_append (by simp) (by simp [loadArr]) ?_
  obtain hl₉ : ∀ i < 32, InRegions (s₉.rd ++ s₉.wr) (off B (8 * i)) 8 := fun i hi => hcP₉.scr.ld (by omega_using [hoq, hQZ, hi])
  obtain hlp₉ : InRegions (s₉.rd ++ s₉.wr) (off (off B (offP w)) (8 * sLink)) 8 :=
    hcP₉.good.scr.ld (by unfold sLink sFn; omega_using [hP8])
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B (offQ w pl) ∧ t.mem = s₉.mem)
    (by xrun [leave, enterQ, State.ea, hdr, hcP₉.rdi, hdrOff, hlp₉, hcP₉.link, hl₉ sWsQ (by decide), hWsQ₉]) rfl)
    fun s₁₀ ⟨⟨hdi₁₀, hm₁₀⟩, k₁₀⟩ => ?_
  obtain k010 := ((k07.trans k₈).trans k₉).trans k₁₀
  obtain hs₁₀ := hs.congr k010.2.2
  obtain hHn₁₀ : Hdr s₁₀.mem B w minv := by
    rw [hm₁₀]
    exact ⟨(hb₉ _ (by decide)).trans ((hb₈ _ (by decide)).trans hHn₇.hw),
      (hb₉ _ (by decide)).trans ((hb₈ _ (by decide)).trans hHn₇.hminv),
      fun j hj => (hb₉ _ (by unfold sArr; omega_using [hj])).trans ((hb₈ _ (by unfold sArr; omega_using [hj])).trans (hHn₇.harr j hj))⟩
  obtain hqs₇ : ∀ i < 32, word s₇.mem (off B (offQ w pl)) (8 * i) = word s₆.mem (off B (offQ w pl)) (8 * i) :=
    fun i _ => by rw [hm₇]
  obtain hWq₁₀ : WsAt s₁₀.mem B (offQ w pl) (wsWords ql) (word s₁₀.mem (off B (offQ w pl)) (8 * sMinv)) := by
    rw [hm₁₀]
    exact ⟨hdr_any ((hq₉ _ (by decide)).trans ((hqs₇ _ (by decide)).trans hwQ₆))
      fun j hj => (hq₉ _ (by unfold sArr; omega_using [hj])).trans ((hqs₇ _ (by unfold sArr; omega_using [hj])).trans (haQ₆ j hj)),
      (hq₉ _ (by decide)).trans ((hqs₇ _ (by decide)).trans hlQ₆)⟩
  obtain hcQ₁₀ := SubCtx.mk' hs₁₀ hHn₁₀ hWq₁₀ hdi₁₀ (by unfold offQ; omega_using []) (by omega_using [hTQ, hQZ])
  refine wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (primeLoad_ok hcQ₁₀ hwq2 (wsWords_le hql2 (by omega_using [hqw, hwq2])) (by omega_using [hw30]) (j := Public.aN) (by decide)
    (sp := sQ) (sl := sQlen) (by decide) (by decide)
    (by rw [hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide)]; exact hqp)
    (by rw [hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide), hqbl]; exact hql)
    (hqb.congrK ((i07.trans i78).trans (by rw [hm₁₀]; exact i89)) k010) (by omega_using [hqbl, hql1]) (by omega_using [hw30, hqbl, hql2])
    (by unfold wsWords; omega_using [hqbl])) fun s₁₁ ⟨hcQ₁₁, hqv₁₁, ho₁₁, k₁₁⟩ => ?_
  obtain hl₁₁ : InRegions (s₁₁.rd ++ s₁₁.wr) (off (off B (offQ w pl)) (8 * sLink)) 8 :=
    hcQ₁₁.good.scr.ld (by unfold sLink sFn; omega_using [hQ8])
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₁₁.mem)
    (by xrun [leave, State.ea, hdr, hcQ₁₁.rdi, hdrOff, hl₁₁, hcQ₁₁.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  obtain fl11 : Frm B [(offQ w pl + 256, slot (wsWords ql) 8 - 256)] s₁₀.mem t.mem := by
    rw [hm]; exact Frm.of_load ho₁₁ (by decide) (by omega_using [hn, hQZ]) (by simp)
  obtain hbt : ∀ i < 32, word t.mem B (8 * i) = word s₁₀.mem B (8 * i) := fun i hi =>
    fl11.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ offQ w pl + 256 by unfold offQ; omega_using [hi]))
      (by omega_using [hi])
  obtain hpt : ∀ i < 17, word t.mem (off B (offP w)) (8 * i) = word s₇.mem (off B (offP w)) (8 * i) := fun i hi => by
    rw [word_off, word_off, fl11.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show offP w + 8 * i + 8 ≤ offQ w pl + 256 by unfold offQ offP; omega_using [hi])) (by unfold offP; omega_using [hZ, hn, hQ8, hi]),
      hm₁₀, (fl8.trans fl9).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show offP w + 8 * i + 8 ≤ offP w + 256 by omega_using [hi]))
      (by unfold offP; omega_using [hZ, hn, hQ8, hi])]
  obtain hqt : ∀ i < 17, word t.mem (off B (offQ w pl)) (8 * i) = word s₁₀.mem (off B (offQ w pl)) (8 * i) :=
    fun i hi => by
      rw [word_off, word_off, fl11.word_eq (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Or.inl (show offQ w pl + 8 * i + 8 ≤ offQ w pl + 256 by omega_using [hi]))
        (by unfold offQ; omega_using [hZ, hn, hQ8, hi])]
  obtain kall := ((k010.trans k₁₁).trans k')
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, ?_, ?_, ⟨_, hWp₇.of_words hpt⟩, ⟨_, hWq₁₀.of_words hqt⟩, ?_, ?_, ?_, ?_,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · exact ⟨(hbt _ (by decide)).trans hHn₁₀.hw, (hbt _ (by decide)).trans hHn₁₀.hminv,
      fun j hj => (hbt _ (by unfold sArr; omega_using [hj])).trans (hHn₁₀.harr j hj)⟩
  · rw [hbt _ (by decide), hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hm₇]; exact hWsP₆
  · rw [hbt _ (by decide), hm₁₀]; exact hWsQ₉
  · have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide)
    have := Rsa.slot_lt (w := wsWords pl) (show Public.aN < aChunk by decide)
    rw [wv_off, fl11.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show offP w + slot (wsWords pl) Public.aN + 8 * wsWords pl ≤ offQ w pl + 256 by
        unfold offQ offP; omega_arith)) (by unfold offP; omega_arith), hm₁₀, ← wv_off,
      ho₉.wv (by omega_arith) (by omega_arith)]
    exact hpv₈
  · have := slot_le (w := wsWords pl) (show aChunk < 8 by decide)
    rw [wv_off, fl11.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show offP w + slot (wsWords pl) aChunk + 8 * wsWords pl ≤ offQ w pl + 256 by
        unfold offQ offP; omega_using [this])) (by unfold offP; omega_using [hZ, hn, this]), hm₁₀, ← wv_off]
    exact hcv₉
  · rw [hm]; exact hqv₁₁
  · have f02 : Frm B [(8 * sWsP, 8), (offP w, 8 * 17)] s.mem s₃.mem := by rw [← hm02]; exact f₃
    obtain f36' : Frm B [(8 * sWsQ, 8), (offQ w pl, 8 * 17)] s₃.mem s₆.mem := by rw [← hm35]; exact f₆
    obtain f710 : Frm B [(offP w + 256, slot (wsWords pl) 8 - 256)] s₆.mem s₁₀.mem := by
      rw [hm₁₀, ← hm₇]; exact fl8.trans fl9
    refine (((f02.append f36').append f710).append fl11).widen fun r hr => ?_
    obtain hP : (offP w, slot (wsWords pl) 8 + wsTab (wsWords pl) + slot (wsWords ql) 8) ∈
        [(8 * sWsP, 8), (8 * sWsQ, 8), (offP w, slot (wsWords pl) 8 + wsTab (wsWords pl) + slot (wsWords ql) 8)] := by
      simp
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hP, Nat.le_refl _, show offP w + 8 * 17 ≤ _ by omega_using [hQ8]⟩
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hP, show offP w ≤ offQ w pl by unfold offQ offP; omega_using [],
        show offQ w pl + 8 * 17 ≤ _ by unfold offQ offP; omega_using [hQ8]⟩
    · exact ⟨_, hP, show offP w ≤ offP w + 256 by omega_using [], show offP w + 256 + _ ≤ _ by omega_using [hQ8]⟩
    · exact ⟨_, hP, show offP w ≤ offQ w pl + 256 by unfold offQ offP; omega_using [],
        show offQ w pl + 256 + _ ≤ _ by unfold offQ offP; omega_using [hQ8]⟩
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by revert hr h; cases r <;> decide)

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.CrtGPow`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_crt` on x86-64: `G = 2^E mod n`

`gPow`: `K = ⌈w / w_X⌉` (`kLoop_ok`), `D = 64 ((K + 1) w_X - w)` into
slot `sD` (`gHead_ok`), its top bit into `sCnt`, `Y := R mod n`, then a
squaring and a doubling under each bit of `D` from the top (`gBit_ok`,
`gBits_ok`): `Y ≡ 2^D R = 2^(64 w_X (K + 1))` (`gPow_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64 (Crt.ws Crt.sD Crt.gPow Crt.gFast Crt.gSlow)

/-- The loop `rcx += w_X` while `rcx < w`, from `rcx = 0`: `rcx = K w_X`. -/
theorem kLoop_ok {s : State} {w wx : Nat} (hwx : 1 ≤ wx) (hw : 1 ≤ w) (hw' : w + wx < 2 ^ 32)
    (hax : s.gpr .rax = BitVec.ofNat 64 wx) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 0) :
    WP isa (.loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b) s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 ((w + wx - 1) / wx * wx) ∧ t.mem = s.mem ∧ Keep [.rcx] s t := by
  generalize hK : (w + wx - 1) / wx = K
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  rw [hK] at hK1 hK2
  obtain hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, Nat.zero_mul] at hK1; omega_using [hw, hK1]
    · exact h
  refine WP.loop (M := isa) (fun n t => ∃ k, n = K - k ∧ k < K ∧ t.gpr .rcx = BitVec.ofNat 64 (k * wx) ∧
      t.mem = s.mem ∧ Keep [.rcx] s t) ?_ _ s ⟨0, rfl, hK0, by rw [hcx, Nat.zero_mul], rfl, Keep.refl _ _⟩
  rintro n t ⟨k, rfl, hk, hcx', hm, k₀⟩
  obtain hle : (k + 1) * wx ≤ K * wx := Nat.mul_le_mul_right _ hk
  obtain hle' : k * wx + wx ≤ K * wx := by rw [← Nat.succ_mul]; exact hle
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 ((k + 1) * wx) ∧
      t'.cf = some (decide ((k + 1) * wx < w)) ∧ t'.mem = t.mem) (by
    xrun [hcx', (k₀.gpr (by decide)).trans hax, (k₀.gpr (by decide)).trans h12, ← BitVec.ofNat_add]
    rw [Nat.succ_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw', hK2, hle']),
      Nat.mod_eq_of_lt (by omega_using [hw'])]
    exact ⟨rfl, rfl⟩) rfl) fun t' ⟨⟨hcx'', hcf, hm'⟩, k'⟩ => ?_
  by_cases hc : (k + 1) * wx < w
  · refine .inr ⟨by simp [eval, hcf, hc], K - (k + 1), by omega_using [hk], k + 1, rfl, ?_, hcx'', hm'.trans hm,
      (k₀.trans k').mono (by decide)⟩
    rcases Nat.lt_or_ge (k + 1) K with h | h
    · exact h
    · have := Nat.mul_le_mul_right wx h; omega_using [hK1, hc, this]
  · have hkK : k + 1 = K := by
      rcases Nat.lt_or_ge (k + 1) K with h | h
      · have := Nat.mul_le_mul_right wx (show k + 2 ≤ K by omega_using [h])
        rw [Nat.succ_mul (k + 1)] at this; omega_using [hK2, hc, this]
      · omega_using [hk, h]
    exact .inl ⟨by simp [eval, hcf, hc], by rw [hcx'', hkK], hm'.trans hm, (k₀.trans k').mono (by decide)⟩

/-- `gPow`'s first steps: `D` into slot `sD` and `rax`. -/
def gHead (slotWs : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr slotWs)), .mov .rax (.mem (Crt.ws .rax sW)), .mov .r12 (.mem (hdr sW)),
    .mov32 .rcx (.imm 0)],
  .loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b,
  .block [.alu .add .rcx (.reg .rax), .alu .sub .rcx (.reg .r12), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .store (hdr Crt.sD) .rcx, .mov .rax (.reg .rcx)]]

/-- The steps of `D`. -/
theorem gHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (_hw : 2 ≤ w) (hw30 : w < 2 ^ 30) {sl : Nat} (hsl' : sl < 32) {Bx : Addr} {wx : Nat}
    (hX : word s.mem B (8 * sl) = Bx) (hXw : word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (gHead sl)) s fun t => t.gpr .rax = BitVec.ofNat 64 (gD w wx) ∧
      t.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx)) ∧ Keep [.rax, .rcx, .r12] s t := by
  have hs := hg.scr
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.rax, .r12, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 wx ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hl sl hsl', hX, hXr, hXw, hl sW (by decide), hg.hdr.hw]) rfl)
    fun t₁ ⟨⟨hax₁, h12₁, hcx₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (kLoop_ok hwx (by omega_using [hwx, hwx']) (by omega_using [hw30, hwx']) hax₁ h12₁ hcx₁)
      fun t₂ ⟨hcx₂, hm₂, k₂⟩ => ?_)
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  have hD : gD w wx = 64 * ((w + wx - 1) / wx * wx + wx - w) := rfl
  generalize (w + wx - 1) / wx * wx = a at hcx₂ hK1 hK2 hD
  obtain hsub : BitVec.ofNat 64 (a + wx) - BitVec.ofNat 64 w = BitVec.ofNat 64 (a + wx - w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hw30, hwx', hK1, hK2]),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hw30, hwx', hK2]
  obtain hdi₂ : t₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hg.rdi
  obtain hs₂ := hs.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (gD w wx) ∧
      t.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * Crt.sD + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_using [hZ, this]), hcx₂, (k₂.gpr (by decide)).trans hax₁,
      (k₂.gpr (by decide)).trans h12₁, hm₂, hm₁, ← BitVec.ofNat_add, hsub]
    rw [hD]
    generalize a + wx - w = c
    refine ⟨congrArg (BitVec.ofNat 64) ?_,
      congrArg (fun v => s.mem.writeW (off B (8 * Crt.sD)) v) (congrArg
          (BitVec.ofNat 64) ?_)⟩ <;> omega_using []) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, ((k₁.trans k₂).trans k).mono (by decide)⟩

/-! ## The bits of `D` -/

/-- The loop's body: `Y := Y² R⁻¹`, doubled if the bit is set, and the
next bit. -/
def gBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  .block [.mov .rax (.mem (hdr Crt.sD)), .alu .and .rax (.mem (hdr sCnt))],
  .ite .ne (double aN aAcc aTmp aY) (.block []),
  .block [.mov .rax (.mem (hdr sCnt)), .shift .shr .rax 1, .store (hdr sCnt) .rax, .alu .test .rax (.reg .rax)]]

/-- After the top `j` of the `L + 1` bits of `D`, from `s₀`: `Y ≡ 2^⌊D / 2^(L + 1 - j)⌋ R`. -/
structure GInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N D L : Nat) (j : Nat) (t : State) :
    Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  ylt : wv t.mem B (slot w aY) w < N
  y : wv t.mem B (slot w aY) w % N = 2 ^ (D / 2 ^ (L + 1 - j)) * 2 ^ (64 * w) % N
  d : word t.mem B (8 * Crt.sD) = BitVec.ofNat 64 D
  c : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L + 1 - j) / 2)
  frm : Frm B (gRanges w) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- Bit `L - j` of `D`. -/
theorem gBit_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) {j : Nat} (hj : j < L + 1) (hI : GInv s₀ B Z w minv N D L j t) :
    WP isa (seqs (gBody M.mm)) t fun t' =>
      t'.zf = some (decide (j + 1 = L + 1)) ∧ GInv s₀ B Z w minv N D L (j + 1) t' := by
  have hn := hI.good.scr.nowrap
  obtain hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  obtain hc2 : 2 ^ (L + 1 - j) / 2 = 2 ^ (L - j) := by
    rw [show L + 1 - j = (L - j) + 1 by omega_using [hj], Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
  obtain hpL : 2 ^ (L - j) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega_using [hL])
  -- `Y := Y²`.
  refine WP.seq (WP.mono (mmN_ok M (o := aY) (a := aY) (b := aY) hI.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv hI.ylt)
    fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  obtain hY₁ : wv t₁.mem B (slot w aY) w % N = 2 ^ (2 * (D / 2 ^ (L + 1 - j))) * 2 ^ (64 * w) % N :=
    VG.Proof.Bignum.mont_sq hR hI.y hm₁
  obtain hd₁ : word t₁.mem B (8 * Crt.sD) = BitVec.ofNat 64 D := by rw [ha₁.hslot (by decide)]; exact hI.d
  obtain hc₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₁.hslot (by decide), hI.c, hc2]
  obtain hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₁.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₂ => t₂.zf = some (decide (D / 2 ^ (L - j) % 2 = 0)) ∧
      t₂.mem = t₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl₁ Crt.sD (by decide), hl₁ sCnt (by decide), hd₁, hc₁,
      and_pow_beq D (L - j) (by omega_using [hL])]) rfl) fun t₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
  obtain hg₂ : Good t₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, hm₂ ▸ hg₁.hdr⟩
  -- Doubled if it is set.
  obtain hdbl : WP isa (.ite .ne (double aN aAcc aTmp aY) (.block [])) t₂ fun t₃ => Good t₃ B Z w minv ∧
      wv t₃.mem B (slot w aY) w < N ∧
      wv t₃.mem B (slot w aY) w % N =
        2 ^ (2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aY] t₂.mem t₃.mem ∧ Keep mmRegs t₂ t₃ := by
    by_cases hbit : D / 2 ^ (L - j) % 2 = 0
    · refine WP.ite false (by simp [eval, hz₂, hbit]) (by simp) (fun _ => WP.block_nil ⟨hg₂, ?_, ?_,
        fun _ _ => rfl, Keep.refl _ _⟩)
      · rw [hm₂]; exact hlt₁
      · rw [hm₂, hY₁, hbit]; rfl
    · refine WP.ite true (by simp [eval, hz₂, hbit]) (fun _ => ?_) (by simp)
      refine WP.mono (double_ok hg₂.scr hg₂.rdi hg₂.hdr hZ hw hw' (mo := aN) (acc := aAcc) (tmp := aTmp)
        (o := aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [hm₂, hn₁]; exact hlt₁)) fun t₃ ⟨hv₃, ha₃, k₃⟩ => ?_
      rw [hm₂, hn₁] at hv₃
      refine ⟨⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, ha₃.hdr hg₂.hdr⟩,
        by rw [hv₃]; exact Nat.mod_lt _ hN0, ?_, ha₃, k₃⟩
      rw [hv₃, Nat.mod_mod, Nat.mul_mod 2 (wv t₁.mem B (slot w aY) w) N, hY₁, ← Nat.mul_mod,
        show D / 2 ^ (L - j) % 2 = 1 by omega_using [hbit], Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
  refine WP.seq (WP.mono hdbl fun t₃ ⟨hg₃, hlt₃, hY₃, ha₃, k₃⟩ => ?_)
  -- The next bit.
  obtain hc₃ : word t₃.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₃.hslot (by decide), hm₂]; exact hc₁
  obtain hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  obtain hs₃ : ∀ i < 32, InRegions t₃.wr (off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₃.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ (L - j) / 2)) ∧ t'.zf = some (decide (2 ^ (L - j) / 2 = 0))) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hl₃ sCnt (by decide), hs₃ sCnt (by decide), hc₃, shr1_ofNat _ hpL,
      BitVec.and_self, ofNat64_beq_zero (show 2 ^ (L - j) / 2 < 2 ^ 64 by omega_using [hpL])]) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  obtain o' : Outside B (8 * sCnt) 8 t₃.mem t'.mem := by
    rw [hm']; exact writeW_outside _ _ _ (by unfold sCnt sFn; omega_using [])
  obtain hkeep : ∀ i < 8, i ≠ aAcc → i ≠ aTmp → i ≠ aY → wv t'.mem B (slot w i) w = wv t₁.mem B (slot w i) w :=
    fun i hi h1 h2 h3 => by
      rw [hm', hdrStore_wv _ _ _ (by decide) hi hn', ha₃.wv_of_not_mem hi (by simp [h1, h2, h3]) hn', hm₂]
  obtain hY' : wv t'.mem B (slot w aY) w = wv t₃.mem B (slot w aY) w := by
    rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) hn']
  obtain hle : L + 1 - (j + 1) = L - j := by omega_using []
  refine ⟨?_, ⟨⟨hg₃.scr.congr k'.2.2, (k'.gpr (by decide)).trans hg₃.rdi, by
      rw [hm']; exact Hdr.store hg₃.hdr (by decide) (by decide) _⟩,
    by rw [hkeep aN (by decide) (by decide) (by decide) (by decide)]; exact hn₁,
    by rw [hm', hdrStore_word _ _ _ (by decide) (by decide) hn',
      ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hw]), hm₂]; exact hinv₁,
    by rw [hY']; exact hlt₃,
    by rw [hY', hY₃, hle, show 2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2 = D / 2 ^ (L - j) by
      rw [show L + 1 - j = L - j + 1 by omega_using [hj]]; exact div_bit D (L - j)],
    by rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₃.hslot (by decide), hm₂]; exact hd₁,
    by rw [hm', word_writeW_self, hle],
    ?_, (((hI.keep.trans k₁).trans k₂).trans (k₃.trans k')).mono (by decide)⟩⟩
  · rw [hz']; congr 1; refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rcases Nat.eq_zero_or_pos (L - j) with h0 | h0
      · omega_using [hj, h0]
      · rw [show L - j = (L - j - 1) + 1 by omega_using [h0], Nat.pow_succ, Nat.mul_div_cancel _ (by decide)] at h
        exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · rw [show L - j = 0 by omega_using [h]]
  · exact (((hI.frm.trans (Frm.of_arrays ha₁ (by simp [gRanges]))).trans
      (by rw [hm₂]; exact Frm.refl _ _ _)).trans (Frm.of_arrays ha₃ (by simp [gRanges]))).trans
      (Frm.of_outside o' (by simp [gRanges]))

/-- The `L + 1` bits of `D`: `Y ≡ 2^D R`. -/
theorem gBits_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) (h0 : GInv s₀ B Z w minv N D L 0 t) :
    WP isa (.loop (seqs (gBody M.mm)) .ne) t (GInv s₀ B Z w minv N D L (L + 1)) :=
  wp_upto (a := 0) (N := L + 1) (by omega_using []) (GInv s₀ B Z w minv N D L)
    (fun _ _ hj _ hI => gBit_ok M hZ hw hw' hR hN0 hL hj hI) (fun _ h => h) h0

/-! ## `G` -/

/-- `gPow`'s loads of `w` and `n`'s base. -/
def gLd : List Instr := [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))]

/-- Its test of `n`'s top word: ZF is whether it is 0. -/
def gTest : List Instr := [.mov .rax (.mem (ix .r10 .r12 (-8))), .alu .test .rax (.reg .rax)]

/-- Its test of `D / 64 < w - 1`, into CF, with `D / 64` into `rcx`. -/
def gCmp : List Instr :=
  [.mov .rcx (.mem (hdr Crt.sD)), .shift .shr .rcx 6, .mov .rdx (.reg .r12), .alu .sub .rdx (.imm 1),
    .alu .cmp .rcx (.reg .rdx)]

theorem gPow_eq (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : Crt.gPow mul slotWs =
    gHead slotWs ++ ([.block gLd, .block gTest,
      .ite .ne (.seq (.block gCmp) (.ite .b (Crt.gFast mul) (Crt.gSlow mul))) (Crt.gSlow mul)] : List (Prog isa)) :=
  rfl

theorem gSlow_eq (mul : Nat → Nat → Nat → Prog isa) : Crt.gSlow mul =
    seqs [.block [.mov .rax (.mem (hdr Crt.sD))], topBit, .block [.store (hdr sCnt) .rdx], mul aY aR2 aOne,
      .loop (seqs (gBody mul)) .ne] :=
  rfl

theorem gFast_eq (mul : Nat → Nat → Nat → Prog isa) : Crt.gFast mul =
    .seq (.block [.mov32 .rdx (.imm 1)]) (.seq (setWord aY .rcx) (mul aY aR2 aY)) :=
  rfl

theorem shr_ofNat (n k : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

/-- What `gPow` gives, from `s`. -/
def GPost (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N wx : Nat) (t : State) : Prop :=
  Good t B Z w minv ∧ wv t.mem B (slot w aY) w < N ∧
    wv t.mem B (slot w aY) w % N = 2 ^ (64 * wx * ((w + wx - 1) / wx + 1)) % N ∧
    Frm B (gRanges w) s.mem t.mem ∧ Keep mmRegs s t

/-- `gPow_ok`'s hypotheses on the state it starts from. -/
structure GHyp (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N wx : Nat) : Prop where
  good : Good s B Z w minv
  hZ : slot w 8 ≤ Z
  hw : 2 ≤ w
  hw30 : w < 2 ^ 30
  n : wv s.mem B (slot w aN) w = N
  inv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  odd : N % 2 = 1
  n1 : 1 < N
  r2 : wv s.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  one : wv s.mem B (slot w aOne) w = 1
  wx1 : 1 ≤ wx
  wxw : wx ≤ w

/-- `D` from slot `sD` into `rax`, where `gSlow` starts. -/
theorem gLdD_ok {s t₁ : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {D : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hm₁ : t₁.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D))
    (k₁ : Keep mmRegs s t₁) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sD))]) t₁ fun t =>
      t.gpr .rax = BitVec.ofNat 64 D ∧ t.mem = t₁.mem ∧ Keep [.rax] t₁ t := by
  obtain hdi : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  obtain hl : InRegions (t₁.rd ++ t₁.wr) (off B (8 * Crt.sD)) 8 := (hg.scr.congr k₁.2.2).ld
    (show 8 * Crt.sD + 8 ≤ Z by have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_using [hZ, this])
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 D ∧ t.mem = t₁.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hm₁, word_writeW_self]) rfl) fun _ ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- `w` and `n`'s base into `r12` and `r10`. -/
theorem gLd_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr t B Z) (hdi : t.gpr .rdi = B)
    (hH : Hdr t.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block gLd) t fun t' => t'.gpr .r12 = BitVec.ofNat 64 w ∧ t'.gpr .r10 = off B (slot w aN) ∧
      t'.mem = t.mem ∧ Keep [.r12, .r10] t t' :=
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  WP.mono (WP.keep [.r12, .r10] (Q := fun t' => t'.gpr .r12 = BitVec.ofNat 64 w ∧
      t'.gpr .r10 = off B (slot w aN) ∧ t'.mem = t.mem)
    (by xrun [gLd, State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hH.hw,
      hH.harr aN (by decide)]) rfl) fun _ ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

theorem beq_zero (v : BitVec 64) : (v == 0) = decide (v.toNat = 0) := by
  by_cases h : v = 0
  · subst h; rfl
  · have : v.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    simp only [this, decide_false]
    exact beq_eq_false_iff_ne.mpr h

/-- ZF := whether `n`'s top word is 0. -/
theorem gTest_ok {t : State} {B : Addr} {Z w N : Nat} (hs : Scr t B Z) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (h10 : t.gpr .r10 = off B (slot w aN))
    (hn : wv t.mem B (slot w aN) w = N) :
    WP isa (.block gTest) t fun t' => t'.zf = some (decide (N / 2 ^ (64 * (w - 1)) = 0)) ∧ t'.mem = t.mem ∧
      Keep [.rax] t t' := by
  obtain hT := wv_top t.mem B (slot w aN) w (by omega_using [hw])
  rw [hn] at hT
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (N / 2 ^ (64 * (w - 1)) = 0)) ∧
      t'.mem = t.mem) (by
    xrun [gTest, State.ea, ix, addrm8 h10 h12 (show 1 ≤ w by omega_using [hw]),
      hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, this])]
    rw [← hT, BitVec.and_self]
    exact beq_zero _) rfl) fun _ ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- CF := whether `D / 64 < w - 1`, and `rcx := D / 64`. -/
theorem gCmp_ok {t : State} {B : Addr} {Z w wx : Nat} (hs : Scr t B Z) (hdi : t.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) (_hw : 2 ≤ w) (hw30 : w < 2 ^ 30) (hwx : 1 ≤ wx) (hwx' : wx ≤ w)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hD : word t.mem B (8 * Crt.sD) = BitVec.ofNat 64 (gD w wx)) :
    WP isa (.block gCmp) t fun t' => t'.cf = some (decide (gC w wx < w - 1)) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (gC w wx) ∧ t'.mem = t.mem ∧ Keep [.rcx, .rdx] t t' := by
  obtain ⟨-, hD1, -⟩ := gD_bounds hwx hwx' hw30
  obtain hC : gD w wx / 2 ^ 6 = gC w wx := by unfold gD; omega_using []
  refine WP.mono (WP.keep [.rcx, .rdx] (Q := fun t' => t'.cf = some (decide (gC w wx < w - 1)) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (gC w wx) ∧ t'.mem = t.mem) (by
    xrun [gCmp, State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * Crt.sD + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_using [hZ,
          this]), hD, h12, shr_ofNat (gD w wx) 6 (by omega_using [hD1]), hC,
      ofNat64_pred (show 1 ≤ w by omega_using [hwx, hwx']) (by omega_using [hw30])]
    have : gC w wx < 2 ^ 64 := by unfold gD at hD1; omega_using [hD1]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this,
        Nat.mod_eq_of_lt (by omega_using [hw30])]) rfl) fun _ ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- `G` the long way, after `gHead`: `Y := R`, then the bits of `D`. -/
theorem gSlow_ok (M : Mont) {s t₁ : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N wx : Nat}
    (h : GHyp s B Z w minv N wx)
    (hm₁ : t₁.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx))) (k₁ : Keep mmRegs s t₁) :
    WP isa (Crt.gSlow M.mm) t₁ (GPost s B Z w minv N wx) := by
  obtain ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2', hone, hwx, hwx'⟩ := h
  obtain hw' : w < 2 ^ 31 := by omega_using [hw30]
  have hs := hg.scr
  have hnw := hs.nowrap
  obtain hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hnw]
  obtain hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain hN0 : 0 < N := by omega_using [hN1]
  obtain ⟨hD0, hD1, hDE⟩ := gD_bounds hwx hwx' hw30
  rw [gSlow_eq]
  -- `D` again.
  refine WP.seq (WP.mono (gLdD_ok hg hZ hm₁ k₁) fun t₂ ⟨hax₁, hm₂, k₂⟩ => ?_)
  obtain hmA : t₂.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx)) := hm₂.trans hm₁
  obtain kA : Keep mmRegs s t₂ := (k₁.trans k₂).mono (by decide)
  generalize gD w wx = D at hD0 hD1 hDE hax₁ hmA
  obtain hs₁ := hs.congr kA.2.2
  obtain hdi₁ : t₂.gpr .rdi = B := (kA.gpr (by decide)).trans hg.rdi
  -- The top bit `L` of `D`.
  refine WP.seq (WP.mono (topBit_ok hax₁ hD0 (by omega_using [hD1])) fun t₃ ⟨hdx₃, _, hm₃, k₃⟩ => ?_)
  obtain hL : D.log2 < 62 := (Nat.log2_lt (by omega_using [hD0])).mpr hD1
  obtain hs₃ := hs₁.congr k₃.2.2
  obtain hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₁
  refine WP.seq (WP.mono (WP.keep [] (Q := fun t => t.mem = t₃.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2))) (by
    xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.st (show 8 * sCnt + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sCnt < 32 by decide); omega_using [hZ, this]), hdx₃]) rfl) fun t₄ ⟨hm₄, k₄⟩ => ?_)
  obtain hm₄' : t₄.mem = (s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D)).writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2)) := by rw [hm₄, hm₃, hmA]
  obtain hwv₄ : ∀ j < 8, wv t₄.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    rw [hm₄', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  obtain hg₄ : Good t₄ B Z w minv := ⟨hs₃.congr k₄.2.2, (k₄.gpr (by decide)).trans hdi₃, by
    rw [hm₄']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  -- `Y := R`.
  refine WP.seq (WP.mono (mmN_ok M (N := N) (o := aY) (a := aR2) (b := aOne) hg₄ hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₄ aN (by decide)).trans hn)
    (by rw [hm₄', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₄ aOne (by decide), hone]; exact hN1))
    fun t₅ ⟨hg₅, hn₅, hinv₅, hlt₅, hm₅, ha₅, k₅⟩ => ?_)
  rw [hwv₄ aR2 (by decide), hwv₄ aOne (by decide), hone, Nat.mul_one] at hm₅
  obtain hY₅ : wv t₅.mem B (slot w aY) w % N = 2 ^ (D / 2 ^ (D.log2 + 1 - 0)) * 2 ^ (64 * w) % N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₅, hr2']
  obtain hfr₅ : Frm B (gRanges w) s.mem t₅.mem := by
    obtain o1 := writeW_outside s.mem B (BitVec.ofNat 64 D) (d := 8 * Crt.sD) (by unfold Crt.sD sFn; omega_using [])
    obtain o2 := writeW_outside (s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D)) B
      (BitVec.ofNat 64 (2 ^ D.log2)) (d := 8 * sCnt) (by unfold sCnt sFn; omega_using [])
    rw [← hm₄'] at o2
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_outside o2 (by simp [gRanges]))).trans
      (Frm.of_arrays ha₅ (by simp [gRanges]))
  obtain h0 : GInv s B Z w minv N D D.log2 0 t₅ := ⟨hg₅, hn₅, hinv₅, hlt₅, hY₅,
    by rw [ha₅.hslot (by decide), hm₄', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [ha₅.hslot (by decide), hm₄', word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₅, ((((kA.trans k₃).trans k₄).trans k₅).mono (by decide))⟩
  -- The bits.
  refine WP.mono (gBits_ok M hZ hw hw' hR hN0 (by omega_using [hL]) h0) fun t hI => ⟨hI.good, hI.ylt, ?_, hI.frm, hI.keep⟩
  rw [hI.y, Nat.sub_self, Nat.pow_zero, Nat.div_one, ← Nat.pow_add, hDE]

/-- `G` in one multiplication, after `gHead` and the tests: `Y := 2^D`, then
`Y := R² Y R⁻¹`. -/
theorem gFast_ok (M : Mont) {s t₁ : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N wx : Nat}
    (h : GHyp s B Z w minv N wx)
    (hm₁ : t₁.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx))) (k₁ : Keep mmRegs s t₁)
    (hcx : t₁.gpr .rcx = BitVec.ofNat 64 (gC w wx)) (h12 : t₁.gpr .r12 = BitVec.ofNat 64 w)
    (hc : gC w wx < w - 1) (htop : N / 2 ^ (64 * (w - 1)) ≠ 0) :
    WP isa (Crt.gFast M.mm) t₁ (GPost s B Z w minv N wx) := by
  obtain ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2', hone, hwx, hwx'⟩ := h
  obtain hw' : w < 2 ^ 31 := by omega_using [hw30]
  have hs := hg.scr
  have hnw := hs.nowrap
  obtain hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hnw]
  obtain hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain ⟨-, -, hDE⟩ := gD_bounds hwx hwx' hw30
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  obtain hH₁ : Hdr t₁.mem B w minv := by rw [hm₁]; exact Hdr.store hg.hdr (by decide) (by decide) _
  obtain hwv₁ : ∀ j < 8, wv t₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    rw [hm₁, hdrStore_wv _ _ _ (by decide) hj hn']
  rw [gFast_eq]
  -- `rdx := 1`.
  refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 1 ∧ t.mem = t₁.mem)
    (by xrun) rfl) fun t₂ ⟨⟨hdx₂, hm₂⟩, k₂⟩ => ?_)
  -- `Y := 2^D`.
  refine WP.seq (WP.mono (setWord_ok (hs₁.congr k₂.2.2) ((k₂.gpr (by decide)).trans hdi₁) (hm₂ ▸ hH₁) hZ
    ((k₂.gpr (by decide)).trans h12) (by omega_using [hwx, hwx']) hw' (o := aY) (by decide) (ri := .rcx) (by decide)
    (i := gC w wx) (by omega_using [hc]) ((k₂.gpr (by decide)).trans hcx)) fun t₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  rw [hdx₂, BitVec.toNat_ofNat, Nat.one_mod, Nat.one_mul] at hv₃
  obtain ha₃ : Arrays B w [aY] t₂.mem t₃.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₃ (Nat.le_refl _) (Nat.le_refl _)
  obtain hg₃ : Good t₃ B Z w minv := ⟨(hs₁.congr k₂.2.2).congr k₃.2.2,
    ((k₂.trans k₃).gpr (by decide)).trans hdi₁, ha₃.hdr (hm₂ ▸ hH₁)⟩
  obtain hwv₃ : ∀ j < 8, j ≠ aY → wv t₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj hj' => by
    rw [ha₃.wv_of_not_mem hj (by simp [hj']) hn', hm₂, hwv₁ j hj]
  -- `Y := R² 2^D R⁻¹`.
  refine WP.mono (mmN_ok M (N := N) (o := aY) (a := aR2) (b := aY) hg₃ hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ aN (by decide) (by decide)).trans hn)
    (by rw [ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hwx, hwx']), hm₂, hm₁,
        hdrStore_word _ _ _ (by decide) (by decide) hn']; exact hinv)
    (by rw [hv₃]; exact gFast_lt hc htop))
    fun t₄ ⟨hg₄, _, _, hlt₄, hm₄, ha₄, k₄⟩ => ⟨hg₄, hlt₄, ?_, ?_, ?_⟩
  · rw [hwv₃ aR2 (by decide) (by decide), hv₃] at hm₄
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, ← hDE, gD, Nat.pow_add, Nat.mul_mod, hr2', ← Nat.mul_mod]
    simp only [Nat.mul_comm]
    rw [Nat.mul_assoc]
  · have o1 := writeW_outside s.mem B (BitVec.ofNat 64 (gD w wx)) (d := 8 * Crt.sD) (by unfold Crt.sD sFn; omega_using [])
    rw [← hm₁, ← hm₂] at o1
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_arrays ha₃ (by simp [gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [gRanges]))
  · exact ((((k₁.trans k₂).trans k₃).trans k₄).mono (by decide))

/-- `gPow`: `[aY] ≡ 2^(64 w_X (K + 1)) (mod N)` for `K = ⌈w / w_X⌉`, with `w_X` in
the header of the workspace whose base is in slot `sl`. -/
theorem gPow_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hr2' : wv s.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N)
    (hone : wv s.mem B (slot w aOne) w = 1)
    {sl : Nat} (hsl' : sl < 32)
    {Bx : Addr} {wx : Nat} (hX : word s.mem B (8 * sl) = Bx)
    (hXw : word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (Crt.gPow M.mm sl)) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = 2 ^ (64 * wx * ((w + wx - 1) / wx + 1)) % N ∧
      Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
        (8 * Crt.sD, 8), (8 * sCnt, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  obtain hH : GHyp s B Z w minv N wx := ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2', hone, hwx, hwx'⟩
  have hs := hg.scr
  have hnw := hs.nowrap
  obtain hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hnw]
  rw [gPow_eq]
  refine wp_seqs_append (by simp [gHead]) (by simp) (WP.mono (gHead_ok hg hZ hw hw30 hsl' hX hXw hXr hwx hwx')
    fun t₁ ⟨_, hm₁, k₁⟩ => ?_)
  obtain k₁' : Keep mmRegs s t₁ := k₁.mono (by decide)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  obtain hH₁ : Hdr t₁.mem B w minv := by rw [hm₁]; exact Hdr.store hg.hdr (by decide) (by decide) _
  obtain hn₁ : wv t₁.mem B (slot w aN) w = N := by rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) hn']; exact hn
  -- Is `n`'s top word 0?
  refine WP.seq (WP.mono (gLd_ok hs₁ hdi₁ hH₁ hZ) fun t₁' ⟨h12, h10, hm₁', k₁''⟩ => ?_)
  refine WP.seq (WP.mono (gTest_ok (hs₁.congr k₁''.2.2) hZ hw h12 h10 (hm₁' ▸ hn₁))
    fun t₂ ⟨hz₂, hm₂₀, k₂₀⟩ => ?_)
  obtain hm₂ : t₂.mem = t₁.mem := hm₂₀.trans hm₁'
  obtain k₂ := k₁''.trans k₂₀
  obtain h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂₀.gpr (by decide)).trans h12
  obtain hm₂' := hm₂.trans hm₁
  by_cases htop : N / 2 ^ (64 * (w - 1)) = 0
  · exact WP.ite false (by simp [eval, hz₂, htop]) (by simp)
      (fun _ => gSlow_ok M hH hm₂' ((k₁'.trans k₂).mono (by decide)))
  refine WP.ite true (by simp [eval, hz₂, htop]) (fun _ => ?_) (by simp)
  -- Is `D / 64 < w - 1`?
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  obtain hD : word t₂.mem B (8 * Crt.sD) = BitVec.ofNat 64 (gD w wx) := by rw [hm₂', word_writeW_self]
  refine WP.seq (WP.mono (gCmp_ok hs₂ hdi₂ hZ hw hw30 hwx hwx' h12₂ hD) fun t₃ ⟨hc₃, hcx₃, hm₃, k₃⟩ => ?_)
  obtain k₃' : Keep mmRegs s t₃ := ((k₁'.trans k₂).trans k₃).mono (by decide)
  by_cases hc : gC w wx < w - 1
  · exact WP.ite true (by simp [eval, hc₃, hc]) (fun _ => gFast_ok M hH (hm₃.trans hm₂') k₃' hcx₃
      ((k₃.gpr (by decide)).trans h12₂) hc htop) (by simp)
  · exact WP.ite false (by simp [eval, hc₃, hc]) (by simp) (fun _ => gSlow_ok M hH (hm₃.trans hm₂') k₃')

end VG.Proof.Bignum.X86_64

end

end

/-!
# RSA with the CRT on x86-64: `R_X mod X`

The start of each prime's phase (`unitPhase_ok`): `G = 2^E mod n` in the
modulus' workspace, reduced into the prime's (`G R_X^(-K) ≡ R_X (mod X)` if
`X` divides `n`), as its `Y`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The modulus `N` in its workspace, `-N⁻¹`, `R² mod N` and the number 1. -/
structure NVals (t : State) (B : Addr) (w : Nat) (minv : BitVec 64) (N : Nat) : Prop where
  n : wv t.mem B (slot w Public.aN) w = N
  inv : ((word t.mem B (slot w Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  r2 : wv t.mem B (slot w Public.aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  r2lt : wv t.mem B (slot w Public.aR2) w < N
  one : wv t.mem B (slot w Public.aOne) w = 1

theorem XVals.of_below {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (h : XVals s B o wx mx X) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o)
    (ho : o + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  obtain hN := slot_le (w := wx) (show Public.aN < 8 by decide)
  obtain hO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  exact ⟨by rw [wv_off, hf.wv_eq (fun r h' => Or.inr (by have := hr r h'; omega_arith)) (by omega_arith), ← wv_off]; exact h.n,
    by rw [word_off, hf.word_eq (fun r h' => Or.inr (by have := hr r h'; omega_arith)) (by omega_arith), ← word_off]; exact h.inv,
    by rw [wv_off, hf.wv_eq (fun r h' => Or.inr (by have := hr r h'; omega_arith)) (by omega_arith), ← wv_off]; exact h.one⟩

theorem XVals.of_outside {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X j n : Nat}
    (h : XVals s B o wx mx X) (ho : Outside (off B o) (slot wx j) n s.mem t.mem) (hj : j < 8)
    (h1 : j ≠ Public.aN) (h2 : j ≠ Public.aOne) (hn : n ≤ 8 * (wx + 2))
    (hz : (off B o).toNat + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  obtain s1 := slot_sep (w := wx) h1
  obtain s2 := slot_sep (w := wx) h2
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have := slot_le (w := wx) hj
  exact ⟨by rw [ho.wv (by omega_arith) (by omega_arith)]; exact h.n, by rw [ho.word (by omega_arith) (by omega_arith)]; exact h.inv,
    by rw [ho.wv (by omega_arith) (by omega_arith)]; exact h.one⟩

/-- The start of a prime's phase: `G = 2^(64 w_X (K + 1)) mod N` into the
modulus' `Y`, reduced into the prime's `Y`: `R_X mod X` if `X` divides `N`. -/
theorem unitPhase_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32) (hsl1 : sl ≠ Crt.sD)
    (hsl2 : sl ≠ Public.sCnt) (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N) (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hXodd : X % 2 = 1) :
    WP isa (seqs (Crt.gPow M.mm sl ++ ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
        redc M.mm Public.aY ++ copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))) s fun t =>
      Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem B (slot w Public.aY) w < N ∧
      wv t.mem B (slot w Public.aY) w % N = 2 ^ (64 * wx * (nChunks w wx + 1)) % N ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
      word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX) ∧
      Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  obtain ho64 : o < 2 ^ 64 := by omega_arith
  obtain hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  obtain hgr : ∀ r ∈ gRanges w, r.1 + r.2 ≤ slot w 8 := by
    have := slot_le (w := w) (show Public.aAcc < 8 by decide)
    have := slot_le (w := w) (show Public.aTmp < 8 by decide)
    have := slot_le (w := w) (show Public.aY < 8 by decide)
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega_arith
  simp only [List.append_assoc]
  -- `G`.
  refine wp_seqs_append (by simp [Crt.gPow]) (by simp) ?_
  refine WP.mono (gPow_ok M hg (by omega_arith) (by omega_arith) (by omega_arith) hN.n hN.inv hodd hN1 hN.r2 hN.one hsl hslv
    hws.hdr.hw (by
      have := (hs.sub (o := o) (n := slot wx 8) (by omega_arith) (by omega_arith)).ld (d := 8 * sW) (by unfold sW; omega_arith)
      exact this) (by omega_arith) hwx) fun s₁ ⟨hg₁, hlt₁, hG₁, f₁, k₁⟩ => ?_
  obtain hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word s₁.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi h1 h2 => f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot w Public.aAcc (show i < 32 from hi)
      have := hdr_lt_slot w Public.aTmp (show i < 32 from hi)
      have := hdr_lt_slot w Public.aY (show i < 32 from hi)
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by omega_arith)
      · exact Or.inl (by omega_arith)
      · exact Or.inl (by omega_arith)
      · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
        unfold Crt.sD sFn at h1 ⊢; omega_arith
      · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
        unfold Public.sCnt sFn at h2 ⊢; omega_arith) (by omega_arith)
  obtain hxw₁ : ∀ i < 32, word s₁.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact f₁.word_eq (fun r hr => Or.inr (by have := hgr r hr; omega_arith)) (by omega_arith)
  -- Into the prime's workspace.
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * sl) (by omega_arith),
      hb₁ sl hsl hsl1 hsl2, hslv]) rfl) fun s₂ ⟨⟨hdi₂, hm₂⟩, k₂⟩ => ?_
  obtain k02 := k₁.trans k₂
  obtain hws₂ : WsAt s₂.mem B o wx mx := hws.of_words fun i hi => by rw [hm₂]; exact hxw₁ i (by omega_arith)
  obtain hc₂ : SubCtx s₂ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k02.2.2) (by rw [hm₂]; exact hg₁.hdr) hws₂ hdi₂ hlo (by have := tabBytes_le_wsTab wx; omega_arith)
  obtain hX₂ : XVals s₂ B o wx mx X := hX.of_below (by rw [hm₂]; exact f₁) (fun r hr => (hgr r hr).trans hlo) hoL
  -- `A R^K ≡ G (mod X)`.
  refine wp_seqs_append (by simp [redc]) (by simp [copyArr]) ?_
  refine WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega_arith) hX1 (j := Public.aY) (by decide))
    fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, f₃, k₃⟩ => ?_
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hc₃.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := Public.aY) (a := aXc)
    (by decide) (by decide) (by decide)) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  obtain hc₄ := hc₃.of_frm (rs := [(slot wx Public.aY, 8 * wx)]) (Frm.of_outside ho₄ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
    simp only; omega_arith) k₄.2.2 (k₄.gpr (by decide))
  -- Back to the modulus'.
  obtain hl₄ : InRegions (s₄.rd ++ s₄.wr) (off (off B o) (8 * sLink)) 8 :=
    hc₄.good.scr.ld (by unfold sLink sFn; omega_arith)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₄.mem)
    (by xrun [leave, State.ea, hdr, hc₄.rdi, hdrOff, hl₄, hc₄.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  obtain f34 : Frm B [xRange o wx] s₂.mem t.mem := by
    rw [hm]
    exact (f₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)).trans
      (ho₄.mono (o' := slot wx Public.aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith) |>.to_x
        (by decide) hoL (List.mem_singleton_self _))
  obtain hb : ∀ d, d + 8 ≤ o → word t.mem B d = word s₂.mem B d := fun d hd => f34.x_below hd ho64
  obtain hbw : ∀ d k, d + 8 * k ≤ o → wv t.mem B d k = wv s₂.mem B d k := fun d k hd =>
    wv_congr fun i hi => hb _ (by omega_arith)
  obtain kall := ((k02.trans k₃).trans k₄).trans k'
  obtain hY : wv t.mem (off B o) (slot wx Public.aY) wx = wv s₃.mem (off B o) (slot wx aXc) wx := by rw [hm, hv₄]
  obtain hXc : wv s₃.mem (off B o) (slot wx aXc) wx * (2 ^ (64 * wx)) ^ nChunks w wx % X =
      wv s₂.mem B (slot w Public.aY) w % X := by
    rw [← Nat.pow_mul]; exact hv₃
  obtain hYn : wv s₂.mem B (slot w Public.aY) w = wv s₁.mem B (slot w Public.aY) w := by rw [hm₂]
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, ?_, ?_, ?_, ?_, by rw [hY]; exact hlt₃, fun hdvd => ?_, ?_, ?_,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · have hH := hg₁.hdr
    exact ⟨(hb _ (by unfold sW; omega_arith)).trans (by rw [hm₂]; exact hH.hw),
      (hb _ (by unfold sMinv; omega_arith)).trans (by rw [hm₂]; exact hH.hminv),
      fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_arith); omega_arith)).trans
        (by rw [hm₂]; exact hH.harr j hj)⟩
  · rw [hm]; exact hc₄.ws
  · exact hX₃.of_outside (by rw [hm]; exact ho₄) (by decide) (by decide) (by decide) (by omega_arith)
      (by have := hc₃.good.scr.nowrap; omega_arith)
  · rw [hbw _ _ (by have := slot_le (w := w) (show Public.aY < 8 by decide); omega_arith), hYn]; exact hlt₁
  · rw [hbw _ _ (by have := slot_le (w := w) (show Public.aY < 8 by decide); omega_arith), hYn]; exact hG₁
  · rw [hY]
    obtain hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
    obtain e : wv s₂.mem B (slot w Public.aY) w % X = 1 * (2 ^ (64 * wx)) ^ (nChunks w wx + 1) % X := by
      rw [hYn, ← Nat.mod_mod_of_dvd _ hdvd, hG₁, Nat.mod_mod_of_dvd _ hdvd, Nat.one_mul, ← Nat.pow_mul]
    have := VG.Proof.Bignum.redc_cancel hR (hXc.trans e)
    rwa [Nat.one_mul] at this
  · have := hdr_lt_slot wx Public.aY (show sMaskX < 32 by decide)
    rw [hm, ho₄.word (Or.inl (by omega_arith)) (by unfold sMaskX sFn; omega_arith),
      f₃.word_eq (sMaskX_redc wx) (by unfold sMaskX sFn; omega_arith), hm₂]
    exact hxw₁ _ (by decide)
  · have f₁' : Frm B (gRanges w) s.mem s₂.mem := by rw [hm₂]; exact f₁
    exact f₁'.append f34
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by revert hr h; cases r <;> decide)

end VG.Proof.Bignum.X86_64
