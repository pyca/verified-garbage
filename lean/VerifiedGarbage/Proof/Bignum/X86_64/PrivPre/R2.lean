module

public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_private_precompute` on x86-64: `R_X² mod X`

In a prime's workspace, `r2X` doubles 1 `128 w_X` times modulo `X`:
`2^(128 w_X) mod X` in `aY` (`r2X_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2X count r2At r2Phase)

/-- What `r2X` changes in a prime's workspace. -/
def r2Ranges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx aY, 8 * (wx + 2)), (slot wx aAcc, 8 * (wx + 2)), (slot wx aTmp, 8 * (wx + 2)), (8 * sRem, 8)]

theorem r2Ranges_ok (wx : Nat) : ∀ r ∈ r2Ranges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have a1 := slot_le (w := wx) (show aY < 8 by decide)
  have a2 := slot_le (w := wx) (show aAcc < 8 by decide)
  have a3 := slot_le (w := wx) (show aTmp < 8 by decide)
  have b1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have b2 := hdr_lt_slot wx aAcc (show 31 < 32 by decide)
  have b3 := hdr_lt_slot wx aTmp (show 31 < 32 by decide)
  have b4 := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  have b5 := slot_le (w := wx) (show 0 < 8 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sRem, sFn] <;> omega

/-- The arrays `X` and 1 are outside what `r2X` changes. -/
theorem r2Ranges_arr (wx : Nat) {j : Nat} (hj : j = aN ∨ j = aOne) :
    ∀ r ∈ r2Ranges wx, slot wx j + 8 * wx ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  have hj8 : j < 8 := by rcases hj with rfl | rfl <;> decide
  have s1 := slot_sep (w := wx) (show j ≠ aY by rcases hj with rfl | rfl <;> decide)
  have s2 := slot_sep (w := wx) (show j ≠ aAcc by rcases hj with rfl | rfl <;> decide)
  have s3 := slot_sep (w := wx) (show j ≠ aTmp by rcases hj with rfl | rfl <;> decide)
  have b := hdr_lt_slot wx j (show 31 < 32 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sRem, sFn] at * <;> omega

theorem shl7_w {w : Nat} (hw : 128 * w < 2 ^ 64) : BitVec.ofNat 64 w <<< 7 = BitVec.ofNat 64 (128 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : w < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hw]
  omega

/-- `r2X`: `[aY] := 2^(128 w_X) mod X` in the prime's workspace, keeping
`X`, 1 and the workspace. -/
theorem r2X_ok {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X : Nat}
    (hc : SubCtx s B Z o w wx mx) (hv : XVals s B o wx mx X) (hX1 : 1 < X) (hwx2 : 2 ≤ wx) (hwx : wx < 2 ^ 20) :
    WP isa (seqs r2X) s fun t => SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx aY) wx = 2 ^ (128 * wx) % X ∧ Frm (off B o) (r2Ranges wx) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hz : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have hr := r2Ranges_ok wx
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lO := slot_le (w := wx) (show aOne < 8 by decide)
  have lY := slot_le (w := wx) (show aY < 8 by decide)
  unfold r2X
  -- `[aY] := 1`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) (by omega) (o := aY) (a := aOne) (by decide) (by decide)
    (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_
  have f₁ : Frm (off B o) (r2Ranges wx) s.mem s₁.mem :=
    (Frm.of_outside ho₁ (List.mem_singleton_self _)).widen fun r h => by
      rw [List.mem_singleton.mp h]; exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp only; omega⟩
  have hc₁ := hc.of_frm f₁ hr k₁.2.2 (k₁.gpr (by decide))
  have hX₁ : XVals s₁ B o wx mx X := hv.of_outside ho₁ (by decide) (by decide) (by decide) (by omega) hz
  have hg₁ := hc₁.good
  have hl₁ : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [k₁.2.1, k₁.2.2]; exact hl i hi
  -- The count.
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (128 * wx) ∧ t.mem = s₁.mem)
    (by xrun [count, State.ea, hdr, hg₁.rdi, hdrOff, hl₁ sW (by decide), hg₁.hdr.hw, shl7_w (show 128 * wx < 2 ^ 64 by omega)]) rfl)
    fun s₂ ⟨⟨hcx, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good s₂ (off B o) (slot wx 8) wx mx := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
    by rw [hm₂]; exact hg₁.hdr⟩
  -- The doublings.
  refine WP.mono (doubles_ok hg₂.scr hg₂.rdi hg₂.hdr (Nat.le_refl _) hwx2 (by omega) (mo := aN) (acc := aAcc)
    (tmp := aTmp) (o := aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (sl := sRem) (by decide) (by decide) (c := 128 * wx) (by omega) (by omega) hcx
    (by rw [hm₂, hv₁, hv.one, hX₁.n]; exact hX1)) fun t ⟨hy, ft, _, kt⟩ => ?_
  have f₂ : Frm (off B o) (r2Ranges wx) s₁.mem t.mem := by
    rw [← hm₂]
    exact ft.mono fun r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
      rcases h with rfl | rfl | rfl | rfl <;> simp
  have kk := (k₁.trans k₂).trans kt
  have hc₂ := hc₁.of_frm f₂ hr (by rw [kt.2.2, k₂.2.2]) (by rw [kt.gpr (by decide), k₂.gpr (by decide)])
  have rN := r2Ranges_arr wx (j := aN) (Or.inl rfl)
  have rO := r2Ranges_arr wx (j := aOne) (Or.inr rfl)
  refine ⟨hc₂, ⟨?_, ?_, ?_⟩, ?_, f₁.trans f₂, kk.mono (by decide)⟩
  · rw [f₂.wv_eq rN (by omega)]; exact hX₁.n
  · rw [f₂.word_eq (fun r h => by have := rN r h; omega) (by omega)]; exact hX₁.inv
  · rw [f₂.wv_eq rO (by omega)]; exact hX₁.one
  · rw [hy, hm₂, hv₁, hv.one, hX₁.n, Nat.mul_one]

/-- `r2At sl`: into the prime's workspace (its base in slot `sl`), `r2X`,
and back. -/
theorem r2At_ok {s : State} {B : Addr} {Z w o wx : Nat} {minv mx : BitVec 64} {X sl : Nat}
    (hg : Good s B Z w minv) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx)
    (hwx : wx < 2 ^ 20) (hsl : sl < 32) (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) :
    WP isa (seqs (r2At sl)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧
      wv t.mem (off B o) (slot wx aY) wx = 2 ^ (128 * wx) % X ∧ Frm B [xRange o wx] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  unfold r2At
  simp only [List.append_assoc]
  -- Into the prime's workspace.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl) fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo (hi_of_wsTab hhi)
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  refine wp_seqs_append (by simp [r2X]) (by simp) ?_
  refine WP.mono (r2X_ok hc₁ hX₁ hX1 hwx2 hwx) fun s₂ ⟨hc₂, _, hy₂, f₂, k₂⟩ => ?_
  -- Back to the modulus'.
  have hl₂ : InRegions (s₂.rd ++ s₂.wr) (off (off B o) (8 * sLink)) 8 :=
    hc₂.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₂.mem)
    (by xrun [leave, State.ea, hdr, hc₂.rdi, hdrOff, hl₂, hc₂.link]) rfl) fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have fx : Frm B [xRange o wx] s.mem t.mem := by
    rw [hm, ← hm₁]; exact f₂.to_x (r2Ranges_ok wx) hoL (List.mem_singleton_self _)
  have kall := (k₁.trans k₂).trans k₃
  have hb : ∀ d, d + 8 ≤ o → word t.mem B d = word s.mem B d := fun d hd => fx.x_below hd ho64
  have hH := hg.hdr
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, by rw [hm]; exact hc₂.ws, by rw [hm]; exact hy₂, fx, ⟨fun r hr => ?_, kall.2⟩⟩
  · exact ⟨(hb _ (by unfold sW; omega)).trans hH.hw, (hb _ (by unfold sMinv; omega)).trans hH.hminv,
      fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH.harr j hj)⟩
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by revert hr h; cases r <;> decide)

/-- After `R_p² mod p` and `R_q² mod q`: `n`'s values, the mask, and the
primes' `aY`. -/
structure R2Done (σ t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  msk : word t.mem B (8 * sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  py : wv t.mem (off B (offP w)) (slot (wsWords pl) aY) (wsWords pl) =
    2 ^ (128 * wsWords pl) % (if M then P else 3)
  qy : wv t.mem (off B (offQ w pl)) (slot (wsWords ql) aY) (wsWords ql) =
    2 ^ (128 * wsWords ql) % (if M then Q else 3)
  hfix : HFix B σ.mem t.mem
  iscr : InScr B Z σ.mem t.mem
  keep : Keep mmRegs σ t

/-- After `R_p² mod p`: as after the checks, and `p`'s `aY`. -/
structure R2Mid (σ t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  msk : word t.mem B (8 * sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  py : wv t.mem (off B (offP w)) (slot (wsWords pl) aY) (wsWords pl) =
    2 ^ (128 * wsWords pl) % (if M then P else 3)
  qxv : XVals t B (offQ w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B σ.mem t.mem
  iscr : InScr B Z σ.mem t.mem
  keep : Keep mmRegs σ t

/-- `R_p² mod p`, from what the checks leave. -/
theorem r2P_ok {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (r2At sWsP)) t₀ fun t => R2Mid s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  generalize (k + 7) / 8 = w at *
  obtain ⟨-, hP', -⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwp : wsWords pl < 2 ^ 20 := by unfold wsWords; omega
  have hloP : slot w 8 ≤ offP w := Nat.le_refl _
  have hhiP : offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) ≤ Z := by unfold offQ at hZq; unfold offP; omega
  have hPQ : offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) = offQ w pl := rfl
  refine WP.mono (r2At_ok hr.good hloP hhiP hwp2 hwp (by decide) hr.wsP hr.pws hr.pxv hP'.1)
    fun t₁ ⟨hg₁, hpws₁, hpy₁, f₁, k₁⟩ => ?_
  have hb₁ : ∀ d, d + 8 ≤ offP w → word t₁.mem B d = word t₀.mem B d := fun d hd => f₁.x_below hd (by omega)
  have hq₁ : ∀ d, offQ w pl ≤ d → d + 8 ≤ Z → word t₁.mem B d = word t₀.mem B d := fun d hd hd' =>
    f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) (by omega)
  have hqw : ∀ i < 32, word t₁.mem (off B (offQ w pl)) (8 * i) = word t₀.mem (off B (offQ w pl)) (8 * i) :=
    fun i hi => by rw [word_off, word_off]; exact hq₁ _ (by omega) (by omega)
  have hqv : ∀ d m, d + 8 * m ≤ slot (wsWords ql) 8 → wv t₁.mem (off B (offQ w pl)) d m =
      wv t₀.mem (off B (offQ w pl)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hq₁ _ (by omega) (by omega)
  have lN := slot_le (w := wsWords ql) (show aN < 8 by decide)
  have lO := slot_le (w := wsWords ql) (show aOne < 8 by decide)
  have hwv : ∀ j < 8, wv t₁.mem B (slot w j) w = wv t₀.mem B (slot w j) w := fun j hj =>
    wv_congr fun i hi => hb₁ _ (by have := slot_le (w := w) hj; unfold offP; omega)
  exact ⟨hg₁, ⟨by rw [hwv _ (by decide)]; exact hr.nv.n,
      by rw [hb₁ _ (by have := slot_le (w := w) (show aN < 8 by decide); unfold offP; omega)]; exact hr.nv.inv,
      by rw [hwv _ (by decide)]; exact hr.nv.r2, by rw [hwv _ (by decide)]; exact hr.nv.r2lt,
      by rw [hwv _ (by decide)]; exact hr.nv.one⟩,
    by rw [hb₁ _ (by unfold sMask sFn offP; omega)]; exact hr.msk,
    by rw [hb₁ _ (by unfold sWsP sFn offP; omega)]; exact hr.wsP,
    by rw [hb₁ _ (by unfold sWsQ sFn offP; omega)]; exact hr.wsQ,
    hpws₁, hr.qws.of_words fun i hi => hqw i (by omega), hpy₁,
    ⟨by rw [hqv _ _ (by omega)]; exact hr.qxv.n,
      by rw [word_off, hq₁ _ (by omega) (by omega), ← word_off]; exact hr.qxv.inv,
      by rw [hqv _ _ (by omega)]; exact hr.qxv.one⟩,
    hr.hfix.trans fun i hi _ => hb₁ _ (by unfold offP; omega),
    hr.iscr.trans (InScr.of_frm f₁ fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only [xRange]; unfold offQ at *; omega),
    (hr.keep.trans k₁).mono (by decide)⟩

/-- `R_q² mod q`, after `p`'s. -/
theorem r2Q_ok {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : R2Mid s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (r2At sWsQ)) t₁ fun t => R2Done s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  generalize (k + 7) / 8 = w at *
  obtain ⟨-, -, hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwq : wsWords ql < 2 ^ 20 := by unfold wsWords; omega
  have hloQ : slot w 8 ≤ offQ w pl := by unfold offQ; omega
  refine WP.mono (r2At_ok hr.good hloQ hZq hwq2 hwq (by decide) hr.wsQ hr.qws hr.qxv hQ'.1)
    fun t ⟨hg, hqws, hqy, f₂, k₂⟩ => ?_
  have hb : ∀ d, d + 8 ≤ offQ w pl → word t.mem B d = word t₁.mem B d := fun d hd => f₂.x_below hd (by omega)
  have hpv : ∀ d m, d + 8 * m ≤ slot (wsWords pl) 8 → wv t.mem (off B (offP w)) d m =
      wv t₁.mem (off B (offP w)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hb _ (by unfold offP offQ; omega)
  have hpw : ∀ i < 32, word t.mem (off B (offP w)) (8 * i) = word t₁.mem (off B (offP w)) (8 * i) :=
    fun i hi => by rw [word_off, word_off]; exact hb _ (by unfold offP offQ; omega)
  have hwv : ∀ j < 8, wv t.mem B (slot w j) w = wv t₁.mem B (slot w j) w := fun j hj =>
    wv_congr fun i hi => hb _ (by have := slot_le (w := w) hj; unfold offQ; omega)
  refine ⟨hg, ⟨by rw [hwv _ (by decide)]; exact hr.nv.n,
      by rw [hb _ (by have := slot_le (w := w) (show aN < 8 by decide); unfold offQ; omega)]; exact hr.nv.inv,
      by rw [hwv _ (by decide)]; exact hr.nv.r2, by rw [hwv _ (by decide)]; exact hr.nv.r2lt,
      by rw [hwv _ (by decide)]; exact hr.nv.one⟩,
    by rw [hb _ (by unfold sMask sFn offQ; omega)]; exact hr.msk,
    by rw [hb _ (by unfold sWsP sFn offQ; omega)]; exact hr.wsP,
    by rw [hb _ (by unfold sWsQ sFn offQ; omega)]; exact hr.wsQ,
    hr.pws.of_words fun i hi => hpw i (by omega), hqws,
    by rw [hpv _ _ (by have := slot_le (w := wsWords pl) (show aY < 8 by decide); omega)]; exact hr.py, hqy,
    hr.hfix.trans fun i hi _ => hb _ (by unfold offQ; omega),
    hr.iscr.trans (InScr.of_frm f₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only [xRange]; omega),
    (hr.keep.trans k₂).mono (by decide)⟩

/-- `r2Phase`, from what the checks leave. -/
theorem r2Phase_ok {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs r2Phase) t₀ fun t => R2Done s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk :=
  wp_seqs_append (by simp [r2At]) (by simp [r2At])
    (WP.mono (r2P_ok h hv hr hMk) fun _ hm => r2Q_ok h hv hm hMk)

end VG.Proof.Bignum.X86_64.PrivPre
