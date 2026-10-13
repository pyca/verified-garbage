module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowQ
public import VerifiedGarbage.Proof.Bignum.CrtWindowPRanges
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFix
public import VerifiedGarbage.Proof.Bignum.CrtPRanges
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Int.ModEq

/-!
# RSA with the CRT on AArch64: `p`'s phase

`pPhase`: `m_p = c^dP mod p` as `pPhase`'s `qPhase` computes `m_q`, then
`m_q R_p mod p` (from `m_q G mod n`, `mqPart_ok`), and
`h = (m_p - m_q) qInv mod p` into `p`'s `Y` (`hPart_ok`, `pPhase_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (xRange32 tabBytes32 px_hdr px_above px_wv x_below32 pxR_bound)
open VG.Proof.MlKem.AArch64 (Keep)

theorem pPhase_eq (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.AArch64.WindowFive.pPhase window select mul =
    unitSteps mul sWsP ++ (mqSteps mul ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps window select mul sWsP sDp sPlen ++ (([.block [leave]] : List (Prog isa)) ++ hSteps mul)))) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.pPhase, unitSteps, powSteps, mqSteps, hSteps, enterP, List.append_assoc, List.cons_append,
    List.nil_append]

/-- `p`'s phase: `h = (m_p - m_q) qInv mod p` into `p`'s `Y` if `p` divides
`N`, `X_m ≡ c R (mod N)`, `m_q` in `q`'s `Y` and `qInv` (masked by `c`). -/
theorem pPhase_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes32 wx ≤ oq)
    (hqhi : oq + slot wq 8 + tabBytes wq ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w)
    (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hslq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wq mq)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c) (hc : c = true → X ∣ N)
    (hep : word s.mem B (8 * sDp) = ep) (hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (c = true → ∃ a b, a % X = C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X ∧
        b % X = wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (off B o) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X =
          (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B (pRanges w ++ [xRange32 o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have ht : tabBytes wx ≤ tabBytes32 wx := by unfold tabBytes tabBytes32; omega
  have hhi16 : o + slot wx 8 + tabBytes wx ≤ Z := by omega
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega_using []
  have ho64 : o < 2 ^ 64 := by omega_using [hhi, hqhi, hn, hQ8]
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hlo, hhi, hqhi, hn]
  have hhi' : o + slot wx 8 + tabBytes32 wx ≤ Z := by omega_using [hhi, hqhi]
  have hsub : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r ∈ pRanges w ++ [xRange32 o wx]) → ∀ {m m' : Mem},
      Frm B rs m m' → Frm B (pRanges w ++ [xRange32 o wx]) m m' := fun h _ _ f => f.mono h
  have sgx : ∀ r ∈ gRanges w ++ [xRange32 o wx], r ∈ pRanges w ++ [xRange32 o wx] := fun r hr =>
    (List.mem_append.mp hr).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      (fun h => List.mem_append_right _ h)
  have sp : ∀ r ∈ pRanges w, r ∈ pRanges w ++ [xRange32 o wx] := fun r hr => List.mem_append_left _ hr
  have sg : ∀ r ∈ gRanges w, r ∈ pRanges w ++ [xRange32 o wx] := fun r hr =>
    List.mem_append_left _ (List.mem_append_left _ hr)
  have sx : ∀ r ∈ [xRange32 o wx], r ∈ pRanges w ++ [xRange32 o wx] := fun r hr => List.mem_append_right _ hr
  -- What the frame keeps.
  have hq : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange32 o wx]) m m' → ∀ d k, d + 8 * k ≤ slot wq 8 →
      wv m' (off B oq) d k = wv m (off B oq) d k := fun f d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => px_above f hlo (by omega_using [hhi]) (by omega_using [hqhi, hn, hd, hi])
  have hqh : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange32 o wx]) m m' → ∀ i < 32,
      word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun f i hi => by
    rw [word_off, word_off]; exact px_above f hlo (by omega_using [hhi]) (by omega_using [hqhi, hn, hQ8, hi])
  rw [pPhase_eq]
  -- `R_p mod p`.
  refine wp_seqs_append (by simp [unitSteps]) (by simp [mqSteps]) ?_
  refine WP.mono (unitPhase_ok M hg hw hw28 hlo hhi16 hwx2 hwx (sl := sWsP) (by decide) (by decide) (by decide) hslv
    hws hN hodd hN1 hX hX1 hXodd) fun s₁ ⟨hg₁, hws₁, hX₁, hlt₁, hG₁, hpl₁, hpy₁, hM₁, f₁, k₁⟩ => ?_
  have f₁wide : Frm B (gRanges w ++ [xRange32 o wx]) s.mem s₁.mem := by
    apply f₁.widen
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r,List.mem_append_left _ hr,le_rfl,le_rfl⟩
    · rw [List.mem_singleton.mp hr]
      refine ⟨xRange32 o wx,by simp,le_rfl,?_⟩
      simp only [VG.Proof.Bignum.xRange,xRange32]
      omega
  have f₁' := hsub sgx f₁wide
  -- `m_q G mod N`.
  refine wp_seqs_append (by simp [mqSteps]) (by simp) ?_
  refine WP.mono (mqPart_ok M hg₁ hw hw28 (hN.of_frm f₁ hlo hz (by omega_using [hwq, hwq'])) hodd hlt₁ hG₁
    (by rw [px_hdr f₁' hlo (by decide) (by decide) (by decide)]; exact hslq)
    (hwsq.of_words fun i hi => hqh f₁' i (by omega_using [hi])) (by omega_using [hlo, hhi]) hqhi hwq hwq')
    fun s₂ ⟨hg₂, hlt₂, hmq₂, hY₂, f₂, k₂⟩ => ?_
  have f₂' := hsub sp f₂
  have f₀₂ := f₁'.trans f₂'
  have hN₂ : NVals s₂ B w minv N := by
    have := hN.of_frm f₁ hlo hz (by omega_using [hwq, hwq'])
    exact ⟨by rw [px_wv f₂' hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.n,
      by rw [f₂'.word_eq (fun r hr => by
        have := CrtWindowFive.pxR_bound hlo r hr
        have := slot_le (w := w) (show Public.aN < 8 by decide)
        simp only [pRanges, gRanges, xRange32, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        have s1 := slot_sep (w := w) (show Public.aN ≠ Public.aAcc by decide)
        have s2 := slot_sep (w := w) (show Public.aN ≠ Public.aTmp by decide)
        have s3 := slot_sep (w := w) (show Public.aN ≠ Public.aY by decide)
        have s4 := slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
        have := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega_arith)
        (by have := slot_le (w := w) (show Public.aN < 8 by decide); omega_using [hz, this])]; exact this.inv,
      by rw [px_wv f₂' hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.r2,
      by rw [px_wv f₂' hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.r2lt,
      by rw [px_wv f₂' hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.one⟩
  -- `c G mod N`.
  refine wp_seqs_append (by simp) (by simp [powSteps]) ?_
  refine WP.mono (mmY_ok M hg₂ (by omega_using [hlo, hhi']) (by omega_using [hwx2, hwx]) (by omega_using [hw28])
      (a := Public.aXm) (by decide) (by decide)
    (by decide) hN₂ (by rw [hY₂]; exact hlt₁)) fun s₃ ⟨hg₃, hlt₃, hm₃, f₃, k₃⟩ => ?_
  have f₃' := hsub sg f₃
  have f₀₃ := f₀₂.trans f₃'
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hXm₂ : wv s₂.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    px_wv f₀₂ hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcg : wv s₃.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, Nat.mul_mod, hXm₂, hXm, hY₂, hG₁, ← Nat.mul_mod]
    congr 1; ac_rfl
  have hpo : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d,
      o ≤ d → d + 8 ≤ 2 ^ 64 → word m' B d = word m B d := fun f hrs d hd hd' =>
    f.word_eq (fun r hr => Or.inr (by have := pRanges_le w r (hrs r hr); omega_using [hlo, hd, this])) hd'
  have hpw : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ i < 32,
      word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun f hrs i hi => by
    rw [word_off, word_off]; exact hpo f hrs _ (by omega_using []) (by omega_using [hn, hX8, hhi', hi])
  have sg' : ∀ r ∈ gRanges w, r ∈ pRanges w := fun r hr => List.mem_append_left _ hr
  have hpv : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d k,
      d + 8 * k ≤ slot wx 8 → wv m' (off B o) d k = wv m (off B o) d k := fun f hrs d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpo f hrs _ (by omega_using []) (by omega_using [hn, hhi', hd, hi])
  have hY8 := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hpY₃ : wv s₃.mem (off B o) (slot wx Public.aY) wx = wv s₁.mem (off B o) (slot wx Public.aY) wx := by
    rw [hpv f₃ sg' _ _ (by omega_using [hY8]), hpv f₂ (fun r h => h) _ _ (by omega_using [hY8])]
  have hws₃ : WsAt s₃.mem B o wx mx := hws₁.of_words fun i hi => by
    rw [hpw f₃ sg' i (by omega_using [hi]), hpw f₂ (fun r h => h) i (by omega_using [hi])]
  have hX₃ : XVals s₃ B o wx mx X :=
    (hX₁.of_below f₂ (fun r hr => (pRanges_le w r hr).trans hlo) (by omega_using [hn, hhi'])).of_below f₃
      (fun r hr => (pRanges_le w r (sg' r hr)).trans hlo) (by omega_using [hn, hhi'])
  have i03 : InScr B Z s.mem s₃.mem := InScr.of_frm f₀₃ fun r hr => by have := CrtWindowFive.pxR_bound hlo r hr; omega_using [hhi', this]
  -- `c^dP R_p mod p`.
  refine wp_seqs_append (by simp [powSteps]) (by simp) ?_
  refine WP.mono (powPhase_ok W M S hg₃ hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide)
    (by rw [px_hdr f₀₃ hlo (by decide) (by decide) (by decide)]; exact hslv) hws₃ hX₃ hX1 hXodd hcg
    (by rw [hpY₃]; exact hpl₁) (fun hd => by rw [hpY₃]; exact hpy₁ hd) (sd := sDp) (slen := sPlen) (by decide)
    (by decide) (by rw [px_hdr f₀₃ hlo (by decide) (by decide) (by decide)]; exact hep)
    (by rw [px_hdr f₀₃ hlo (by decide) (by decide) (by decide)]; exact hel) hL1 hL2
    (he.congrK i03 ((k₁.trans k₂).trans k₃))) fun s₄ ⟨hc₄, hX₄, hlt₄, hv₄, hM₄, fx₄, k₄⟩ => ?_
  -- Back to the modulus'.
  refine wp_seqs_append (by simp) (by simp [hSteps]) ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₄.mem)
    (by brun [leave, hc₄.x0, hdr_enc (show sLink < 32 by decide), hc₄.ld' (show sLink < 32 by decide), hc₄.link'])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_
  have fx₅ : Frm B [xRange32 o wx] s₃.mem s₅.mem := by rw [hm₅]; exact fx₄
  have f₀₅ := f₀₃.trans (hsub sx fx₅)
  have k05 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  have hb₅ : ∀ d, d + 8 ≤ o → word s₅.mem B d = word s₃.mem B d := fun d hd => x_below32 fx₅ hd ho64
  have hg₅ : Good s₅ B Z w minv := ⟨hs.congr k05.wr, hdi₅, ⟨(hb₅ _ (by unfold sW; omega_arith)).trans hg₃.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega_arith)).trans hg₃.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_arith); omega_arith)).trans
      (hg₃.hdr.harr j hj)⟩⟩
  have hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  have hXn₅ : wv s₅.mem B (slot w Public.aX) w % N =
      wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    rw [wv_congr fun i hi => hb₅ _ (by have := slot_le (w := w) (show Public.aX < 8 by decide); omega_arith),
      f₃.wv_eq (fun r hr => by
        have := slot_le (w := w) (show Public.aX < 8 by decide)
        have s1 := slot_sep (w := w) (show Public.aX ≠ Public.aAcc by decide)
        have s2 := slot_sep (w := w) (show Public.aX ≠ Public.aTmp by decide)
        have s3 := slot_sep (w := w) (show Public.aX ≠ Public.aY by decide)
        have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
        simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega_arith)
        (by have := slot_le (w := w) (show Public.aX < 8 by decide); omega_arith), hmq₂,
      hq f₁' _ _ (by have := slot_le (w := wq) (show Public.aY < 8 by decide); omega_arith)]
  have i05 : InScr B Z s.mem s₅.mem := InScr.of_frm f₀₅ fun r hr => by have := CrtWindowFive.pxR_bound hlo r hr; omega_arith
  -- `h`.
  have a1 : word s₅.mem B (8 * sWsP) = off B o := by
    rw [px_hdr f₀₅ hlo (by decide) (by decide) (by decide)]; exact hslv
  have a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  have a3 : wv s₅.mem (off B o) (slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  have a4 : X ∣ N → wv s₅.mem (off B o) (slot wx Public.aY) wx % X =
      C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X := fun hd => by rw [hm₅]; exact hv₄ hd
  have a5 : word s₅.mem (off B o) (8 * sMaskX) = mask c := by
    rw [hm₅, hM₄, hpw f₃ sg' _ (by decide), hpw f₂ (fun r h => h) _ (by decide), hM₁]; exact hmask
  have a6 : word s₅.mem B (8 * sQinv) = qp := by
    rw [px_hdr f₀₅ hlo (by decide) (by decide) (by decide)]; exact hqp
  have a7 : word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [px_hdr f₀₅ hlo (by decide) (by decide) (by decide), hql]; exact hel
  refine WP.mono (hPart_ok M hg₅ hw28 hlo hhi16 hwx2 hwx a1 a2 hX₅ hX1 hXodd hXn₅ a3 a4 a5 hc a6 a7
    (hqs.congrK i05 k05) (by omega_arith) (by omega_arith) hqw hqi) fun t ⟨hg', hws', hX', hlt', hh', fx', k'⟩ => ?_
  have kall := k05.trans k'
  refine ⟨hg', hws', hX', hlt', hh', f₀₅.trans (hsub sx (fx'.widen (fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine ⟨xRange32 o wx,by simp,le_rfl,?_⟩
      simp only [VG.Proof.Bignum.xRange,xRange32]
      omega))), ⟨fun r hr => ?_, kall.rd, kall.wr, kall.sp, kall.vcs⟩⟩
  by_cases h : r = .x0
  · subst h; rw [hg'.x0, hg.x0]
  · exact kall.gpr r (by simp only [List.mem_append, List.mem_singleton, hr, h, or_self, not_false_eq_true])

end VG.Proof.Bignum.AArch64.WindowFive
