module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Pre
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnitPc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed_ifma` on x86-64: `pre`

The IFMA path's `pre` taking each prime's `R_X mod X` from `pre`
(`prepPc_ok`, `prePc_ok`): `R_X mod X` is right if `pre` holds it, and
`x R_X mod X` if `ok` (`R² mod n` right), as before.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The start of a prime's `prep`, up to `aXc := aT`: in the prime's
workspace, which alone it changes. -/
theorem prepHead_frame (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X)
    (hX1 : 1 < X) :
    WP isa (seqs (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aR2 ++
      copyArr Public.aY aXc ++ redc M.mm Public.aXm ++ ([M.mm aT Public.aY aXc] : List (Prog isa)) ++
      copyArr aXc aT)) s fun s₅ =>
      SubCtx s₅ B Z o w wx mx ∧ Keep (mmRegs ++ ([.rdi] : List Reg)) s s₅ ∧ Frm B [xRange o wx] s.mem s₅.mem := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_using [hhi, hn]
  have lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
  rw [show ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aR2 ++
      copyArr Public.aY aXc ++ redc M.mm Public.aXm ++ ([M.mm aT Public.aY aXc] : List (Prog isa)) ++
      copyArr aXc aT =
      (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aR2) ++
      (copyArr Public.aY aXc ++ (redc M.mm Public.aXm ++ (([M.mm aT Public.aY aXc] : List (Prog isa)) ++
      copyArr aXc aT))) by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp [copyArr]) (WP.mono (enterRedc_ok M (j := Public.aR2) (by decide) hg
    hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1) fun s₁ ⟨hc₁, hX₁, _, _, f₁, _, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [copyArr]) (by simp [redc]) (WP.mono (copyArr_ok hc₁.good (Nat.le_refl _)
    (by omega_using [hwx2]) (by omega_using [hw28, hwx]) (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide))
    fun s₂ ⟨_, ho₂, k₂⟩ => ?_)
  have hc₂ := hc₁.of_frm (rs := [(slot wx Public.aY, 8 * wx)]) (Frm.of_outside ho₂ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lY, hY0]) k₂.2.2 (k₂.gpr (by decide))
  have hX₂ : XVals s₂ B o wx mx X := hX₁.of_outside ho₂ (by decide) (by decide) (by decide) (by omega_using [])
    (by have := hc₁.good.scr.nowrap; omega_using [this])
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem :=
    (ho₂.mono (o' := slot wx Public.aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_using [])).to_x
      (by decide) hoL (List.mem_singleton_self _)
  refine wp_seqs_append (by simp [redc]) (by simp) (WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega_using [hw28]) hX1
    (j := Public.aXm) (by decide)) fun s₃ ⟨hc₃, hX₃, hlt₃, _, r₃, k₃⟩ => ?_)
  have fx₃ : Frm B [xRange o wx] s₂.mem s₃.mem := r₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  refine wp_seqs_append (by simp) (by simp [copyArr]) (WP.mono (M.mm_ok (o := aT) (a := Public.aY) (b := aXc)
    hc₃.good (Nat.le_refl _) hwx2 (by omega_using [hw28, hwx]) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX₃.inv (by rw [hX₃.n]; exact hlt₃)) fun s₄ ⟨_, _, _, ha₄, k₄⟩ => ?_)
  obtain ⟨hc₄, -, fx₄⟩ := hc₃.of_arrays hX₃ ha₄ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₄.2.2 (k₄.gpr (by decide)) (by omega_using [hwx2])
  refine WP.mono (copyArr_ok hc₄.good (Nat.le_refl _)
    (by omega_using [hwx2]) (by omega_using [hw28, hwx]) (o := aXc) (a := aT) (by decide) (by decide) (by decide))
    fun s₅ ⟨_, ho₅, k₅⟩ => ?_
  have lC := slot_le (w := wx) (show aXc < 8 by decide)
  have hC0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have hc₅ := hc₄.of_frm (rs := [(slot wx aXc, 8 * wx)]) (Frm.of_outside ho₅ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) k₅.2.2 (k₅.gpr (by decide))
  have fx₅ : Frm B [xRange o wx] s₄.mem s₅.mem :=
    (ho₅.mono (o' := slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_using [])).to_x
      (by decide) hoL (List.mem_singleton_self _)
  exact ⟨hc₅, (((k₁.trans k₂).trans k₃).trans k₄).trans k₅ |>.mono (by decide),
    (((f₁.trans fx₂).trans fx₃).trans fx₄).trans fx₅⟩

theorem prepPc_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C : Nat}
    {sl o wx : Nat} {ok : Prop} {P : Addr} {W d : Nat} {po : List Instr} (hg : Good s B Z w minv)
    (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hw2 : w = 2 * wx) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hN : NVals s B w minv N ok)
    (hXm : ok → wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hpre : PreSrc s B Z P W) (hdW : d + wx ≤ W)
    (hpo : ∀ t : State, t.gpr .rdi = off B o → t.rd = s.rd → t.wr = s.wr →
      word t.mem (off B o) (8 * sLink) = B → Frm B [xRange o wx] s.mem t.mem →
      WP isa (.block po) t fun t' => t'.gpr .rax = BitVec.ofNat 64 d ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t') :
    WP isa (seqs (CrtIfma.prep M.mm sl true po)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧
      XVals t B o wx mx X ∧ wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (wv s.mem P (8 * d) wx = 2 ^ (64 * wx) % X → X ∣ N →
        wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
      wv t.mem (off B o) (slot wx aXc) wx < X ∧
      (ok → X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X) ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Keep mmRegs s t ∧
      word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX) := by
  have hn := hg.scr.nowrap
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have hT := tabBytes_le_wsTab wx
  rw [show CrtIfma.prep M.mm sl true po = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
      redc M.mm Public.aR2 ++ copyArr Public.aY aXc ++ redc M.mm Public.aXm ++
      ([M.mm aT Public.aY aXc] : List (Prog isa)) ++ copyArr aXc aT ++ Crt.loadPre Public.aY po ++
      ([.block [leave]] : List (Prog isa)) by simp only [CrtIfma.prep, ↓reduceIte]]
  refine prepWith_ok M (fin := Crt.loadPre Public.aY po) (by simp [Crt.loadPre]) hg hw28 hlo hhi hwx2 hw2 hsl hslv
    hws hN hXm hX hX1 hXodd fun s₅ hc₅ hX₅ k₅ f₅ _ _ => ?_
  have i₅ : InScr B Z s.mem s₅.mem := InScr.of_frm f₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hp₅ := hpre.congrK i₅ k₅ (by decide)
  have hg₅ := hc₅.good
  have hY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
  have hfar : ∀ x : Addr, Z ≤ ofs B x → slot wx Public.aY + 8 * (wx + 2) ≤ ofs (off B o) x := fun x hx => by
    rcases ofs_rebase B x (o := o) (by omega) with ⟨_, e⟩ | ⟨h, _⟩
    · rw [e]; omega
    · omega
  refine WP.mono (loadPre_ok hg₅ (Nat.le_refl _) (by omega) (by omega) (by decide) (by decide) hp₅.arg hp₅.val
    (d := d) (fun t hm kt => hpo t ((kt.gpr (by decide)).trans hc₅.rdi) (kt.2.1.trans k₅.2.1) (kt.2.2.trans k₅.2.2)
      (by rw [hm]; exact hc₅.link) (by rw [hm]; exact f₅))
    (fun i hi => by rw [show 8 * d + 8 * i = 8 * (d + i) by omega]; exact hp₅.rd _ (by omega))
    (fun i hi b hb => .inr (hfar _ (by
      have := hp₅.out (d + i) (by omega) b hb; rwa [show 8 * (d + i) = 8 * d + 8 * i by omega] at this))))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hpre.wv_eq i₅ hdW, hX₅.n] at hv
  have hc := hc₅.of_frm (rs := [(slot wx Public.aY, 8 * (wx + 2))]) (Frm.of_outside ho (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) kt.2.2 (kt.gpr (by decide))
  have hC := slot_le (w := wx) (show aXc < 8 by decide)
  have sYC := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
  refine ⟨hc, hX₅.of_outside ho (by decide) (by decide) (by decide) (Nat.le_refl _)
      (by have := hg₅.scr.nowrap; omega), ho.to_x (by decide) hoL (List.mem_singleton_self _),
    by rw [hv]; split <;> omega, fun hok _ => ?_, ho.wv (by omega) (by have := hg₅.scr.nowrap; omega),
    ho.word (.inl (by have := hdr_lt_slot wx Public.aY (show sMaskX < 32 by decide); omega))
      (by unfold sMaskX sFn; omega), kt⟩
  have hlt : 2 ^ (64 * wx) % X < X := Nat.mod_lt _ (by omega)
  rw [hv, hok]; simp only [hlt, ↓reduceIte, Nat.mod_mod]

theorem pre_pc (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.pre mul true = CrtIfma.prep mul sWsQ true Crt.offQ ++ CrtIfma.prep mul sWsP true Crt.offP := rfl

/-- `pre` with `R_q mod q` and `R_p mod p` from words `2 w + w_p` and `2 w` of
`pre`. -/
theorem prePc_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {N P Q C op wp oq : Nat}
    {ok : Prop} {Pr : Addr} {W : Nat}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hpq : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wp 8 + wsTab wp ≤ Z) (hwp2 : 2 ≤ wp)
    (hw2 : w = 2 * wp) (hsp : word s.mem B (8 * sWsP) = off B op) (hsq : word s.mem B (8 * sWsQ) = off B oq)
    (hwsp : WsAt s.mem B op wp mp) (hwsq : WsAt s.mem B oq wp mq) (hN : NVals s B w minv N ok)
    (hXm : ok → wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hP : XVals s B op wp mp P) (hP1 : 1 < P) (hPodd : P % 2 = 1)
    (hQ : XVals s B oq wp mq Q) (hQ1 : 1 < Q) (hQodd : Q % 2 = 1)
    (hpre : PreSrc s B Z Pr W) (hW : 2 * w + wp + wp ≤ W) :
    WP isa (seqs (CrtIfma.pre M.mm true)) s fun t => Good t B Z w minv ∧ NVals t B w minv N ok ∧
      PrimeRdy t B op wp mp N P C (ok ∧ wv s.mem Pr (8 * (2 * w)) wp = 2 ^ (64 * wp) % P) ∧
      PrimeRdy t B oq wp mq N Q C (ok ∧ wv s.mem Pr (8 * (2 * w + wp)) wp = 2 ^ (64 * wp) % Q) ∧
      Frm B (preRanges w op wp oq wp) s.mem t.mem ∧ Keep mmRegs s t ∧
      word t.mem (off B op) (8 * sMaskX) = word s.mem (off B op) (8 * sMaskX) := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_using []
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hlo, hpq, hoq, hn]
  have hmk : 8 * sMaskX + 8 ≤ slot wp 8 := by unfold sMaskX sFn; omega_using [hX8]
  have hl : ∀ d, d + 8 ≤ Z → InRegions (s.rd ++ s.wr) (off B d) 8 := fun d hd => hs.ld hd
  have ho64 : oq < 2 ^ 64 := by omega_using [hoq, hn, hmk]
  rw [pre_pc]
  -- `q`.
  refine wp_seqs_append (by simp [CrtIfma.prep]) (by simp [CrtIfma.prep]) (WP.mono (prepPc_ok (C := C) M hg hw28
    (by omega_using [hlo, hpq]) hoq hwp2 hw2 (by decide) hsq hwsq hN hXm hQ hQ1 hQodd hpre (d := 2 * w + wp)
    (by omega) fun t hdi hrd hwr hlk hf => ?_)
    fun s₁ ⟨hg₁, hwsq₁, hQ₁, hqy, hqyv, hqx, hqxv, fQ, kQ, _⟩ => ?_)
  · have hb : ∀ d, d + 8 ≤ oq → word t.mem B d = word s.mem B d := fun d hd => hf.x_below hd ho64
    refine offQ_ok hdi (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sLink sFn; omega)) hlk
      (by rw [hrd, hwr]; exact hl _ (by unfold sW; omega)) (by rw [hb _ (by unfold sW; omega)]; exact hg.hdr.hw)
      (by rw [hrd, hwr]; exact hl _ (by unfold sWsP sFn; omega))
      (by rw [hb _ (by unfold sWsP sFn; omega)]; exact hsp)
      (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sW; omega))
      (by rw [word_off, hb _ (by unfold sW; omega), ← word_off]; exact hwsp.hdr.hw)
  have hb : ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := fun d hd => fQ.x_below hd ho64
  have hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega_using [hpq])
  have hN₁ : NVals s₁ B w minv N ok := hN.of_frm (fQ.mono fun r hr => List.mem_append_right _ hr)
    (by omega_using [hlo, hpq]) hz (by omega_using [hwp2, hw2])
  have hXm₁ : wv s₁.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    wv_congr fun i hi => hb _ (by have := slot_le (w := w) (show Public.aXm < 8 by decide); omega_using [hlo, hpq, hi, this])
  have i₁ : InScr B Z s.mem s₁.mem := InScr.of_frm fQ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hl₁ : ∀ d, d + 8 ≤ Z → InRegions (s₁.rd ++ s₁.wr) (off B d) 8 := fun d hd => hg₁.scr.ld hd
  -- `p`.
  refine WP.mono (prepPc_ok (C := C) M hg₁ hw28 hlo (by omega_using [hpq, hoq]) hwp2 hw2 (by decide)
    (by rw [hb _ (by unfold sWsP sFn; omega_using [hpq, hX8])]; exact hsp)
    (hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega_using [h, hX8]) (by omega_using [hpq, hX8, ho64])) hN₁
    (by rw [hXm₁]; exact hXm) (hP.of_disj fQ hQd (by omega_using [hpq, ho64])) hP1 hPodd
    (hpre.congrK i₁ kQ (by decide)) (d := 2 * w) (by omega) fun t hdi hrd hwr hlk hf => ?_)
    fun t ⟨hgt, hwspt, hPt, hpy, hpyv, hpx, hpxv, fP, kP, mkP⟩ => ?_
  · have hop : op < 2 ^ 64 := by omega
    have hb' : ∀ d, d + 8 ≤ op → word t.mem B d = word s₁.mem B d := fun d hd => hf.x_below hd hop
    exact offP_ok hdi (by rw [hrd, hwr, off_off]; exact hl₁ _ (by unfold sLink sFn; omega)) hlk
      (by rw [hrd, hwr]; exact hl₁ _ (by unfold sW; omega))
      (by rw [hb' _ (by unfold sW; omega), hb _ (by unfold sW; omega)]; exact hg.hdr.hw)
  have hPd : ∀ r ∈ [xRange op wp], r.1 + r.2 ≤ oq ∨ oq + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega_using [hpq, hX8])
  rw [hpre.wv_eq i₁ (by omega)] at hpyv
  refine ⟨hgt, hN₁.of_frm (fP.mono fun r hr => List.mem_append_right _ hr) hlo hz (by omega_using [hwp2, hw2]),
    ⟨hwspt, hPt, hpy, fun h hd => hpyv h.2 hd, hpx, fun h hd => hpxv h.1 hd⟩,
    PrimeRdy.of_disj ⟨hwsq₁, hQ₁, hqy, fun h hd => hqyv h.2 hd, hqx, fun h hd => hqxv h.1 hd⟩ fP hPd
      (by omega_using [hoq, hn]),
    (fQ.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [preRanges]).trans
      (fP.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [preRanges]),
    kQ.trans kP |>.mono (by decide), ?_⟩
  rw [mkP, word_off, word_off, fQ.word_eq (fun r hr => by rcases hQd r hr with h | h <;> omega_arith) (by omega_using [hpq, hmk, ho64])]

end VG.Proof.Bignum.X86_64
