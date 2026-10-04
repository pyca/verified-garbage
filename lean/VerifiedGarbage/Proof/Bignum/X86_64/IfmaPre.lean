import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ

/-!
# RSA with AVX512_IFMA on x86-64: the bases in the primes' workspaces

`pre` computes `G` once in `n`'s workspace and, for each prime `X`, enters
its workspace and reduces (`enterRedc_ok`): `R_X` into `aY` (from `G`)
and `x R_X` into `aXc` (from `x G`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Into a prime's workspace (`rdi := [sl]`), and `aXc := [aY] R^-K mod X`. -/
theorem enterRedc_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X)
    (hX1 : 1 < X) :
    WP isa (seqs (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aY)) s fun t =>
      SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧ wv t.mem (off B o) (slot wx aXc) wx < X ∧
      wv t.mem (off B o) (slot wx aXc) wx * 2 ^ (64 * wx * nChunks w wx) % X =
        wv s.mem B (slot w Public.aY) w % X ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Frm (off B o) (redcRanges wx) s.mem t.mem ∧
      Keep (mmRegs ++ [.rdi]) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun s₂ ⟨⟨hdi₂, hm₂⟩, k₂⟩ => ?_
  have hc₂ : SubCtx s₂ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₂.2.2) (by rw [hm₂]; exact hg.hdr) (by rw [hm₂]; exact hws) hdi₂ hlo hhi
  have hX₂ : XVals s₂ B o wx mx X := by
    rw [show s₂ = { s₂ with mem := s.mem } by rw [← hm₂]] ; exact ⟨hX.n, hX.inv, hX.one⟩
  refine WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide))
    fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, f₃, k₃⟩ => ⟨hc₃, hX₃, hlt₃, by rw [← hm₂]; exact hv₃, ?_, ?_, ?_⟩
  · rw [← hm₂]; exact f₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  · rw [← hm₂]; exact f₃
  · exact (k₂.trans k₃).mono (by simp [mmRegs])


/-- Back to `n`'s workspace, whose header the prime's phase kept. -/
theorem leaveBack_ok {s₀ t : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {o wx : Nat}
    (hg : Good s₀ B Z w minv) (hc : SubCtx t B Z o w wx mx) (hf : Frm B [xRange o wx] s₀.mem t.mem)
    (hlo : slot w 8 ≤ o) :
    WP isa (.block [leave]) t fun t' => Good t' B Z w minv ∧ t'.mem = t.mem ∧ Keep [.rdi] t t' := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hl : InRegions (t.rd ++ t.wr) (off (off B o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t' => t'.gpr .rdi = B ∧ t'.mem = t.mem)
    (by xrun [leave, State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl) fun t' ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hb : ∀ d, d + 8 ≤ o → word t'.mem B d = word s₀.mem B d := fun d hd => by
    rw [hm]; exact hf.x_below hd ho64
  have hH := hg.hdr
  exact ⟨⟨hc.scr.congr k.2.2, hdi, (hb _ (by unfold sW; omega)).trans hH.hw,
    (hb _ (by unfold sMinv; omega)).trans hH.hminv,
    fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hH.harr j hj)⟩, hm, k⟩


/-- One prime's part of `pre`: `R_X` into its `aY`, `x R_X` into its `aXc`. -/
def prepCode (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) : List (Prog isa) :=
  (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc mul Public.aY) ++
  (copyArr Public.aY aXc ++ (([.block [leave]] : List (Prog isa)) ++ (([mul Public.aY Public.aXm Public.aY] :
    List (Prog isa)) ++ ((([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc mul Public.aY) ++
    ([.block [leave]] : List (Prog isa))))))

theorem prep_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32) (hsl1 : sl ≠ Crt.sD)
    (hsl2 : sl ≠ Public.sCnt) (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hYl : wv s.mem B (slot w Public.aY) w < N)
    (hYv : wv s.mem B (slot w Public.aY) w % N = 2 ^ (64 * wx * (nChunks w wx + 1)) % N) :
    WP isa (seqs (prepCode M.mm sl)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
      wv t.mem (off B o) (slot wx aXc) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X) ∧
      NVals t B w minv N ∧ Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hRx : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have hgr : ∀ r ∈ gRanges w, r.1 + r.2 ≤ slot w 8 := by
    have := slot_le (w := w) (show Public.aAcc < 8 by decide)
    have := slot_le (w := w) (show Public.aTmp < 8 by decide)
    have := slot_le (w := w) (show Public.aY < 8 by decide)
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega
  unfold prepCode
  -- `aXc := G R^-K = R_X`.
  refine wp_seqs_append (by simp) (by simp [copyArr]) (WP.mono (enterRedc_ok M hg hw28 hlo hhi hwx2 hwx hsl
    hslv hws hX hX1) fun s₁ ⟨hc₁, hX₁, hlt₁, hv₁, f₁, _, k₁⟩ => ?_)
  -- `aY := aXc`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hc₁.good (Nat.le_refl _) (by omega)
    (by omega) (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide)) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  have hc₂ := hc₁.of_frm (rs := [(slot wx Public.aY, 8 * wx)]) (Frm.of_outside ho₂ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
    simp only; omega) k₂.2.2 (k₂.gpr (by decide))
  have hX₂ : XVals s₂ B o wx mx X := hX₁.of_outside ho₂ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₁.good.scr.nowrap; omega)
  have f02 : Frm B [xRange o wx] s.mem s₂.mem := f₁.trans
    (ho₂.mono (o' := slot wx Public.aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega) |>.to_x
      (by decide) hoL (List.mem_singleton_self _))
  -- Back to `n`'s workspace.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (leaveBack_ok hg hc₂ f02 hlo) fun s₃ ⟨hg₃, hm₃, k₃⟩ => ?_)
  have f03 : Frm B (gRanges w ++ [xRange o wx]) s.mem s₃.mem := by
    rw [hm₃]; exact f02.mono fun r hr => List.mem_append_right _ hr
  have hN₃ := hN.of_frm f03 hlo hz (by omega)
  have hbw : ∀ d k, d + 8 * k ≤ o → wv s₃.mem B d k = wv s.mem B d k := fun d k hd => by
    rw [hm₃]; exact wv_congr fun i hi => f02.x_below (by omega) ho64
  have hY₃ : wv s₃.mem B (slot w Public.aY) w = wv s.mem B (slot w Public.aY) w :=
    hbw _ _ (by have := slot_le (w := w) (show Public.aY < 8 by decide); omega)
  have hXm₃ : wv s₃.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    hbw _ _ (by have := slot_le (w := w) (show Public.aXm < 8 by decide); omega)
  -- `aY := x G` in `n`'s workspace.
  refine wp_seqs_append (by simp) (by simp [redc]) (WP.mono (mmY_ok M hg₃ (by omega) (by omega) (by omega)
    (a := Public.aXm) (by decide) (by decide) (by decide) hN₃ (by rw [hY₃]; exact hYl))
    fun s₄ ⟨hg₄, hlt₄, hm₄, f₄, k₄⟩ => ?_)
  have hRn : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hcg : wv s₄.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hRn
    rw [hm₄, Nat.mul_mod, hXm₃, hXm, hY₃, hYv, ← Nat.mul_mod]
    congr 1
    ac_rfl
  have hxo : ∀ i < 32, word s₄.mem (off B o) (8 * i) = word s₃.mem (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact f₄.word_eq (fun r hr => Or.inr (by have := hgr r hr; omega)) (by omega)
  have hb₄ : word s₄.mem B (8 * sl) = off B o := by
    rw [f₄.word_eq (fun r hr => by
      have := hdr_lt_slot w Public.aAcc (show sl < 32 from hsl)
      have := hdr_lt_slot w Public.aTmp (show sl < 32 from hsl)
      have := hdr_lt_slot w Public.aY (show sl < 32 from hsl)
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · show 8 * sl + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * sl
        unfold Crt.sD sFn at hsl1 ⊢; omega
      · show 8 * sl + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * sl
        unfold Public.sCnt sFn at hsl2 ⊢; omega) (by omega)]
    rw [hm₃]; exact (f02.x_below (by have := hdr_lt_slot w 8 hsl; omega) ho64).trans hslv
  have hws₄ : WsAt s₄.mem B o wx mx := (by rw [hm₃]; exact hc₂.ws : WsAt s₃.mem B o wx mx).of_words
    fun i hi => hxo i (by omega)
  have hX₄ : XVals s₄ B o wx mx X := (show XVals s₃ B o wx mx X from by
    rw [show s₃ = { s₃ with mem := s₂.mem } by rw [← hm₃]]; exact ⟨hX₂.n, hX₂.inv, hX₂.one⟩).of_below f₄
    (fun r hr => (hgr r hr).trans hlo) hoL
  -- `aXc := x G R^-K = x R_X`.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (enterRedc_ok M hg₄ hw28 hlo hhi hwx2 hwx hsl hb₄ hws₄ hX₄
    hX1) fun s₅ ⟨hc₅, hX₅, hlt₅, hv₅, f₅, r₅, k₅⟩ => ?_)
  refine WP.mono (leaveBack_ok hg₄ hc₅ f₅ hlo) fun t ⟨hg', hm', k'⟩ => ?_
  -- `x.aY`, kept since the copy.
  have hY₅ : wv s₅.mem (off B o) (slot wx Public.aY) wx = wv s₂.mem (off B o) (slot wx Public.aY) wx := by
    have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    rw [r₅.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), wv_off, wv_off,
      f₄.wv_eq (fun r hr => Or.inr (by have := hgr r hr; omega)) (by omega), hm₃]
  have kall := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k'
  have fall : Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem := by
    rw [hm']
    exact (f03.trans (f₄.mono fun r hr => List.mem_append_left _ hr)).trans
      (f₅.mono fun r hr => List.mem_append_right _ hr)
  have hXt : XVals t B o wx mx X := by
    rw [show t = { t with mem := s₅.mem } by rw [← hm']]
    exact ⟨hX₅.n, hX₅.inv, hX₅.one⟩
  refine ⟨hg', by rw [hm']; exact hc₅.ws, hXt, by rw [hm', hY₅, hv₂]; exact hlt₁, fun hd => ?_,
    by rw [hm']; exact hlt₅, fun hd => ?_, ?_, ?_, ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [hm', hY₅, hv₂]
    have e : wv s.mem B (slot w Public.aY) w % X = 1 * (2 ^ (64 * wx)) ^ (nChunks w wx + 1) % X := by
      rw [← Nat.mod_mod_of_dvd _ hd, hYv, Nat.mod_mod_of_dvd _ hd, Nat.one_mul, ← Nat.pow_mul]
    have := VG.Proof.Bignum.redc_cancel hRx ((by rw [← Nat.pow_mul]; exact hv₁ :
      wv s₁.mem (off B o) (slot wx aXc) wx * (2 ^ (64 * wx)) ^ nChunks w wx % X = _).trans e)
    rwa [Nat.one_mul] at this
  · rw [hm']
    have e : wv s₄.mem B (slot w Public.aY) w % X = C * (2 ^ (64 * wx)) ^ (nChunks w wx + 1) % X := by
      rw [← Nat.mod_mod_of_dvd _ hd, hcg, Nat.mod_mod_of_dvd _ hd, ← Nat.pow_mul]
    exact VG.Proof.Bignum.redc_cancel hRx ((by rw [← Nat.pow_mul]; exact hv₅ :
      wv s₅.mem (off B o) (slot wx aXc) wx * (2 ^ (64 * wx)) ^ nChunks w wx % X = _).trans e)
  · exact hN.of_frm fall hlo hz (by omega)
  · exact fall
  · by_cases h : r = .rdi
    · subst h; rw [hg'.rdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)


end VG.Proof.Bignum.X86_64
