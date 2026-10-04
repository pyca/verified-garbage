import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma

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
      Keep (mmRegs ++ ([.rdi] : List Reg)) s t := by
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



theorem pre_eq (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.X86_64.CrtIfma.pre mul =
    Crt.gPow mul sWsQ ++ (copyArr Public.aX Public.aY ++ (prepCode mul sWsQ ++
      (copyArr Public.aY Public.aX ++ prepCode mul sWsP))) := by
  simp only [VG.Impl.Rsa.X86_64.CrtIfma.pre, prepCode, enterQ, enterP, List.append_assoc, List.cons_append,
    List.nil_append]


/-- `n`'s values after a write to another of its arrays. -/
theorem NVals.of_outsideArr {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N j n : Nat}
    (h : NVals s B w minv N) (ho : Outside B (slot w j) n s.mem t.mem) (hj : j < 8) (h1 : j ≠ Public.aN)
    (h2 : j ≠ Public.aR2) (h3 : j ≠ Public.aOne) (hn : n ≤ 8 * (w + 2)) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) :
    NVals t B w minv N := by
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  have l1 := slot_le (w := w) (show Public.aN < 8 by decide)
  have l2 := slot_le (w := w) (show Public.aR2 < 8 by decide)
  have l3 := slot_le (w := w) (show Public.aOne < 8 by decide)
  have lj := slot_le (w := w) hj
  exact ⟨by rw [ho.wv (by omega) (by omega)]; exact h.n,
    by rw [ho.word (by omega) (by omega)]; exact h.inv,
    by rw [ho.wv (by omega) (by omega)]; exact h.r2, by rw [ho.wv (by omega) (by omega)]; exact h.r2lt,
    by rw [ho.wv (by omega) (by omega)]; exact h.one⟩

theorem Good.of_outsideArr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {j n : Nat}
    (h : Good s B Z w minv) (ho : Outside B (slot w j) n s.mem t.mem) (hk : Keep mmRegs s t) :
    Good t B Z w minv := by
  have hn := h.scr.nowrap
  have hh : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot w j hi; omega)) (by have := hdr_lt_slot w j hi; omega)
  exact ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, (hh _ (by decide)).trans h.hdr.hw,
    (hh _ (by decide)).trans h.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩


/-- `n`'s header and the arrays but `aAcc`, `aTmp`, `aY` and `aX`, and both primes' workspaces. -/
def preRanges (w op wp oq wq : Nat) : List (Nat × Nat) :=
  gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange oq wq, xRange op wp]

/-- A prime's values after a change on either side of its workspace. -/
theorem XVals.of_disj {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (h : XVals s B o wx mx X) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  have hN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have hd : ∀ d n, d + n ≤ slot wx 8 → ∀ r ∈ rs, o + d + n ≤ r.1 ∨ r.1 + r.2 ≤ o + d := fun d n hd r h' => by
    rcases hr r h' with h | h <;> omega
  exact ⟨by rw [wv_off, hf.wv_eq (hd _ _ (by omega)) (by omega), ← wv_off]; exact h.n,
    by rw [word_off, hf.word_eq (fun r h' => by have := hd (slot wx Public.aN) 8 (by omega) r h'; omega)
      (by omega), ← word_off]; exact h.inv,
    by rw [wv_off, hf.wv_eq (hd _ _ (by omega)) (by omega), ← wv_off]; exact h.one⟩

theorem WsAt.of_disj {m m' : Mem} {B : Addr} {o wx : Nat} {mx : BitVec 64} {rs : List (Nat × Nat)}
    (h : WsAt m B o wx mx) (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + 8 * 17 ≤ r.1)
    (ho : o + 8 * 17 ≤ 2 ^ 64) : WsAt m' B o wx mx :=
  h.of_words fun i hi => by
    rw [word_off, word_off]
    exact hf.word_eq (fun r h' => by rcases hr r h' with h | h <;> omega) (by omega)

theorem wvX_disj {m m' : Mem} {B : Addr} {o wx j : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) (hj : j < 8) :
    wv m' (off B o) (slot wx j) wx = wv m (off B o) (slot wx j) wx := by
  have := slot_le (w := wx) hj
  rw [wv_off, wv_off]
  exact hf.wv_eq (fun r h' => by rcases hr r h' with h | h <;> omega) (by omega)

theorem gRanges_lt (w : Nat) : ∀ r ∈ gRanges w, 8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

/-- `n`'s header words but `sD` and `sCnt` are kept by a change within `gRanges` and above. -/
theorem gRanges_hdr {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)}
    (hf : Frm B (gRanges w ++ rs) m m') (hr : ∀ r ∈ rs, hdrBytes ≤ r.1) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD)
    (h2 : i ≠ Public.sCnt) (hz : 8 * i + 8 ≤ 2 ^ 64) : word m' B (8 * i) = word m B (8 * i) :=
  hf.word_eq (fun r hr' => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · have := hdr_lt_slot w Public.aAcc hi
      have := hdr_lt_slot w Public.aTmp hi
      have := hdr_lt_slot w Public.aY hi
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
        unfold Crt.sD sFn at h1 ⊢; omega
      · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
        unfold Public.sCnt sFn at h2 ⊢; omega
    · exact Or.inl (by have := hr r hr'; unfold hdrBytes at this; omega)) hz

/-- An array of `n` but `aAcc`, `aTmp`, `aY` is kept by a change within `gRanges` and above. -/
theorem gRanges_arr {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)}
    {j : Nat} (hf : Frm B (gRanges w ++ rs) m m') (hr : ∀ r ∈ rs, slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (hj : j < 8)
    (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) (hz : slot w 8 ≤ 2 ^ 64) :
    wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  exact hf.wv_eq (fun r hr' => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
      have := slot_sep (w := w) h1
      have := slot_sep (w := w) h2
      have := slot_sep (w := w) h3
      have := hdr_lt_slot w j (show Crt.sD < 32 by decide)
      have := hdr_lt_slot w j (show Public.sCnt < 32 by decide)
      rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega
    · exact hr r hr') (by omega)

/-- `pre`'s start: `G` into `n`'s `aY` and `aX`. -/
theorem preA_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mq : BitVec 64} {N oq wq : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ oq)
    (hoq : oq + slot wq 8 + tabBytes wq ≤ Z) (hwq2 : 2 ≤ wq) (hwq : wq ≤ w)
    (hsq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wq mq)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N) :
    WP isa (seqs (Crt.gPow M.mm sWsQ ++ copyArr Public.aX Public.aY)) s fun t => Good t B Z w minv ∧
      NVals t B w minv N ∧ wv t.mem B (slot w Public.aY) w < N ∧
      wv t.mem B (slot w Public.aY) w % N = 2 ^ (64 * wq * (nChunks w wq + 1)) % N ∧
      wv t.mem B (slot w Public.aX) w = wv t.mem B (slot w Public.aY) w ∧
      Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2))]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  refine wp_seqs_append (by simp [Crt.gPow]) (by simp [copyArr]) (WP.mono (gPow_ok M hg (by omega) (by omega)
    (by omega) hN.n hN.inv hodd hN1 hN.r2 hN.one (sl := sWsQ) (by decide) hsq hwsq.hdr.hw (by
      have := (hs.sub (o := oq) (n := slot wq 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega)
      exact this) (by omega) hwq) fun s₁ ⟨hg₁, hlt₁, hG₁, f₁, k₁⟩ => ?_)
  have f₁' : Frm B (gRanges w) s.mem s₁.mem := f₁
  refine WP.mono (copyArr_ok hg₁ (by omega) (by omega) (by omega) (o := Public.aX) (a := Public.aY) (by decide)
    (by decide) (by decide)) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have sXY := slot_sep (w := w) (show Public.aX ≠ Public.aY by decide)
  have lY := slot_le (w := w) (show Public.aY < 8 by decide)
  have hY₂ : wv s₂.mem B (slot w Public.aY) w = wv s₁.mem B (slot w Public.aY) w :=
    ho₂.wv (by omega) (by omega)
  refine ⟨hg₁.of_outsideArr ho₂ k₂, (hN.of_frm (f₁'.mono fun r hr => List.mem_append_left _ hr :
    Frm B (gRanges w ++ [xRange oq wq]) s.mem s₁.mem) hlo hz (by omega)).of_outsideArr ho₂ (by decide)
    (by decide) (by decide) (by decide) (by omega) hz, by rw [hY₂]; exact hlt₁, by rw [hY₂]; exact hG₁,
    by rw [hv₂, hY₂], (f₁'.mono fun r hr => List.mem_append_left _ hr).trans
      (Frm.of_outside (ho₂.mono (o' := slot w Public.aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
        (by simp)), k₁.trans k₂ |>.mono (by simp [mmRegs])⟩

/-- `pre`'s end: `G` back into `n`'s `aY`, then `p`. -/
theorem preB_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mp : BitVec 64} {N P C op wp : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + tabBytes wp ≤ Z) (hwp2 : 2 ≤ wp) (hwp : wp ≤ w)
    (hsp : word s.mem B (8 * sWsP) = off B op) (hwsp : WsAt s.mem B op wp mp)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hP : XVals s B op wp mp P) (hP1 : 1 < P) (hPodd : P % 2 = 1)
    (hXl : wv s.mem B (slot w Public.aX) w < N)
    (hXv : wv s.mem B (slot w Public.aX) w % N = 2 ^ (64 * wp * (nChunks w wp + 1)) % N) :
    WP isa (seqs (copyArr Public.aY Public.aX ++ prepCode M.mm sWsP)) s fun t => Good t B Z w minv ∧
      NVals t B w minv N ∧ WsAt t.mem B op wp mp ∧ XVals t B op wp mp P ∧
      wv t.mem (off B op) (slot wp Public.aY) wp < P ∧
      (P ∣ N → wv t.mem (off B op) (slot wp Public.aY) wp % P = 2 ^ (64 * wp) % P) ∧
      wv t.mem (off B op) (slot wp aXc) wp < P ∧
      (P ∣ N → wv t.mem (off B op) (slot wp aXc) wp % P = C * 2 ^ (64 * wp) % P) ∧
      wv t.mem B (slot w Public.aX) w = wv s.mem B (slot w Public.aX) w ∧
      Frm B (gRanges w ++ [xRange op wp]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  refine wp_seqs_append (by simp [copyArr]) (by simp [prepCode]) (WP.mono (copyArr_ok hg (by omega) (by omega)
    (by omega) (o := Public.aY) (a := Public.aX) (by decide) (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_)
  have lY := slot_le (w := w) (show Public.aY < 8 by decide)
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have lM := slot_le (w := w) (show Public.aXm < 8 by decide)
  have sYX := slot_sep (w := w) (show Public.aY ≠ Public.aX by decide)
  have sYM := slot_sep (w := w) (show Public.aY ≠ Public.aXm by decide)
  have fo₁ : Frm B (gRanges w) s.mem s₁.mem :=
    Frm.of_outside (ho₁.mono (o' := slot w Public.aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [gRanges])
  have hr₁ : ∀ r ∈ gRanges w, r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr =>
    .inl (by have := (gRanges_lt w r hr).2; omega)
  refine WP.mono (prep_ok (C := C) M (hg.of_outsideArr ho₁ k₁) hw hw28 hlo hop hwp2 hwp (by decide) (by decide)
    (by decide) (by rw [ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aY (show sWsP < 32 by decide); omega))
      (by unfold sWsP sFn; omega)]; exact hsp)
    (hwsp.of_words fun i hi => by rw [word_off, word_off]; exact ho₁.word (Or.inr (by omega)) (by omega))
    (hN.of_outsideArr ho₁ (by decide) (by decide) (by decide) (by decide) (by omega) hz) hodd
    (by rw [ho₁.wv (by omega) (by omega)]; exact hXm)
    (hP.of_disj fo₁ hr₁ (by omega)) hP1 hPodd (by rw [hv₁]; exact hXl) (by rw [hv₁]; exact hXv))
    fun t ⟨hg', hwsp', hP', hpy, hpyv, hpx, hpxv, hN', f', k'⟩ =>
      ⟨hg', hN', hwsp', hP', hpy, hpyv, hpx, hpxv, ?_, (fo₁.mono fun r hr => List.mem_append_left _ hr).trans f',
        k₁.trans k' |>.mono (by simp [mmRegs])⟩
  rw [gRanges_arr f' (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega))
    (by decide) (by decide) (by decide) (by decide) (by omega)]
  exact ho₁.wv (by omega) (by omega)

/-- A prime's part of `pre`'s result: `R_X` in its `aY`, `x R_X` in its `aXc`. -/
structure PrimeRdy (t : State) (B : Addr) (o wx : Nat) (mx : BitVec 64) (N X C : Nat) : Prop where
  ws : WsAt t.mem B o wx mx
  x : XVals t B o wx mx X
  ylt : wv t.mem (off B o) (slot wx Public.aY) wx < X
  yv : X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X
  clt : wv t.mem (off B o) (slot wx aXc) wx < X
  cv : X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X

theorem PrimeRdy.of_disj {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {N X C : Nat}
    {rs : List (Nat × Nat)} (h : PrimeRdy s B o wx mx N X C) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) :
    PrimeRdy t B o wx mx N X C := by
  have h17 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine ⟨h.ws.of_disj hf (fun r hr' => by rcases hr r hr' with h | h <;> omega) (by omega),
    h.x.of_disj hf hr ho, ?_, fun hd => ?_, ?_, fun hd => ?_⟩
  · rw [wvX_disj hf hr ho (by decide)]; exact h.ylt
  · rw [wvX_disj hf hr ho (by decide)]; exact h.yv hd
  · rw [wvX_disj hf hr ho (by decide)]; exact h.clt
  · rw [wvX_disj hf hr ho (by decide)]; exact h.cv hd

/-- `pre`: `G` in `n`'s `aX`, and both primes ready. -/
theorem pre_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {N P Q C op wp oq : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hpq : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wp 8 + tabBytes wp ≤ Z) (hwp2 : 2 ≤ wp)
    (hwp : wp ≤ w) (hsp : word s.mem B (8 * sWsP) = off B op) (hsq : word s.mem B (8 * sWsQ) = off B oq)
    (hwsp : WsAt s.mem B op wp mp) (hwsq : WsAt s.mem B oq wp mq)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hP : XVals s B op wp mp P) (hP1 : 1 < P) (hPodd : P % 2 = 1)
    (hQ : XVals s B oq wp mq Q) (hQ1 : 1 < Q) (hQodd : Q % 2 = 1) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.CrtIfma.pre M.mm)) s fun t => Good t B Z w minv ∧ NVals t B w minv N ∧
      PrimeRdy t B op wp mp N P C ∧ PrimeRdy t B oq wp mq N Q C ∧
      wv t.mem B (slot w Public.aX) w < N ∧
      wv t.mem B (slot w Public.aX) w % N = 2 ^ (64 * wp * (nChunks w wp + 1)) % N ∧
      Frm B (preRanges w op wp oq wp) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have lM := slot_le (w := w) (show Public.aXm < 8 by decide)
  have sXM := slot_sep (w := w) (show Public.aX ≠ Public.aXm by decide)
  have hXh := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have hgl := gRanges_lt w
  rw [pre_eq, ← List.append_assoc]
  -- `G` into `aY` and `aX`.
  refine wp_seqs_append (by simp [Crt.gPow, copyArr]) (by simp [copyArr, prepCode])
    (WP.mono (preA_ok M hg hw hw28 (by omega) hoq hwp2 hwp hsq hwsq hN hodd hN1)
      fun s₁ ⟨hg₁, hN₁, hYl₁, hYv₁, hXY₁, fA, kA⟩ => ?_)
  have hA : ∀ r ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))], r.1 + r.2 ≤ slot w 8 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact (hgl r hr).2
    · rw [List.mem_singleton.mp hr]; simp only; omega
  have hAd : ∀ {o}, slot w 8 ≤ o → ∀ r ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))],
      r.1 + r.2 ≤ o ∨ o + slot wp 8 ≤ r.1 := fun ho r hr => .inl (by have := hA r hr; omega)
  have hsq₁ : word s₁.mem B (8 * sWsQ) = off B oq := by
    rw [gRanges_hdr fA (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hdrBytes]; omega) (by decide)
      (by decide) (by decide) (by unfold sWsQ sFn; omega)]; exact hsq
  have hsp₁ : word s₁.mem B (8 * sWsP) = off B op := by
    rw [gRanges_hdr fA (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hdrBytes]; omega) (by decide)
      (by decide) (by decide) (by unfold sWsP sFn; omega)]; exact hsp
  have hXm₁ : wv s₁.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N := by
    rw [gRanges_arr fA (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by decide)
      (by decide) (by decide) (by decide) (by omega)]; exact hXm
  -- `q`.
  refine wp_seqs_append (by simp [prepCode]) (by simp [copyArr, prepCode])
    (WP.mono (prep_ok (C := C) M hg₁ hw hw28 (by omega) hoq hwp2 hwp (by decide) (by decide) (by decide) hsq₁
      (hwsq.of_disj fA (fun r hr => by rcases hAd (o := oq) (by omega) r hr with h | h <;> omega) (by omega))
      hN₁ hodd hXm₁ (hQ.of_disj fA (hAd (by omega)) (by omega)) hQ1 hQodd hYl₁ hYv₁)
      fun s₂ ⟨hg₂, hwsq₂, hQ₂, hqy, hqyv, hqx, hqxv, hN₂, fQ, kQ⟩ => ?_)
  have hQd : ∀ r ∈ gRanges w ++ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (by have := (hgl r hr).2; omega)
    · rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega)
  have hsp₂ : word s₂.mem B (8 * sWsP) = off B op := by
    rw [gRanges_hdr fQ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange, hdrBytes]; omega) (by decide)
      (by decide) (by decide) (by unfold sWsP sFn; omega)]; exact hsp₁
  have hX₂ : wv s₂.mem B (slot w Public.aX) w = wv s₁.mem B (slot w Public.aX) w :=
    gRanges_arr fQ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega))
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have hXm₂ : wv s₂.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N := by
    rw [gRanges_arr fQ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega))
      (by decide) (by decide) (by decide) (by decide) (by omega)]; exact hXm₁
  have hP₁ := hP.of_disj fA (hAd (o := op) (by omega)) (by omega)
  -- `p`.
  refine WP.mono (preB_ok (C := C) M hg₂ hw hw28 hlo (by omega) hwp2 hwp hsp₂
    ((hwsp.of_disj fA (fun r hr => by rcases hAd (o := op) (by omega) r hr with h | h <;> omega) (by omega)).of_disj
      fQ (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega))
    hN₂ hodd hXm₂ (hP₁.of_disj fQ hQd (by omega)) hP1 hPodd (by rw [hX₂, hXY₁]; exact hYl₁)
    (by rw [hX₂, hXY₁]; exact hYv₁))
    fun t ⟨hgt, hNt, hwspt, hPt, hpy, hpyv, hpx, hpxv, hXt, fB, kB⟩ => ?_
  have hBd : ∀ r ∈ gRanges w ++ [xRange op wp], r.1 + r.2 ≤ oq ∨ oq + slot wp 8 ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (by have := (hgl r hr).2; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega)
  have hsub : ∀ {r : Nat × Nat} {x : Nat × Nat}, r ∈ gRanges w ++ [x] → x ∈ [(slot w Public.aX, 8 * (w + 2)),
      xRange oq wp, xRange op wp] → r ∈ preRanges w op wp oq wp := fun hr hx => by
    unfold preRanges
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ hx
  refine ⟨hgt, hNt, ⟨hwspt, hPt, hpy, hpyv, hpx, hpxv⟩,
    PrimeRdy.of_disj ⟨hwsq₂, hQ₂, hqy, hqyv, hqx, hqxv⟩ fB hBd (by omega), by rw [hXt, hX₂, hXY₁]; exact hYl₁,
    by rw [hXt, hX₂, hXY₁]; exact hYv₁, ?_, (kA.trans kQ).trans kB |>.mono (by simp [mmRegs])⟩
  exact ((fA.mono fun r hr => hsub hr (by simp)).trans (fQ.mono fun r hr => hsub hr (by simp))).trans
    (fB.mono fun r hr => hsub hr (by simp))

end VG.Proof.Bignum.X86_64
