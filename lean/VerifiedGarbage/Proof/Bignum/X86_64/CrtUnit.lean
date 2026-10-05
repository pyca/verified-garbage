import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry

/-!
# RSA with the CRT on x86-64: `R_X mod X`

The start of each prime's phase (`unitPhase_ok`): `G = 2^E mod n` in the
modulus' workspace, reduced into the prime's (`G R_X^(-K) ≡ R_X (mod X)` if
`X` divides `n`), as its `Y`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What code in a prime's workspace may change, at `B`: all but its link,
`w_X`, `-X⁻¹` and its arrays' bases. -/
def xRange (o wx : Nat) : Nat × Nat := (o + 8 * 17, VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx - 8 * 17)

theorem Frm.to_x {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (VG.Proof.Bignum.X86_64.off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8) (ho : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  refine (h.rebase (by omega) fun r hr' => by have := hr r hr'; omega).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange]
  omega

/-- `Frm.to_x` for changes that reach the table. -/
theorem Frm.to_xT {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (VG.Proof.Bignum.X86_64.off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx) (ho : o + (VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx) ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  refine (h.rebase (by omega) fun r hr' => by have := hr r hr'; omega).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange]
  omega

theorem Outside.to_x {B : Addr} {o wx j : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) (8 * (wx + 2)) m m')
    (hj : j < 8) (ho : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64) {rs' : List (Nat × Nat)} (hx : xRange o wx ∈ rs') :
    Frm B rs' m m' :=
  Frm.to_x (rs := [(VG.Proof.Bignum.X86_64.slot wx j, 8 * (wx + 2))]) (Frm.of_outside h (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) hj
    have := hdr_lt_slot wx j (show 31 < 32 by decide)
    simp only; omega) ho hx

/-- The words of the modulus' header and arrays, below `o`, past code in
the prime's workspace. -/
theorem Frm.x_below {B : Addr} {o wx : Nat} {m m' : Mem} (h : Frm B [xRange o wx] m m') {d : Nat}
    (hd : d + 8 ≤ o) (ho : o < 2 ^ 64) : VG.Proof.Bignum.X86_64.word m' B d = VG.Proof.Bignum.X86_64.word m B d :=
  h.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) (by omega)

theorem sMaskX_redc (wx : Nat) : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := by
  intro r hr
  simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  have := hdr_lt_slot wx aT (show 31 < 32 by decide)
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn] <;> omega

/-- The modulus `N` in its workspace, `-N⁻¹`, `R² mod N` and the number 1. -/
structure NVals (t : State) (B : Addr) (w : Nat) (minv : BitVec 64) (N : Nat) : Prop where
  n : wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w = N
  inv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  r2 : wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  r2lt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aR2) w < N
  one : wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aOne) w = 1

theorem XVals.of_below {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (h : XVals s B o wx mx X) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o)
    (ho : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  have hN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  exact ⟨by rw [wv_off, hf.wv_eq (fun r h' => Or.inr (by have := hr r h'; omega)) (by omega), ← wv_off]; exact h.n,
    by rw [word_off, hf.word_eq (fun r h' => Or.inr (by have := hr r h'; omega)) (by omega), ← word_off]; exact h.inv,
    by rw [wv_off, hf.wv_eq (fun r h' => Or.inr (by have := hr r h'; omega)) (by omega), ← wv_off]; exact h.one⟩

theorem XVals.of_outside {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X j n : Nat}
    (h : XVals s B o wx mx X) (ho : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) n s.mem t.mem) (hj : j < 8)
    (h1 : j ≠ Public.aN) (h2 : j ≠ Public.aOne) (hn : n ≤ 8 * (wx + 2))
    (hz : (VG.Proof.Bignum.X86_64.off B o).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have := slot_le (w := wx) hj
  exact ⟨by rw [ho.wv (by omega) (by omega)]; exact h.n, by rw [ho.word (by omega) (by omega)]; exact h.inv,
    by rw [ho.wv (by omega) (by omega)]; exact h.one⟩

/-- `K = ⌈w / w_X⌉`. -/
abbrev nChunks (w wx : Nat) : Nat := (w + wx - 1) / wx

/-- The start of a prime's phase: `G = 2^(64 w_X (K + 1)) mod N` into the
modulus' `Y`, reduced into the prime's `Y`: `R_X mod X` if `X` divides `N`. -/
theorem unitPhase_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o)
    (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32) (hsl1 : sl ≠ Crt.sD)
    (hsl2 : sl ≠ Public.sCnt) (hslv : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = VG.Proof.Bignum.X86_64.off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N) (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hXodd : X % 2 = 1) :
    WP isa (seqs (Crt.gPow M.mm sl ++ ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
        redc M.mm Public.aY ++ copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))) s fun t =>
      Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w < N ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w % N = 2 ^ (64 * wx * (nChunks w wx + 1)) % N ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X ∧
      (X ∣ N → wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) ∧
      Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  have hgr : ∀ r ∈ gRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
    have := slot_le (w := w) (show Public.aAcc < 8 by decide)
    have := slot_le (w := w) (show Public.aTmp < 8 by decide)
    have := slot_le (w := w) (show Public.aY < 8 by decide)
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega
  simp only [List.append_assoc]
  -- `G`.
  refine wp_seqs_append (by simp [Crt.gPow]) (by simp) ?_
  refine WP.mono (gPow_ok M hg (by omega) (by omega) (by omega) hN.n hN.inv hodd hN1 hN.r2 hN.one hsl hslv
    hws.hdr.hw (by
      have := (hs.sub (o := o) (n := VG.Proof.Bignum.X86_64.slot wx 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega)
      exact this) (by omega) hwx) fun s₁ ⟨hg₁, hlt₁, hG₁, f₁, k₁⟩ => ?_
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) :=
    fun i hi h1 h2 => f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot w Public.aAcc (show i < 32 from hi)
      have := hdr_lt_slot w Public.aTmp (show i < 32 from hi)
      have := hdr_lt_slot w Public.aY (show i < 32 from hi)
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
        unfold Crt.sD sFn at h1 ⊢; omega
      · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
        unfold Public.sCnt sFn at h2 ⊢; omega) (by omega)
  have hxw₁ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact f₁.word_eq (fun r hr => Or.inr (by have := hgr r hr; omega)) (by omega)
  -- Into the prime's workspace.
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B o ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * sl) (by omega),
      hb₁ sl hsl hsl1 hsl2, hslv]) rfl) fun s₂ ⟨⟨hdi₂, hm₂⟩, k₂⟩ => ?_
  have k02 := k₁.trans k₂
  have hws₂ : WsAt s₂.mem B o wx mx := hws.of_words fun i hi => by rw [hm₂]; exact hxw₁ i (by omega)
  have hc₂ : SubCtx s₂ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k02.2.2) (by rw [hm₂]; exact hg₁.hdr) hws₂ hdi₂ hlo hhi
  have hX₂ : XVals s₂ B o wx mx X := hX.of_below (by rw [hm₂]; exact f₁) (fun r hr => (hgr r hr).trans hlo) hoL
  -- `A R^K ≡ G (mod X)`.
  refine wp_seqs_append (by simp [redc]) (by simp [copyArr]) ?_
  refine WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide))
    fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, f₃, k₃⟩ => ?_
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hc₃.good (Nat.le_refl _) (by omega) (by omega) (o := Public.aY) (a := aXc)
    (by decide) (by decide) (by decide)) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  have hc₄ := hc₃.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot wx Public.aY, 8 * wx)]) (Frm.of_outside ho₄ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
    simp only; omega) k₄.2.2 (k₄.gpr (by decide))
  -- Back to the modulus'.
  have hl₄ : InRegions (s₄.rd ++ s₄.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sLink)) 8 :=
    hc₄.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₄.mem)
    (by xrun [leave, State.ea, hdr, hc₄.rdi, hdrOff, hl₄, hc₄.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have f34 : Frm B [xRange o wx] s₂.mem t.mem := by
    rw [hm]
    exact (f₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)).trans
      (ho₄.mono (o' := VG.Proof.Bignum.X86_64.slot wx Public.aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega) |>.to_x
        (by decide) hoL (List.mem_singleton_self _))
  have hb : ∀ d, d + 8 ≤ o → VG.Proof.Bignum.X86_64.word t.mem B d = VG.Proof.Bignum.X86_64.word s₂.mem B d := fun d hd => f34.x_below hd ho64
  have hbw : ∀ d k, d + 8 * k ≤ o → wv t.mem B d k = wv s₂.mem B d k := fun d k hd =>
    wv_congr fun i hi => hb _ (by omega)
  have kall := ((k02.trans k₃).trans k₄).trans k'
  have hY : wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx = wv s₃.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx := by rw [hm, hv₄]
  have hXc : wv s₃.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx * (2 ^ (64 * wx)) ^ nChunks w wx % X =
      wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w % X := by
    rw [← Nat.pow_mul]; exact hv₃
  have hYn : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w := by rw [hm₂]
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, ?_, ?_, ?_, ?_, by rw [hY]; exact hlt₃, fun hdvd => ?_, ?_, ?_,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · have hH := hg₁.hdr
    exact ⟨(hb _ (by unfold sW; omega)).trans (by rw [hm₂]; exact hH.hw),
      (hb _ (by unfold sMinv; omega)).trans (by rw [hm₂]; exact hH.hminv),
      fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (by rw [hm₂]; exact hH.harr j hj)⟩
  · rw [hm]; exact hc₄.ws
  · exact hX₃.of_outside (by rw [hm]; exact ho₄) (by decide) (by decide) (by decide) (by omega)
      (by have := hc₃.good.scr.nowrap; omega)
  · rw [hbw _ _ (by have := slot_le (w := w) (show Public.aY < 8 by decide); omega), hYn]; exact hlt₁
  · rw [hbw _ _ (by have := slot_le (w := w) (show Public.aY < 8 by decide); omega), hYn]; exact hG₁
  · rw [hY]
    have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
    have e : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w % X = 1 * (2 ^ (64 * wx)) ^ (nChunks w wx + 1) % X := by
      rw [hYn, ← Nat.mod_mod_of_dvd _ hdvd, hG₁, Nat.mod_mod_of_dvd _ hdvd, Nat.one_mul, ← Nat.pow_mul]
    have := VG.Proof.Bignum.redc_cancel hR (hXc.trans e)
    rwa [Nat.one_mul] at this
  · have := hdr_lt_slot wx Public.aY (show sMaskX < 32 by decide)
    rw [hm, ho₄.word (Or.inl (by omega)) (by unfold sMaskX sFn; omega),
      f₃.word_eq (sMaskX_redc wx) (by unfold sMaskX sFn; omega), hm₂]
    exact hxw₁ _ (by decide)
  · have f₁' : Frm B (gRanges w) s.mem s₂.mem := by rw [hm₂]; exact f₁
    exact f₁'.append f34
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64
