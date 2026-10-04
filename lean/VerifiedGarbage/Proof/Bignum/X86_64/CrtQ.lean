import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow

/-!
# RSA with the CRT on x86-64: `q`'s phase

`qPhase`: `m_q = c^dQ mod q` into `q`'s `Y` (`qPhase_ok`), if `q` divides
`n` and the modulus' `X_m ≡ c R`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The start of a prime's phase (`unitPhase_ok`). -/
def unitSteps (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) : List (Prog isa) :=
  Crt.gPow mul sl ++ [.block [.mov .rdi (.mem (hdr sl))]] ++ redc mul Public.aY ++ copyArr Public.aY aXc ++
    [.block [leave]]

/-- The power in a prime's phase (`powPhase_ok`). -/
def powSteps (mul : Nat → Nat → Nat → Prog isa) (sl sd slen : Nat) : List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr sl))]] ++ redc mul Public.aY ++ Crt.expLoop mul sd slen

theorem qPhase_eq (mul : Nat → Nat → Nat → Prog isa) : qPhase mul =
    unitSteps mul sWsQ ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps mul sWsQ sDq sQlen ++ [mul Public.aY Public.aY Public.aOne, .block [leave]])) := by
  simp only [qPhase, unitSteps, powSteps, enterQ, List.append_assoc, List.cons_append, List.nil_append]

/-- A Montgomery multiplication in the modulus' workspace that changes only
`Y`, the accumulator and the temporary. -/
theorem mmY_ok (M : Mont) {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8)
    (d3 : a ≠ Public.aAcc) (d6 : a ≠ Public.aTmp) (hN : NVals t B w minv N)
    (hB : wv t.mem B (slot w Public.aY) w < N) :
    WP isa (M.mm Public.aY a Public.aY) t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (slot w Public.aY) w < N ∧
      wv t'.mem B (slot w Public.aY) w * 2 ^ (64 * w) % N =
        wv t.mem B (slot w a) w * wv t.mem B (slot w Public.aY) w % N ∧
      Frm B (gRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  refine WP.mono (mmN_ok M hg hZ hw hw' (by decide) ha (by decide) (by decide) (by decide) d3 (by decide)
    (by decide) hN.n hN.inv hB d6) fun t' ⟨hg', _, _, hlt, hm, ha', k⟩ => ⟨hg', hlt, hm, ?_, k⟩
  exact Frm.of_arrays ha' fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [gRanges]

/-- The modulus' arrays but `Y`, the accumulator and the temporary are kept
by a change within `gRanges` and a prime's workspace. -/
theorem Frm.gx_wv {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (gRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  refine hf.wv_eq (fun r hr => ?_) (by omega)
  simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem NVals.of_frm {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N o wx : Nat}
    (h : NVals s B w minv N) (hf : Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem) (hlo : slot w 8 ≤ o)
    (hz : B.toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) : NVals t B w minv N := by
  have hr : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ Public.aY →
      ∀ r ∈ gRanges w ++ [xRange o wx], slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj h1 h2 h3 r hr
    have := slot_le (w := w) hj
    have := hdr_lt_slot w j (show 31 < 32 by decide)
    have s1 := slot_sep (w := w) h1
    have s2 := slot_sep (w := w) h2
    have s3 := slot_sep (w := w) h3
    simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega
  have lN := slot_le (w := w) (show Public.aN < 8 by decide)
  have lR := slot_le (w := w) (show Public.aR2 < 8 by decide)
  have lO := slot_le (w := w) (show Public.aOne < 8 by decide)
  have rN := hr Public.aN (by decide) (by decide) (by decide) (by decide)
  have rR := hr Public.aR2 (by decide) (by decide) (by decide) (by decide)
  have rO := hr Public.aOne (by decide) (by decide) (by decide) (by decide)
  exact ⟨by rw [hf.wv_eq (fun r h' => rN r h') (by omega)]; exact h.n,
    by rw [hf.word_eq (fun r h' => by have := rN r h'; omega) (by omega)]; exact h.inv,
    by rw [hf.wv_eq (fun r h' => rR r h') (by omega)]; exact h.r2,
    by rw [hf.wv_eq (fun r h' => rR r h') (by omega)]; exact h.r2lt,
    by rw [hf.wv_eq (fun r h' => rO r h') (by omega)]; exact h.one⟩

/-- `q`'s phase: `m_q = c^dQ mod q` into `q`'s `Y`, if `q` divides `N` and
`X_m ≡ c R (mod N)`. -/
theorem qPhase_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C o wx : Nat}
    {ep : Addr} {eb : List Byte}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsQ) = off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hep : word s.mem B (8 * sDq) = ep) (hel : word s.mem B (8 * sQlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (qPhase M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = C ^ Spec.Rsa.os2ip eb % X) ∧
      Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hgr : ∀ r ∈ gRanges w ++ [xRange o wx], 8 * 22 ≤ r.1 := by
    have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
    intro r hr
    simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega
  -- The words of the modulus' header that the phase's parts keep.
  have hhd : ∀ {m m' : Mem}, Frm B (gRanges w ++ [xRange o wx]) m m' → ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt →
      word m' B (8 * i) = word m B (8 * i) := fun hf i hi h1 h2 => hf.word_eq (fun r hr => by
    have := hgr r hr
    have := hdr_lt_slot w Public.aAcc (show i < 32 from hi)
    simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by omega)
    · exact Or.inl (by have := hdr_lt_slot w Public.aTmp (show i < 32 from hi); omega)
    · exact Or.inl (by have := hdr_lt_slot w Public.aY (show i < 32 from hi); omega)
    · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
      unfold Crt.sD sFn at h1 ⊢; omega
    · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
      unfold Public.sCnt sFn at h2 ⊢; omega
    · exact Or.inl (by omega)) (by omega)
  rw [qPhase_eq]
  -- `R_q mod q`.
  refine wp_seqs_append (by simp [unitSteps]) (by simp) ?_
  refine WP.mono (unitPhase_ok M hg hw hw28 hlo hhi hwx2 hwx (by decide) (by decide) (by decide) hslv hws hN
    hodd hN1 hX hX1 hXodd) fun s₁ ⟨hg₁, hws₁, hX₁, hlt₁, hG₁, hlq₁, hyq₁, _, f₁, k₁⟩ => ?_
  have hN₁ := hN.of_frm f₁ hlo hz (by omega)
  have hXm₁ : wv s₁.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    f₁.gx_wv hlo hz (by decide) (by decide) (by decide) (by decide)
  -- `c G mod N`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (mmY_ok M hg₁ (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
    (by decide) hN₁ hlt₁) fun s₂ ⟨hg₂, hlt₂, hm₂, f₂, k₂⟩ => ?_
  have f₂' : Frm B (gRanges w ++ [xRange o wx]) s₁.mem s₂.mem :=
    Frm.mono f₂ fun r hr => List.mem_append_left _ hr
  have hN₂ := hN₁.of_frm f₂' hlo hz (by omega)
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hcg : wv s₂.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₂, Nat.mul_mod, hXm₁, hXm, hG₁, ← Nat.mul_mod]
    congr 1
    ac_rfl
  have hxo : ∀ i < 32, word s₂.mem (off B o) (8 * i) = word s₁.mem (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact f₂.word_eq (fun r hr => Or.inr (by
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := w) (show Public.aAcc < 8 by decide)
      have := slot_le (w := w) (show Public.aTmp < 8 by decide)
      have := slot_le (w := w) (show Public.aY < 8 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega)) (by omega)
  have f02 : Frm B (gRanges w ++ [xRange o wx]) s.mem s₂.mem := f₁.trans f₂'
  have hb₂ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word s₂.mem B (8 * i) = word s.mem B (8 * i) :=
    hhd f02
  have i02 : InScr B Z s.mem s₂.mem := InScr.of_frm f02 fun r hr => by
    simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    have := slot_le (w := w) (show Public.aAcc < 8 by decide)
    have := slot_le (w := w) (show Public.aTmp < 8 by decide)
    have := slot_le (w := w) (show Public.aY < 8 by decide)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega
  have hYq₂ : wv s₂.mem (off B o) (slot wx Public.aY) wx = wv s₁.mem (off B o) (slot wx Public.aY) wx := by
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]
    exact f₂.wv_eq (fun r hr => Or.inr (by
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := w) (show Public.aAcc < 8 by decide)
      have := slot_le (w := w) (show Public.aTmp < 8 by decide)
      have := slot_le (w := w) (show Public.aY < 8 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega)) (by omega)
  -- `c^dQ R_q mod q`.
  refine wp_seqs_append (by simp [powSteps]) (by simp) ?_
  refine WP.mono (powPhase_ok M hg₂ hw28 hlo hhi hwx2 hwx (sl := sWsQ) (by decide)
    (by rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hslv) (hws₁.of_words fun i hi => hxo i (by omega))
    (hX₁.of_below f₂ (fun r hr => by
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := w) (show Public.aAcc < 8 by decide)
      have := slot_le (w := w) (show Public.aTmp < 8 by decide)
      have := slot_le (w := w) (show Public.aY < 8 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega) hoL)
    hX1 hXodd hcg (by rw [hYq₂]; exact hlq₁) (fun hd => by rw [hYq₂]; exact hyq₁ hd) (sd := sDq) (slen := sQlen)
    (by decide) (by decide) (by rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hep)
    (by rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hel) hL1 hL2 (he.congrK i02 (k₁.trans k₂)))
    fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, _, fx₃, k₃⟩ => ?_
  -- `m_q = (c^dQ R_q) R_q⁻¹`.
  have hz₃ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₃.good.scr.nowrap; omega
  refine WP.seq (WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aOne) hc₃.good (Nat.le_refl _)
    hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₃.inv
    (by rw [hX₃.one, hX₃.n]; exact hX1)) fun s₄ ⟨hg₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hX₃.n] at hlt₄ hm₄
  rw [hX₃.one, Nat.mul_one] at hm₄
  have f₄ : Frm (off B o) (redcRanges wx ++ [(slot wx Public.aY, 8 * (wx + 2))]) s₃.mem s₄.mem :=
    Frm.of_arrays ha₄ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp [redcRanges]
  have hr₄ : ∀ r ∈ redcRanges wx ++ [(slot wx Public.aY, 8 * (wx + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact redcRanges_ok wx r hr
    · rw [List.mem_singleton.mp hr]
      have := slot_le (w := wx) (show Public.aY < 8 by decide)
      have := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
      simp only; omega
  have hc₄ := hc₃.of_frm f₄ hr₄ k₄.2.2 (k₄.gpr (by decide))
  have hX₄ : XVals s₄ B o wx mx X := by
    have rN := redcRanges_arr wx (j := Public.aN) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have rO := redcRanges_arr wx (j := Public.aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aN < 8 by decide)
    have := slot_le (w := wx) (show Public.aOne < 8 by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have sN := slot_sep (w := wx) (show Public.aN ≠ Public.aY by decide)
    have sO := slot_sep (w := wx) (show Public.aOne ≠ Public.aY by decide)
    have hd : ∀ j, j = Public.aN ∨ j = Public.aOne → ∀ r ∈ redcRanges wx ++ [(slot wx Public.aY, 8 * (wx + 2))],
        slot wx j + 8 * wx ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
      rintro j (rfl | rfl) r hr <;> rcases List.mem_append.mp hr with hr | hr
      · have := rN r hr; omega
      · rw [List.mem_singleton.mp hr]; simp only; omega
      · have := rO r hr; omega
      · rw [List.mem_singleton.mp hr]; simp only; omega
    exact ⟨by rw [f₄.wv_eq (hd _ (Or.inl rfl)) (by omega)]; exact hX₃.n,
      by rw [f₄.word_eq (fun r hr => by have := hd _ (Or.inl rfl) r hr; omega) (by omega)]; exact hX₃.inv,
      by rw [f₄.wv_eq (hd _ (Or.inr rfl)) (by omega)]; exact hX₃.one⟩
  -- Back to the modulus'.
  have hl₄ : InRegions (s₄.rd ++ s₄.wr) (off (off B o) (8 * sLink)) 8 :=
    hc₄.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₄.mem)
    (by xrun [leave, State.ea, hdr, hc₄.rdi, hdrOff, hl₄, hc₄.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have fx₄ : Frm B [xRange o wx] s₂.mem t.mem := by
    rw [hm]; exact fx₃.trans (f₄.to_x hr₄ hoL (List.mem_singleton_self _))
  have kall := (((k₁.trans k₂).trans k₃).trans k₄).trans k'
  have hb : ∀ d, d + 8 ≤ o → word t.mem B d = word s₂.mem B d := fun d hd => fx₄.x_below hd ho64
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, by rw [hm]; exact hc₄.ws, ⟨by rw [hm]; exact hX₄.n,
    by rw [hm]; exact hX₄.inv, by rw [hm]; exact hX₄.one⟩, by rw [hm]; exact hlt₄, fun hd => ?_,
    f02.trans (fx₄.mono fun r hr => List.mem_append_right _ hr), ⟨fun r hr => ?_, kall.2⟩⟩
  · have hH := hg₂.hdr
    exact ⟨(hb _ (by unfold sW; omega)).trans hH.hw, (hb _ (by unfold sMinv; omega)).trans hH.hminv,
      fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH.harr j hj)⟩
  · rw [hm]
    have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
    exact VG.Proof.Bignum.mont_cancel hR (by rw [hm₄, hv₃ hd])
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64
