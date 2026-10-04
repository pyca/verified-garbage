import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix

/-!
# RSA with the CRT on x86-64: `p`'s phase

`pPhase`: `m_p = c^dP mod p` as `pPhase`'s `qPhase` computes `m_q`, then
`m_q R_p mod p` (from `m_q G mod n`, `mqPart_ok`), and
`h = (m_p - m_q) qInv mod p` into `p`'s `Y` (`hPart_ok`, `pPhase_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `m_q G mod n` into the modulus' `X`. -/
def mqSteps (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [zeroArr Public.aX,
  .block [.mov .rax (.mem (hdr sWsQ)), .mov .rsi (.mem (ws .rax (sArr Public.aY))), .mov .r12 (.mem (ws .rax sW)),
    .mov .rbx (.mem (hdr (sArr Public.aX)))],
  copyWords, mul Public.aX Public.aX Public.aR2, mul Public.aX Public.aX Public.aY]

/-- `h = (m_p - m_q) qInv mod p` into `p`'s `Y`. -/
def hSteps (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr sWsP))]] ++ redc mul Public.aX ++ subModArr aT Public.aY aXc ++
    loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul Public.aY aT aChunk, .block [leave]]

theorem pPhase_eq (mul : Nat → Nat → Nat → Prog isa) : pPhase mul =
    unitSteps mul sWsP ++ (mqSteps mul ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps mul sWsP sDp sPlen ++ (([.block [leave]] : List (Prog isa)) ++ hSteps mul)))) := by
  simp only [pPhase, unitSteps, powSteps, mqSteps, hSteps, enterP, List.append_assoc, List.cons_append,
    List.nil_append]

/-- `m_q`, `q`'s `Y`, times `G` (the modulus' `Y`) modulo `N` into the
modulus' `X`. -/
theorem mqPart_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mq : BitVec 64} {N G oq wq : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N) (hodd : N % 2 = 1)
    (hYl : wv s.mem B (slot w Public.aY) w < N) (hY : wv s.mem B (slot w Public.aY) w % N = G % N)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hws : WsAt s.mem B oq wq mq) (hlo : slot w 8 ≤ oq)
    (hhi : oq + slot wq 8 + tabBytes wq ≤ Z) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs (mqSteps M.mm)) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w Public.aX) w < N ∧
      wv t.mem B (slot w Public.aX) w % N = wv s.mem (off B oq) (slot wq Public.aY) wq * G % N ∧
      wv t.mem B (slot w Public.aY) w = wv s.mem B (slot w Public.aY) w ∧
      Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2))]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have hX0 := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have hY8 := slot_le (w := wq) (show Public.aY < 8 by decide)
  have hq8 : 8 * 32 ≤ slot wq 8 := by unfold slot hdrBytes; omega
  have hqo : oq < 2 ^ 64 := by omega
  simp only [mqSteps, seqs]
  -- `X := 0`.
  refine WP.seq (WP.mono (zeroArr_ok hg (by omega) (by omega) (by omega) (show Public.aX < 8 by decide))
    fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega)) (by omega)
  have hq₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega)) hd'
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hsq : Scr s₁ (off B oq) (slot wq 8) := hs₁.sub (by omega) (by omega)
  have hqw : ∀ i < 32, word s₁.mem (off B oq) (8 * i) = word s.mem (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hq₁ _ (by omega) (by omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t => t.gpr .rsi = off (off B oq) (slot wq Public.aY) ∧
      t.gpr .r12 = BitVec.ofNat 64 wq ∧ t.gpr .rbx = off B (slot w Public.aX) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, ws, hdi₁, hdrOff, hs₁.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega),
      hb₁ sWsQ (by decide), hq, hsq.ld (d := 8 * sArr Public.aY) (by unfold sArr Public.aY; omega),
      hqw (sArr Public.aY) (by decide), hws.hdr.harr Public.aY (by decide),
      hsq.ld (d := 8 * sW) (by unfold sW; omega), hqw sW (by decide), hws.hdr.hw,
      hs₁.ld (d := 8 * sArr Public.aX) (by unfold sArr Public.aX; omega), hb₁ (sArr Public.aX) (by decide),
      hg.hdr.harr Public.aX (by decide)]) rfl) fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hsq₂ := hsq.congr k₂.2.2
  -- `X := m_q`.
  refine WP.seq (WP.mono (copyWords_ok (S := off B oq) (eS := slot wq Public.aY) (D := B) (eD := slot w Public.aX)
    (w := wq) hsi₂ hbx₂ h12₂ hwq (by omega) (by omega) (fun j hj => hsq₂.ld (by omega))
    (fun j hj => hs₂.st (by omega)) (fun j hj b hb => Or.inr (by
      rw [off_off, ofs_off B (by omega)]; omega))) fun s₃ ⟨hv₃, _, ho₃, k₃⟩ => ?_)
  have hX₃ : wv s₃.mem B (slot w Public.aX) w = wv s.mem (off B oq) (slot wq Public.aY) wq := by
    have hz : wv s₃.mem B (slot w Public.aX + 8 * wq) (w - wq) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
        rw [ho₃.word (by omega) (by omega), hm₂, show slot w Public.aX + 8 * wq + 8 * q =
          slot w Public.aX + 8 * (wq + q) by omega]
        exact (wv_eq_zero_iff _ _ _ _).mp hz₁ _ (by omega)
    rw [wv_split _ _ _ (show wq + (w - wq) = w by omega), hv₃, hz, Nat.mul_zero, Nat.add_zero, wv_off, wv_off, hm₂]
    exact wv_congr fun i hi => hq₁ _ (by omega) (by omega)
  have hn₃ : ∀ j < 8, j ≠ Public.aX → wv s₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj hjx => by
    have := slot_sep (w := w) hjx
    have := slot_le (w := w) hj
    rw [ho₃.wv (by omega) (by omega), hm₂, ho₁.wv (by omega) (by omega)]
  have hg₃ : Good s₃ B Z w minv := ⟨hs.congr ((k₁.trans k₂).trans k₃).2.2,
    ((k₂.trans k₃).gpr (by decide)).trans hdi₁, by
      have : ∀ i < 32, word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
        rw [ho₃.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega)) (by omega), hm₂, hb₁ i hi]
      exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
        fun j hj => (this _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩
  have hN₃ : NVals s₃ B w minv N := by
    have hw0 : word s₃.mem B (slot w Public.aN) = word s.mem B (slot w Public.aN) := by
      have := slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
      have := slot_le (w := w) (show Public.aN < 8 by decide)
      rw [ho₃.word (by omega) (by omega), hm₂, ho₁.word (by omega) (by omega)]
    exact ⟨(hn₃ _ (by decide) (by decide)).trans hN.n, by rw [hw0]; exact hN.inv,
      by rw [hn₃ _ (by decide) (by decide)]; exact hN.r2, by rw [hn₃ _ (by decide) (by decide)]; exact hN.r2lt,
      (hn₃ _ (by decide) (by decide)).trans hN.one⟩
  -- `X := m_q R`, then `m_q G`.
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  refine WP.seq (WP.mono (mmN_ok M hg₃ (by omega) (by omega) (by omega) (o := Public.aX) (a := Public.aX)
    (b := Public.aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hN₃.n hN₃.inv hN₃.r2lt) fun s₄ ⟨hg₄, hn₄, hi₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  have hY₄ : wv s₄.mem B (slot w Public.aY) w = wv s.mem B (slot w Public.aY) w := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) hz]; exact hn₃ _ (by decide) (by decide)
  refine WP.mono (mmN_ok M hg₄ (by omega) (by omega) (by omega) (o := Public.aX) (a := Public.aX)
    (b := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hn₄ hi₄ (by rw [hY₄]; exact hYl)) fun t ⟨hg', _, _, hlt', hm', ha', k'⟩ => ?_
  refine ⟨hg', hlt', ?_, by rw [ha'.wv_of_not_mem (by decide) (by decide) hz]; exact hY₄, ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · -- `X' R ≡ X G ≡ m_q R G`.
    have e₄ : wv s₄.mem B (slot w Public.aX) w % N = wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * w) % N := by
      apply VG.Proof.Bignum.mont_cancel hR
      rw [hm₄, hX₃, Nat.mul_mod, hN₃.r2, ← Nat.mul_mod, Nat.mul_assoc]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm', Nat.mul_mod, e₄, hY₄, hY, ← Nat.mul_mod]
    congr 1; ac_rfl
  · have hx : (slot w Public.aX, 8 * (w + 2)) ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))] := by simp
    have ha : ∀ j ∈ [Public.aAcc, Public.aTmp, Public.aX], (slot w j, 8 * (w + 2)) ∈
        gRanges w ++ [(slot w Public.aX, 8 * (w + 2))] := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp [gRanges]
    have f₃ : Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2))]) s₂.mem s₃.mem :=
      Frm.of_outside (ho₃.mono (o' := slot w Public.aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) hx
    rw [hm₂] at f₃
    exact (((Frm.of_outside ho₁ hx).trans f₃).trans (Frm.of_arrays ha₄ ha)).trans (Frm.of_arrays ha' ha)

/-- The end of `h`: from `m_p R_p` in `p`'s `Y` and `m_q R_p` in its `X_c`,
`h = (m_p - m_q) qInv R_p⁻¹ R_p` into `p`'s `Y`, `qInv` masked by `c`. -/
theorem hTail_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hc : SubCtx s B Z o w wx mx) (hX : XVals s B o wx mx X) (hw28 : w < 2 ^ 28) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X) (hlt : wv s.mem (off B o) (slot wx aXc) wx < X)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    WP isa (seqs (subModArr aT Public.aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++
        [M.mm Public.aY aT aChunk])) s fun t => SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (c = true → wv t.mem (off B o) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X =
        (wv s.mem (off B o) (slot wx Public.aY) wx + X - wv s.mem (off B o) (slot wx aXc) wx) % X *
          Spec.Rsa.os2ip qib % X) ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Keep mmRegs s t ∧ t.gpr .rdi = s.gpr .rdi := by
  have hn := hc.good.scr.nowrap
  have hhi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by have := hc.scr.nowrap; omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by have := hc.scr.nowrap; omega
  simp only [List.append_assoc]
  -- `T = (m_p - m_q) R_p mod p`.
  refine wp_seqs_append (by simp [subModArr]) (by simp [loadArr]) ?_
  refine WP.mono (subModArr_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hwx2 (by omega)
    (o := aT) (a := Public.aY) (b := aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX.n]; exact hyl) (by rw [hX.n]; exact hlt))
    fun s₃ ⟨hT₃, ha₃, k₃⟩ => ?_
  rw [hX.n] at hT₃
  obtain ⟨hc₃, hX₃, fx₃⟩ := hc.of_arrays hX ha₃ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> decide) k₃.2.2 (k₃.gpr (by decide)) (by omega)
  have hb₃ : ∀ d, d + 8 ≤ o → word s₃.mem B d = word s.mem B d := fun d hd => fx₃.x_below hd ho64
  have i03 : InScr B Z s.mem s₃.mem :=
    InScr.of_frm fx₃ fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hM₃ : word s₃.mem (off B o) (8 * sMaskX) = mask c := by
    rw [ha₃.hslot (by decide)]; exact hmask
  -- `qInv`, masked.
  refine wp_seqs_append (by simp [loadArr]) (by simp [maskArr]) ?_
  refine WP.mono (primeLoad_ok hc₃ hwx2 hwx (by omega) (j := aChunk) (by decide) (sp := sQinv) (sl := sPlen)
    (by decide) (by decide) (by rw [hb₃ _ (by unfold sQinv sFn; omega)]; exact hqp)
    (by rw [hb₃ _ (by unfold sPlen sFn; omega)]; exact hql) (hqs.congrK i03 k₃) hq1 hq2 hqw)
    fun s₄ ⟨hc₄, hq₄, ho₄, k₄⟩ => ?_
  have hz₄ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₄.good.scr.nowrap; omega
  have hX₄ := hX₃.of_outside ho₄ (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  have fx₄ : Frm B [xRange o wx] s₃.mem s₄.mem := ho₄.to_x (by decide) hoL (List.mem_singleton_self _)
  have hM₄ : word s₄.mem (off B o) (8 * sMaskX) = mask c := by
    rw [ho₄.word (Or.inl (by have := hdr_lt_slot wx aChunk (show sMaskX < 32 by decide); omega))
      (by unfold sMaskX sFn; omega)]; exact hM₃
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (maskArr_ok hc₄.good (Nat.le_refl _) (by omega) (by omega) (j := aChunk) (by decide) hM₄)
    fun s₅ ⟨_, hq₅, ho₅, k₅⟩ => ?_
  have ho₅' : Outside (off B o) (slot wx aChunk) (8 * (wx + 2)) s₄.mem s₅.mem :=
    ho₅.mono (Nat.le_refl _) (by omega)
  have hc₅ := hc₄.of_frm (rs := [(slot wx aChunk, 8 * (wx + 2))]) (Frm.of_outside ho₅' (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show aChunk < 8 by decide)
    have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
    simp only; omega) k₅.2.2 (k₅.gpr (by decide))
  have hX₅ := hX₄.of_outside ho₅' (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  have fx₅ : Frm B [xRange o wx] s₄.mem s₅.mem := ho₅'.to_x (by decide) hoL (List.mem_singleton_self _)
  have hch : wv s₅.mem (off B o) (slot wx aChunk) wx < X := by
    rw [hq₅, hq₄]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [↓reduceIte]; exact hqi rfl
  have hT₅ : wv s₅.mem (off B o) (slot wx aT) wx = wv s₃.mem (off B o) (slot wx aT) wx := by
    have := slot_sep (w := wx) (show aT ≠ aChunk by decide)
    have := slot_le (w := wx) (show aT < 8 by decide)
    rw [ho₅'.wv (by omega) (by omega), ho₄.wv (by omega) (by omega)]
  -- `h = T qInv R_p⁻¹`.
  refine WP.mono (M.mm_ok (o := Public.aY) (a := aT) (b := aChunk) hc₅.good (Nat.le_refl _) hwx2
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₅.inv
    (by rw [hX₅.n]; exact hch)) fun s₆ ⟨_, hlt₆, hm₆, ha₆, k₆⟩ => ?_
  rw [hX₅.n] at hlt₆ hm₆
  obtain ⟨hc₆, hX₆, fx₆⟩ := hc₅.of_arrays hX₅ ha₆ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₆.2.2 (k₆.gpr (by decide)) (by omega)
  have kall := (((k₃.trans k₄).trans k₅).trans k₆)
  refine ⟨hc₆, hX₆, hlt₆, fun hct => ?_, ((fx₃.trans fx₄).trans fx₅).trans fx₆, kall.mono (by simp [mmRegs]),
    (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans (k₃.gpr (by decide))))⟩
  simp only [hm₆, hT₅, hT₃, hq₅, hq₄, hct, ↓reduceIte]

/-- `h`: from `m_q G mod N` in the modulus' `X` and `m_p R_p` in `p`'s `Y`,
`h = (m_p - m_q) qInv R_p⁻¹ R_p` into `p`'s `Y`, `qInv` masked by `c`. -/
theorem hPart_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X mqv m1 o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hXn : wv s.mem B (slot w Public.aX) w % N = mqv * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = m1 * 2 ^ (64 * wx) % X)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c) (hc : c = true → X ∣ N)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    WP isa (seqs (hSteps M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (c = true → ∃ a b, a % X = m1 * 2 ^ (64 * wx) % X ∧ b % X = mqv * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (off B o) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X =
          (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  simp only [hSteps, List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hslv]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo hhi
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  -- `m_q R_p` into `p`'s `X_c`.
  refine wp_seqs_append (by simp [redc]) (by simp [subModArr]) ?_
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aX) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, hv₂, f₂, k₂⟩ => ?_
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem := f₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hY₂ : wv s₂.mem (off B o) (slot wx Public.aY) wx = wv s.mem (off B o) (slot wx Public.aY) wx := by
    have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hc₁.good.scr.nowrap
    rw [f₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hm₁]
  have hM₂ : word s₂.mem (off B o) (8 * sMaskX) = mask c := by
    rw [f₂.word_eq (fun r hr => by
      simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
      have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
      have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
      have := hdr_lt_slot wx aT (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn] <;> omega)
      (by unfold sMaskX sFn; omega), hm₁]
    exact hmask
  have hb₂ : ∀ d, d + 8 ≤ o → word s₂.mem B d = word s.mem B d := fun d hd => by
    rw [fx₂.x_below hd ho64, hm₁]
  have hxc : X ∣ N → wv s₂.mem (off B o) (slot wx aXc) wx % X = mqv * 2 ^ (64 * wx) % X := fun hd => by
    apply VG.Proof.Bignum.redc_cancel hR
    rw [Nat.pow_mul] at hv₂
    rw [hv₂, hm₁, ← Nat.mod_mod_of_dvd _ hd, hXn, Nat.mod_mod_of_dvd _ hd, ← Nat.pow_mul]
  rw [show subModArr aT Public.aY aXc ++ (loadArr aChunk sQinv sPlen ++ (maskArr aChunk ++
      [M.mm Public.aY aT aChunk, .block [leave]])) = (subModArr aT Public.aY aXc ++ loadArr aChunk sQinv sPlen ++
      maskArr aChunk ++ [M.mm Public.aY aT aChunk]) ++ [.block [leave]] by simp]
  refine wp_seqs_append (by simp [subModArr]) (by simp) (WP.mono (hTail_ok M hc₂ hX₂ hw28 hwx2 hwx
    (by rw [hY₂]; exact hyl) hlt₂ hM₂ (by rw [hb₂ _ (by unfold sQinv sFn; omega)]; exact hqp)
    (by rw [hb₂ _ (by unfold sPlen sFn; omega)]; exact hql)
    (hqs.congrK (by
      have f := fx₂
      rw [hm₁] at f
      exact InScr.of_frm f fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) (k₁.trans k₂))
    hq1 hq2 hqw hqi) fun s₆ ⟨hc₆, hX₆, hlt₆, hh₆, fx₆, k₆, hdi₆⟩ => ?_)
  -- Back to the modulus'.
  have hl₆ : InRegions (s₆.rd ++ s₆.wr) (off (off B o) (8 * sLink)) 8 :=
    hc₆.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₆.mem)
    (by xrun [leave, State.ea, hdr, hc₆.rdi, hdrOff, hl₆, hc₆.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have fall : Frm B [xRange o wx] s.mem t.mem := by
    rw [hm, ← hm₁]; exact fx₂.trans fx₆
  have kall := ((k₁.trans k₂).trans k₆).trans k'
  have hb : ∀ d, d + 8 ≤ o → word t.mem B d = word s.mem B d := fun d hd => fall.x_below hd ho64
  refine ⟨⟨hs.congr kall.2.2, hdi, ⟨(hb _ (by unfold sW; omega)).trans hg.hdr.hw,
      (hb _ (by unfold sMinv; omega)).trans hg.hdr.hminv,
      fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hg.hdr.harr j hj)⟩⟩, by rw [hm]; exact hc₆.ws, ⟨by rw [hm]; exact hX₆.n, by rw [hm]; exact hX₆.inv,
      by rw [hm]; exact hX₆.one⟩, by rw [hm]; exact hlt₆, fun hct => ?_, fall,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · refine ⟨wv s.mem (off B o) (slot wx Public.aY) wx, wv s₂.mem (off B o) (slot wx aXc) wx,
      hyc (hc hct), hxc (hc hct), hlt₂, ?_⟩
    rw [hm, hh₆ hct, hY₂]
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact (kall.mono (rs' := .rdi :: mmRegs) (by decide)).1 r (by rw [List.mem_cons, not_or]; exact ⟨h, hr⟩)

/-- What `p`'s phase changes in the modulus' workspace. -/
def pRanges (w : Nat) : List (Nat × Nat) := gRanges w ++ [(slot w Public.aX, 8 * (w + 2))]

theorem pRanges_le (w : Nat) : ∀ r ∈ pRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  intro r hr
  simp only [pRanges, gRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem pxR_bound {w o wx : Nat} (hlo : slot w 8 ≤ o) :
    ∀ r ∈ pRanges w ++ [xRange o wx], 8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ o + slot wx 8 + tabBytes wx := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  have : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  intro r hr
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem Frm.px_hdr {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD) (h2 : i ≠ Public.sCnt) :
    word m' B (8 * i) = word m B (8 * i) := hf.word_eq (fun r hr => by
  have hb := pxR_bound hlo r hr
  have := hdr_lt_slot w Public.aAcc (show i < 32 from hi)
  have := hdr_lt_slot w Public.aTmp (show i < 32 from hi)
  have := hdr_lt_slot w Public.aY (show i < 32 from hi)
  have := hdr_lt_slot w Public.aX (show i < 32 from hi)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
    unfold Crt.sD sFn at h1 ⊢; omega
  · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
    unfold Public.sCnt sFn at h2 ⊢; omega
  · exact Or.inl (by omega)
  · exact Or.inl (by simp only at hb ⊢; omega)) (by omega)

theorem Frm.px_above {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) {d : Nat} (hd : o + slot wx 8 + tabBytes wx ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  hf.word_eq (fun r hr => Or.inr (by have := pxR_bound hlo r hr; omega)) hd'

theorem Frm.px_wv {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) (h4 : j ≠ Public.aX) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  have s4 := slot_sep (w := w) h4
  refine hf.wv_eq (fun r hr => ?_) (by omega)
  have hb := pxR_bound hlo r hr
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at hb ⊢ <;> omega

/-- `p`'s phase: `h = (m_p - m_q) qInv mod p` into `p`'s `Y` if `p` divides
`N`, `X_m ≡ c R (mod N)`, `m_q` in `q`'s `Y` and `qInv` (masked by `c`). -/
theorem pPhase_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ oq)
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
    WP isa (seqs (pPhase M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (c = true → ∃ a b, a % X = C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X ∧
        b % X = wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (off B o) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X =
          (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B (pRanges w ++ [xRange o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hhi' : o + slot wx 8 + tabBytes wx ≤ Z := by omega
  have hsub : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r ∈ pRanges w ++ [xRange o wx]) → ∀ {m m' : Mem},
      Frm B rs m m' → Frm B (pRanges w ++ [xRange o wx]) m m' := fun h _ _ f => f.mono h
  have sgx : ∀ r ∈ gRanges w ++ [xRange o wx], r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    (List.mem_append.mp hr).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      (fun h => List.mem_append_right _ h)
  have sp : ∀ r ∈ pRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr => List.mem_append_left _ hr
  have sg : ∀ r ∈ gRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    List.mem_append_left _ (List.mem_append_left _ hr)
  have sx : ∀ r ∈ [xRange o wx], r ∈ pRanges w ++ [xRange o wx] := fun r hr => List.mem_append_right _ hr
  -- What the frame keeps.
  have hq : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange o wx]) m m' → ∀ d k, d + 8 * k ≤ slot wq 8 →
      wv m' (off B oq) d k = wv m (off B oq) d k := fun f d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => f.px_above hlo (by omega) (by omega)
  have hqh : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange o wx]) m m' → ∀ i < 32,
      word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun f i hi => by
    rw [word_off, word_off]; exact f.px_above hlo (by omega) (by omega)
  rw [pPhase_eq]
  -- `R_p mod p`.
  refine wp_seqs_append (by simp [unitSteps]) (by simp [mqSteps]) ?_
  refine WP.mono (unitPhase_ok M hg hw hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide) (by decide) (by decide) hslv
    hws hN hodd hN1 hX hX1 hXodd) fun s₁ ⟨hg₁, hws₁, hX₁, hlt₁, hG₁, hpl₁, hpy₁, hM₁, f₁, k₁⟩ => ?_
  have f₁' := hsub sgx f₁
  -- `m_q G mod N`.
  refine wp_seqs_append (by simp [mqSteps]) (by simp) ?_
  refine WP.mono (mqPart_ok M hg₁ hw hw28 (hN.of_frm f₁ hlo hz (by omega)) hodd hlt₁ hG₁
    (by rw [f₁'.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslq)
    (hwsq.of_words fun i hi => hqh f₁' i (by omega)) (by omega) hqhi hwq hwq')
    fun s₂ ⟨hg₂, hlt₂, hmq₂, hY₂, f₂, k₂⟩ => ?_
  have f₂' := hsub sp f₂
  have f₀₂ := f₁'.trans f₂'
  have hN₂ : NVals s₂ B w minv N := by
    have := hN.of_frm f₁ hlo hz (by omega)
    exact ⟨by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.n,
      by rw [f₂'.word_eq (fun r hr => by
        have := pxR_bound hlo r hr
        have := slot_le (w := w) (show Public.aN < 8 by decide)
        simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        have s1 := slot_sep (w := w) (show Public.aN ≠ Public.aAcc by decide)
        have s2 := slot_sep (w := w) (show Public.aN ≠ Public.aTmp by decide)
        have s3 := slot_sep (w := w) (show Public.aN ≠ Public.aY by decide)
        have s4 := slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
        have := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega)
        (by have := slot_le (w := w) (show Public.aN < 8 by decide); omega)]; exact this.inv,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.r2,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.r2lt,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact this.one⟩
  -- `c G mod N`.
  refine wp_seqs_append (by simp) (by simp [powSteps]) ?_
  refine WP.mono (mmY_ok M hg₂ (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
    (by decide) hN₂ (by rw [hY₂]; exact hlt₁)) fun s₃ ⟨hg₃, hlt₃, hm₃, f₃, k₃⟩ => ?_
  have f₃' := hsub sg f₃
  have f₀₃ := f₀₂.trans f₃'
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hXm₂ : wv s₂.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    f₀₂.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcg : wv s₃.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, Nat.mul_mod, hXm₂, hXm, hY₂, hG₁, ← Nat.mul_mod]
    congr 1; ac_rfl
  have hpo : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d,
      o ≤ d → d + 8 ≤ 2 ^ 64 → word m' B d = word m B d := fun f hrs d hd hd' =>
    f.word_eq (fun r hr => Or.inr (by have := pRanges_le w r (hrs r hr); omega)) hd'
  have hpw : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ i < 32,
      word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun f hrs i hi => by
    rw [word_off, word_off]; exact hpo f hrs _ (by omega) (by omega)
  have sg' : ∀ r ∈ gRanges w, r ∈ pRanges w := fun r hr => List.mem_append_left _ hr
  have hpv : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d k,
      d + 8 * k ≤ slot wx 8 → wv m' (off B o) d k = wv m (off B o) d k := fun f hrs d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpo f hrs _ (by omega) (by omega)
  have hY8 := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hpY₃ : wv s₃.mem (off B o) (slot wx Public.aY) wx = wv s₁.mem (off B o) (slot wx Public.aY) wx := by
    rw [hpv f₃ sg' _ _ (by omega), hpv f₂ (fun r h => h) _ _ (by omega)]
  have hws₃ : WsAt s₃.mem B o wx mx := hws₁.of_words fun i hi => by
    rw [hpw f₃ sg' i (by omega), hpw f₂ (fun r h => h) i (by omega)]
  have hX₃ : XVals s₃ B o wx mx X :=
    (hX₁.of_below f₂ (fun r hr => (pRanges_le w r hr).trans hlo) (by omega)).of_below f₃
      (fun r hr => (pRanges_le w r (sg' r hr)).trans hlo) (by omega)
  have i03 : InScr B Z s.mem s₃.mem := InScr.of_frm f₀₃ fun r hr => by have := pxR_bound hlo r hr; omega
  -- `c^dP R_p mod p`.
  refine wp_seqs_append (by simp [powSteps]) (by simp) ?_
  refine WP.mono (powPhase_ok M hg₃ hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslv) hws₃ hX₃ hX1 hXodd hcg
    (by rw [hpY₃]; exact hpl₁) (fun hd => by rw [hpY₃]; exact hpy₁ hd) (sd := sDp) (slen := sPlen) (by decide)
    (by decide) (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hep)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hel) hL1 hL2
    (he.congrK i03 ((k₁.trans k₂).trans k₃))) fun s₄ ⟨hc₄, hX₄, hlt₄, hv₄, hM₄, fx₄, k₄⟩ => ?_
  -- Back to the modulus'.
  have hl₄ : InRegions (s₄.rd ++ s₄.wr) (off (off B o) (8 * sLink)) 8 :=
    hc₄.good.scr.ld (by unfold sLink sFn; omega)
  refine wp_seqs_append (by simp) (by simp [hSteps]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₄.mem)
    (by xrun [leave, State.ea, hdr, hc₄.rdi, hdrOff, hl₄, hc₄.link]) rfl) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_
  have fx₅ : Frm B [xRange o wx] s₃.mem s₅.mem := by rw [hm₅]; exact fx₄
  have f₀₅ := f₀₃.trans (hsub sx fx₅)
  have k05 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  have hb₅ : ∀ d, d + 8 ≤ o → word s₅.mem B d = word s₃.mem B d := fun d hd => fx₅.x_below hd ho64
  have hg₅ : Good s₅ B Z w minv := ⟨hs.congr k05.2.2, hdi₅, ⟨(hb₅ _ (by unfold sW; omega)).trans hg₃.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega)).trans hg₃.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hg₃.hdr.harr j hj)⟩⟩
  have hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  have hXn₅ : wv s₅.mem B (slot w Public.aX) w % N =
      wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    rw [wv_congr fun i hi => hb₅ _ (by have := slot_le (w := w) (show Public.aX < 8 by decide); omega),
      f₃.wv_eq (fun r hr => by
        have := slot_le (w := w) (show Public.aX < 8 by decide)
        have s1 := slot_sep (w := w) (show Public.aX ≠ Public.aAcc by decide)
        have s2 := slot_sep (w := w) (show Public.aX ≠ Public.aTmp by decide)
        have s3 := slot_sep (w := w) (show Public.aX ≠ Public.aY by decide)
        have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
        simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega)
        (by have := slot_le (w := w) (show Public.aX < 8 by decide); omega), hmq₂,
      hq f₁' _ _ (by have := slot_le (w := wq) (show Public.aY < 8 by decide); omega)]
  have i05 : InScr B Z s.mem s₅.mem := InScr.of_frm f₀₅ fun r hr => by have := pxR_bound hlo r hr; omega
  -- `h`.
  have a1 : word s₅.mem B (8 * sWsP) = off B o := by
    rw [f₀₅.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslv
  have a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  have a3 : wv s₅.mem (off B o) (slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  have a4 : X ∣ N → wv s₅.mem (off B o) (slot wx Public.aY) wx % X =
      C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X := fun hd => by rw [hm₅]; exact hv₄ hd
  have a5 : word s₅.mem (off B o) (8 * sMaskX) = mask c := by
    rw [hm₅, hM₄, hpw f₃ sg' _ (by decide), hpw f₂ (fun r h => h) _ (by decide), hM₁]; exact hmask
  have a6 : word s₅.mem B (8 * sQinv) = qp := by
    rw [f₀₅.px_hdr hlo (by decide) (by decide) (by decide)]; exact hqp
  have a7 : word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [f₀₅.px_hdr hlo (by decide) (by decide) (by decide), hql]; exact hel
  refine WP.mono (hPart_ok M hg₅ hw28 hlo hhi' hwx2 hwx a1 a2 hX₅ hX1 hXodd hXn₅ a3 a4 a5 hc a6 a7
    (hqs.congrK i05 k05) (by omega) (by omega) hqw hqi) fun t ⟨hg', hws', hX', hlt', hh', fx', k'⟩ => ?_
  have kall := k05.trans k'
  refine ⟨hg', hws', hX', hlt', hh', f₀₅.trans (hsub sx fx'), ⟨fun r hr => ?_, kall.2⟩⟩
  by_cases h : r = .rdi
  · subst h; rw [hg'.rdi, hg.rdi]
  · exact (kall.mono (rs' := .rdi :: mmRegs) (by decide)).1 r (by rw [List.mem_cons, not_or]; exact ⟨h, hr⟩)

end VG.Proof.Bignum.X86_64
