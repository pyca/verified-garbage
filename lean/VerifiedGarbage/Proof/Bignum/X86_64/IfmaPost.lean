import VerifiedGarbage.Proof.Bignum.X86_64.IfmaComp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtP

/-!
# RSA with AVX512_IFMA on x86-64: after the exponentiations

`post` is `p`'s phase after its exponentiation, as in `pPhase`: `G` back
into `n`'s `aY` (`copyArr`), `m_q G mod n` (`mqSteps`) and
`h = (m_p - m_q) qInv mod p` (`hSteps`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem post_eq (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.post mul = copyArr Public.aY Public.aX ++ (mqSteps mul ++ hSteps mul) := by
  simp only [CrtIfma.post, mqSteps, hSteps, enterP, List.append_assoc, List.cons_append, List.nil_append]

/-- `post`: with `G` in `n`'s `aX` and `q`'s result `mqv` in its `aY`, `p`'s
`aY := h` as `pPhase` leaves it. -/
theorem post_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X oq wq op wx m1 : Nat} {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N) (hodd : N % 2 = 1)
    (hXl : wv s.mem B (slot w Public.aX) w < N)
    (hXv : wv s.mem B (slot w Public.aX) w % N = 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wq mq)
    (hhiq : oq + slot wq 8 + tabBytes wq ≤ Z) (hwq : 1 ≤ wq) (hwq' : wq ≤ w)
    (hlo : slot w 8 ≤ op) (hhi : op + slot wx 8 + tabBytes wx ≤ oq) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hsp : word s.mem B (8 * sWsP) = off B op) (hws : WsAt s.mem B op wx mx) (hX : XVals s B op wx mx X)
    (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hyl : wv s.mem (off B op) (slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (off B op) (slot wx Public.aY) wx % X = m1 * 2 ^ (64 * wx) % X)
    (hmask : word s.mem (off B op) (8 * sMaskX) = mask c) (hc : c = true → X ∣ N)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    WP isa (seqs (CrtIfma.post M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B op wx mx ∧
      XVals t B op wx mx X ∧ wv t.mem (off B op) (slot wx Public.aY) wx < X ∧
      (c = true → ∃ a b, a % X = m1 * 2 ^ (64 * wx) % X ∧
        b % X = wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (off B op) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X = (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange op wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hq8 := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have lY := slot_le (w := w) (show Public.aY < 8 by decide)
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have sYX := slot_sep (w := w) (show Public.aY ≠ Public.aX by decide)
  rw [post_eq]
  -- `aY := G`.
  refine wp_seqs_append (by simp [copyArr]) (by simp [mqSteps]) (WP.mono (copyArr_ok hg (by omega) (by omega)
    (by omega) (o := Public.aY) (a := Public.aX) (by decide) (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_)
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ := hN.of_outsideArr ho₁ (by decide) (by decide) (by decide) (by decide) (by omega) hz
  have hup : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (.inr (by omega)) hd'
  have hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (.inl (by have := hdr_lt_slot w Public.aY hi; omega)) (by omega)
  have hwsq₁ : WsAt s₁.mem B oq wq mq := hwsq.of_words fun i hi => by
    rw [word_off, word_off]; exact hup _ (by omega) (by omega)
  -- `m_q G mod n` into `aX`.
  refine wp_seqs_append (by simp [mqSteps]) (by simp [hSteps]) (WP.mono (mqPart_ok M hg₁ hw hw28 hN₁ hodd
    (G := wv s₁.mem B (slot w Public.aY) w) (by rw [hv₁]; exact hXl) rfl (by rw [hb₁ _ (by decide)]; exact hq)
    hwsq₁ (by omega) hhiq hwq hwq') fun s₂ ⟨hg₂, _, hx₂, _, f₂, k₂⟩ => ?_)
  have hlt₂ : ∀ r ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))], r.1 + r.2 ≤ slot w 8 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact (gRanges_lt w r hr).2
    · rw [List.mem_singleton.mp hr]; simp only; omega
  have hab : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₂.mem B d = word s.mem B d := fun d hd hd' => by
    rw [f₂.word_eq (fun r hr => .inr (by have := hlt₂ r hr; omega)) hd', hup d hd hd']
  have hhd : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word s₂.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi h1 h2 => by
      rw [gRanges_hdr f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]; have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
        unfold slot hdrBytes at this ⊢; simp only; omega) hi h1 h2 (by omega), hb₁ i hi]
  have hpw : ∀ i < 32, word s₂.mem (off B op) (8 * i) = word s.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab _ (by omega) (by omega)
  have hpv : ∀ j < 8, wv s₂.mem (off B op) (slot wx j) wx = wv s.mem (off B op) (slot wx j) wx := fun j hj => by
    have := slot_le (w := wx) hj
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab _ (by omega) (by omega)
  have hX₂ : XVals s₂ B op wx mx X :=
    ⟨by rw [hpv _ (by decide)]; exact hX.n, by
      have := slot_le (w := wx) (show Public.aN < 8 by decide)
      rw [word_off, hab _ (by omega) (by omega), ← word_off]; exact hX.inv,
      by rw [hpv _ (by decide)]; exact hX.one⟩
  have hZ₂ : ∀ r ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))], r.1 + r.2 ≤ Z := fun r hr => by
    have := hlt₂ r hr; omega
  have hqY : wv s₁.mem (off B oq) (slot wq Public.aY) wq = wv s.mem (off B oq) (slot wq Public.aY) wq := by
    have := slot_le (w := wq) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hup _ (by omega) (by omega)
  -- `h` into `p`'s `aY`.
  refine WP.mono (hPart_ok M hg₂ hw28 hlo (by omega) hwx2 hwx
    (by rw [hhd _ (by decide) (by decide) (by decide)]; exact hsp) (hws.of_words fun i hi => hpw i (by omega)) hX₂
    hX1 hXodd (mqv := wv s.mem (off B oq) (slot wq Public.aY) wq)
    (by rw [hx₂, Nat.mul_mod, hv₁, hXv, ← Nat.mul_mod, hqY]) (by rw [hpv _ (by decide)]; exact hyl)
    (fun hd => by rw [hpv _ (by decide)]; exact hyc hd) (by rw [hpw _ (by decide)]; exact hmask) hc
    (by rw [hhd _ (by decide) (by decide) (by decide)]; exact hqp)
    (by rw [hhd _ (by decide) (by decide) (by decide)]; exact hql)
    (hqs.congr ((InScr.of_outside ho₁ (by omega)).trans (InScr.of_frm f₂ hZ₂)) (by rw [k₂.2.1, k₁.2.1])
      (by rw [k₂.2.2, k₁.2.2])) hq1 hq2 hqw hqi) fun t ⟨hg', hws', hX', hlt', hh', f', k'⟩ =>
    ⟨hg', hws', hX', hlt', hh', ?_, ((k₁.trans k₂).trans k').mono (by simp [mmRegs])⟩
  have fo : Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange op wx]) s.mem s₁.mem :=
    Frm.of_outside (ho₁.mono (o' := slot w Public.aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [gRanges])
  exact (fo.trans (f₂.mono fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · rw [List.mem_singleton.mp hr]; simp)).trans (f'.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp)

end VG.Proof.Bignum.X86_64
