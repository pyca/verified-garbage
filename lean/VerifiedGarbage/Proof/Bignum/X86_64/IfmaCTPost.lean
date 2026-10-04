import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPH

/-!
# RSA with AVX512_IFMA on x86-64: constant time, after the exponentiations

`post` is `G` copied back into `n`'s `aY`, then `pPhase`'s `mqSteps` and
`hSteps`, which are constant time (`mq_ct`, `h_ct`): so is `post`
(`post_ct`), for `post_ok`'s hypotheses (`PostPre`), from which `post_chain`
proves what each piece needs, as `post_ok` runs them.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `post`: `n`'s workspace, `p`'s and `q`'s, and
`qInv`'s pointer and length. -/
structure PostPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  wx : Nat
  oq : Nat
  wq : Nat
  qp : Addr
  len : Nat

abbrev PostPub.nw (p : PostPub) : Ws := ⟨p.B, p.Z, p.w⟩
abbrev PostPub.mq (p : PostPub) : MqPub := ⟨p.B, p.Z, p.w, p.oq, p.wq⟩
abbrev PostPub.h (p : PostPub) : HPub := ⟨p.B, p.Z, p.w, p.op, p.wx, p.qp, p.len⟩

/-- Before `post`'s `mqSteps`. -/
def PostQ (M : Mont) (p : PostPub) (s : State) : Prop :=
  Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s (H0 M p.h)

/-- `post_ok`'s hypotheses, with what `post` reads of them public. -/
def PostPre (p : PostPub) (s : State) : Prop :=
  ∃ (minv mx mq : BitVec 64) (N X m1 : Nat) (qib : List Byte) (c : Bool),
    Good s p.B p.Z p.w minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ NVals s p.B p.w minv N ∧ N % 2 = 1 ∧
    wv s.mem p.B (slot p.w Public.aX) p.w < N ∧
    wv s.mem p.B (slot p.w Public.aX) p.w % N = 2 ^ (64 * p.wx * (nChunks p.w p.wx + 1)) % N ∧
    word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsAt s.mem p.B p.oq p.wq mq ∧
    p.oq + slot p.wq 8 + tabBytes p.wq ≤ p.Z ∧ 1 ≤ p.wq ∧ p.wq ≤ p.w ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wx 8 + tabBytes p.wx ≤ p.oq ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    word s.mem p.B (8 * sWsP) = off p.B p.op ∧ WsAt s.mem p.B p.op p.wx mx ∧ XVals s p.B p.op p.wx mx X ∧
    1 < X ∧ X % 2 = 1 ∧ wv s.mem (off p.B p.op) (slot p.wx Public.aY) p.wx < X ∧
    (X ∣ N → wv s.mem (off p.B p.op) (slot p.wx Public.aY) p.wx % X = m1 * 2 ^ (64 * p.wx) % X) ∧
    word s.mem (off p.B p.op) (8 * sMaskX) = mask c ∧ (c = true → X ∣ N) ∧ word s.mem p.B (8 * sQinv) = p.qp ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 qib.length ∧ Src s p.B p.Z p.qp qib ∧ 1 ≤ qib.length ∧
    qib.length < 2 ^ 31 ∧ (qib.length + 7) / 8 ≤ p.wx ∧ (c = true → Spec.Rsa.os2ip qib < X) ∧ qib.length = p.len

/-- `post_ok`'s hypotheses give, after the copy, `mqSteps`' and `hSteps`'. -/
theorem post_chain (M : Mont) {p : PostPub} {s : State} (h : PostPre p s) :
    WP isa (seqs (copyArr Public.aY Public.aX)) s (PostQ M p) := by
  obtain ⟨B, Z, w, op, wx, oq, wq, qp, len⟩ := p
  dsimp only [PostPre] at h
  obtain ⟨minv, mx, mq, N, X, m1, qib, c, hg, hw, hw28, hN, hodd, hXl, hXv, hq, hwsq, hhiq, hwq, hwq', hlo, hhi,
    hwx2, hwx, hsp, hws, hX, hX1, hXodd, hyl, hyc, hmask, hc, hqp, hql, hqs, hq1, hq2, hqw, hqi, rfl⟩ := h
  show WP isa _ s fun t => Mq0 M ⟨B, Z, w, oq, wq⟩ t ∧
    WP isa (seqs (mqSteps M.mm)) t (H0 M ⟨B, Z, w, op, wx, qp, qib.length⟩)
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hq8 := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have lY := slot_le (w := w) (show Public.aY < 8 by decide)
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have sYX := slot_sep (w := w) (show Public.aY ≠ Public.aX by decide)
  -- `aY := G`.
  refine WP.mono (copyArr_ok hg (by omega) (by omega) (by omega) (o := Public.aY) (a := Public.aX) (by decide)
    (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ := hN.of_outsideArr ho₁ (by decide) (by decide) (by decide) (by decide) (by omega) hz
  have hup : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (.inr (by omega)) hd'
  have hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (.inl (by have := hdr_lt_slot w Public.aY hi; omega)) (by omega)
  have hwsq₁ : WsAt s₁.mem B oq wq mq := hwsq.of_words fun i hi => by
    rw [word_off, word_off]; exact hup _ (by omega) (by omega)
  have hq₁ : word s₁.mem B (8 * sWsQ) = off B oq := by rw [hb₁ _ (by decide)]; exact hq
  -- `m_q G mod n` into `aX`.
  refine ⟨mq_chain M hg₁ hw hw28 hN₁ hq₁ hwsq₁ (by omega) hhiq hwq hwq', WP.mono (mqPart_ok M hg₁ hw hw28 hN₁ hodd
    (G := wv s₁.mem B (slot w Public.aY) w) (by rw [hv₁]; exact hXl) rfl hq₁ hwsq₁ (by omega) hhiq hwq hwq')
    fun s₂ ⟨hg₂, _, _, _, f₂, k₂⟩ => ?_⟩
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
  -- `h` into `p`'s `aY`.
  exact h_chain M hg₂ hw28 hlo (by omega) hwx2 hwx
    (by rw [hhd _ (by decide) (by decide) (by decide)]; exact hsp) (hws.of_words fun i hi => hpw i (by omega)) hX₂
    hX1 (by rw [hpv _ (by decide)]; exact hyl) (by rw [hpw _ (by decide)]; exact hmask)
    (by rw [hhd _ (by decide) (by decide) (by decide)]; exact hqp)
    (by rw [hhd _ (by decide) (by decide) (by decide)]; exact hql)
    (hqs.congr ((InScr.of_outside ho₁ (by omega)).trans (InScr.of_frm f₂ hZ₂)) (by rw [k₂.2.1, k₁.2.1])
      (by rw [k₂.2.2, k₁.2.2])) hq1 hq2 hqw hqi

/-- `post` is constant time. -/
theorem post_ct (M : Mont) (hR : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two PostPre) (seqs (CrtIfma.post M.mm)) fun _ _ => True := by
  rw [post_eq]
  refine ct_steps (by simp [copyArr]) (by simp [mqSteps]) PostPub.nw
    (fun _ _ ⟨minv, _, _, _, _, _, _, _, hg, _, _, _, _, _, _, _, _, hhi, _, _, hlo, hpq, _⟩ =>
      ⟨minv, hg, by dsimp only [PostPub.nw]; omega⟩)
    (fun _ _ h => post_chain M h) (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  exact ct_steps (by simp [mqSteps]) (by simp [hSteps]) PostPub.mq (fun _ _ h => h.1) (fun _ _ h => h.2)
    (mq_ct M) (ct_last PostPub.h (fun _ _ h => h) (h_ct M hR hL))

end VG.Proof.Bignum.X86_64
