import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Pre
import VerifiedGarbage.Proof.Bignum.X86_64.CrtP
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma

/-!
# RSA with AVX512_IFMA on x86-64: after the exponentiations

`post` is `p`'s phase after its exponentiation, in `p`'s workspace:
`R_p² mod p` from `n`'s `R_n² mod n` (`redc`), `m_q R_p mod p` from `q`'s
result, and `h = (m_p - m_q) qInv mod p` (`hTail_ok`, as `pPhase`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem post_eq (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.post mul = (([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++ redc mul Public.aR2) ++
      (.block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (ws .rax sWsQ)),
          .mov .rsi (.mem (ws .rax (sArr Public.aY))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))] ::
        copyWords :: mul aChunk aChunk aXc :: (copyArr aXc aChunk ++
      ((subModArr aT Public.aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++
        ([mul Public.aY aT aChunk] : List (Prog isa))) ++ ([.block [leave]] : List (Prog isa))))) := by
  simp only [CrtIfma.post, enterP, List.append_assoc, List.cons_append, List.nil_append]

/-- `post`: with `q`'s result in its `aY`, `p`'s `aY := h` as `pPhase` leaves
it. Only `p`'s workspace changes. -/
theorem post_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X oq op wx m1 : Nat} {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N) (hw2 : w = 2 * wx)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wx mq)
    (hhiq : oq + slot wx 8 + tabBytes wx ≤ Z)
    (hlo : slot w 8 ≤ op) (hhi : op + slot wx 8 + tabBytes wx ≤ oq) (hwx2 : 2 ≤ wx)
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
        b % X = wv s.mem (off B oq) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (off B op) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X = (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange op wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hhiq, hlo, hhi, hn]
  have ho64 : op < 2 ^ 64 := by omega_using [hhiq, hhi, hn, hX8]
  have hoL : op + slot wx 8 ≤ 2 ^ 64 := by omega_using [hhiq, hhi, hn]
  have hwx : wx ≤ w := by omega_using [hw2]
  have hK := nChunks_two hw2 (by omega_using [hq1, hqw])
  have hRx : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have hRR : Nat.Coprime (2 ^ (64 * wx * 2)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have e2 : 2 ^ (64 * w) = 2 ^ (64 * wx * 2) := by rw [hw2]; congr 1; omega_using []
  have lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have lC := slot_le (w := wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  have hrm : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := fun r hr => by
    simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn, slot, hdrBytes] <;>
      omega_using []
  have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [post_eq]
  -- `aXc := R_n² R_p^-2 = R_p²`.
  refine wp_seqs_append (by simp) (by simp [subModArr]) (WP.mono (enterRedc_ok M (j := Public.aR2) (by decide) hg
    hw28 hlo (by omega_using [hhiq, hhi]) hwx2 hwx (by decide) hsp hws hX hX1) fun s₁ ⟨hc₁, hX₁, hlt₁, hv₁, f₁, r₁, k₁⟩ => ?_)
  rw [hK] at hv₁
  have hb₁ : ∀ d, d + 8 ≤ op → word s₁.mem B d = word s.mem B d := fun d hd => f₁.x_below hd ho64
  have hab₁ : ∀ d, op + slot wx 8 + tabBytes wx ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d :=
    fun d hd hd' => f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_using [lC, hC0, hd]) hd'
  have hs₁ := hs.congr k₁.2.2
  have hsP := hc₁.good.scr
  have hdi₁ := hc₁.rdi
  have hldq := (hs₁.sub (o := oq) (n := slot wx 8) (by omega_using [hhiq]) (by omega_using [lC])).ld (d := 8 * sArr Public.aY)
    (by unfold sArr Public.aY; omega_using [lC, hC0])
  have hqa : word s₁.mem (off B oq) (8 * sArr Public.aY) = off (off B oq) (slot wx Public.aY) := by
    rw [word_off, hab₁ (oq + 8 * sArr Public.aY) (by omega_using [hhi])
        (by unfold sArr Public.aY; omega_using [hhiq, hn, lC, hC0]), ← word_off]
    exact hwsq.hdr.harr Public.aY (by decide)
  -- `m_q` into `aChunk`.
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = off (off B oq) (slot wx Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rbx = off (off B op) (slot wx aChunk) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, ws, hdi₁, hdrOff, hsP.ld (d := 8 * sLink) (by unfold sLink sFn; omega_using [lC, hC0]), hc₁.link,
      hs₁.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega_using [hhiq, lC, hC0]),
          hb₁ (8 * sWsQ) (by unfold sWsQ sFn; omega_using [hlo, h8]), hq,
      hldq, hqa, hsP.ld (d := 8 * sW) (by unfold sW; omega_using [lC, hC0]), hc₁.hdr.hw,
      hsP.ld (d := 8 * sArr aChunk) (by unfold sArr aChunk; omega_using [lC, hC0]), hc₁.hdr.harr aChunk (by decide)]) rfl)
    fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hsP₂ := hsP.congr k₂.2.2
  have hsi₂' : s₂.gpr .rsi = off B (oq + slot wx Public.aY) := by rw [hsi₂, off_off]
  refine WP.seq (WP.mono (copyWords_ok (S := B) (eS := oq + slot wx Public.aY) (D := off B op) (eD := slot wx aChunk)
    (w := wx) hsi₂' hbx₂ h12₂ (by omega_using [hq1, hqw]) (by omega_using [hw28, hwx]) (by omega_using [hoL, lC])
        (fun j hj => hs₂.ld (by omega_using [hhiq, lY, hj]))
    (fun j hj => hsP₂.st (by omega_using [lC, hj])) (fun j hj b hb => Or.inr (by
      rw [show off B (oq + slot wx Public.aY + 8 * j) = off (off B op) (oq + slot wx Public.aY + 8 * j - op) by
        rw [off_off]; congr 1; omega_using [hhi],
            ofs_off (off B op) (by omega_using [hhiq, hn, lY, hj, hb])]; omega_using [hhi,
            lC]))) fun s₃ ⟨hv₃, _, ho₃, k₃⟩ => ?_)
  rw [hm₂] at ho₃
  have hz₁ : (off B op).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₁.good.scr.nowrap; omega_using [this]
  have hX₃ : XVals s₃ B op wx mx X := hX₁.of_outside ho₃ (by decide) (by decide) (by decide) (by omega_using []) hz₁
  have fo₃ : Frm (off B op) [(slot wx aChunk, 8 * wx)] s₁.mem s₃.mem := Frm.of_outside ho₃ (by simp)
  have hc₃ : SubCtx s₃ B Z op w wx mx := hc₁.of_frm fo₃ (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) (k₂.trans k₃).2.2 ((k₂.trans k₃).gpr (by decide))
  have fx₃ : Frm B [xRange op wx] s₁.mem s₃.mem :=
    fo₃.to_x (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) hoL (List.mem_singleton_self _)
  have hC₃ : wv s₃.mem (off B op) (slot wx aChunk) wx = wv s.mem (off B oq) (slot wx Public.aY) wx := by
    rw [hv₃, hm₂, wv_off]
    exact wv_congr fun i hi => hab₁ _ (by omega_using [hhi]) (by omega_using [hhiq, hn, lY, hi])
  have hxc₃ : wv s₃.mem (off B op) (slot wx aXc) wx = wv s₁.mem (off B op) (slot wx aXc) wx := by
    have := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    exact ho₃.wv (by omega_arith) (by omega_using [hz₁, this])
  -- `aChunk := m_q R_p² R_p^-1 = m_q R_p`.
  refine WP.seq (WP.mono (M.mm_ok (o := aChunk) (a := aChunk) (b := aXc) hc₃.good (Nat.le_refl _) hwx2
    (by omega_using [hw28, hwx]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₃.inv
    (by rw [hX₃.n, hxc₃]; exact hlt₁)) fun s₄₀ ⟨_, hlt₄, hm₄, ha₄, k₄₀⟩ => ?_)
  rw [hX₃.n] at hlt₄ hm₄
  obtain ⟨hc₄₀, hX₄₀, fx₄₀⟩ := hc₃.of_arrays hX₃ ha₄ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₄₀.2.2 (k₄₀.gpr (by decide)) (by omega_using [hq1, hqw])
  have hz₄ : (off B op).toNat + slot wx 8 ≤ 2 ^ 64 := hz₁
  -- `aXc := aChunk`.
  refine wp_seqs_append (by simp [copyArr]) (by simp [subModArr]) (WP.mono (copyArr_ok hc₄₀.good (Nat.le_refl _)
    (by omega_using [hq1, hqw]) (by omega_using [hw28, hwx]) (o := aXc) (a := aChunk) (by decide) (by decide) (by decide))
    fun s₄ ⟨hv₄c, ho₄c, k₄c⟩ => ?_)
  have lX := slot_le (w := wx) (show aXc < 8 by decide)
  have hX0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have hc₄ := hc₄₀.of_frm (rs := [(slot wx aXc, 8 * wx)]) (Frm.of_outside ho₄c (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lX, hX0]) k₄c.2.2 (k₄c.gpr (by decide))
  have hX₄ : XVals s₄ B op wx mx X := hX₄₀.of_outside ho₄c (by decide) (by decide) (by decide) (by omega_using []) hz₄
  have fx₄ : Frm B [xRange op wx] s₃.mem s₄.mem := fx₄₀.trans
    ((ho₄c.mono (o' := slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_using [])).to_x
      (by decide) hoL (List.mem_singleton_self _))
  have k₄ := k₄₀.trans k₄c
  have hY₄ : wv s₄.mem (off B op) (slot wx Public.aY) wx = wv s.mem (off B op) (slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    rw [ho₄c.wv (by omega_using [this]) (by omega_using [lY, hz₄]), ha₄.wv_of_not_mem (by decide) (by decide) hz₄]
    have := slot_sep (w := wx) (show Public.aY ≠ aChunk by decide)
    rw [ho₃.wv (by omega_using [this]) (by omega_using [lY, hz₄]),
        r₁.wv_eq (fun r hr => by have := rY r hr; omega_using [this]) (by omega_using [lY, hz₄])]
  have hM₄ : word s₄.mem (off B op) (8 * sMaskX) = mask c := by
    have hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega_using []
    rw [ho₄c.word (.inl (by omega_arith)) (by omega_arith), ha₄.hslot (by decide), ho₃.word (.inl (by omega_arith)) (by omega_arith),
      r₁.word_eq hrm (by omega_arith)]; exact hmask
  have hlt₄' : wv s₄.mem (off B op) (slot wx aXc) wx < X := by rw [hv₄c]; exact hlt₄
  have f04 : Frm B [xRange op wx] s.mem s₄.mem := (f₁.trans fx₃).trans fx₄
  have hb₄ : ∀ d, d + 8 ≤ op → word s₄.mem B d = word s.mem B d := fun d hd => f04.x_below hd ho64
  have i04 : InScr B Z s.mem s₄.mem :=
    InScr.of_frm f04 fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith
  -- `h`.
  refine wp_seqs_append (by simp [subModArr]) (by simp) (WP.mono (hTail_ok M hc₄ hX₄ hw28 hwx2 hwx
    (by rw [hY₄]; exact hyl) hlt₄' hM₄ (by rw [hb₄ _ (by unfold sQinv sFn; omega_arith)]; exact hqp)
    (by rw [hb₄ _ (by unfold sPlen sFn; omega_arith)]; exact hql)
    (hqs.congrK i04 (((k₁.trans k₂).trans k₃).trans k₄)) hq1 hq2 hqw hqi)
    fun s₅ ⟨hc₅, hX₅, hlt₅, hh₅, fx₅, k₅, _⟩ => ?_)
  refine WP.mono (leaveBack_ok hg hc₅ (f04.trans fx₅) hlo) fun t ⟨hg', hm', k'⟩ => ?_
  have kall := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k'
  refine ⟨hg', by rw [hm']; exact hc₅.ws, ?_, by rw [hm']; exact hlt₅, fun hct => ?_,
    by rw [hm']; exact (f04.trans fx₅).mono fun r hr => by rw [List.mem_singleton.mp hr]; simp,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [show t = { t with mem := s₅.mem } by rw [← hm']]; exact ⟨hX₅.n, hX₅.inv, hX₅.one⟩
  · refine ⟨wv s.mem (off B op) (slot wx Public.aY) wx, wv s₄.mem (off B op) (slot wx aXc) wx,
      hyc (hc hct), ?_, hlt₄', by rw [hm', hh₅ hct, hY₄]⟩
    -- `aXc₁ = R_p²`, so `aXc₄ R_p ≡ m_q R_p²`.
    have h1 : wv s₁.mem (off B op) (slot wx aXc) wx % X = 2 ^ (64 * wx * 2) % X :=
      VG.Proof.Bignum.mont_cancel hRR (by
        rw [hv₁, ← Nat.mod_mod_of_dvd _ (hc hct), hN.r2, Nat.mod_mod_of_dvd _ (hc hct), e2, ← Nat.pow_add])
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hv₄c, hm₄, hC₃, hxc₃, Nat.mul_mod, h1, ← Nat.mul_mod, Nat.mul_assoc _ (2 ^ (64 * wx)), ← Nat.pow_add]
    congr 3; omega_arith
  · by_cases h : r = .rdi
    · subst h; rw [hg'.rdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64
