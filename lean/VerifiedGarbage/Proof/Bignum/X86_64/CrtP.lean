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
      (powSteps mul sWsP sDp sPlen ++ ([.block [leave]] ++ hSteps mul)))) := by
  simp only [pPhase, unitSteps, powSteps, mqSteps, hSteps, enterP, List.append_assoc, List.cons_append,
    List.nil_append]

/-- `m_q`, `q`'s `Y`, times `G` (the modulus' `Y`) modulo `N` into the
modulus' `X`. -/
theorem mqPart_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mq : BitVec 64} {N G oq wq : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N) (hodd : N % 2 = 1)
    (hYl : wv s.mem B (slot w Public.aY) w < N) (hY : wv s.mem B (slot w Public.aY) w % N = G % N)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hws : WsAt s.mem B oq wq mq) (hlo : slot w 8 ≤ oq)
    (hhi : oq + slot wq 8 ≤ Z) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs (mqSteps M.mm)) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w Public.aX) w < N ∧
      wv t.mem B (slot w Public.aX) w % N = wv s.mem (off B oq) (slot wq Public.aY) wq * G % N ∧
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
  have hsq : Scr s₁ (off B oq) (slot wq 8) := hs₁.sub hhi (by omega)
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
  refine ⟨hg', hlt', ?_, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
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

end VG.Proof.Bignum.X86_64
