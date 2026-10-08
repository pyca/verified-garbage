import VerifiedGarbage.Proof.Rsa.X86_64.KeyReduce
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Impl.Rsa.X86_64.CheckCrtKey
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-!
# `vg_rsa_check_crt_key` on x86-64: remainders with a small quotient

`reduceTop`: `r` starts as the words of `x` from `c` up, then `reduce`'s
loop divides `x`'s low `c` words (`reduceLoopFrom_ok`), over numbers of
`w'` words. When `⌊x / 2^(64 c)⌋ < m`, `r` is then `x mod m`
(`reduceTop_ok`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- `reduce`'s loop from `r = ⌊x / 2^(64 c)⌋ mod M`: `c` words left. -/
theorem reduceLoopFrom_ok {Q : Prop} {s₀ : State} {B : Addr} {Z w eo em eA eT eS cnt c : Nat}
    (hL : RedLay B Z w eo em eA eT eS cnt) (hs : Scr s₀ B Z) (hr : RedRegs B w eo em eA eT eS s₀)
    (hc : 1 ≤ c) (hcN : c ≤ cnt) (h13 : s₀.gpr .r13 = BitVec.ofNat 64 c)
    (hR : Q → 0 < wv s₀.mem B em w →
      wv s₀.mem B eo w = wv s₀.mem B (eS + 8 * c) (cnt - c) % wv s₀.mem B em w) :
    WP isa (.loop wordStep .ne) s₀ fun t => Scr t B Z ∧
      Keep [.rax, .rbp, .r14, .rdx, .r11, .r15, .r13] s₀ t ∧ Frm B (redRs eA eT eo w) s₀.mem t.mem ∧
      (Q → 0 < wv s₀.mem B em w → wv t.mem B eo w = wv s₀.mem B eS cnt % wv s₀.mem B em w) := by
  refine wp_upto (a := cnt - c) (N := cnt) (by omega) (WInv Q s₀ B Z w eo em eA eT eS cnt)
    (fun i _ hi t hI => wordStep_ok hL hi hI) (fun t hI => ⟨hI.scr, hI.keep, hI.frm, fun hq hM0 => ?_⟩)
    ⟨hs, hr, Keep.refl _ _, by rw [h13, show cnt - (cnt - c) = c by omega], Frm.refl _ _ _,
      fun hq hM0 => by rw [hR hq hM0, show cnt - (cnt - c) = c by omega]⟩
  rw [hI.val hq hM0, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- `8 c` added to `rsi` from `r13 = c`. -/
theorem eight_add (c : Nat) : BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c) +
    (BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c)) = BitVec.ofNat 64 (8 * c) := by
  simp only [BitVec.ofNat_add_ofNat]; congr 1; omega

/-- A number below `2^(64 k)` is its low `k` words. -/
theorem wv_low {m : Mem} {B : Addr} {d k n : Nat} (hk : k ≤ n) (h : wv m B d n < 2 ^ (64 * k)) :
    wv m B d k = wv m B d n := by
  have e := wv_add m B d k (n - k)
  rw [show k + (n - k) = n by omega] at e
  rw [e] at h ⊢
  have hp : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
  rcases Nat.eq_zero_or_pos (wv m B (d + 8 * k) (n - k)) with h0 | h0
  · rw [h0]; simp
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * k)) h0; omega

/-- `reduceTop sl top`: `[aR] := x mod [aM]` for the number `x` of the `N`
words of the accumulator, over numbers of `w' = ⌈L / 8⌉` words (`L` in
slot `sl`), from the `c` that `top` puts in `r13`, when `[aM] > 0`, `[aM]`
fits in `w'` words and `⌊x / 2^(64 c)⌋ < [aM]`. -/
theorem reduceTop_ok {sl : Nat} {top : List Instr} {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {L c N : Nat} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28)
    (hsl : sl < 32) (hLs : word s.mem B (8 * sl) = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : L ≤ 8 * w)
    (htop : ∀ t : State, Good t B Z w minv → (∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i)) →
      WP isa (.block top) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 c ∧ t'.mem = t.mem ∧ Keep [.r13] t t')
    (hc : 1 ≤ c) (hcN : c + (L + 7) / 8 ≤ N) (hN : N ≤ 2 * w + 4) :
    WP isa (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sl top)) s fun t => Good t B Z w minv ∧
      (wv s.mem B (slot w aM) w < 2 ^ (64 * ((L + 7) / 8)) → 0 < wv s.mem B (slot w aM) w →
        wv s.mem B (slot w Public.aAcc + 8 * c) (N - c) < wv s.mem B (slot w aM) w →
        wv t.mem B (slot w aR) w = wv s.mem B (slot w Public.aAcc) N % wv s.mem B (slot w aM) w) ∧
      Arrays B w [aR, Public.aX, aT] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have e8 : slot w 8 = 256 + 8 * (8 * (w + 2)) := by unfold slot hdrBytes; omega
  have hw1 : 1 ≤ (L + 7) / 8 := by omega
  have hww : (L + 7) / 8 ≤ w := by omega
  have eAcc : slot w Public.aAcc = 256 + 16 * (w + 2) := by unfold slot hdrBytes Public.aAcc; omega
  have eR : slot w aR = 256 + 48 * (w + 2) := by unfold slot hdrBytes aR; omega
  have eM : slot w aM = 256 + 32 * (w + 2) := by unfold slot hdrBytes aM; omega
  have eX : slot w Public.aX = 256 + 8 * (w + 2) := by unfold slot hdrBytes Public.aX; omega
  have eT : slot w aT = 256 + 40 * (w + 2) := by unfold slot hdrBytes aT; omega
  show WP isa (.seq (Impl.Rsa.X86_64.Crt.zeroArr aR) (.seq (.block _) (.seq Impl.Rsa.X86_64.copyWords (.seq (.block _)
    (.loop wordStep .ne))))) s _
  refine WP.seq (WP.mono (zeroArr_ok hg hZ hw (by omega) (show aR < 8 by decide))
    fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have a₁ : Arrays B w [aR, Public.aX, aT] s.mem s₁.mem :=
    Arrays.of_outside (j := aR) (by simp) ho₁ (Nat.le_refl _) (by omega)
  have hs₁ := hg.scr.congr k₁.2.2
  have hH₁ := a₁.hdr hg.hdr
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hh₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    a₁.word_eq (fun j _ => .inl (hdr_lt_slot w j hi)) (by have := hdr_lt_slot w 8 hi; omega)
  have hl₁ : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₁.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The block: `w'`, `c`, the copy's source and destination.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((L + 7) / 8) ∧ t.mem = s₁.mem)
    (by xrun [Impl.Rsa.X86_64.CheckCrtKey.lenWords, State.ea, hdr, hdi₁, hdrOff, hl₁ sl hsl, hh₁ sl hsl, hLs,
      shr3_w L (by omega)]) rfl) fun s₂ ⟨⟨h12₂, hm₂⟩, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w minv := ⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans hdi₁, by rw [hm₂]; exact hH₁⟩
  refine WP.mono (htop s₂ hg₂ (fun i hi => by rw [hm₂]; exact hh₁ i hi)) fun s₃ ⟨h13₃, hm₃, k₃⟩ => ?_
  have hs₃ := hg₂.scr.congr k₃.2.2
  have hdi₃ : s₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hg₂.rdi
  have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 ((L + 7) / 8) := (k₃.gpr (by decide)).trans h12₂
  have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₃.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hH₃ : Hdr s₃.mem B w minv := by rw [hm₃, hm₂]; exact hH₁
  refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off B (slot w Public.aAcc + 8 * c) ∧
      t.gpr .rbx = off B (slot w aR) ∧ t.mem = s₃.mem)
    (by
      xrun [State.ea, hdr, hdi₃, hdrOff, h13₃, hl₃ (sArr Public.aAcc) (by unfold sArr Public.aAcc; omega),
        hl₃ (sArr aR) (by unfold sArr aR; omega), hH₃.harr Public.aAcc (by decide), hH₃.harr aR (by decide)]
      rw [eight_add]; exact off_off B _ _) rfl) fun s₄ ⟨⟨hsi₄, hbx₄, hm₄⟩, k₄⟩ => ?_
  have hs₄ := hs₃.congr k₄.2.2
  have h12₄ : s₄.gpr .r12 = BitVec.ofNat 64 ((L + 7) / 8) := (k₄.gpr (by decide)).trans h12₃
  have h13₄ : s₄.gpr .r13 = BitVec.ofNat 64 c := (k₄.gpr (by decide)).trans h13₃
  -- The copy of `x`'s words from `c` up.
  refine WP.seq (WP.mono (copyWords_ok hsi₄ hbx₄ h12₄ hw1 (by omega) (by omega)
    (fun i hi => hs₄.ld (by omega)) (fun i hi => hs₄.st (by omega))
    (fun i hi b hb => by rw [ofs_off B (by omega)]; omega)) fun s₅ ⟨hv₅, _, ho₅, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  have a₅ : Arrays B w [aR, Public.aX, aT] s₄.mem s₅.mem :=
    Arrays.of_outside (j := aR) (by simp) ho₅ (Nat.le_refl _) (by omega)
  have hH₅ : Hdr s₅.mem B w minv := a₅.hdr (by rw [hm₄]; exact hH₃)
  have hdi₅ : s₅.gpr .rdi = B := (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans hdi₃)
  have hl₅ : ∀ i < 32, InRegions (s₅.rd ++ s₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₅.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq (WP.mono (WP.keep [.rbx, .r10, .r8, .rsi, .r9] (Q := fun t =>
      t.gpr .rbx = off B (slot w aR) ∧ t.gpr .r10 = off B (slot w aM) ∧ t.gpr .r8 = off B (slot w Public.aX) ∧
      t.gpr .rsi = off B (slot w aT) ∧ t.gpr .r9 = off B (slot w Public.aAcc) ∧ t.mem = s₅.mem)
    (by
      xrun [State.ea, hdr, hdi₅, hdrOff, hl₅ (sArr aR) (by unfold sArr aR; omega),
        hl₅ (sArr aM) (by unfold sArr aM; omega), hl₅ (sArr Public.aX) (by unfold sArr Public.aX; omega),
        hl₅ (sArr aT) (by unfold sArr aT; omega), hl₅ (sArr Public.aAcc) (by unfold sArr Public.aAcc; omega),
        hH₅.harr aR (by decide), hH₅.harr aM (by decide), hH₅.harr Public.aX (by decide), hH₅.harr aT (by decide),
        hH₅.harr Public.aAcc (by decide)]) rfl) fun s₆ ⟨⟨hbx₆, h10₆, h8₆, hsi₆, h9₆, hm₆⟩, k₆⟩ => ?_)
  have k5 := k₅.trans k₆
  have rg₆ : RedRegs B ((L + 7) / 8) (slot w aR) (slot w aM) (slot w Public.aX) (slot w aT)
      (slot w Public.aAcc) s₆ :=
    ⟨hbx₆, h10₆, h8₆, (k5.gpr (by decide)).trans h12₄, hsi₆, h9₆⟩
  have hs₆ := hs₅.congr k₆.2.2
  have hLay : RedLay B Z ((L + 7) / 8) (slot w aR) (slot w aM) (slot w Public.aX) (slot w aT)
      (slot w Public.aAcc) N := by
    refine ⟨hw1, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  -- What the copy and the frames leave.
  have mS : ∀ {m m' : Mem}, Arrays B w [aR, Public.aX, aT] m m' → ∀ {d k : Nat}, d + 8 * k ≤ slot w Public.aX ∨
      (slot w Public.aX + 8 * (w + 2) ≤ d ∧ d + 8 * k ≤ slot w aT) →
      wv m' B d k = wv m B d k := by
    intro m m' h d k hd
    refine h.wv_eq (fun j hj => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> omega
  have hMs : wv s₆.mem B (slot w aM) w = wv s.mem B (slot w aM) w := by
    rw [hm₆, mS a₅ (by omega), hm₄, hm₃, hm₂,
      mS a₁ (by omega)]
  have hXs : ∀ {d k : Nat}, d + 8 * k ≤ slot w Public.aX ∨
      (slot w Public.aX + 8 * (w + 2) ≤ d ∧ d + 8 * k ≤ slot w aT) → wv s₆.mem B d k = wv s.mem B d k :=
    fun hd => by rw [hm₆, mS a₅ hd, hm₄, hm₃, hm₂, mS a₁ hd]
  have hM' : wv s.mem B (slot w aM) w < 2 ^ (64 * ((L + 7) / 8)) →
      wv s₆.mem B (slot w aM) ((L + 7) / 8) = wv s.mem B (slot w aM) w := fun hM => by
    rw [← hMs]; exact wv_low hww (by rw [hMs]; exact hM)
  have hAcc : ∀ k ≤ N, wv s₆.mem B (slot w Public.aAcc) k = wv s.mem B (slot w Public.aAcc) k := fun k hk =>
    hXs (Or.inr ⟨by omega, by omega⟩)
  have hTop : wv s₆.mem B (slot w Public.aAcc + 8 * c) (N - c) =
      wv s.mem B (slot w Public.aAcc + 8 * c) (N - c) :=
    hXs (Or.inr ⟨by omega, by omega⟩)
  have hR₆ : wv s₆.mem B (slot w aR) ((L + 7) / 8) =
      wv s.mem B (slot w Public.aAcc + 8 * c) ((L + 7) / 8) := by
    rw [hm₆, hv₅, hm₄, hm₃, hm₂]
    exact mS a₁ (Or.inr ⟨by omega, by omega⟩)
  refine WP.mono (reduceLoopFrom_ok (Q := wv s.mem B (slot w aM) w < 2 ^ (64 * ((L + 7) / 8)) ∧
      wv s.mem B (slot w Public.aAcc + 8 * c) (N - c) < wv s.mem B (slot w aM) w) hLay hs₆ rg₆ hc (by omega) ((k5.gpr (by decide)).trans h13₄)
    (fun hq _ => ?_)) fun t ⟨hst, kt, ft, hv⟩ => ?_
  · rw [hR₆, hTop, hM' hq.1, wv_low (by omega) (Nat.lt_of_lt_of_le hq.2 (Nat.le_of_lt hq.1)),
      Nat.mod_eq_of_lt hq.2]
  · have at₆ : Arrays B w [aR, Public.aX, aT] s₆.mem t.mem := fun x hx => ft x fun r hr => by
      simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
      have h1 := hx Public.aX (by simp); have h2 := hx aT (by simp); have h3 := hx aR (by simp)
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
    have aall : Arrays B w [aR, Public.aX, aT] s.mem t.mem := by
      refine a₁.trans ?_
      rw [← hm₂, ← hm₃, ← hm₄]
      exact a₅.trans (by rw [← hm₆]; exact at₆)
    have k := ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans kt)
    -- `r`'s words above `w'`: zero since `zeroArr`.
    have hHi : wv t.mem B (slot w aR + 8 * ((L + 7) / 8)) (w - (L + 7) / 8) = 0 := by
      have hz := wv_add s₁.mem B (slot w aR) ((L + 7) / 8) (w - (L + 7) / 8 + (2 + (L + 7) / 8))
      rw [show (L + 7) / 8 + (w - (L + 7) / 8 + (2 + (L + 7) / 8)) = w + 2 + (L + 7) / 8 by omega] at hz
      have hz' := wv_add s₁.mem B (slot w aR) (w + 2) ((L + 7) / 8)
      rw [hz₁] at hz'
      have e2 := wv_add s₁.mem B (slot w aR + 8 * ((L + 7) / 8)) (w - (L + 7) / 8) (2 + (L + 7) / 8)
      have h0 : wv s₁.mem B (slot w aR + 8 * ((L + 7) / 8)) (w - (L + 7) / 8) = 0 := by
        have hp : 0 < 2 ^ (64 * ((L + 7) / 8)) := Nat.two_pow_pos _
        have hlow := wv_add s₁.mem B (slot w aR) ((L + 7) / 8) (w + 2 - (L + 7) / 8)
        rw [show (L + 7) / 8 + (w + 2 - (L + 7) / 8) = w + 2 by omega, hz₁] at hlow
        have hh : wv s₁.mem B (slot w aR + 8 * ((L + 7) / 8)) (w + 2 - (L + 7) / 8) = 0 := by
          rcases Nat.eq_zero_or_pos (wv s₁.mem B (slot w aR + 8 * ((L + 7) / 8)) (w + 2 - (L + 7) / 8)) with h | h
          · exact h
          · have := Nat.le_mul_of_pos_right (2 ^ (64 * ((L + 7) / 8))) h; omega
        have e3 := wv_add s₁.mem B (slot w aR + 8 * ((L + 7) / 8)) (w - (L + 7) / 8) 2
        rw [show w - (L + 7) / 8 + 2 = w + 2 - (L + 7) / 8 by omega, hh] at e3
        omega
      rw [← h0]
      have f1 : wv t.mem B (slot w aR + 8 * ((L + 7) / 8)) (w - (L + 7) / 8) =
          wv s₆.mem B (slot w aR + 8 * ((L + 7) / 8)) (w - (L + 7) / 8) :=
        ft.wv_eq (fun r hr => by
          simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)
      rw [f1, hm₆]
      rw [ho₅.wv (by omega) (by omega), hm₄, hm₃, hm₂]
    refine ⟨⟨hst, (kt.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hdi₅), at₆.hdr (by rw [hm₆]; exact hH₅)⟩,
      fun hMb hM0 hq => ?_, aall, k.mono (by decide)⟩
    have e := wv_add t.mem B (slot w aR) ((L + 7) / 8) (w - (L + 7) / 8)
    rw [show (L + 7) / 8 + (w - (L + 7) / 8) = w by omega, hHi, Nat.mul_zero, Nat.add_zero] at e
    rw [e, hv ⟨hMb, hq⟩ (by rw [hM' hMb]; exact hM0), hAcc N (Nat.le_refl _), hM' hMb]

end VG.Proof.Rsa.X86_64.Key
