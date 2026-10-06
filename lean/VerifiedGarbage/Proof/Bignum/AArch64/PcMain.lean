import VerifiedGarbage.Proof.Bignum.AArch64.PubFail

/-!
# `vg_rsa_public_precompute` on AArch64: the computation for a valid modulus

`main`, from the header that `entry` leaves, for a valid modulus `m` of `w`
words: `m` and `R² mod m` to `pre`, and 1 returned (`pcMain_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem seqs_one (c : Prog isa) : seqs [c] = c := rfl

theorem pcMain_eq (M : Mont) : Precompute.main M.mm = seqs (pcLoad ++ (r2Steps M.mm ++ Precompute.pcOut)) := rfl

/-- `pcOut`: the arrays of `m` and `R² mod m` to `pre`, and 1 returned. -/
theorem pcOut_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {op : Addr} {N R : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30)
    (hO : word s.mem B (8 * sOut) = op) (hn : wv s.mem B (slot w aN) w = N)
    (hr : wv s.mem B (slot w aR2) w = R)
    (hpw : ∀ i < 2 * w, InRegions s.wr (off op (8 * i)) 8)
    (hps : ∀ i < 16 * w, Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (seqs Precompute.pcOut) s fun t =>
      PcPost s t B Z w op (Spec.Rsa.toWords N w ++ Spec.Rsa.toWords R w) true := by
  have hs := hg.scr
  have hnw := hs.nowrap
  have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := w) (show 0 < 8 by decide)
  have hsN := slot_le (w := w) (show aN < 8 by decide)
  have hsR := slot_le (w := w) (show aR2 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  -- A byte of the working space is past `pre`'s `16 w` bytes.
  have hsep : ∀ x, ofs B x < Z → 16 * w ≤ ofs op x := fun x hx => le_ofs_of_sep hps hx
  have hsepw : ∀ e, e + 8 * w ≤ Z → ∀ j < w, ∀ b < 8,
      16 * w ≤ ofs op (off B (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb =>
    hsep _ (by rw [ofs_off B (by omega)]; omega)
  unfold Precompute.pcOut
  refine WP.seq (WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x16 = off B (slot w aN) ∧ t.gpr .x17 = off op 0 ∧ t.mem = s.mem) (by
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
      hdr_enc (show sOut < 32 by decide), hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
      hg.hdr.hw, hg.hdr.harr aN (by decide), hO]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h12, h16, h17, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyWords_ok h16 h17 h12 hw (by omega) (by omega)
    (fun j hj => by rw [k₁.rd, k₁.wr]; exact hs.ld (by omega))
    (fun j hj => by rw [k₁.wr, Nat.zero_add]; exact hpw j (by omega))
    (fun j hj b hb => Or.inr (by have := hsepw (slot w aN) (by omega) j hj b hb; omega)))
    fun t₂ ⟨_, hc₂, ho₂, _, h17₂, k₂⟩ => ?_)
  rw [hm₁] at hc₂ ho₂
  -- The working space is as it was.
  have hin₂ : ∀ x, ofs B x < Z → t₂.mem x = s.mem x := fun x hx =>
    ho₂ x (Or.inr (by have := hsep x hx; omega))
  have hword₂ : ∀ d, d + 8 ≤ Z → word t₂.mem B d = word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hin₂ _ (by rw [ofs_off B (d := d) (i := b) (by omega)]; omega)
  have k12 := k₁.trans k₂
  have h0₂ : t₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans hg.x0
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.rd, k12.wr]; exact hl i hi
  refine WP.seq (WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off B (slot w aR2) ∧ t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show sArr aR2 < 32 by decide), hl₂ (sArr aR2) (by decide),
      hword₂ _ (show 8 * sArr aR2 + 8 ≤ Z by unfold sArr aR2; omega), hg.hdr.harr aR2 (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h16₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have h12₃ : t₃.gpr .x12 = BitVec.ofNat 64 w := (k₃.gpr .x12 (by decide)).trans h12₂
  have h17₃ : t₃.gpr .x17 = off op (8 * w) := by rw [k₃.gpr .x17 (by decide), h17₂, Nat.zero_add]
  refine WP.seq (WP.mono (copyWords_ok h16₃ h17₃ h12₃ hw (by omega) (by omega)
    (fun j hj => by rw [k13.rd, k13.wr]; exact hs.ld (by omega))
    (fun j hj => by
      rw [k13.wr, show 8 * w + 8 * j = 8 * (w + j) by omega]; exact hpw (w + j) (by omega))
    (fun j hj b hb => Or.inr (by have := hsepw (slot w aR2) (by omega) j hj b hb; omega)))
    fun t₄ ⟨_, hc₄, ho₄, _, _, k₄⟩ => ?_)
  rw [hm₃] at hc₄ ho₄
  have k14 := k13.trans k₄
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = BitVec.ofNat 64 1 ∧ t.mem = t₄.mem) (by brun)
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨hx, hm⟩, k₅⟩ => ⟨?_, hx, ?_, (k14.trans k₅).mono (by decide)⟩
  · rw [hm]
    refine wordsAt_two (fun i hi => ?_) (fun i hi => ?_)
    · have h := hc₂ i hi
      rw [Nat.zero_add] at h
      rw [ho₄.word (by omega) (by omega), h, ← hn]
      exact word_eq_ofNat _ _ _ _ hi
    · rw [hc₄ i hi, hword₂ _ (by omega), ← hr]
      exact word_eq_ofNat _ _ _ _ hi
  · intro x _ hx
    rw [hm, ho₄ x (Or.inr (by omega)), ho₂ x (Or.inr (by omega))]

/-- `main`, for a valid modulus `m`: `m` and `R² mod m` to `pre`, and 1
returned. -/
theorem pcMain_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hN : word s.mem B (8 * sN) = np) (hnb : Src s B Z np nb) (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hpw : ∀ i < 2 * ((k + 7) / 8), InRegions s.wr (off op (8 * i)) 8)
    (hps : ∀ i < 16 * ((k + 7) / 8), Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (Precompute.main M.mm) s fun t => ∃ ws, Spec.Rsa.publicPrecompute nb = some ws ∧
      PcPost s t B Z ((k + 7) / 8) op ws true := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv hk1
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  rw [pcMain_eq M]
  refine wp_seqs_append (by simp [pcLoad]) (by simp [r2Steps])
    (WP.mono (pcLoad_ok hs h0 hZ (by omega) (by omega) hK hN hnb hnl hodd)
      fun t₁ ⟨minv, hg₁, hn₁, hinv₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [r2Steps]) (by simp [Precompute.pcOut])
    (WP.mono (r2_ok M hg₁ hZ (by omega) (by omega) hn₁ hinv₁ hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have x₁₂ := (Fixed.of_frm f₁ (pcLoadRanges_fixed _)).trans (Fixed.of_frm f₂ (r2Ranges_fixed _))
  have i₁₂ : InScr B Z s.mem t₂.mem := (InScr.of_frm f₁ fun r hr => Nat.le_trans (pcLoadRanges_le _ r hr) hZ).trans
    (InScr.of_frm f₂ fun r hr => Nat.le_trans (r2Ranges_le _ r hr) hZ)
  have k₁₂ := k₁.trans k₂
  have hR : wv t₂.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) =
      2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    rw [← Nat.mod_eq_of_lt hlt₂, hr₂, ← Nat.pow_add]; congr 2; omega
  refine WP.mono (pcOut_ok hg₂ hZ (by omega) (by omega) (by rw [x₁₂ sOut (by decide)]; exact hO)
    (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hn₁) hR
    (fun i hi => by rw [k₁₂.wr]; exact hpw i hi) hps)
    fun t hp => ⟨_, publicPrecompute_some hnl hv, hp.words, hp.x0,
      fun x hx hx' => by rw [hp.frame x hx hx', i₁₂ x hx], (k₁₂.trans hp.keep).mono (by decide)⟩

end VG.Proof.Bignum.AArch64
