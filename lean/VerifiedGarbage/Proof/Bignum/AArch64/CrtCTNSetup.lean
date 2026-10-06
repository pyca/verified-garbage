import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain

/-!
# RSA with the CRT on AArch64: `n`'s setup in constant time

`nSetup` is `pcLoad`, `nInput`, `r2Steps` and `c R mod n` (`nSetup_ct`),
each constant time for its correctness lemma's hypotheses, which the one
before it gives, as `nPart_ok` runs them; `-n⁻¹` is the same in both runs,
as `n` is.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- After `pcLoad`: `nInput_ok`'s hypotheses and what `r2_ok` needs. -/
def NS1 (p : CrtPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (xb : List Byte), Good t p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word t.mem p.B (8 * Public.sK) = BitVec.ofNat 64 p.k ∧ word t.mem p.B (8 * Public.sIn) = p.ip ∧
    Src t p.B p.Z p.ip xb ∧ xb.length = p.k ∧ wv t.mem p.B (slot p.w Public.aN) p.w = p.N ∧
    ((word t.mem p.B (slot p.w Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.w - 1)) ≤ p.N

/-- After `nInput`: `r2_ok`'s hypotheses, for some `-n⁻¹`. -/
def NS2 (p : CrtPub) (t : State) : Prop := ∃ minv : BitVec 64, R2Pre ⟨⟨p.B, p.Z, p.w, minv⟩, p.N⟩ t

theorem stage0_pcl {p : CrtPub} {s : State} (h : Stage R0 p s) : PcL ⟨p.B, p.Z, p.k, p.op, p.np, p.nb⟩ s := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, rfl⟩ := h
  have hZq := h.z
  exact ⟨h.scr, h.x0, show slot ((p.k + 7) / 8) 8 ≤ p.Z by unfold offQ at hZq; omega, h.k1, h.k2, h.hK, h.hN,
    h.n, h.nl, hv⟩

theorem ns1_ok {p : CrtPub} {s : State} (h : Stage R0 p s) : WP isa (seqs pcLoad) s (NS1 p) := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, rfl⟩ := h
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((p.k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ p.Z :=
    fun h' r hr => (h' r hr).trans hZ
  refine WP.mono (pcLoad_ok h.scr h.x0 hZ (by omega) (by omega) h.hK h.hN h.n h.nl hodd)
    fun t₁ ⟨minv, hg₁, hn₁, hi₁, f₁, k₁⟩ => ?_
  have f₁' : Frm p.B (setupRanges p.w) s.mem t₁.mem := f₁.mono (by simp [pcLoadRanges, setupRanges, loadRanges])
  have hh₁ := HFix.of_frm f₁' (keepsHdr_setupRanges _)
  exact ⟨minv, xb, hg₁, hZ, hk1, hk2, by rw [hh₁ _ (by decide) (by decide)]; exact h.hK,
    by rw [hh₁ _ (by decide) (by decide)]; exact h.hIn, h.x.congrK (InScr.of_frm f₁' (hZs (setupRanges_le _))) k₁,
    h.xl, hn₁, hi₁, hodd, hlo⟩

theorem ns2_ok {p : CrtPub} {s : State} (h : NS1 p s) : WP isa (seqs nInput) s (NS2 p) := by
  obtain ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl, hn, hi, hodd, hlo⟩ := h
  unfold NS2 R2Pre GoodL
  simp only [CrtPub.w] at *
  have hnw := hg.scr.nowrap
  refine WP.mono (nInput_ok hg hZ hk1 hk2 hK hIn hx hxl hn) fun t ⟨hg₂, _, _, _, f₂, _⟩ => ?_
  have hN₂ : wv t.mem p.B (slot ((p.k + 7) / 8) Public.aN) ((p.k + 7) / 8) = p.N := by
    rw [f₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aX by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aOne by decide)
      have := hdr_lt_slot ((p.k + 7) / 8) Public.aN (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega)
      (by have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide); omega)]; exact hn
  have hI₂ : ((word t.mem p.B (slot ((p.k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aX by decide)
      have := slot_sep (w := (p.k + 7) / 8) (show Public.aN ≠ Public.aOne by decide)
      have := hdr_lt_slot ((p.k + 7) / 8) Public.aN (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega)
      (by have := slot_le (w := (p.k + 7) / 8) (show Public.aN < 8 by decide); omega)]; exact hi
  exact ⟨minv, ⟨hg₂, hZ⟩, by omega, by omega, hN₂, hI₂, hodd, hlo⟩

/-- `-n⁻¹` is the same in runs that agree on `n`. -/
theorem r2_minv {B : Addr} {Z w : Nat} {N : Nat} {m₁ m₂ : BitVec 64} {s₁ s₂ : State}
    (h₁ : R2Pre ⟨⟨B, Z, w, m₁⟩, N⟩ s₁) (h₂ : R2Pre ⟨⟨B, Z, w, m₂⟩, N⟩ s₂) : m₁ = m₂ := by
  obtain ⟨-, hw, -, n₁, i₁, hodd, -⟩ := h₁
  obtain ⟨-, -, -, n₂, i₂, -, -⟩ := h₂
  have e : ∀ {t : State}, wv t.mem B (slot w Public.aN) w = N →
      (word t.mem B (slot w Public.aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ (show 1 ≤ w by simp only at hw; omega), h]
  rw [e n₁] at i₁
  rw [e n₂] at i₂
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i₁ i₂

/-- `n`'s setup leaks the same in runs that agree on the public data. -/
theorem nSetup_ct (M : Mont) : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True := by
  rw [nSetup_eq]
  refine RelCT.seqs_append (by simp [pcLoad]) (by simp [nInput]) (RelCT.seq (R := Two NS1) (two_post
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.k, p.op, p.np, p.nb⟩ : PcPub)) (fun _ _ h => stage0_pcl h) pcLoad_ct)
    fun _ _ h => ns1_ok h) ?_)
  refine RelCT.seqs_append (by simp [nInput]) (by simp [r2Steps]) (RelCT.seq (R := Two NS2) (two_post
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.k, p.ip⟩ : NIPub))
      (fun _ _ ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl, _⟩ => ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl⟩)
      nInput_ct) fun _ _ h => ns2_ok h) ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp)
    (RelCT.seq (R := Two fun (p : CrtPub) t => GoodW ⟨p.B, p.Z, p.w⟩ t) (two_post
      ((r2_ct M).mono (fun _ _ h => two_bind (fun (p : CrtPub) s₁ s₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ => by
        obtain rfl := r2_minv h₁ h₂
        exact ⟨_, h₁, h₂⟩) h) fun _ _ h => h)
      fun p s hh => ?_) ?_)
  · obtain ⟨minv, ⟨hg, hZ⟩, hw, hw30, hn, hinv, hodd, hlo⟩ := hh
    exact WP.mono (r2_ok M hg hZ hw hw30 hn hinv hodd hlo) fun t ⟨hg', _⟩ => ⟨minv, hg', hZ⟩
  simp only [seqs]
  exact two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h) (M.ct (by unfold MmUse; decide))

end VG.Proof.Bignum.AArch64
