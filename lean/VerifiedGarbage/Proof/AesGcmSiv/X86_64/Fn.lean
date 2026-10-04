import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Cmp

/-!
# AES-GCM-SIV on x86-64: the keys, and what the pieces write

Untrusted: everything here is checked by Lean. `keys` derives the message
keys, expands the encryption key and sets up GHASH's key and accumulator
(`keys_ok`). Every piece but counter mode and the mask writes only parts of
`W` and the stack below `SP` (`mutW`), which miss the buffers, the key
schedule and what the entry keeps in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- What the pieces before counter mode write. -/
abbrev mutW (W SP : Addr) : List Region := [wA W, wO W, wC W, below SP 8]

theorem mutW_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ mutW W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' :=
  fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp, fun _ h => h⟩

/-- `⟨W + d, k⟩` within `[0, 160)` of `W`. -/
theorem sub_wA {W SP : Addr} {d k : Nat} (h : d + k ≤ 160) :
    ∃ r' ∈ mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wA W, by simp, Offset.sub_base W h⟩

/-- `⟨W + d, k⟩` within `[512, 4096)` of `W`. -/
theorem sub_wC {W SP : Addr} {d k : Nat} (h₁ : 512 ≤ d) (h₂ : d + k ≤ 4096) :
    ∃ r' ∈ mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wC W, by simp, Offset.sub W h₁ (by omega)⟩

theorem sub_stk {W SP : Addr} : ∃ r' ∈ mutW W SP, Region.Sub (below SP 8) r' := ⟨_, by simp, fun _ h => h⟩

theorem buf_mutW {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (mutW W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem mutW_frame {K W SP : Addr} (L : Lay K W SP) {d k : Nat}
    (hd : 160 ≤ d ∧ d + k ≤ 208 ∨ 216 ≤ d ∧ d + k ≤ 512) :
    ∀ r ∈ mutW W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 160) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W SP : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 128⟩, wC W, below SP 8]

theorem keyR_mutW (W SP : Addr) : ∀ r ∈ keyR W SP, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact sub_stk

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (K W SP : Addr) (R : Nat) (N : Addr) (σ t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (keyR W SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).1 =
    bytesAt t.mem (W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 512) R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
    GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem)
    (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) :
    WP isa (keys v.callees) σ (KeysPost K W SP R N σ) := by
  refine WP.seq (WP.mono (derive_ok v L hR E S hN hDW) fun t₂ I => ?_)
  have f₂ : Frame (keyR W SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have S₂ := slots_mut L hDW ((f₂.sub (keyR_mutW W SP)).sub (mutW_mut W SP D n)) S
  refine WP.seq (WP.mono (expand_ok v L hR I.env S₂) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hG, hY, f₄, hg₄, hrd₄, hwr₄⟩ := hkey_ok X.env
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  have fX := X.frame
  have f₃ : Frame (keyR W SP) t₂.mem t₃.mem := fX.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dA : ∀ q ∈ [(⟨W + BitVec.ofNat 64 512, 240⟩ : Region), ⟨W + BitVec.ofNat 64 2048, 512⟩, below SP 8],
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have d64 : ∀ q ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hA₄ : bytesAt t₄.mem (W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (W + BitVec.ofNat 64 16) 16 := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₄ d64 (by decide), Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)]
  have hK := I.keys hR
  refine ⟨X.env.keep (fun r hr => ?_) hrd₄ hwr₄, by rw [hrd₄, X.rd, I.rd], by rw [hwr₄, X.wr, I.wr],
    (f₂.trans f₃).trans (f₄.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩),
    ?_, ?_,
    by rw [hG, hA₄, ← Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)], hY⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by simp)
  · rw [hK, hA₄]
  · rw [ctxCiph_frame f₄ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide), X.ciph, hK]

end VG.Proof.AesGcmSiv.X86_64
