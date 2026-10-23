module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Fused
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Stash
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Prologue
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages

/-!
# ChaCha20-Poly1305 on AArch64, 257 to 511 bytes: the parts

`ShortRest.first` XORs the first 256 bytes with the keystream of
`Short.prologue`, and `ShortRest.rest` the rest with the stream from the
state `stash` copied; together they encrypt the data from counter 1. After
the prologue, the code branches to `Short.lean`'s for up to 256 bytes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.ShortRest

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.ShortRest
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_mov wp_movz wp_subImm)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ks5 ks5_eq kp' xorKsAt_ok)
open VG.Spec.ChaCha20 (stateAt keystream serialize block initState)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data after the first 256 bytes. -/
abbrev restR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 256, L s₀ - 256⟩

theorem restR_sub {s₀ : State} (hL : 256 ≤ L s₀) : Region.Sub (restR s₀) (dR s₀) :=
  Offset.sub_base _ (by omega)

/-- The regions the stream writes. -/
abbrev streamR (s₀ : State) : List Region := [sub s₀ 64 64, restR s₀, sub s₀ 128 320]

theorem streamR_work {s₀ : State} (hL : 256 ≤ L s₀) : ∀ r ∈ streamR s₀, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · exact ⟨dR s₀, by simp, restR_sub hL⟩
  · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩

theorem streamR_saved {s₀ : State} (hp : APre e s₀) (hL : 256 ≤ L s₀) : ∀ r ∈ streamR s₀, (sub s₀ 576 56).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (restR_sub hL)
  · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## The state copied -/

theorem stash_ok {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)) :
    WP isa (.block stash) s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 64 64] s s' ∧
      stateAt s'.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
  rw [stash_eq]
  refine WP.mono (WP.withSp (stashN_ok hp h.x21 h.rd h.wr 16 (Nat.le_refl _))) fun s' ⟨c, sp⟩ => ?_
  have k : Kept [sub s₀ 64 64] s s' :=
    ⟨fun r hr _ => c.gpr r (by rintro rfl; exact absurd hr (by decide)), sp, c.rd, c.wr, c.frame⟩
  refine ⟨h.step k (fun r hr => ?_) (fun r hr => ?_), k, stateAt_copy c hst⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## The first 256 bytes -/

theorem first_ok {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) (hL : 256 ≤ L s₀) :
    WP isa first s fun s' => Inv s₀ s' ∧ Kept [dR s₀] s s' ∧
      (∀ i < 256, s'.mem (dp s₀ + BitVec.ofNat 64 i) =
        s.mem (dp s₀ + BitVec.ofNat 64 i) ^^^ s.mem (kp' s₀ + BitVec.ofNat 64 i)) ∧
      Frame [⟨dp s₀, 256⟩] s.mem s'.mem := by
  unfold first
  have hstart : WP isa (.block [mov .x14 .x23, .movz .x .x23 256 0]) s fun s' =>
      s'.gpr .x14 = s.gpr .x23 ∧ s'.gpr .x23 = BitVec.ofNat 64 256 ∧
      (∀ r, r ≠ .x14 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
    wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl,
        fun r h14 h23 => by rw [u₂.other r h23, u₁.other r h14], by rw [u₂.mem, u₁.mem],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  refine WP.seq ((WP.withSp hstart).mono fun s₁ h₁ => ?_)
  obtain ⟨⟨x14₁, x23₁, g₁, m₁, rd₁, wr₁⟩, sp₁⟩ := h₁
  refine WP.seq ((xorKsAt_ok hp (o := 0) (n := 256) (by decide) (by omega)
    (by rw [g₁ _ (by decide) (by decide), h.x21]) (by rw [g₁ _ (by decide) (by decide), h.x22, BitVec.add_zero])
    x23₁ (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])).mono fun s₂ ⟨k₂, x₂, f₂, g₂⟩ => ?_)
  have hlast : WP isa (.block [mov .x23 .x14]) s₂ fun s' => Upd s₂ s' .x23 (s₂.gpr .x14) :=
    wp_mov fun s' u => WP.block_nil u
  refine (WP.withSp hlast).mono fun s₃ ⟨u₃, sp₃⟩ => ?_
  have k : Kept [dR s₀] s s₃ := by
    refine ⟨fun r hr h30 => ?_, by rw [sp₃, k₂.sp, sp₁], by rw [u₃.rd, k₂.rd, rd₁],
      by rw [u₃.wr, k₂.wr, wr₁], ?_⟩
    · by_cases h23 : r = .x23
      · subst h23
        rw [u₃.gpr, g₂ _ (by decide), x14₁]
      · have h14 : r ≠ .x14 := by rintro rfl; exact absurd hr (by decide)
        rw [u₃.other r h23, k₂.cs r hr h30, g₁ r h14 h23]
    · rw [u₃.mem, ← m₁]; exact k₂.frame
  refine ⟨h.step k (fun r hr => ?_) (Short.dR_inv hp).2, k, fun i hi => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩
  · have := x₂ i hi
    rw [Nat.zero_add] at this
    rw [u₃.mem, this, m₁]
  · rw [u₃.mem, ← m₁]
    simpa only [BitVec.add_zero] using f₂

/-! ## The rest -/

theorem restArgs_ok {s₀ s : State} (h : Inv s₀ s) (hL : 256 ≤ L s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x22 256, .subImm .x .x2 .x23 256,
      .addImm .x .x3 .x21 128]) s fun s' =>
      s'.gpr .x0 = off (cx s₀) 64 ∧ s'.gpr .x1 = dp s₀ + BitVec.ofNat 64 256 ∧
      s'.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256) ∧ s'.gpr .x3 = off (cx s₀) 128 ∧
      Kept [] s s' ∧ s'.mem = s.mem := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x22 256, .subImm .x .x2 .x23 256,
      .addImm .x .x3 .x21 128]) s fun s₄ =>
      s₄.gpr .x0 = off (cx s₀) 64 ∧ s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 256 ∧
      s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256) ∧ s₄.gpr .x3 = off (cx s₀) 128 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s₄.gpr r = s.gpr r) ∧ s₄.mem = s.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ =>
    wp_subImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x21],
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x22],
       by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.x23,
         VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hL],
       by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x21],
       fun r h0 h1 h2 h3 => by rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h0],
       by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
       by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine (WP.withSp core).mono fun s' ⟨⟨x0, x1, x2, x3, g, m, rd, wr⟩, sp'⟩ => ?_
  refine ⟨x0, x1, x2, x3, ⟨fun r hr _ => g r ?_ ?_ ?_ ?_, sp', rd, wr, by rw [m]; exact Frame.refl _ _⟩, m⟩ <;>
    rintro rfl <;> exact absurd hr (by decide)

theorem rest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s)
    (hL : 256 ≤ L s₀) (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀)) :
    WP isa (rest v.callee) s fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ Inv s₀ s' ∧
      Kept (streamR s₀) s s' ∧
      Spec.ChaCha20.bytesAt s'.mem (dp s₀ + BitVec.ofNat 64 256) (L s₀ - 256) =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (dp s₀ + BitVec.ofNat 64 256) (L s₀ - 256))
          (keystream (initState (K s₀) 5 (N s₀)) (L s₀ - 256)) := by
  unfold rest
  refine WP.seq (WP.mono (WP.preservedV (restArgs_ok h hL) (by lit_decide))
    fun s₁ ⟨⟨x0₁, x1₁, x2₁, x3₁, k₁, m₁⟩, v₁⟩ => ?_)
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have wd := hp.wrap_d
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 256, L s₀ - 256⟩, ⟨off (cx s₀) 128, 320⟩]
      s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega⟩
    · exact ⟨dR s₀, by rw [wr₁]; exact hp.d_wr, 256, rfl, by show 256 + (L s₀ - 256) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₁]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  have hn : L s₀ - 256 < 2 ^ 64 := by have := (s₀.gpr .x5).isLt; simp only [L]; omega
  refine VG.Proof.ChaCha20Poly1305.AArch64.xor_call v x0₁ x1₁ x2₁ x3₁ hn
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right (restR_sub hL))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left (restR_sub hL))
    (by have := Short.toNat_add_le (dp s₀) 256; simp only [L, dp] at wd hL this ⊢; omega)
    (Covers.right hw) hw fun s₂ v₂ k₂ data₂ => ?_
  have k : Kept (streamR s₀) s s₂ := (k₁.sub fun r hr => absurd hr List.not_mem_nil).trans k₂
  refine ⟨fun r hr => (v₂ r hr).trans (v₁ r hr), h.step k (streamR_work hL) (streamR_saved hp hL), k, ?_⟩
  rw [data₂, m₁, hst]

/-! ## The data encrypted -/

/-- Byte `i` of the data is in its region. -/
theorem dR_byte {s₀ : State} (hp : APre e s₀) {i : Nat} (hi : i < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
  have := hp.wrap_d
  have h := Offset.contains (dp s₀) (d := i) (n := 1) (e := 0) (k := L s₀) (by omega) (by omega)
    (by simp only [L, dp] at this hi ⊢; omega)
  simpa only [BitVec.add_zero] using h

/-- Byte `i < 256` of the data is outside what the stream writes. -/
theorem first_out {s₀ : State} (hp : APre e s₀) (hL : 256 ≤ L s₀) {i : Nat} (hi : i < 256) :
    ∀ r ∈ streamR s₀, ¬ r.Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
  have hb := dR_byte hp (i := i) (by omega)
  intro r hr hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))) _ hc hb
  · have := hp.wrap_d
    have hd := Offset.base_disjoint (dp s₀) (e := 256) (n := L s₀ - 256) (k := 256) (Nat.le_refl _)
      (by simp only [L, dp] at this hL ⊢; omega)
    have h1 := Offset.contains (dp s₀) (d := i) (n := 1) (e := 0) (k := 256) (by omega) (by omega) (by omega)
    rw [BitVec.add_zero] at h1
    exact hd _ h1 hc
  · exact (hp.c_d.sub_left (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) _ hc hb

/-- Byte `i ≥ 256` of the data is outside the first 256. -/
theorem rest_out {s₀ : State} (hp : APre e s₀) {i : Nat} (h₁ : 256 ≤ i) (h₂ : i < L s₀) :
    ∀ r ∈ [(⟨dp s₀, 256⟩ : Region)], ¬ r.Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
  have := hp.wrap_d
  intro r hr hc
  simp only [List.mem_singleton] at hr; subst hr
  have hd := Offset.base_disjoint (dp s₀) (e := i) (n := 1) (k := 256) h₁
    (by simp only [L, dp] at this h₂ ⊢; omega)
  have h1 := Offset.contains (dp s₀) (d := i) (n := 1) (e := i) (k := 1) (by omega) (by omega)
    (by simp only [L, dp] at this h₂ ⊢; omega)
  exact hd _ hc h1

/-- The keystream from counter 5 continues the one from counter 1 after 256 bytes. -/
theorem ks_rest (key nonce : List Byte) {n i : Nat} (h₁ : 256 ≤ i) (h₂ : i < n) :
    (keystream (initState key 5 nonce) (n - 256)).getD (i - 256) 0 =
      (keystream (initState key 1 nonce) n).getD i 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega), VG.Proof.ChaCha20.keystream_getD _ h₂,
    VG.Proof.ChaCha20Poly1305.ctr_initState, VG.Proof.ChaCha20Poly1305.ctr_initState,
    show (i - 256) % 64 = i % 64 by omega]
  congr 4
  rw [show i / 64 = (i - 256) / 64 + 4 by omega, BitVec.ofNat_add]
  bv_omega

theorem ct_rest {s₀ : State} (hp : APre e s₀) (hL : 256 ≤ L s₀) {m₃ m₄ m₅ : Mem}
    (hD : bytesAt m₃ (dp s₀) (L s₀) = D s₀)
    (hk : ∀ i < 256, m₃ (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i))
    (hx : ∀ i < 256, m₄ (dp s₀ + BitVec.ofNat 64 i) =
      m₃ (dp s₀ + BitVec.ofNat 64 i) ^^^ m₃ (kp' s₀ + BitVec.ofNat 64 i))
    (hf₄ : Frame [⟨dp s₀, 256⟩] m₃ m₄)
    (hr : Spec.ChaCha20.bytesAt m₅ (dp s₀ + BitVec.ofNat 64 256) (L s₀ - 256) =
      List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt m₄ (dp s₀ + BitVec.ofNat 64 256) (L s₀ - 256))
        (keystream (initState (K s₀) 5 (N s₀)) (L s₀ - 256)))
    (hf₅ : Frame (streamR s₀) m₄ m₅) :
    bytesAt m₅ (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  have hDl : (D s₀).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
  have hDi : ∀ i < L s₀, (D s₀).getD i 0 = m₃ (dp s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [← hD]; exact VG.Proof.ChaCha20.bytesAt_getD _ _ hi
  rw [encrypt_eq]
  apply List.ext_getElem
  · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
  · intro i h₁ h₂
    have hiL : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
    have e1 : (bytesAt m₅ (dp s₀) (L s₀))[i] = m₅ (dp s₀ + BitVec.ofNat 64 i) := by simp [bytesAt]
    have e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = m₃ (dp s₀ + BitVec.ofNat 64 i) := fun h => by
      rw [← List.getElem_of_eq hD (by rw [VG.Proof.Poly1305.length_bytesAt]; exact hiL)]
      simp [bytesAt]
    have e3 : ∀ h : i < (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length).length,
        (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length)[i] =
          (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun h => by
      rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, hDl]
    rw [List.getElem_zipWith, e1, e2, e3]
    by_cases hi : i < 256
    · rw [hf₅ _ (first_out hp hL hi), hx i hi, hk i hi, ks5_eq s₀ (n := L s₀) hiL]
    · have hi' : 256 ≤ i := by omega
      have x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) hr (j := i - 256)
        (by omega)
      rw [show dp s₀ + BitVec.ofNat 64 256 + BitVec.ofNat 64 (i - 256) = dp s₀ + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hi']] at x
      rw [x, hf₄ _ (rest_out hp hi' hiL), ks_rest _ _ hi' hiL]

/-! ## `seal` and `open` up to the tag -/

/-- After the prologue. -/
theorem sealAfter_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ s₁ : State} (hp : APre true s₀)
    (hL₁ : 256 ≤ L s₀) (h₁ : Short.PostP s₀ s₁)
    (v₁ : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    WP isa (ShortRest.sealAfter v.callee) s₁ (MainS s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  have hAL := (Nat.le_of_lt (s₀.gpr .x3).isLt)
  unfold ShortRest.sealAfter
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.inv.frame (by rdisj_all) hAL
  refine WP.seq (WP.mono (WP.preservedV (stash_ok hp h₁.inv h₁.st0) (by lit_decide))
    fun s₂ ⟨⟨i₂, k₂, st₂⟩, v₂⟩ => ?_)
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  have K₂ : ∀ i < 256, s₂.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [Short.ks_frame k₂.frame (by rdisj_all) hi]
    exact Short.ks_post h₁.ks hi
  refine WP.seq (WP.mono (WP.preservedV (first_ok hp i₂ hL₁) (by lit_decide))
    fun s₃ ⟨⟨i₃, k₃, x₃, f₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), st₂]
  refine WP.seq (WP.mono (rest_ok v hp i₃ hL₁ st₃) fun s₄ ⟨v₄, i₄, k₄, r₄⟩ => ?_)
  have ct₄ := ct_rest hp hL₁ D₂ K₂ x₃ f₃ r₄ k₄.frame
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₄) (by lit_decide)) fun s₅ ⟨⟨i₅, k₅, len₅⟩, v₅⟩ => ?_)
  refine WP.mono (WP.preservedV (Fused.macAll_ok hp (srcA hp) (srcD hp) i₅) (by lit_decide))
    fun s₆ ⟨⟨k₆, r₆⟩, v₆⟩ => ?_
  have i₆ := mac_inv i₅ k₆
  have hd4 : ∀ r ∈ streamR s₀, (sub s₀ 448 128).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (restR_sub hL₁)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have R₄ : Repr s₄.mem (off (cx s₀) 448) (otk s₀) [] :=
    Repr.frame k₄.frame hd4 (Repr.frame k₃.frame (by rdisj_all) (Repr.frame k₂.frame (by rdisj_all) h₁.poly))
  have A₄ : bytesAt s₄.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₄.frame (fun r hr => ?_) hAL, bytesAt_frame k₃.frame (by rdisj_all) hAL,
      bytesAt_frame k₂.frame (by rdisj_all) hAL, hA]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm.sub_right (sub_ctx s₀ (by lit_omega))
    · exact hp.a_d.sub_right (restR_sub hL₁)
    · exact hp.c_a.symm.sub_right (sub_ctx s₀ (by lit_omega))
  have A₅ : bytesAt s₅.mem (ad s₀) (AL s₀) = A s₀ := by rw [bytesAt_frame k₅.frame (by rdisj_all) hAL, A₄]
  have ct₅ : bytesAt s₅.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [bytesAt_frame k₅.frame (by rdisj_all) hL', ct₄]
  have R₆ := r₆ (otk s₀) [] (Repr.frame k₅.frame (by rdisj_all) R₄)
  rw [A₅, ct₅, len₅] at R₆
  refine ⟨i₆.inv0, fun r hr => (v₆ r hr).trans ((v₅ r hr).trans
      ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))), ?_, ?_⟩
  · refine (congrArg (Repr s₆.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₆
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₆.frame (by rdisj_all) hL', ct₅]

/-- After the prologue. -/
theorem openAfter_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ s₁ : State} (hp : APre false s₀)
    (hL₁ : 256 ≤ L s₀) (h₁ : Short.PostP s₀ s₁)
    (v₁ : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    WP isa (ShortRest.openAfter v.callee) s₁ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  have hAL := (Nat.le_of_lt (s₀.gpr .x3).isLt)
  unfold ShortRest.openAfter
  refine WP.seq (WP.mono (WP.preservedV (stash_ok hp h₁.inv h₁.st0) (by lit_decide))
    fun s₂ ⟨⟨i₂, k₂, st₂⟩, v₂⟩ => ?_)
  have A₂ : bytesAt s₂.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hAL, bytesAt_frame h₁.inv.frame (by rdisj_all) hAL]
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have A₃ : bytesAt s₃.mem (ad s₀) (AL s₀) = A s₀ := by rw [bytesAt_frame k₃.frame (by rdisj_all) hAL, A₂]
  refine WP.seq (WP.mono (WP.preservedV (Fused.macAll_ok hp (srcA hp) (srcD hp) i₃) (by lit_decide))
    fun s₄ ⟨⟨k₄, r₄⟩, v₄⟩ => ?_)
  have i₄ := mac_inv i₃ k₄
  have R₄ := r₄ (otk s₀) [] (Repr.frame k₃.frame (by rdisj_all) (Repr.frame k₂.frame (by rdisj_all) h₁.poly))
  rw [A₃, D₃, len₃] at R₄
  have D₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame k₄.frame (by rdisj_all) hL', D₃]
  have K₄ : ∀ i < 256, s₄.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [Short.ks_frame k₄.frame (by rdisj_all) hi, Short.ks_frame k₃.frame (by rdisj_all) hi,
      Short.ks_frame k₂.frame (by rdisj_all) hi]
    exact Short.ks_post h₁.ks hi
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
    rw [stateAt_frame k₄.frame (by rdisj_all), stateAt_frame k₃.frame (by rdisj_all), st₂]
  refine WP.seq (WP.mono (WP.preservedV (first_ok hp i₄ hL₁) (by lit_decide))
    fun s₅ ⟨⟨i₅, k₅, x₅, f₅⟩, v₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
    rw [stateAt_frame k₅.frame (by rdisj_all), st₄]
  refine WP.seq (WP.mono (rest_ok v hp i₅ hL₁ st₅) fun s₆ ⟨v₆, i₆, k₆, r₆⟩ => ?_)
  have pt₆ := ct_rest hp hL₁ D₄ K₄ x₅ f₅ r₆ k₆.frame
  refine WP.mono (WP.preservedV (finalizeTo_ok hp i₆ (out := 48) (by omega)) (by lit_decide))
    fun s₇ ⟨⟨k₇, tag₇⟩, v₇⟩ => ?_
  have hd6 : ∀ r ∈ streamR s₀, (sub s₀ 448 128).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (restR_sub hL₁)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have T₇ := tag₇ _ _ (Repr.frame k₆.frame hd6 (Repr.frame k₅.frame (by rdisj_all) R₄))
  refine ⟨i₆.inv0.step k₇ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₇ r hr).trans ((v₆ r hr).trans
      ((v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', pt₆]

/-! ## The branch on the length, after the prologue -/

/-- `s₁` but for `x9` and `x10` is still after the prologue. -/
theorem postP_agree {s₀ s₁ s₂ : State} (h : Short.Agree s₁ s₂) (hp : Short.PostP s₀ s₁) :
    Short.PostP s₀ s₂ := by
  obtain ⟨⟨x21, x22, x23, x24, x25, un, sp, rd, wr, sv, fr⟩, fine, poly, ks, st0⟩ := hp
  have hu : ∀ r ∈ untouched, r ≠ .x9 ∧ r ≠ .x10 := by decide
  refine ⟨⟨by rw [h.gpr _ (by decide) (by decide), x21], by rw [h.gpr _ (by decide) (by decide), x22],
    by rw [h.gpr _ (by decide) (by decide), x23], by rw [h.gpr _ (by decide) (by decide), x24],
    by rw [h.gpr _ (by decide) (by decide), x25],
    fun r hr => by rw [h.gpr r (hu r hr).1 (hu r hr).2, un r hr], by rw [h.sp, sp], by rw [h.rd, rd],
    by rw [h.wr, wr], by rw [h.mem]; exact sv, by rw [h.mem]; exact fr⟩,
    by rw [h.mem]; exact fine, by rw [h.mem]; exact poly, by rw [h.mem]; exact ks, by rw [h.mem]; exact st0⟩

/-- The value `split` leaves in `x9`. -/
abbrev splitVal (x : BitVec 64) : BitVec 64 := (x - BitVec.ofNat 64 1) >>> 8

/-- `x9`, zero iff `1 ≤ len ≤ 256`. -/
theorem split_ok (s₀ : State) :
    WP isa (.block split) s₀ fun s₁ => Short.Agree s₀ s₁ ∧ s₁.gpr .x9 = splitVal (s₀.gpr .x23) := by
  have h : WP isa (.block split) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = splitVal (s₀.gpr .x23) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr :=
    wp_subImm (by decide) fun s₁ u₁ => VG.Proof.ChaCha20.AArch64.Xor.wp_lsr (by decide) fun s₂ u₂ =>
      WP.block_nil
      ⟨fun r h9 _ => by rw [u₂.other r h9, u₁.other r h9],
        by rw [u₂.gpr, u₁.gpr],
        by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.withSp h) (by lit_decide))
    fun s₁ ⟨⟨⟨g, x9, m, rd, wr⟩, sp⟩, v⟩ => ⟨⟨g, m, v, sp, rd, wr⟩, x9⟩

theorem splitVal_eq {L : Nat} (h : L < 2 ^ 64) :
    (splitVal (BitVec.ofNat 64 L) == 0) = decide (1 ≤ L ∧ L ≤ 256) := by
  have hz : ∀ x : BitVec 64, (x == 0) = decide (x.toNat = 0) := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    · have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (x == 0) = false from beq_eq_false_iff_ne.mpr hx]
      simp [this]
  rw [hz]
  congr 1
  apply propext
  simp only [splitVal, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The branch: to `Short.lean`'s code iff `1 ≤ len ≤ 256`. -/
theorem split_eval {s₀ s₁ s₂ : State} (h₁ : Short.PostP s₀ s₁) (h : s₂.gpr .x9 = splitVal (s₁.gpr .x23)) :
    isa.eval (.zero .x .x9) s₂ = some (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) := by
  have e : isa.eval (.zero .x .x9) s₂ = some (s₂.gpr .x9 == 0) :=
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₂ .x9
  rw [e, h, h₁.inv.x23, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, splitVal_eq (s₀.gpr .x5).isLt]

/-! ## `seal` and `open` up to the tag, for `lo ≤ len ≤ 511` -/

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hlo : 1 ≤ L s₀) : WP isa (ShortRest.sealMain v.callee) s₀ (MainS s₀) := by
  unfold ShortRest.sealMain
  refine WP.seq (WP.mono (WP.preservedV (Short.prologue_ok hp) (Short.prologue_keepsV v.callee.sve))
    fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (split_ok s₁) fun s₂ ⟨ag, x9⟩ => ?_)
  have h₂ := postP_agree ag h₁
  have v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 :=
    fun r hr => (ag.v r hr).trans (v₁ r hr)
  refine WP.ite (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) (split_eval h₁ x9) (fun h => ?_) (fun h => ?_)
  · exact Short.sealAfter_ok hp (of_decide_eq_true h).2 h₂ v₂
  · exact sealAfter_ok v hp (by have := of_decide_eq_false h; omega) h₂ v₂

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 1 ≤ L s₀) : WP isa (ShortRest.openMain v.callee) s₀ (MainO s₀) := by
  unfold ShortRest.openMain
  refine WP.seq (WP.mono (WP.preservedV (Short.prologue_ok hp) (Short.prologue_keepsV v.callee.sve))
    fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (split_ok s₁) fun s₂ ⟨ag, x9⟩ => ?_)
  have h₂ := postP_agree ag h₁
  have v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 :=
    fun r hr => (ag.v r hr).trans (v₁ r hr)
  refine WP.ite (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) (split_eval h₁ x9) (fun h => ?_) (fun h => ?_)
  · exact Short.openAfter_ok hp (of_decide_eq_true h).2 h₂ v₂
  · exact openAfter_ok v hp (by have := of_decide_eq_false h; omega) h₂ v₂

end VG.Proof.ChaCha20Poly1305.AArch64.ShortRest
