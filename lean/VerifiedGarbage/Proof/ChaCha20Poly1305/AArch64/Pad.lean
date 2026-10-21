module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64: the data's keystream from eight blocks

`Pad.cryptPad` zeroes `ctx[768, 1280)`, has the stream encrypt it from
counter 1 (so that it holds the keystream of counters 1 to 8), XORs the data
with it, and zeroes it again: it leaves what `cryptWith` does (`CryptOk`),
for up to 512 bytes of data. `sealMainWith_ok` and `openMainWith_ok` then
give `Pad.sealMain` and `Pad.openMain`, and the route's branch on the length
picks them or `ShortRest.lean`'s code.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Pad

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Pad
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_movz wp_str32 Mupd)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ZeroedAt zeroAt_ok kpAt xorKsFromAt_ok)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (bytesAt)

variable {e : Bool}

/-- `Pad.zero`: `ctx[768, 1280)` zeroed. -/
theorem zero_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block zero) s fun s' => Kept [sub s₀ 768 512] s s' ∧
      ZeroedAt (cx s₀) 768 32 s.mem s'.mem ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have hv0 : ∀ r ∈ preservedV, r ≠ .v0 := by decide
  refine WP.mono (zeroAt_ok (b := 768) (J := 32) (by decide) (by decide) hx21 fun a ha => by
    rw [hwr]; exact hp.in_ctx (a := 768 + a) (by omega)) fun s' ⟨g, rd, wr, sp, v, z⟩ =>
      ⟨Kept.of (fun r _ => by rw [g]) sp rd wr (z.frame (by decide)), z,
        fun r hr => by rw [v r (hv0 r hr)]⟩

/-- The stream's arguments, with the counter set to 1. -/
theorem args_ok {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) :
    WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) 768 ∧ s'.gpr .x2 = BitVec.ofNat 64 512 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ Kept [sub s₀ 64 64] s s' := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) 768 ∧ s'.gpr .x2 = BitVec.ofNat 64 512 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_movz fun s₅ u₅ =>
      wp_addImm (by decide) fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, one32]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.gpr]; rfl
    · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core rfl)
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

/-- The keystream of the data from counter 1, `i < n ≤ 512` bytes in. -/
theorem ks_prefix (S : VG.Spec.ChaCha20.State) {n i : Nat} (hi : i < n) (hn : n ≤ 512) :
    (keystream S 512).getD i 0 = (keystream S n).getD i 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega), VG.Proof.ChaCha20.keystream_getD _ hi]

/-- `Pad.cryptPad` encrypts up to 512 bytes of data from counter 1. -/
theorem cryptPad_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀)
    (h512 : L s₀ ≤ 512) : CryptOk s₀ (cryptPad v.callee) := by
  intro s h hst
  have hL' := Nat.le_of_lt (s₀.gpr .x5).isLt
  have wc := hp.wrap_c
  unfold cryptPad
  refine WP.seq (WP.block_append (WP.mono (zero_ok hp h.x21 h.wr) fun s₁ ⟨k₁, z₁, v₁⟩ => ?_))
  have i₁ : Inv s₀ s₁ := h.step1 k₁ (by omega) (by omega) (by omega)
  refine WP.mono (WP.preservedV (args_ok hp i₁) (by lit_decide))
    fun s₂ ⟨⟨m₂, x0₂, x1₂, x2₂, x3₂, k₂⟩, v₂⟩ => ?_
  have i₂ : Inv s₀ s₂ := i₁.step1 k₂ (by omega) (by omega) (by omega)
  have wr₂ : s₂.wr = s₀.wr := i₂.wr
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨off (cx s₀) 768, 512⟩, ⟨off (cx s₀) 128, 320⟩] s₂.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 768, rfl, by show 768 + 512 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  refine WP.seq (xor_call v x0₂ x1₂ x2₂ x3₂ (by decide)
    (sub_disj s₀ (a := 64) (n := 64) (b := 768) (m := 512) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := 512) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by decide)]; lit_omega) (Covers.right hw) hw fun s₃ v₃ k₃ data₃ => ?_)
  have i₃ : Inv s₀ s₃ := i₂.step k₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  -- The keystream the stream leaves.
  have st₂ : stateAt s₂.mem (off (cx s₀) 64) = initState (K s₀) 1 (N s₀) := by
    rw [m₂, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      stateAt_frame k₁.frame (by rdisj_all), hst, set12_initState]
  have ks₃ : ∀ i < 512, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) 512).getD i 0 := fun i hi => by
    have x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₃ hi
    rw [x, st₂]
    have z : s₂.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) = 0 := by
      rw [k₂.frame.bytes (R := ⟨off (cx s₀) 768, 512⟩) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hi,
        show off (cx s₀) 768 + BitVec.ofNat 64 i = cx s₀ + BitVec.ofNat 64 (768 + i) from off_off _ _ _]
      exact z₁.byte (k := i) hi (by decide)
    rw [z]; simp
  -- The data XORed with it.
  have x22₃ : s₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 0 := by rw [i₃.x22, BitVec.add_zero]
  have x23₃ : s₃.gpr .x23 = BitVec.ofNat 64 (L s₀) := by rw [i₃.x23, hL s₀]
  refine WP.seq (WP.mono (WP.preservedV (xorKsFromAt_ok hp (k := 768) (o := 0) (n := L s₀) (by omega)
    (by omega) i₃.x21 x22₃ x23₃ i₃.rd i₃.wr) (by lit_decide)) fun s₄ ⟨⟨k₄, d₄, _, _⟩, v₄⟩ => ?_)
  have i₄ : Inv s₀ s₄ := i₃.step k₄
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  -- The keystream zeroed.
  refine WP.mono (zero_ok hp i₄.x21 i₄.wr) fun s₅ ⟨k₅, _, v₅⟩ => ?_
  have i₅ : Inv s₀ s₅ := i₄.step1 k₅ (by omega) (by omega) (by omega)
  have T₁ : ∀ r ∈ [sub s₀ 768 512], ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨fun r hr => (v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))),
    i₅, ?_, ?_⟩
  · refine ((((k₁.sub T₁).trans (k₂.sub fun r hr => ?_)).trans (k₃.sub fun r hr => ?_)).trans
      (k₄.sub fun r hr => ?_)).trans (k₅.sub T₁)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨sub s₀ 768 512, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩
  · have dat : ∀ i < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 i) = s.mem (dp s₀ + BitVec.ofNat 64 i) :=
      fun i hi => by
        rw [k₃.frame.bytes (R := dR s₀) (by rdisj_all) hL' hi, k₂.frame.bytes (R := dR s₀) (by rdisj_all) hL' hi,
          k₁.frame.bytes (R := dR s₀) (by rdisj_all) hL' hi]
    have hDl : (bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
    rw [bytesAt_frame k₅.frame (by rdisj_all) hL', encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      have hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      have e1 : (bytesAt s₄.mem (dp s₀) (L s₀))[i] = s₄.mem (dp s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      have e2 : ∀ h : i < (bytesAt s.mem (dp s₀) (L s₀)).length,
          (bytesAt s.mem (dp s₀) (L s₀))[i] = s.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [bytesAt]
      have e3 : ∀ h : i < (keystream (initState (K s₀) 1 (N s₀))
            (bytesAt s.mem (dp s₀) (L s₀)).length).length,
          (keystream (initState (K s₀) 1 (N s₀)) (bytesAt s.mem (dp s₀) (L s₀)).length)[i] =
            (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun h => by
        rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, hDl]
      rw [List.getElem_zipWith, e1, e2, e3]
      have d := d₄ i hi
      simp only [Nat.zero_add, kpAt] at d
      rw [d, dat i hi, ks₃ i (by omega), ks_prefix _ hi h512]

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (h512 : L s₀ ≤ 512) : WP isa (Pad.sealMain v.callee) s₀ (MainS s₀) :=
  sealMainWith_ok hp (cryptPad_ok v hp h512)

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (h512 : L s₀ ≤ 512) : WP isa (Pad.openMain v.callee) s₀ (MainO s₀) :=
  openMainWith_ok hp (cryptPad_ok v hp h512)

/-! ## The branch on the length -/

/-- The value `split` leaves in `x9`. -/
abbrev splitVal (sve : Bool) (x : BitVec 64) : BitVec 64 := (x + BitVec.ofNat 64 (511 - threshold sve)) >>> 9

/-- `x9`, zero iff `len ≤ threshold`. -/
theorem split_ok (sve : Bool) (s₀ : State) :
    WP isa (.block (split sve)) s₀ fun s₁ => Short.Agree s₀ s₁ ∧ s₁.gpr .x9 = splitVal sve (s₀.gpr .x5) := by
  have h : WP isa (.block (split sve)) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = splitVal sve (s₀.gpr .x5) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr :=
    wp_addImm (by cases sve <;> decide) fun s₁ u₁ => VG.Proof.ChaCha20.AArch64.Xor.wp_lsr (by decide) fun s₂ u₂ =>
      WP.block_nil
      ⟨fun r h9 _ => by rw [u₂.other r h9, u₁.other r h9],
        by rw [u₂.gpr, u₁.gpr],
        by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.withSp h) (by cases sve <;> lit_decide))
    fun s₁ ⟨⟨⟨g, x9, m, rd, wr⟩, sp⟩, v⟩ => ⟨⟨g, m, v, sp, rd, wr⟩, x9⟩

theorem splitVal_eq (sve : Bool) {L : Nat} (h : L ≤ 511) :
    (splitVal sve (BitVec.ofNat 64 L) == 0) = decide (L ≤ threshold sve) := by
  have hz : ∀ x : BitVec 64, (x == 0) = decide (x.toNat = 0) := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    · have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (x == 0) = false from beq_eq_false_iff_ne.mpr hx]
      simp [this]
  rw [hz]
  congr 1
  apply propext
  cases sve <;>
  simp only [splitVal, threshold, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Bool.false_eq_true, ite_true, ite_false] <;>
  omega

/-- The branch: to `ShortRest.lean`'s code iff `len ≤ threshold sve` (for `len ≤ 511`, where
the addition does not wrap around). -/
theorem split_eval {sve : Bool} {s₀ s₁ : State} (h511 : L s₀ ≤ 511)
    (h : s₁.gpr .x9 = splitVal sve (s₀.gpr .x5)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (L s₀ ≤ threshold sve)) := by
  have e : isa.eval (.zero .x .x9) s₁ = some (s₁.gpr .x9 == 0) :=
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₁ .x9
  rw [e, h, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, splitVal_eq sve h511]

theorem threshold_lt (sve : Bool) : threshold sve < 512 := by cases sve <;> decide

theorem sealRoute_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hlo : 1 ≤ L s₀) (h511 : L s₀ ≤ 511) : WP isa (sealRoute v.callee) s₀ (MainS s₀) := by
  unfold sealRoute
  refine WP.seq (WP.mono (split_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  have hp₁ := Short.APre.agree ag hp
  have hL₁ : L s₁ = L s₀ := by rw [L, L, ag.gpr .x5 (by decide) (by decide)]
  refine WP.ite (decide (L s₀ ≤ threshold v.callee.sve)) (split_eval h511 x9) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (ShortRest.sealMain_ok v hp₁ (by omega)) fun _ h => Short.MainS.agree ag h
  · have := threshold_lt v.callee.sve
    exact WP.mono (sealMain_ok v hp₁ (by omega)) fun _ h => Short.MainS.agree ag h

theorem openRoute_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 1 ≤ L s₀) (h511 : L s₀ ≤ 511) : WP isa (openRoute v.callee) s₀ (MainO s₀) := by
  unfold openRoute
  refine WP.seq (WP.mono (split_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  have hp₁ := Short.APre.agree ag hp
  have hL₁ : L s₁ = L s₀ := by rw [L, L, ag.gpr .x5 (by decide) (by decide)]
  refine WP.ite (decide (L s₀ ≤ threshold v.callee.sve)) (split_eval h511 x9) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (ShortRest.openMain_ok v hp₁ (by omega)) fun _ h => Short.MainO.agree ag h
  · have := threshold_lt v.callee.sve
    exact WP.mono (openMain_ok v hp₁ (by omega)) fun _ h => Short.MainO.agree ag h

end VG.Proof.ChaCha20Poly1305.AArch64.Pad
