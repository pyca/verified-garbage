module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Pad
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch

/-! ### `ChaCha20Poly1305.AArch64.Pad`, which this module and modules that import it used -/

section

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
  obtain hv0 : ∀ r ∈ preservedV, r ≠ .v0 := by decide
  refine WP.mono (zeroAt_ok (b := 768) (J := 32) (by decide) (by decide) hx21 fun a ha => by
    rw [hwr]; exact hp.in_ctx (a := 768 + a) (by omega_arith)) fun s' ⟨g, rd, wr, sp, v, z⟩ =>
      ⟨Kept.of (fun r _ => by rw [g]) sp rd wr (z.frame (by decide)), z,
        fun r hr => by rw [v r (hv0 r hr)]⟩

/-- The stream's arguments, with the counter set to 1. -/
theorem args_ok {s₀ s : State} (hp : APre e s₀) (h : Inv e s₀ s) :
    WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) 768 ∧ s'.gpr .x2 = BitVec.ofNat 64 512 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ Kept [sub s₀ 64 64] s s' := by
  obtain o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  obtain core : WP isa (.block args) s fun s' =>
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
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega_arith), VG.Proof.ChaCha20.keystream_getD _ hi]

/-- `Pad.cryptPad` encrypts up to 512 bytes of data from counter 1. -/
theorem cryptPad_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀)
    (h512 : L s₀ ≤ 512) : CryptOk e s₀ (cryptPad v.callee (!e)) := by
  intro s h hst
  obtain hL' := Nat.le_of_lt (s₀.gpr .x5).isLt
  have wc := hp.wrap_c
  unfold cryptPad
  refine WP.seq (WP.block_append (WP.mono (zero_ok hp h.x21 h.wr) fun s₁ ⟨k₁, z₁, v₁⟩ => ?_))
  obtain i₁ : Inv e s₀ s₁ := h.step1 k₁ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (WP.preservedV (args_ok hp i₁) (by lit_decide))
    fun s₂ ⟨⟨m₂, x0₂, x1₂, x2₂, x3₂, k₂⟩, v₂⟩ => ?_
  obtain i₂ : Inv e s₀ s₂ := i₁.step1 k₂ (by omega_arith) (by omega_arith) (by omega_arith)
  have wr₂ : s₂.wr = s₀.wr := i₂.wr
  obtain hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨off (cx s₀) 768, 512⟩, ⟨off (cx s₀) 128, 320⟩] s₂.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega_arith⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 768, rfl, by show 768 + 512 ≤ 1280; omega_arith⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega_arith⟩
  refine WP.seq (xor_call v x0₂ x1₂ x2₂ x3₂ (by decide)
    (sub_disj s₀ (a := 64) (n := 64) (b := 768) (m := 512) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := 512) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by decide)]; lit_omega) hw fun s₃ v₃ k₃ data₃ => ?_)
  obtain i₃ : Inv e s₀ s₃ := i₂.step k₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  -- The keystream the stream leaves.
  obtain st₂ : stateAt s₂.mem (off (cx s₀) 64) = initState (K s₀) 1 (N s₀) := by
    rw [m₂, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      stateAt_frame k₁.frame (by rdisj_all), hst, set12_initState]
  obtain ks₃ : ∀ i < 512, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) 512).getD i 0 := fun i hi => by
    obtain x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₃ hi
    rw [x, st₂]
    obtain z : s₂.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) = 0 := by
      rw [k₂.frame.bytes (R := ⟨off (cx s₀) 768, 512⟩) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hi,
        show off (cx s₀) 768 + BitVec.ofNat 64 i = cx s₀ + BitVec.ofNat 64 (768 + i) from off_off _ _ _]
      exact z₁.byte (k := i) hi (by decide)
    rw [z]; simp
  -- The data XORed with it.
  obtain x22₃ : s₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 0 := by rw [i₃.x22, BitVec.add_zero]
  obtain x23₃ : s₃.gpr .x23 = BitVec.ofNat 64 (L s₀) := by rw [i₃.x23, hL s₀]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsFromDst_ok hp hp.o (!e) (k := 768) (o := 0) (n := L s₀)
    (by omega_arith) (by omega_arith) i₃.x21 x22₃ (cond_out s₀ (i₃.un .x28 (by decide)) 0) x23₃ i₃.rd
    i₃.wr) (by cases e <;> lit_decide)) fun s₄ ⟨⟨k₄, d₄, _, _⟩, v₄⟩ => ?_)
  obtain i₄ : Inv e s₀ s₄ := i₃.step k₄ (oR_inv hp).1 (oR_inv hp).2
  -- The keystream zeroed.
  refine WP.mono (zero_ok hp i₄.x21 i₄.wr) fun s₅ ⟨k₅, _, v₅⟩ => ?_
  obtain i₅ : Inv e s₀ s₅ := i₄.step1 k₅ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain T₁ : ∀ r ∈ [sub s₀ 768 512], ∃ r' ∈ [sub s₀ 64 384, oR e s₀, sub s₀ 768 512], Region.Sub r r' :=
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
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨oR e s₀, by simp, fun _ h => h⟩
  · have dat : ∀ i < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 i) = s.mem (dp s₀ + BitVec.ofNat 64 i) :=
      fun i hi => by
        rw [k₃.frame.bytes (R := dR s₀) (by rdisj_all) hL' hi, k₂.frame.bytes (R := dR s₀) (by rdisj_all) hL' hi,
          k₁.frame.bytes (R := dR s₀) (by rdisj_all) hL' hi]
    obtain hDl : (bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
    rw [bytesAt_frame k₅.frame (by rdisj_all) hL', encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      obtain hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      obtain e1 : (bytesAt s₄.mem (op e s₀) (L s₀))[i] = s₄.mem (op e s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      obtain e2 : ∀ h : i < (bytesAt s.mem (dp s₀) (L s₀)).length,
          (bytesAt s.mem (dp s₀) (L s₀))[i] = s.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [bytesAt]
      obtain e3 : ∀ h : i < (keystream (initState (K s₀) 1 (N s₀))
            (bytesAt s.mem (dp s₀) (L s₀)).length).length,
          (keystream (initState (K s₀) 1 (N s₀)) (bytesAt s.mem (dp s₀) (L s₀)).length)[i] =
            (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun h => by
        rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, hDl]
      rw [List.getElem_zipWith, e1, e2, e3]
      obtain d := d₄ i hi
      simp only [Nat.zero_add, kpAt] at d
      rw [d, dat i hi, ks₃ i (by omega_arith), ks_prefix _ hi h512]

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
  obtain h : WP isa (.block (split sve)) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
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
  obtain hz : ∀ x : BitVec 64, (x == 0) = decide (x.toNat = 0) := fun x => by
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
  omega_arith

/-- The branch: to `ShortRest.lean`'s code iff `len ≤ threshold sve` (for `len ≤ 511`, where
the addition does not wrap around). -/
theorem split_eval {sve : Bool} {s₀ s₁ : State} (h511 : L s₀ ≤ 511)
    (h : s₁.gpr .x9 = splitVal sve (s₀.gpr .x5)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (L s₀ ≤ threshold sve)) := by
  obtain e : isa.eval (.zero .x .x9) s₁ = some (s₁.gpr .x9 == 0) :=
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₁ .x9
  rw [e, h, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, splitVal_eq sve h511]

theorem threshold_lt (sve : Bool) : threshold sve < 512 := by cases sve <;> decide

theorem sealRoute_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hlo : 1 ≤ L s₀) (h511 : L s₀ ≤ 511) : WP isa (sealRoute v.callee) s₀ (MainS s₀) := by
  unfold sealRoute
  refine WP.seq (WP.mono (split_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  obtain hp₁ := Short.APre.agree ag hp
  obtain hL₁ : L s₁ = L s₀ := by rw [L, L, ag.gpr .x5 (by decide) (by decide)]
  refine WP.ite (decide (L s₀ ≤ threshold v.callee.sve)) (split_eval h511 x9) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (ShortRest.sealMain_ok v hp₁ (by omega_arith)) fun _ h => Short.MainS.agree ag h
  · have := threshold_lt v.callee.sve
    exact WP.mono (sealMain_ok v hp₁ (by omega_arith)) fun _ h => Short.MainS.agree ag h

end VG.Proof.ChaCha20Poly1305.AArch64.Pad

end

end

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `open`'s rest through eight blocks

Above `Pad.threshold`, `openRest` has the stream encrypt eight blocks of
zeros at `ctx[768, 1280)` from the counter the chunks left, XORs the data
after the first `P` bytes with them, and zeroes `ctx[768, 1280)` again
(`padRest_ok`): as a call of the stream on the rest would (`rest_call`), but
for that region.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_movz wp_lsr)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ZeroedAt kpAt xorKsFromAt_ok)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

theorem setWidth_ofNat16 {n : Nat} (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- The stream's arguments for `ctx[768, 768 + n)`. -/
theorem padArgs_ok {s₀ w : State} {n : Nat} (hn : n < 2 ^ 16) (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 (BitVec.ofNat 16 n) 0,
        .addImm .x .x3 .x21 128]) w fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 n ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w u := by
  obtain core : WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 (BitVec.ofNat 16 n) 0,
      .addImm .x .x3 .x21 128]) w fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 n ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ => wp_movz fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hx21],
          by rw [u₄.other _ (by decide), u₃.gpr]; exact setWidth_ofNat16 hn,
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.kept core (by rfl))
    fun u ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `openRest`'s branch above the threshold: the data from `P` (fewer than 512
bytes) encrypted from the counter after `P / 64` blocks, through the keystream
of eight blocks at `ctx[768, 1280)`. -/
theorem padRest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {P n : Nat} (hn : n ≤ 512) (hle : P ≤ L s₀) (hlt : L s₀ - P ≤ n) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hdata : ∀ k < L s₀, P ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k))
    (hout : ∀ k < P, w.mem (op e s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0) :
    WP isa (padRest v.callee (!e) n) w
      fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, oR e s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restQ s₀ (op e s₀) P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (op e s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hL
  have wc := hp.wrap_c
  have wo := hp.o.wrap
  obtain ts : Region.Sub (restQ s₀ (op e s₀) P) (oR e s₀) := Offset.sub_base _ (by omega_arith)
  unfold padRest
  -- The keystream's region zeroed, and the stream's arguments.
  refine WP.seq (WP.block_append (WP.mono (Pad.zero_ok hp hx21 hwr) fun s₁ ⟨k₁, z₁, v₁⟩ => ?_))
  refine WP.mono (WP.preservedV (padArgs_ok (s₀ := s₀) (n := n) (by omega_arith) (by rw [k₁.cs _ (pres .x21) (pres30 .x21), hx21]))
    (by rfl)) fun s₂ ⟨⟨x0₂, x1₂, x2₂, x3₂, k₂⟩, v₂⟩ => ?_
  obtain wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, k₁.wr, hwr]
  obtain hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨off (cx s₀) 768, n⟩, ⟨off (cx s₀) 128, 320⟩] s₂.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega_arith⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 768, rfl, by show 768 + n ≤ 1280; omega_arith⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega_arith⟩
  -- The stream on the zeros.
  refine WP.seq (xor_call v x0₂ x1₂ x2₂ x3₂ (by omega_arith)
    (sub_disj s₀ (a := 64) (n := 64) (b := 768) (m := n) (by omega_arith) (by omega_arith) (by omega_arith))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := n) (b := 128) (m := 320) (by omega_arith) (by omega_arith) (by omega_arith))
    (by rw [hp.off_toNat (by decide)]; lit_omega) hw fun s₃ v₃ k₃ data₃ => ?_)
  obtain ctxData : ∀ {a n : Nat}, a + n ≤ 1280 → ∀ k < L s₀,
      ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun h k hk hh => hp.c_d.sub_left (sub_ctx s₀ h) _ hh (data_in hk)
  obtain m₂ : ∀ k < L s₀, s₂.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => by
      rw [k₂.frame _ (fun r hr => absurd hr List.not_mem_nil), k₁.frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ctxData (by lit_omega) k hk)]
  obtain m₃ : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => by
      rw [k₃.frame _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxData (a := 64) (n := 64) (by lit_omega) k hk
        · exact ctxData (a := 768) (n := n) (by omega_arith) k hk
        · exact ctxData (a := 128) (n := 320) (by lit_omega) k hk), m₂ k hk]
  obtain st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt w.mem (off (cx s₀) 64) := by
    rw [stateAt_frame k₂.frame (fun r hr => absurd hr List.not_mem_nil),
      stateAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))]
  -- The keystream from the counter after `P / 64` blocks.
  obtain ks₃ : ∀ i < n, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) =
      (keystream (stateAt w.mem (off (cx s₀) 64)) n).getD i 0 := fun i hi => by
    obtain x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₃ hi
    rw [x, st₂]
    obtain z : s₂.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) = 0 := by
      rw [k₂.frame _ (fun r hr => absurd hr List.not_mem_nil),
        show off (cx s₀) 768 + BitVec.ofNat 64 i = cx s₀ + BitVec.ofNat 64 (768 + i) from off_off _ _ _]
      exact z₁.byte (k := i) (by omega_arith) (by decide)
    rw [z]; simp
  -- The data XORed with it.
  obtain x21₃ : s₃.gpr .x21 = cx s₀ := by
    rw [k₃.cs _ (pres .x21) (pres30 .x21), k₂.cs _ (pres .x21) (pres30 .x21),
      k₁.cs _ (pres .x21) (pres30 .x21), hx21]
  obtain x22₃ : s₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 P := by
    rw [k₃.cs _ (pres .x22) (pres30 .x22), k₂.cs _ (pres .x22) (pres30 .x22),
      k₁.cs _ (pres .x22) (pres30 .x22), hx22]
  obtain x23₃ : s₃.gpr .x23 = BitVec.ofNat 64 (L s₀ - P) := by
    rw [k₃.cs _ (pres .x23) (pres30 .x23), k₂.cs _ (pres .x23) (pres30 .x23),
      k₁.cs _ (pres .x23) (pres30 .x23), hx23]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [k₃.rd, k₂.rd, k₁.rd, hrd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [k₃.wr, wr₂]
  obtain x28₃ : s₃.gpr .x28 = s₀.gpr .x28 := by
    rw [k₃.cs _ (by decide) (by decide), k₂.cs _ (by decide) (by decide), k₁.cs _ (by decide) (by decide), h28]
  obtain ctxOut : ∀ {a n : Nat}, a + n ≤ 1280 → ∀ k < L s₀,
      ¬ (sub s₀ a n).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
    fun h k hk hh => hp.o.ctx.sub_left (sub_ctx s₀ h) _ hh (Offset.contains_base _ (by omega_arith) (by omega_arith))
  obtain q₃ : ∀ k < L s₀, s₃.mem (op e s₀ + BitVec.ofNat 64 k) = w.mem (op e s₀ + BitVec.ofNat 64 k) :=
    fun k hk => by
      rw [k₃.frame _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxOut (a := 64) (n := 64) (by lit_omega) k hk
        · exact ctxOut (a := 768) (n := n) (by omega_arith) k hk
        · exact ctxOut (a := 128) (n := 320) (by lit_omega) k hk),
        k₂.frame _ (fun r hr => absurd hr List.not_mem_nil), k₁.frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ctxOut (by lit_omega) k hk)]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsFromDst_ok hp hp.o (!e) (k := 768) (o := P) (n := L s₀ - P)
    (by omega_arith) (by omega_arith) x21₃ x22₃ (cond_out s₀ x28₃ P) x23₃ rd₃ wr₃) (by cases e <;> lit_decide))
    fun s₄ ⟨⟨k₄, d₄, f₄, _⟩, v₄⟩ => ?_)
  -- The keystream zeroed again.
  refine WP.mono (Pad.zero_ok hp (by rw [k₄.cs _ (pres .x21) (pres30 .x21), x21₃])
    (by rw [k₄.wr, wr₃])) fun s₅ ⟨k₅, _, v₅⟩ => ?_
  obtain T768 : ∀ r ∈ [sub s₀ 768 512], ∃ r' ∈ [sub s₀ 64 384, oR e s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  obtain T3 : ∀ r ∈ [(⟨off (cx s₀) 64, 64⟩ : Region), ⟨off (cx s₀) 768, n⟩, ⟨off (cx s₀) 128, 320⟩],
      ∃ r' ∈ [sub s₀ 64 384, oR e s₀, sub s₀ 768 512], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨sub s₀ 768 512, by simp, sub_sub s₀ (Nat.le_refl _) (by omega_arith) (by omega_arith)⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  obtain K : Kept [sub s₀ 64 384, oR e s₀, sub s₀ 768 512] w s₅ :=
    ((((k₁.sub T768).trans (k₂.sub fun r hr => absurd hr List.not_mem_nil)).trans (k₃.sub T3)).trans
      (k₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨oR e s₀, by simp, fun _ h => h⟩)).trans
      (k₅.sub T768)
  obtain F : Frame [sub s₀ 64 384, restQ s₀ (op e s₀) P, sub s₀ 768 512] w.mem s₅.mem := by
    obtain T768' : ∀ r ∈ [sub s₀ 768 512], ∃ r' ∈ [sub s₀ 64 384, restQ s₀ (op e s₀) P, sub s₀ 768 512],
        Region.Sub r r' :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    refine ((((k₁.frame.sub T768').trans (k₂.frame.sub fun r hr => absurd hr List.not_mem_nil)).trans
      (k₃.frame.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_)).trans (k₅.frame.sub T768')
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨sub s₀ 768 512, by simp, sub_sub s₀ (Nat.le_refl _) (by omega_arith) (by omega_arith)⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨restQ s₀ (op e s₀) P, by simp, fun _ h => h⟩
  refine ⟨fun r hr => (v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))),
    K, F, ?_⟩
  -- The data encrypted.
  show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
  rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
    VG.Proof.Poly1305.length_bytesAt _ _ _]
  refine bytesAt_xor2 (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
  obtain m₅ : s₅.mem (op e s₀ + BitVec.ofNat 64 k) = s₄.mem (op e s₀ + BitVec.ofNat 64 k) :=
    k₅.frame _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ctxOut (by lit_omega) k hk
  rw [m₅]
  by_cases hk' : k < P
  · rw [f₄ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact not_restQ hk' hle),
      q₃ k hk, hout k hk']
  · have hPL : P < L s₀ := by omega_arith
    obtain h64 := hP hPL
    obtain x := d₄ (k - P) (by omega_arith)
    rw [show P + (k - P) = k by omega_arith, m₃ k hk, hdata k hk (by omega_arith)] at x
    rw [x, show kpAt s₀ 768 = off (cx s₀) 768 from rfl, ks₃ (k - P) (by omega_arith), hcnt hPL,
      VG.Proof.ChaCha20.keystream_getD _ (by omega_arith), ks_shift _ hk (q := P / 64) (by omega_arith),
      show 64 * (P / 64) = P by omega_arith]

/-- `openRest`'s test: `x9 = 0` iff the rest is at most `Pad.threshold sve`. -/
theorem restSplit_ok (sve : Bool) (w : State) :
    WP isa (.block [.addImm .x .x9 .x23 (511 - Pad.threshold sve), .lsr .x .x9 .x9 9]) w fun u =>
      u.gpr .x9 = (w.gpr .x23 + BitVec.ofNat 64 (511 - Pad.threshold sve)) >>> 9 ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  obtain core : WP isa (.block [.addImm .x .x9 .x23 (511 - Pad.threshold sve), .lsr .x .x9 .x9 9]) w
      fun u => u.gpr .x9 = (w.gpr .x23 + BitVec.ofNat 64 (511 - Pad.threshold sve)) >>> 9 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_addImm (by cases sve <;> decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
      WP.block_nil ⟨by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
        by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.kept core (by cases sve <;> rfl))
    (by cases sve <;> lit_decide)) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
      ⟨h9, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hv⟩

/-- `openRest`'s test of whole blocks: `x9 = 0` iff the rest is a multiple of 64. -/
theorem restWhole_ok (w : State) :
    WP isa (.block [.lsl .x .x9 .x23 58]) w fun u =>
      u.gpr .x9 = w.gpr .x23 <<< 58 ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  obtain core : WP isa (.block [.lsl .x .x9 .x23 58]) w
      fun u => u.gpr .x9 = w.gpr .x23 <<< 58 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_lsl (by decide) fun s₁ u₁ =>
      WP.block_nil ⟨u₁.gpr, u₁.mem, u₁.rd, u₁.wr⟩
  exact WP.mono (WP.preservedV (WP.kept core (by rfl))
    (by lit_decide)) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
      ⟨h9, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hv⟩

/-- `openRest`'s tests of a bound: `x9 = 0` iff the rest, at least 1, is at most `2^k`. -/
theorem restAtMost_ok (k : Nat) (hk : k < 64) (w : State) :
    WP isa (.block (atMost k)) w fun u =>
      u.gpr .x9 = (w.gpr .x23 - BitVec.ofNat 64 1) >>> k ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  obtain core : WP isa (.block (atMost k)) w
      fun u => u.gpr .x9 = (w.gpr .x23 - BitVec.ofNat 64 1) >>> k ∧ u.mem = w.mem ∧ u.rd = w.rd ∧
        u.wr = w.wr :=
    VG.Proof.ChaCha20.AArch64.Xor.wp_subImm (by decide) fun s₁ u₁ => wp_lsr hk fun s₂ u₂ =>
      WP.block_nil ⟨by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
        by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.kept core (by rfl))
    (by rfl)) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
      ⟨h9, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hv⟩

/-- `openRest`'s test of eight blocks: `x9 = 0` iff the rest is at least 321. -/
theorem restAbove_ok (w : State) :
    WP isa (.block above320) w fun u =>
      u.gpr .x9 = (w.gpr .x23 - BitVec.ofNat 64 321) >>> 63 ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  obtain core : WP isa (.block above320) w
      fun u => u.gpr .x9 = (w.gpr .x23 - BitVec.ofNat 64 321) >>> 63 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧
        u.wr = w.wr :=
    VG.Proof.ChaCha20.AArch64.Xor.wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
      WP.block_nil ⟨by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
        by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.kept core (by rfl))
    (by rfl)) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
      ⟨h9, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hv⟩

theorem beq_zero_toNat (x : BitVec 64) : (x == 0) = decide (x.toNat = 0) := by
  by_cases hx : x = 0
  · subst hx; simp
  · have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [show (x == 0) = false from beq_eq_false_iff_ne.mpr hx]
    simp [this]

theorem whole_eq {r : Nat} (h : r < 2 ^ 64) :
    (BitVec.ofNat 64 r <<< 58 == 0) = decide (r % 64 = 0) := by
  rw [beq_zero_toNat]
  refine decide_eq_decide.mpr ?_
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 64 * 2 ^ 58 by rw [show (64 : Nat) = 2 ^ 6 from rfl, ← Nat.pow_add],
    Nat.mul_mod_mul_right, Nat.mul_eq_zero]
  exact ⟨fun h' => h'.resolve_right (Nat.ne_of_gt (Nat.two_pow_pos 58)), Or.inl⟩

theorem atMost_eq {r k : Nat} (h1 : 1 ≤ r) (h : r < 2 ^ 64) :
    ((BitVec.ofNat 64 r - BitVec.ofNat 64 1) >>> k == 0) = decide (r ≤ 2 ^ k) := by
  rw [beq_zero_toNat]
  refine decide_eq_decide.mpr ?_
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  obtain hp : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [show (2 ^ 64 - 1 % 2 ^ 64 + r) % 2 ^ 64 = r - 1 by omega_arith, Nat.div_eq_zero_iff_lt hp]
  omega_arith

theorem above_eq {r : Nat} (h : r < 2 ^ 63) :
    ((BitVec.ofNat 64 r - BitVec.ofNat 64 321) >>> 63 == 0) = decide (321 ≤ r) := by
  rw [beq_zero_toNat]
  refine decide_eq_decide.mpr ?_
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith : r < 2 ^ 64), Nat.shiftRight_eq_div_pow]
  rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 63)]
  omega_arith

/-- `padRest` after code that kept everything but `x9`. -/
theorem padRest_after (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀)
    {s w w' : State} {P n : Nat} (hn : n ≤ 512) (hle : P ≤ L s₀) (hlt : L s₀ - P ≤ n)
    (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hdata : ∀ k < L s₀, P ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k))
    (hout : ∀ k < P, w.mem (op e s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0)
    (k : Kept [] w w') (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) :
    WP isa (padRest v.callee (!e) n) w' fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, oR e s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restQ s₀ (op e s₀) P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (op e s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have mw := k.mem_eq
  obtain none : ∀ r ∈ ([] : List Region), ∃ r' ∈ [sub s₀ 64 384, oR e s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun _ hr => absurd hr List.not_mem_nil
  exact (padRest_ok v hp hn hle hlt hP (by rw [k.cs _ (pres .x21) (pres30 .x21), hx21])
    (by rw [k.cs _ (pres .x22) (pres30 .x22), hx22]) (by rw [k.cs _ (pres .x23) (pres30 .x23), hx23])
    (by rw [k.rd, hrd]) (by rw [k.wr, hwr]) (fun h => by rw [mw]; exact hcnt h)
    (by rw [k.cs _ (by decide) (by decide), h28])
    (fun i hi hp' => by rw [mw]; exact hdata i hi hp') (fun i hi => by rw [mw]; exact hout i hi)).mono
      fun u ⟨vu, ku, fu, pu⟩ => ⟨fun r hr => (vu r hr).trans (vw r hr), (k.sub none).trans ku,
        by rw [← mw]; exact fu, pu⟩

/-- `cryptRest` after code that kept everything but `x9`. -/
theorem cryptRest_after (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀)
    {s w w' : State} {P : Nat} (hle : P ≤ L s₀) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hdata : ∀ k < L s₀, P ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k))
    (hout : ∀ k < P, w.mem (op e s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0)
    (k : Kept [] w w') (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) :
    WP isa (cryptRest v.callee (!e)) w' fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, oR e s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restQ s₀ (op e s₀) P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (op e s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have mw := k.mem_eq
  obtain none : ∀ r ∈ ([] : List Region), ∃ r' ∈ [sub s₀ 64 384, oR e s₀, sub s₀ 768 512],
      Region.Sub r r' := fun _ hr => absurd hr List.not_mem_nil
  unfold cryptRest
  refine WP.seq ((restArgs_ok (s₀ := s₀) (by rw [k.cs _ (pres .x21) (pres30 .x21), hx21])).mono
    fun w₃ ⟨⟨a0, a1, a2, a3, kw⟩, vw₃⟩ => ?_)
  have mw₃ := kw.mem_eq
  refine (rest_callOut v hp (s := s) (P := P) hle hP a0
    (by rw [a1, k.cs _ (pres .x22) (pres30 .x22), hx22])
    (by rw [a2, k.cs _ (pres .x23) (pres30 .x23), hx23]) a3
    (by rw [kw.rd, k.rd, hrd]) (by rw [kw.wr, k.wr, hwr])
    (by rw [kw.cs _ (by decide) (by decide), k.cs _ (by decide) (by decide), h28])
    (fun h => by rw [mw₃, mw]; exact hcnt h)
    (fun i hi hp' => by rw [mw₃, mw]; exact hdata i hi hp') (fun i hi => by rw [mw₃, mw]; exact hout i hi)).mono
    fun u ⟨vu, ku, fu, pu⟩ =>
      ⟨fun r hr => (vu r hr).trans ((vw₃ r hr).trans (vw r hr)),
        ((k.trans kw).sub none).trans (ku.sub fun r hr => ?_), ?_, pu⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [← mw, ← mw₃]
    refine fu.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

/-- `openRest`: the data from `P` (fewer than 512 bytes) encrypted from the
counter after `P / 64` blocks, as a call of the stream would, but for
`ctx[768, 1280)`. -/
theorem openRest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hlt : L s₀ - P < 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hdata : ∀ k < L s₀, P ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k))
    (hout : ∀ k < P, w.mem (op false s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0) :
    WP isa (openRest v.callee) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, oR false s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restQ s₀ (op false s₀) P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (op false s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain pad := fun {w' : State} {n : Nat} (hn : n ≤ 512) (hlt' : L s₀ - P ≤ n) (k : Kept [] w w')
      (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) =>
    padRest_after (s := s) v hp hn hle hlt' hP hx21 hx22 hx23 hrd hwr hcnt h28 hdata hout k vw
  obtain crypt := fun {w' : State} (k : Kept [] w w')
      (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) =>
    cryptRest_after (s := s) v hp hle hP hx21 hx22 hx23 hrd hwr hcnt h28 hdata hout k vw
  obtain x23k : ∀ {w' : State}, Kept [] w w' → w'.gpr .x23 = BitVec.ofNat 64 (L s₀ - P) :=
    fun k => by rw [k.cs _ (pres .x23) (pres30 .x23), hx23]
  obtain evz : ∀ (u : State), isa.eval (.zero .x .x9) u = some (u.gpr .x9 == 0) :=
    fun u => VG.Proof.ChaCha20.AArch64.Xor.eval_zero u .x9
  unfold openRest
  refine WP.seq (WP.mono (restSplit_ok v.callee.sve w) fun w₁ ⟨x9₁, k₁, v₁⟩ => ?_)
  refine WP.ite (decide (L s₀ - P ≤ Pad.threshold v.callee.sve))
    (by rw [evz, x9₁, hx23]; exact congrArg some (Pad.splitVal_eq _ (by omega_arith)))
    (fun _ => ?_) (fun _ => pad (by omega_arith) (by omega_arith) k₁ v₁)
  -- At most the threshold: whole blocks through the stream.
  refine WP.seq (WP.mono (restWhole_ok w₁) fun w₂ ⟨x9₂, k₂, v₂⟩ => ?_)
  obtain k₂' : Kept [] w w₂ := k₁.trans k₂
  obtain v₂' : ∀ r ∈ preservedV, (w₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₂ r hr).trans (v₁ r hr)
  refine WP.ite (decide ((L s₀ - P) % 64 = 0))
    (by rw [evz, x9₂, x23k k₁]; exact congrArg some (whole_eq (by omega_arith)))
    (fun _ => crypt k₂' v₂') (fun hwh => ?_)
  obtain h1 : 1 ≤ L s₀ - P := Nat.pos_of_ne_zero fun h => by
    rw [h] at hwh; exact absurd hwh (by decide)
  -- At most 64 bytes: one scalar block in the stream.
  refine WP.seq (WP.mono (restAtMost_ok 6 (by decide) w₂) fun w₃ ⟨x9₃, k₃, v₃⟩ => ?_)
  obtain k₃' : Kept [] w w₃ := k₂'.trans k₃
  obtain v₃' : ∀ r ∈ preservedV, (w₃.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₃ r hr).trans (v₂' r hr)
  refine WP.ite (decide (L s₀ - P ≤ 2 ^ 6))
    (by rw [evz, x9₃, x23k k₂']; exact congrArg some (atMost_eq h1 (by omega_arith)))
    (fun _ => crypt k₃' v₃') (fun _ => ?_)
  -- Up to 256 bytes: four blocks of keystream; above, the stream.
  refine WP.seq (WP.mono (restAtMost_ok 8 (by decide) w₃) fun w₄ ⟨x9₄, k₄, v₄⟩ => ?_)
  obtain k₄' : Kept [] w w₄ := k₃'.trans k₄
  obtain v₄' : ∀ r ∈ preservedV, (w₄.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₄ r hr).trans (v₃' r hr)
  refine WP.ite (decide (L s₀ - P ≤ 2 ^ 8))
    (by rw [evz, x9₄, x23k k₃']; exact congrArg some (atMost_eq h1 (by omega_arith)))
    (fun h4 => pad (by decide) (by simpa using h4) k₄' v₄') (fun _ => ?_)
  -- From 321 bytes: eight blocks of keystream; below, the stream.
  refine WP.seq (WP.mono (restAbove_ok w₄) fun w₅ ⟨x9₅, k₅, v₅⟩ => ?_)
  obtain k₅' : Kept [] w w₅ := k₄'.trans k₅
  obtain v₅' : ∀ r ∈ preservedV, (w₅.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₅ r hr).trans (v₄' r hr)
  refine WP.ite (decide (321 ≤ L s₀ - P))
    (by rw [evz, x9₅, x23k k₄']; exact congrArg some (above_eq (by omega_arith)))
    (fun _ => pad (by decide) (by omega_arith) k₅' v₅') (fun _ => crypt k₅' v₅')

end VG.Proof.ChaCha20Poly1305.AArch64
