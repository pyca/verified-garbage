module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
public import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Pad

/-! ### `ChaCha20Poly1305.AArch64.Stitched.PadRest`, which the modules that import this one used -/

section

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

end

end

/-! ### `ChaCha20Poly1305.AArch64.TailO.Kernel`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.AArch64.TailO.Round`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, the rest when decrypting: the rounds

`TailO.rounds`: ten double rounds of the four-block kernel (`Tail.doubleRound_ok`),
and after each up to `k` of the `c` blocks from `W` (`TailO.maybes`, while
`x6`, the blocks left, is not zero): after `i` rounds, `min c (k i)` blocks
are absorbed. The rounds write only vector registers, the blocks only
`Poly.regs` and `x6`; neither writes memory.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.TailO

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState)
open VG.Impl.ChaCha20.AArch64.Neon4 (rol8Table)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds RoundSame)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable absorb_next)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- `n` of the `c` blocks from `W` absorbed, and `x6` the blocks left. -/
structure Absorbed (R a : Nat) (W : Addr) (c : Nat) (m : Mem) (s : State) (n : Nat) : Prop where
  le : n ≤ c
  ptr : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)
  acc : Acc R (absorbAll R a (bytesAt m W (16 * n))) s
  left : s.gpr .x6 = BitVec.ofNat 64 (c - n)

/-- `maybe`: a block if one is left. -/
theorem maybe_ok {R a : Nat} {W : Addr} {c n : Nat} (hc : c < 2 ^ 63) {s : State}
    (hr : Readable W (16 * c) s) (h : Absorbed R a W c s.mem s n) :
    WP isa TailO.maybe s fun u =>
      Absorbed R a W c s.mem u (min c (n + 1)) ∧ (∀ r, r ≠ .x6 → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ v, u.v v = s.v v) := by
  unfold TailO.maybe
  refine WP.ite (decide (c - n = 0)) (by
      rw [show isa.eval (.zero .x .x6) s = some (s.gpr .x6 == 0) from
        VG.Proof.ChaCha20.AArch64.Xor.eval_zero s .x6, h.left,
        VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega_using [hc])]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = c := by have := of_decide_eq_true hz; have := h.le; omega_arith
    subst hn
    refine WP.block_nil ?_
    rw [show min n (n + 1) = n by omega_using []]
    exact ⟨h, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · have hlt : n < c := by have := of_decide_eq_false hz; have := h.le; omega_arith
    obtain hv : ∀ i ∈ Poly.block, vdstOf i = none := by decide +kernel
    refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv
      (absorb_next (by omega_using [hlt]) h.acc h.ptr hr)).mono fun b ⟨⟨hba, hbp, hbk⟩, hbv, hbsp, _, _⟩ => ?_)
    apply WP.block_cons_iff.mpr
    refine ⟨b.write .x .x6 (b.gpr .x6 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
    · simpa only [State.read, BitVec.setWidth_eq] using
        exec_subImm_x (s := b) (d := .x6) (n := .x6) (imm := 1) (by decide)
    have hbm : b.mem = s.mem := hbk.2.1
    rw [show min c (n + 1) = n + 1 by omega_using [hlt]]
    refine ⟨⟨by omega_using [hlt], ?_, ?_, ?_⟩, fun r h6 hp => ?_, hbm, hbk.2.2.1, hbk.2.2.2, hbsp, fun v => ?_⟩
    · rw [RegUpd.gpr_write_of_ne b .x _ (by decide), hbp]
    · exact hba.of (fun r hr' => RegUpd.gpr_write_of_ne b .x _ (by
        intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
    · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hbk.gpr' (r := .x6), h.left,
        Offset.ofNat_sub_ofNat (by omega_using [hlt] : 1 ≤ c - n), Nat.sub_sub]
    · rw [RegUpd.gpr_write_of_ne b .x _ h6, hbk.gpr' (r := r) hp]
    · rw [Stitch.write_v, hbv]

/-- `maybes k`: up to `k` blocks. -/
theorem maybes_ok {R a : Nat} {W : Addr} {c : Nat} (hc : c < 2 ^ 63) :
    ∀ (k : Nat) {n : Nat} {s : State}, Readable W (16 * c) s → Absorbed R a W c s.mem s n →
    WP isa (TailO.maybes k) s fun u =>
      Absorbed R a W c s.mem u (min c (n + k)) ∧ (∀ r, r ≠ .x6 → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ v, u.v v = s.v v)
  | 0, n, s, _, h => WP.block_nil ⟨by rw [Nat.add_zero, Nat.min_eq_right h.le]; exact h,
      fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | k + 1, n, s, hr, h => by
    unfold TailO.maybes
    refine WP.seq ((maybe_ok hc hr h).mono fun d ⟨hda, hdk, hdm, hdrd, hdwr, hdsp, hdv⟩ => ?_)
    obtain hdr : Readable W (16 * c) d := hr.of hdrd hdwr (hdk _ (by decide) (by decide))
    rw [← hdm] at hda
    refine (maybes_ok hc k hdr hda).mono fun f ⟨hfa, hfk, hfm, hfrd, hfwr, hfsp, hfv⟩ => ?_
    rw [hdm, show min c (min c (n + 1) + k) = min c (n + (k + 1)) by omega_using []] at hfa
    exact ⟨hfa, fun r h6 hp => by rw [hfk r h6 hp, hdk r h6 hp], hfm.trans hdm, hfrd.trans hdrd,
      hfwr.trans hdwr, hfsp.trans hdsp, fun v => by rw [hfv, hdv]⟩

/-- After `i` iterations of the loop. -/
structure TI (vs : Nat → CState) (R a : Nat) (W : Addr) (c k : Nat) (s₀ s : State) (i : Nat) : Prop where
  vec : Holds (fun j => Nat.repeat innerBlock i (vs j)) s
  table : s.v .v30 = rol8Table
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ≠ .x4 → r ≠ .x6 → r ∉ Poly.regs → s.gpr r = s₀.gpr r
  abs : Absorbed R a W c s₀.mem s (min c (k * i))
  cnt : s.gpr .x4 = BitVec.ofNat 64 (10 - i)

/-- The loop body, from `TI … i` to `TI … (i + 1)`. -/
theorem iter_ok (sve : Bool) {vs : Nat → CState} {R a : Nat} {W : Addr} {c k : Nat} {s₀ s : State}
    {i : Nat} (hc : c < 2 ^ 63) (hi : i < 10) (hr : Readable W (16 * c) s₀)
    (h : TI vs R a W c k s₀ s i) :
    WP isa (TailO.round sve k) s fun u => TI vs R a W c k s₀ u (i + 1) := by
  unfold TailO.round
  apply WP.seq
  refine (Tail.doubleRound_ok sve h.vec h.table).mono fun b ⟨hb, hsb⟩ => ?_
  obtain hbm : b.mem = s₀.mem := hsb.mem.trans h.mem
  obtain hbr : Readable W (16 * c) b := hr.of (by rw [hsb.rd, h.rd]) (by rw [hsb.wr, h.wr])
    (by rw [hsb.gpr, h.keep _ (by decide) (by decide) (by decide)])
  obtain hba : Absorbed R a W c b.mem b (min c (k * i)) := by
    rw [hbm]
    exact ⟨h.abs.le, by rw [hsb.gpr]; exact h.abs.ptr, h.abs.acc.of (fun r _ => by rw [hsb.gpr]) hsb.mem,
      by rw [hsb.gpr]; exact h.abs.left⟩
  apply WP.seq
  refine (maybes_ok hc k hbr hba).mono fun f ⟨hfa, hfk, hfm, hfrd, hfwr, hfsp, hfv⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨f.write .x .x4 (f.gpr .x4 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
  · simpa only [State.read, BitVec.setWidth_eq] using
      exec_subImm_x (s := f) (d := .x4) (n := .x4) (imm := 1) (by decide)
  obtain hm : min c (min c (k * i) + k) = min c (k * (i + 1)) := by
    rw [Nat.mul_succ]; omega_using []
  obtain hfm' : f.mem = s₀.mem := hfm.trans hbm
  refine ⟨?_, ?_, hfm', hfrd.trans (hsb.rd.trans h.rd),
    hfwr.trans (hsb.wr.trans h.wr), hfsp.trans (hsb.sp.trans h.sp),
    fun r h4 h6 hp => ?_, ?_, ?_⟩
  · intro k j hj
    rw [Stitch.write_v, hfv]
    exact hb k j hj
  · rw [Stitch.write_v, hfv, hsb.v30, h.table]
  · rw [RegUpd.gpr_write_of_ne f .x _ h4, hfk r h6 hp, hsb.gpr]
    exact h.keep r h4 h6 hp
  · rw [← hm]
    rw [hbm] at hfa
    exact ⟨hfa.le, by rw [RegUpd.gpr_write_of_ne f .x _ (by decide)]; exact hfa.ptr,
      hfa.acc.of (fun r hr' => RegUpd.gpr_write_of_ne f .x _ (by
        intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl,
      by rw [RegUpd.gpr_write_of_ne f .x _ (by decide)]; exact hfa.left⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hfk _ (by decide) (by decide),
      hsb.gpr, h.cnt, Offset.ofNat_sub_ofNat (by omega_using [hi] : 1 ≤ 10 - i)]
    simp only [Nat.sub_sub]

/-- The loop: ten iterations. -/
theorem rounds_ok (sve : Bool) {vs : Nat → CState} {R a : Nat} {W : Addr} {c k : Nat} {s₀ s : State}
    (hc : c < 2 ^ 63) (hr : Readable W (16 * c) s₀) (h : TI vs R a W c k s₀ s 0) :
    WP isa (TailO.rounds sve k) s fun u => TI vs R a W c k s₀ u 10 := by
  let Inv : Nat → State → Prop := fun n u => ∃ i, i < 10 ∧ n = 10 - i ∧ TI vs R a W c k s₀ u i
  obtain hstep : ∀ n u, Inv n u → WP isa (TailO.round sve k) u (fun w =>
      (eval (.nonzero .x .x4) w = some false ∧ TI vs R a W c k s₀ w 10) ∨
      (eval (.nonzero .x .x4) w = some true ∧ ∃ m < n, Inv m w)) := by
    rintro n u ⟨i, hi, rfl, hu⟩
    refine (iter_ok sve hc hi hr hu).mono fun w hw => ?_
    obtain he : eval (.nonzero .x .x4) w = some (BitVec.ofNat 64 (10 - (i + 1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hw.cnt]
    by_cases hl : i + 1 = 10
    · exact .inl ⟨by rw [he, hl]; rfl, hl ▸ hw⟩
    · have hn0 : BitVec.ofNat 64 (10 - (i + 1)) ≠ 0 := by
        intro hz
        obtain hz' := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [] : 10 - (i + 1) < 2 ^ 64)] at hz'
        change 10 - (i + 1) = 0 at hz'
        omega_using [hi, hl, hz']
      exact .inr ⟨by rw [he]; simpa using hn0, 10 - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, hl], rfl, hw⟩
  exact WP.loop (M := isa) Inv hstep 10 s ⟨0, by decide, rfl, h⟩

end VG.Proof.ChaCha20Poly1305.AArch64.TailO

end

end


/-!
# ChaCha20-Poly1305 on AArch64, the rest when decrypting: the kernel

`TailO.kernel sve k`, as `Tail.kernel`: the keystream of the four blocks
from the stream's counter in the buffer `x3[0, 256)`, and the `c` blocks from
`W` (`x20`; `x6 = c`, at most `10 k`) absorbed into the accumulator in
`x21`–`x23`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.TailO

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds LoadSame input input_same input_eq)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_subImm)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (zero_ok Zeroed.byte Zeroed.frame block_eq)
open VG.Spec.ChaCha20 (innerBlock stateAt serialize block)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

theorem kernel_ok (sve : Bool) (k : Nat) {R a : Nat} {W : Addr} {c : Nat} {s : State} (hc : c < 2 ^ 63)
    (hx20 : s.gpr .x20 = W) (hx6 : s.gpr .x6 = BitVec.ofNat 64 c)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ d, d + 16 ≤ 256 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16)
    (hst : (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩)
    (hr : Readable W (16 * c) s) (ha : Acc R a s) (hck : c ≤ 10 * k) :
    WP isa (TailO.kernel sve k) s fun u =>
      (∀ k < 256, u.mem (s.gpr .x3 + BitVec.ofNat 64 k) =
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x3, 256⟩] s.mem u.mem ∧
      Poly.hval u % Spec.Poly1305.P = absorbAll R a (bytesAt s.mem W (16 * c)) % Spec.Poly1305.P ∧
      (u.gpr .x23).toNat ≤ 4 ∧ u.gpr .x20 = W + BitVec.ofNat 64 (16 * c) ∧
      (∀ r, r ∉ [Reg.x1, .x4, .x6] → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  unfold TailO.kernel
  -- The four blocks' states.
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Neon4.setup_ok s hin).mono
    fun s₃ ⟨h₂, l₂, t₂⟩ => ?_)
  -- The count.
  have m₂ : s₃.mem = s.mem := l₂.mem
  apply WP.seq
  apply WP.block_cons_iff.mpr
  refine ⟨s₃.write .x .x4 ((10 : BitVec 16).setWidth 64), ?_, WP.block_nil ?_⟩
  · simp only [exec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, show 0 < 64 from by decide,
      ite_true]
  -- The loop, from its invariant.
  let s₄ := s₃.write .x .x4 ((10 : BitVec 16).setWidth 64)
  have m₃ : s₃.mem = s.mem := m₂
  let vs : Nat → CState := fun j => ctr (stateAt s.mem (s.gpr .x0)) j
  obtain h₄ : TI vs R a W c k s₄ s₄ 0 := by
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, ⟨by omega_using [], ?_, ?_, ?_⟩, ?_⟩
    · intro k j hj
      rw [Stitch.write_v]
      exact h₂ k j hj
    · rw [Stitch.write_v, t₂]
    · rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide), hx20, Nat.mul_zero, Nat.min_zero,
        Nat.mul_zero, BitVec.add_zero]
    · have e : bytesAt s₄.mem W (16 * min c (k * 0)) = [] := by simp [bytesAt]
      rw [e, Poly1305.absorbAll_nil]
      refine ha.of (fun r hr => ?_) m₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        (rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide)]; exact l₂.gpr _ (by decide))
    · rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide), hx6]; simp
    · rw [RegUpd.gpr_write_self]; rfl
  obtain hr₄ : Readable W (16 * c) s₄ := hr.of (by show s₃.rd = _; rw [l₂.rd]) (by show s₃.wr = _; rw [l₂.wr])
    (by rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide)])
  refine WP.seq ((rounds_ok sve hc hr₄ h₄).mono fun s₅ h₅ => ?_)
  obtain x3₅ : s₅.gpr .x3 = s.gpr .x3 := by
    rw [h₅.keep _ (by decide) (by decide) (by decide), RegUpd.gpr_write_of_ne s₃ .x _ (by decide),
      l₂.gpr _ (by decide)]
  obtain wr₅ : s₅.wr = s.wr := by rw [h₅.wr]; show s₃.wr = _; rw [l₂.wr]
  obtain rd₅ : s₅.rd = s.rd := by rw [h₅.rd]; show s₃.rd = _; rw [l₂.rd]
  obtain sp₅ : s₅.sp = s.sp := by rw [h₅.sp]; show s₃.sp = _; rw [l₂.sp]
  obtain mm₅ : s₅.mem = s.mem := by rw [h₅.mem]; exact m₃
  -- The buffer zeroed, then the keystream XORed into it.
  rw [Tail.finish, List.append_assoc]
  apply WP.block_append
  refine (zero_ok x3₅ (by rw [wr₅]; exact hw)).mono fun s₆ ⟨g₆, rd₆, wr₆, sp₆, v₆, z₆⟩ => ?_
  let s₇ := s₆.write .x .x1 (s₆.gpr .x3)
  obtain hx₇ : exec (VG.Impl.ChaCha20.AArch64.Xor.mov .x1 .x3) s₆ = some s₇ := by
    show exec (.addImm .x .x1 .x3 0) s₆ = some s₇
    simpa only [State.read, BitVec.setWidth_eq, BitVec.add_zero] using
      exec_addImm_x (s := s₆) (d := .x1) (n := .x3) (imm := 0) (by decide)
  refine WP.block_cons_iff.mpr ⟨s₇, hx₇, ?_⟩
  show WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.finish) s₇ _
  obtain u₇ := VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 s₆ .x1 (s₆.gpr .x3)
  obtain x1₇ : s₇.gpr .x1 = s.gpr .x3 := by rw [u₇.gpr, g₆, x3₅]
  obtain x0₇ : s₇.gpr .x0 = s.gpr .x0 := by
    rw [u₇.other _ (by decide), g₆, h₅.keep _ (by decide) (by decide) (by decide),
      RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide)]
  obtain f₆ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₇.mem := by
    rw [u₇.mem, ← mm₅]; exact z₆.frame
  obtain st₇ : stateAt s₇.mem (s.gpr .x0) = stateAt s.mem (s.gpr .x0) :=
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hst
  obtain hv₇ : Holds (fun j => Nat.repeat innerBlock 10 (vs j)) s₇ := by
    intro k j hj
    rw [show s₇.v = s₆.v from rfl, v₆ _ (fun e => absurd e
      ((show ∀ k : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v28 by decide) k))]
    exact h₅.vec k j hj
  obtain hin₇ : ∀ k : Fin 16, InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [u₇.rd, u₇.wr, rd₆, wr₆, rd₅, wr₅, x0₇]; exact hin k
  unfold VG.Impl.ChaCha20.AArch64.Neon4.finish
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv₇ hin₇).mono
    fun s₈ ⟨h₈, l₈⟩ => ?_)
  obtain hc₈ : Holds (fun j => block (vs j)) s₈ := by
    intro k j hj
    rw [h₈ k j hj, input_eq, x0₇, st₇, block_eq]
  obtain ho : ∀ r j : Fin 4, InRegions s₈.wr
      (s₈.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j
    rw [l₈.wr, l₈.gpr _ (by decide), u₇.wr, wr₆, wr₅, x1₇]
    exact hw _ (by omega_using [])
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hc₈ ho).mono
    fun s₉ ⟨d₉, f₉, k₉⟩ => ?_
  obtain x1₈ : s₈.gpr .x1 = s.gpr .x3 := by rw [l₈.gpr _ (by decide), x1₇]
  have g₉ (r : Reg) (h4 : r ≠ .x4) : s₉.gpr r = s₇.gpr r := by rw [k₉.gpr, l₈.gpr _ h4]
  have g₅ (r : Reg) (h4 : r ≠ .x4) (h6 : r ≠ .x6) (hp : r ∉ Poly.regs) : s₅.gpr r = s₃.gpr r := by
    rw [h₅.keep _ h4 h6 hp, RegUpd.gpr_write_of_ne s₃ .x _ h4]
  have acc₅ := h₅.abs.acc
  have ptr₅ := h₅.abs.ptr
  rw [show min c (k * 10) = c by omega_using [hck], show s₄.mem = s.mem from m₃] at acc₅
  rw [show min c (k * 10) = c by omega_using [hck]] at ptr₅
  obtain e21 : ∀ r ∈ [Reg.x21, .x22, .x23], s₉.gpr r = s₅.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₉ _ (by decide), u₇.other _ (by decide), g₆]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, fun r hr hp => ?_, ?_, ?_, ?_⟩
  · have e := d₉ k hk
    obtain z : ∀ x : BitVec 8, (0 : BitVec 8) ^^^ x = x := fun x => by ext i; simp
    rw [x1₈, show s₈.mem = s₇.mem from l₈.mem, u₇.mem, z₆.byte hk, z] at e
    exact e
  · rw [← x1₈]
    obtain f₈ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₈.mem := by rw [l₈.mem]; exact f₆
    rw [x1₈] at f₉ ⊢
    exact f₈.trans f₉
  · rw [show Poly.hval s₉ = Poly.hval s₅ by
      simp only [Poly.hval, e21 .x21 (by simp), e21 .x22 (by simp), e21 .x23 (by simp)]]
    exact acc₅.h
  · rw [e21 .x23 (by simp)]; exact acc₅.h2
  · rw [g₉ _ (by decide), u₇.other _ (by decide), g₆]; exact ptr₅
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h4, h6⟩ := hr
    rw [g₉ _ h4, u₇.other _ h1, g₆, g₅ _ h4 h6 hp, l₂.gpr _ h4]
  · rw [k₉.rd, l₈.rd, u₇.rd, rd₆, rd₅]
  · rw [k₉.wr, l₈.wr, u₇.wr, wr₆, wr₅]
  · rw [k₉.sp, l₈.sp, show s₇.sp = s₆.sp from rfl, sp₆, sp₅]

end VG.Proof.ChaCha20Poly1305.AArch64.TailO

end

end

/-!
# ChaCha20-Poly1305 on AArch64, the rest when decrypting

`TailO.rest`, from what `cryptStitched` leaves after `T` chunks with a rest
of `r = L - 512 T` bytes, `65 ≤ r ≤ 256` (`Crypted`): the rest's keystream
computed while its `r / 16` whole blocks are absorbed (`kernel_ok`), its last
partial block absorbed with its padding (`macPad_ok`), and the rest XORed
with the keystream into the output (`xorKsDst_ok`): the Poly1305 state and
the output as `macPad` and `openRest` leave them.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.TailO

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_movz wp_lsr wp_sub wp_addImm wp_subImm)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (Rk wp_add)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

/-- `load`: our caller's `x20` in `x8`, the data from `x22` in `x20` and `x7`,
the whole blocks of its `n` bytes counted in `x6`, and the accumulator and
the clamped key as before the chunks. -/
theorem loadAt_ok {s₀ u : State} (hp : APre e s₀) {key M : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx21 : u.gpr .x21 = cx s₀) (hrd : u.rd = s₀.rd) (hwr : u.wr = s₀.wr)
    (hx0 : u.gpr .x0 = off (cx s₀) 64) (hx23 : u.gpr .x23 = BitVec.ofNat 64 n)
    (hm : Repr u.mem (off (cx s₀) 448) key M) :
    WP isa (.block TailO.load) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key) M) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x22 ∧
      s₂.gpr .x6 = BitVec.ofNat 64 (n / 16) ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x6, .x7, .x8, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  unfold TailO.load
  obtain hv : ∀ i ∈ [mov .x8 .x20, mov .x20 .x22, mov .x7 .x22, .lsr .x .x6 .x23 4], vdstOf i = none := by
    decide
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun s₁ =>
      s₁.gpr .x8 = u.gpr .x20 ∧ s₁.gpr .x20 = u.gpr .x22 ∧ s₁.gpr .x7 = u.gpr .x22 ∧
      s₁.gpr .x6 = BitVec.ofNat 64 (n / 16) ∧
      (∀ r, r ≠ .x8 → r ≠ .x20 → r ≠ .x7 → r ≠ .x6 → s₁.gpr r = u.gpr r) ∧ s₁.mem = u.mem)
    (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ =>
      WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx23,
          shr4_ofNat hn],
        fun r h8 h20 h7 h6 => by rw [u₄.other _ h6, u₃.other _ h7, u₂.other _ h20, u₁.other _ h8],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩)).mono
    fun s₁ ⟨⟨x8₁, x20₁, x7₁, x6₁, g₁, m₁⟩, v₁, sp₁, rd₁, wr₁⟩ => ?_)
  refine (polyIn_ok hp (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hx21])
    (by rw [rd₁, hrd]) (by rw [wr₁, hwr])).mono
    fun s₂ ⟨⟨a21, a22, a23, m₂, g₂, _, _⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_
  obtain hr : Repr s₁.mem (off (cx s₀) 448) key M := by rw [m₁]; exact hm
  obtain x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by
    rw [g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide), hx0]
  refine ⟨acc_in hr x0₂ a21 a22 a23 m₂, by rw [g₂ _ (by decide), x20₁], by rw [g₂ _ (by decide), x8₁],
    by rw [g₂ _ (by decide), x7₁], by rw [g₂ _ (by decide), x6₁],
    by rw [m₂, m₁, g₁ _ (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide)], fun r hr' => ?_, by rw [v₂, v₁],
    by rw [sp₂, sp₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  obtain ⟨h6, h7, h8, h20, h21, h22, h23, h24, h25⟩ := hr'
  rw [g₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
    ⟨h21, h22, h23, h24, h25⟩), g₁ r h8 h20 h7 h6]

/-- `load`, from what `cryptStitched` leaves. -/
theorem load_ok {s₀ s w₀ u : State} (hp : APre false s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted false o s₀ s w₀ key msg T u) :
    WP isa (.block TailO.load) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key)
        (msg ++ bytesAt s.mem (dp s₀) (o + 512 * T))) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x22 ∧
      s₂.gpr .x6 = BitVec.ofNat 64 ((L s₀ - (o + 512 * T)) / 16) ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x6, .x7, .x8, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have e := hc.mac
  simp only [Bool.false_eq_true, ite_false] at e
  exact loadAt_ok hp (by omega_arith) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x0
    (by rw [hc.x23, show pre o false T = o + 512 * T from rfl]) e

/-- `out`: the accumulator stored, `x22` and `x23` set to what follows the
absorbed blocks, our caller's `x20` restored, and the rest kept in `x24`,
`x25`. -/
theorem out_ok {s₀ s : State} (hp : APre e s₀) (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block TailO.out) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 → Spec.Poly1305.leNum (bytesAt u.mem (off (cx s₀) 448) 24) =
        hacc s % Spec.Poly1305.P) ∧
      Frame [sub s₀ 448 24] s.mem u.mem ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      u.gpr .x22 = s.gpr .x20 ∧ u.gpr .x23 = s.gpr .x7 + s.gpr .x2 - s.gpr .x20 ∧
      u.gpr .x20 = s.gpr .x8 ∧ u.gpr .x24 = s.gpr .x7 ∧ u.gpr .x25 = s.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x20, .x21, .x22, .x23, .x24,
        .x25, .x27, .x28] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.v = s.v := by
  unfold TailO.out
  refine WP.block_append ((polyOut_ok hp false hx0 hrd hwr).mono
    fun s₁ ⟨⟨hv₁, m₁, x21₁, x27₁, x28₁, _, _, g₁, rd₁, wr₁⟩, v₁, sp₁, _, _⟩ => ?_)
  obtain hv : ∀ i ∈ [mov .x22 .x20, .add .x .x23 .x7 .x2, .sub .x .x23 .x23 .x20, mov .x20 .x8,
      mov .x24 .x7, mov .x25 .x2], vdstOf i = none := by decide
  have gs (r : Reg) (hr : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23,
      .x27, .x28]) : s₁.gpr r = s.gpr r := g₁ r hr
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun u =>
      u.gpr .x22 = s₁.gpr .x20 ∧ u.gpr .x23 = s₁.gpr .x7 + s₁.gpr .x2 - s₁.gpr .x20 ∧
      u.gpr .x20 = s₁.gpr .x8 ∧ u.gpr .x24 = s₁.gpr .x7 ∧ u.gpr .x25 = s₁.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x20, .x22, .x23, .x24, .x25] → u.gpr r = s₁.gpr r) ∧ u.mem = s₁.mem)
    (wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => wp_sub fun t₃ u₃ => wp_mov fun t₄ u₄ =>
      wp_mov fun t₅ u₅ => wp_mov fun t₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩)).mono
    fun u ⟨⟨x22u, x23u, x20u, x24u, x25u, gu, mu⟩, vu, spu, rdu, wru⟩ => ?_
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h20, h22, h23, h24, h25⟩ := hr
    rw [u₆.other _ h25, u₅.other _ h24, u₄.other _ h20, u₃.other _ h23, u₂.other _ h23, u₁.other _ h22]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have go (r : Reg) (hr : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23,
      .x27, .x28]) : s₁.gpr r = s.gpr r := gs r hr
  refine ⟨fun h23 => ?_, ?_, by rw [gu _ (by decide), x21₁], by rw [gu _ (by decide), x27₁],
    by rw [gu _ (by decide), x28₁], by rw [x22u, go _ (by decide)],
    by rw [x23u, go .x7 (by decide), go .x2 (by decide), go .x20 (by decide)],
    by rw [x20u, go _ (by decide)], by rw [x24u, go _ (by decide)], by rw [x25u, go _ (by decide)],
    fun r hr => ?_, by rw [rdu, rd₁], by rw [wru, wr₁], by rw [spu, sp₁], by rw [vu, v₁]⟩
  · rw [mu, m₁, Poly1305.AArch64.storeHm_acc]
    exact hv₁ h23
  · rw [mu, m₁]; exact storeHm_frame _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h20, h21, h22, h23, h24, h25, h27, h28⟩ := hr
    obtain a : r ∉ [Reg.x20, .x22, .x23, .x24, .x25] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h20, h22, h23, h24, h25⟩
    obtain b : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h21, h22, h23, h27, h28⟩
    rw [gu r a, go r b]

/-- `x22`, `x23` set to the rest again. -/
theorem moves_ok {s : State} :
    WP isa (.block [mov .x22 .x24, mov .x23 .x25]) s fun u =>
      (u.gpr .x22 = s.gpr .x24 ∧ u.gpr .x23 = s.gpr .x25 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = s.gpr r) ∧ u.mem = s.mem) ∧ u.v = s.v ∧ u.sp = s.sp ∧
      u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide)
    (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22], by rw [u₂.mem, u₁.mem]⟩)

/-- `loadTo`: `loadAt_ok`, with `x28` kept in `x15`. -/
theorem loadAtTo_ok {s₀ u : State} (hp : APre e s₀) {key M : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx21 : u.gpr .x21 = cx s₀) (hrd : u.rd = s₀.rd) (hwr : u.wr = s₀.wr)
    (hx0 : u.gpr .x0 = off (cx s₀) 64) (hx23 : u.gpr .x23 = BitVec.ofNat 64 n)
    (hm : Repr u.mem (off (cx s₀) 448) key M) :
    WP isa (.block TailO.loadTo) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key) M) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x22 ∧
      s₂.gpr .x6 = BitVec.ofNat 64 (n / 16) ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      s₂.gpr .x15 = u.gpr .x28 ∧
      (∀ r, r ∉ [Reg.x6, .x7, .x8, .x15, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  unfold TailO.loadTo
  refine WP.block_append ((loadAt_ok hp hn hx21 hrd hwr hx0 hx23 hm).mono
    fun s₁ ⟨a₁, x20₁, x8₁, x7₁, x6₁, m₁, g₁, v₁, sp₁, rd₁, wr₁⟩ =>
      VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun s₂ u₂ sp₂ v₂ => WP.block_nil ?_)
  have o2 : ∀ r, r ≠ .x15 → s₂.gpr r = s₁.gpr r := u₂.other
  refine ⟨a₁.of (fun r hr => o2 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) u₂.mem,
    by rw [o2 _ (by decide), x20₁], by rw [o2 _ (by decide), x8₁], by rw [o2 _ (by decide), x7₁],
    by rw [o2 _ (by decide), x6₁], by rw [u₂.mem, m₁],
    by rw [u₂.gpr, g₁ _ (by decide)], fun r hr => ?_, by rw [v₂, v₁], by rw [sp₂, sp₁],
    by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  obtain h15 : r ≠ .x15 := fun h => hr (by subst h; simp)
  rw [o2 r h15, g₁ r (fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h | h | h | h | h | h | h | h <;> simp [h]))]

/-- `loadTo`: `load_ok`, with `x28` kept in `x15`. -/
theorem loadTo_ok {s₀ s w₀ u : State} (hp : APre false s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted false o s₀ s w₀ key msg T u) :
    WP isa (.block TailO.loadTo) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key)
        (msg ++ bytesAt s.mem (dp s₀) (o + 512 * T))) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x22 ∧
      s₂.gpr .x6 = BitVec.ofNat 64 ((L s₀ - (o + 512 * T)) / 16) ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      s₂.gpr .x15 = u.gpr .x28 ∧
      (∀ r, r ∉ [Reg.x6, .x7, .x8, .x15, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  unfold TailO.loadTo
  refine WP.block_append ((load_ok hp hc).mono
    fun s₁ ⟨a₁, x20₁, x8₁, x7₁, x6₁, m₁, g₁, v₁, sp₁, rd₁, wr₁⟩ =>
      VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun s₂ u₂ sp₂ v₂ => WP.block_nil ?_)
  have o2 : ∀ r, r ≠ .x15 → s₂.gpr r = s₁.gpr r := u₂.other
  refine ⟨a₁.of (fun r hr => o2 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) u₂.mem,
    by rw [o2 _ (by decide), x20₁], by rw [o2 _ (by decide), x8₁], by rw [o2 _ (by decide), x7₁],
    by rw [o2 _ (by decide), x6₁], by rw [u₂.mem, m₁],
    by rw [u₂.gpr, g₁ _ (by decide)], fun r hr => ?_, by rw [v₂, v₁], by rw [sp₂, sp₁],
    by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  obtain h15 : r ≠ .x15 := fun h => hr (by subst h; simp)
  rw [o2 r h15, g₁ r (fun hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h | h | h | h | h | h | h | h <;> simp [h]))]

/-- `outTo`: `out_ok`, with `x28` from `x15`. -/
theorem outTo_ok {s₀ s : State} (hp : APre e s₀) (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block TailO.outTo) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 → Spec.Poly1305.leNum (bytesAt u.mem (off (cx s₀) 448) 24) =
        hacc s % Spec.Poly1305.P) ∧
      Frame [sub s₀ 448 24] s.mem u.mem ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.gpr .x15 ∧
      u.gpr .x22 = s.gpr .x20 ∧ u.gpr .x23 = s.gpr .x7 + s.gpr .x2 - s.gpr .x20 ∧
      u.gpr .x20 = s.gpr .x8 ∧ u.gpr .x24 = s.gpr .x7 ∧ u.gpr .x25 = s.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x20, .x21, .x22, .x23, .x24,
        .x25, .x27, .x28] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.v = s.v := by
  unfold TailO.outTo
  refine WP.block_append ((out_ok hp hx0 hrd hwr).mono
    fun s₁ ⟨acc₁, f₁, x21₁, x27₁, _, x22₁, x23₁, x20₁, x24₁, x25₁, g₁, rd₁, wr₁, sp₁, v₁⟩ =>
      VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun s₂ u₂ sp₂ v₂ => WP.block_nil ?_)
  have o2 : ∀ r, r ≠ .x28 → s₂.gpr r = s₁.gpr r := u₂.other
  refine ⟨by rw [u₂.mem]; exact acc₁, by rw [u₂.mem]; exact f₁, by rw [o2 _ (by decide), x21₁],
    by rw [o2 _ (by decide), x27₁], by rw [u₂.gpr, g₁ _ (by decide)],
    by rw [o2 _ (by decide), x22₁], by rw [o2 _ (by decide), x23₁], by rw [o2 _ (by decide), x20₁],
    by rw [o2 _ (by decide), x24₁], by rw [o2 _ (by decide), x25₁],
    fun r hr => ?_, by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁], by rw [sp₂, sp₁], by rw [v₂, v₁]⟩
  rw [o2 r (fun h => hr (by subst h; simp)), g₁ r hr]

/-- `TailO.rest`, after `T` chunks with a rest of 65 to 256 bytes. -/
theorem rest_ok (sve : Bool) {s₀ s w₀ u : State} (hp : APre false s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted false o s₀ s w₀ key msg T u) (ho : o % 64 = 0)
    (hr₁ : 65 ≤ L s₀ - (o + 512 * T)) (hr₂ : L s₀ - (o + 512 * T) ≤ 256) :
    WP isa (TailO.rest sve) u fun w =>
      (∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
      Inv0 false s₀ w ∧ Frame [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, oR false s₀] u.mem w.mem ∧
      Repr w.mem (off (cx s₀) 448) key ((msg ++ bytesAt s.mem (dp s₀) (o + 512 * T)) ++
        (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (o + 512 * T)) (L s₀ - (o + 512 * T)) ++
          Spec.ChaCha20Poly1305.pad16
            (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (o + 512 * T)) (L s₀ - (o + 512 * T))))) ∧
      bytesAt w.mem (op false s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wo := hp.o.wrap
  have wd := hp.wrap_d
  have hle := hc.le
  obtain oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  -- `P`, the rest's offset, `r` its length, `c` its whole blocks.
  generalize hPdef : o + 512 * T = P at hr₁ hr₂ hle ⊢
  generalize hrdef : L s₀ - P = r at hr₁ hr₂ ⊢
  obtain hpre : pre o false T = P := by rw [← hPdef]; rfl
  obtain hc16 : 16 * (r / 16) ≤ r := Nat.mul_div_le _ _
  let W := dp s₀ + BitVec.ofNat 64 P
  refine (WP.withSp (WP.preservedV (c := TailO.rest sve) (Q := fun w =>
      (∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) → w.sp = u.sp →
      Inv0 false s₀ w ∧ Frame [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, oR false s₀] u.mem w.mem ∧
      Repr w.mem (off (cx s₀) 448) key ((msg ++ bytesAt s.mem (dp s₀) P) ++
        (bytesAt s.mem W r ++ Spec.ChaCha20Poly1305.pad16 (bytesAt s.mem W r))) ∧
      bytesAt w.mem (op false s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))) ?_
      (by cases sve <;> lit_decide))).mono
    fun w ⟨⟨hw, vw⟩, spw⟩ => ⟨vw, hw vw spw⟩
  unfold TailO.rest
  -- Load.
  refine WP.seq ((loadTo_ok hp hc).mono
    fun s₂ ⟨a₂, x20₂, x8₂, x7₂, x6₂, m₂, x15₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_)
  rw [hPdef] at a₂ x6₂
  rw [hrdef] at x6₂
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, hc.inv.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, hc.inv.wr]
  obtain x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by rw [g₂ _ (by decide), hc.x0]
  obtain x3₂ : s₂.gpr .x3 = off (cx s₀) 128 := by rw [g₂ _ (by decide), hc.x3]
  obtain x2₂ : s₂.gpr .x2 = BitVec.ofNat 64 r := by rw [g₂ _ (by decide), hc.x2, hPdef, hrdef]
  obtain x22u : u.gpr .x22 = W := by rw [hc.x22, hpre]
  obtain hin : ∀ k : Fin 16, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₂, oo, rd₂', wr₂']; exact hp.in_ctx' (by omega_arith)
  obtain hw : ∀ d, d + 16 ≤ 256 → InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₂, oo, wr₂']; exact hp.in_ctx (by omega_arith)
  obtain hst : (⟨s₂.gpr .x0, 64⟩ : Region).Disjoint ⟨s₂.gpr .x3, 256⟩ := by
    rw [x0₂, x3₂]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain hrd : Readable W (16 * (r / 16)) s₂ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₂', wr₂', VG.Proof.ChaCha20.AArch64.Xor.add_ofNat]
      exact ⟨dR s₀, hp.d_in, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
  -- The kernel.
  refine WP.seq ((kernel_ok sve 2 (c := r / 16) (by omega_arith) (by rw [x20₂, x22u]) x6₂ hin hw hst hrd a₂
      (by omega_arith)).mono fun s₃ ⟨ks₃, f₃, hv₃, h2₃, x20₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  have g₃' (r : Reg) (h : r ≠ .x1 ∧ r ≠ .x4 ∧ r ≠ .x6 ∧ r ∉ Poly.regs) :
      s₃.gpr r = s₂.gpr r :=
    have ⟨h1, h4, h6, hp'⟩ := h
    g₃ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h6⟩) hp'
  obtain x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by
    rw [g₃' _ (by decide), x0₂]
  rw [x3₂] at ks₃ f₃
  -- The accumulator stored.
  refine WP.seq ((outTo_ok hp x0₃ (by rw [rd₃, rd₂']) (by rw [wr₃, wr₂'])).mono
    fun s₄ ⟨acc₄, f₄, x21₄, x27₄, x28₄, x22₄, x23₄, x20₄, x24₄, x25₄, g₄, rd₄, wr₄, sp₄, v₄⟩ => ?_)
  obtain x7₃ : s₃.gpr .x7 = W := by rw [g₃' _ (by decide), x7₂, x22u]
  obtain x2₃ : s₃.gpr .x2 = BitVec.ofNat 64 r := by
    rw [g₃' _ (by decide), x2₂]
  obtain x22₄' : s₄.gpr .x22 = dp s₀ + BitVec.ofNat 64 (P + 16 * (r / 16)) := by
    rw [x22₄, x20₃, BitVec.add_assoc, ← BitVec.ofNat_add]
  obtain x23₄' : s₄.gpr .x23 = BitVec.ofNat 64 (r - 16 * (r / 16)) := by
    rw [x23₄, x7₃, x2₃, x20₃, VG.Offset.add_sub_add_left, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hc16]
  -- The data: the rest is as it was until the XOR.
  obtain dctx : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    obtain e₁ := data_frame (s₀ := s₀) f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk
    obtain e₂ := data_frame (s₀ := s₀) f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk
    obtain e₃ := data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
    rw [e₁, e₂, m₂, e₃]
  obtain uorig : ∀ k < L s₀, P ≤ k → u.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk hPk
    exact hc.data k hk (by rw [hPdef]; exact hPk)
  obtain restEq : ∀ {m : Mem}, (∀ k < L s₀, P ≤ k → m (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k)) →
      ∀ a n, a + n ≤ r → bytesAt m (W + BitVec.ofNat 64 a) n = bytesAt s.mem (W + BitVec.ofNat 64 a) n := by
    intro m hm a n han
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    obtain hi := List.mem_range.mp hi
    obtain e : W + BitVec.ofNat 64 a + BitVec.ofNat 64 i = dp s₀ + BitVec.ofNat 64 (P + a + i) := by
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.add_assoc]
    rw [e]; exact hm _ (by omega_arith) (by omega_arith)
  obtain b₂ : bytesAt s₂.mem W (16 * (r / 16)) = bytesAt s.mem W (16 * (r / 16)) := by
    have := restEq (m := s₂.mem) (fun k hk hPk => by
      rw [m₂, ← uorig k hk hPk]
      exact data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28))
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk) 0 (16 * (r / 16)) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- The Poly1305 state after `out`: the chunks and the rest's whole blocks.
  have hmac := hc.mac
  simp only [Bool.false_eq_true, ite_false, hpre] at hmac
  have hml : (msg ++ bytesAt s.mem (dp s₀) P).length % 16 = 0 := hmac.1
  let tgt := [sub s₀ 32 16, sub s₀ 64 408]
  have c408 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, by simp [tgt], sub_sub s₀ h₁ (by omega_arith) (by lit_omega)⟩
  obtain Fm : Frame tgt u.mem s₂.mem := by
    rw [m₂]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c408 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  obtain Fk : Frame tgt s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 128 256 (by decide) (by decide)
  obtain Fo : Frame tgt s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 448 24 (by decide) (by decide)
  obtain F₄ : Frame tgt u.mem s₄.mem := Fm.trans (Fk.trans Fo)
  obtain R₄ : Repr s₄.mem (off (cx s₀) 448) key
      ((msg ++ bytesAt s.mem (dp s₀) P) ++ bytesAt s.mem W (16 * (r / 16))) := by
    obtain k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    refine ⟨by rw [List.length_append, Poly1305.length_bytesAt]; omega_arith, ?_, ?_⟩
    · have e := hmac.2.1
      rw [k24] at e ⊢
      rw [bytesAt_frame F₄ (fun r hr => by
          simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega)]
      exact e
    · have hlt := Poly1305.accumulate_lt (Rk key) (msg ++ bytesAt s.mem (dp s₀) P)
      rw [acc₄ h2₃, show hacc s₃ = Poly.hval s₃ from rfl, hv₃,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₂]
      exact (Poly1305.accumulate_append hml).symm
  -- The last partial block, absorbed with its padding.
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂']
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂']
  obtain hsrc := srcAt hp (p := P + 16 * (r / 16)) (by omega_arith)
  rw [show L s₀ - (P + 16 * (r / 16)) = r - 16 * (r / 16) by omega_arith] at hsrc
  refine WP.seq ((macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ hsrc x21₄ rd₄' wr₄' x22₄'
    x23₄').mono fun s₅ ⟨k₅, r₅⟩ => ?_)
  obtain R₅ := r₅ _ _ R₄
  -- The rest, back in `x22` and `x23`.
  refine WP.seq (moves_ok.mono fun s₆ ⟨⟨x22₆, x23₆, g₆, m₆⟩, v₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain x24₅ : s₅.gpr .x24 = W := by rw [k₅.cs _ (pres .x24) (pres30 .x24), x24₄, x7₃]
  obtain x25₅ : s₅.gpr .x25 = BitVec.ofNat 64 r := by rw [k₅.cs _ (pres .x25) (pres30 .x25), x25₄, x2₃]
  obtain x21₆ : s₆.gpr .x21 = cx s₀ := by
    rw [g₆ _ (by decide) (by decide), k₅.cs _ (pres .x21) (pres30 .x21), x21₄]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₅.rd, rd₄']
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₅.wr, wr₄']
  -- The rest XORed with its keystream.
  obtain x28₆ : s₆.gpr .x28 = s₀.gpr .x28 := by
    rw [g₆ _ (by decide) (by decide), k₅.cs _ (by decide) (by decide), x28₄, g₃' _ (by decide), x15₂,
      hc.inv.un .x28 (by decide)]
  refine (Short.xorKsDst_ok hp hp.o true (o := P) (n := r) hr₂ (by omega_arith) x21₆ (by rw [x22₆, x24₅])
    (cond_out (e := false) s₀ x28₆ P) (by rw [x23₆, x25₅]) rd₆' wr₆').mono fun s₇ ⟨k₇, d₇, f₇, g₇⟩ =>
      fun vw spw => ?_
  -- Registers.
  have g₇' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₇.gpr r = s₆.gpr r :=
    have ⟨h9, h10, h11, h12, h13, h15⟩ := h
    g₇ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13, h15⟩)
  have to₄ (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧
      r ≠ .x15 ∧ r ≠ .x22 ∧ r ≠ .x23) :
      s₇.gpr r = s₄.gpr r := by
    obtain ⟨hr, h30, h9, h10, h11, h12, h13, h15, h22, h23⟩ := h
    rw [g₇' r ⟨h9, h10, h11, h12, h13, h15⟩, g₆ r h22 h23, k₅.cs r hr h30]
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₃.mem.readW (off (cx s₀) d) 64 = s₂.mem.readW (off (cx s₀) d) 64 :=
    f₃.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by decide)
  obtain un₇ : ∀ r ∈ untouched, s₇.gpr r = s₀.gpr r := by
    intro r hr
    obtain hu := hc.inv.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₄ _ (by decide), g₄ _ (by decide), g₃' _ (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide), x20₄, g₃' _ (by decide), x8₂, hu]
    · rw [to₄ _ (by decide), g₄ _ (by decide), g₃' _ (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide), x27₄, r32 32 (.inl rfl), m₂, memIn_800, hu]
    · rw [to₄ _ (by decide), x28₄, g₃' _ (by decide), x15₂, hu]
  -- The frames.
  let out := [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, oR false s₀]
  obtain Fa : Frame out u.mem s₄.mem := F₄.sub fun r hr => by
    simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 32 16, by simp [out], fun _ h => h⟩
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
  obtain Fb : Frame out s₄.mem s₅.mem := k₅.frame.sub fun r hr => by
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
    · exact ⟨sub s₀ 16 16, by simp [out], fun _ h => h⟩
  obtain Fc : Frame out s₅.mem s₇.mem := by
    rw [← m₆]
    exact k₇.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨oR false s₀, by simp [out], fun _ h => h⟩
  obtain F : Frame out u.mem s₇.mem := Fa.trans (Fb.trans Fc)
  obtain inv₇ : Inv0 false s₀ s₇ := ⟨by rw [g₇' _ (by decide), x21₆],
    un₇, by rw [spw, hc.inv.sp], by rw [k₇.rd, rd₆'], by rw [k₇.wr, wr₆'],
    hc.inv.saved.frame F (fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.o.ctx.sub_left (sub_ctx s₀ (by lit_omega))),
    hc.inv.frame.trans (F.sub fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨oR false s₀, by simp, fun _ h => h⟩)⟩
  -- The data, before the XOR, from `s₄` on.
  obtain d₅ : ∀ k < L s₀, s₆.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₆, ← dctx k hk]
    exact data_frame (s₀ := s₀) k₅.frame (fun r hr => by
      simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
  obtain qctx : ∀ {a n : Nat}, a + n ≤ 1280 → ∀ k < L s₀, (sub s₀ a n).Disjoint ⟨op false s₀, L s₀⟩ :=
    fun h _ _ => hp.o.ctx.sub_left (sub_ctx s₀ h)
  obtain q₅ : ∀ k < L s₀, s₆.mem (op false s₀ + BitVec.ofNat 64 k) = u.mem (op false s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₆, out_frame (s₀ := s₀) k₅.frame (fun r hr => by
        simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (qctx (by lit_omega) k hk).symm) hk,
      out_frame (s₀ := s₀) f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (qctx (by lit_omega) k hk).symm) hk,
      out_frame (s₀ := s₀) f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (qctx (by lit_omega) k hk).symm) hk, m₂,
      out_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (qctx (by lit_omega) k hk).symm) hk]
  refine ⟨inv₇, F, ?_, ?_⟩
  · -- The Poly1305 state.
    obtain e₄ : bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 (P + 16 * (r / 16))) (r - 16 * (r / 16)) =
        bytesAt s.mem (W + BitVec.ofNat 64 (16 * (r / 16))) (r - 16 * (r / 16)) := by
      rw [show dp s₀ + BitVec.ofNat 64 (P + 16 * (r / 16)) = W + BitVec.ofNat 64 (16 * (r / 16)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
      exact restEq (fun k hk hPk => by rw [dctx k hk, uorig k hk hPk]) _ _ (by omega_arith)
    rw [e₄, List.append_assoc, split_pad (m := s.mem) (p := W) (Nat.mul_mod_right 16 _) hc16] at R₅
    refine Repr.frame (k₇.frame) (fun r hr => ?_) (by rw [m₆]; exact R₅)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.o.ctx.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))
  · -- The data.
    show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
    rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      VG.Proof.Poly1305.length_bytesAt _ _ _]
    refine bytesAt_xor2 (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
    by_cases hk' : k < P
    · rw [f₇ _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Tail.not_in (.inl hk') (by omega_arith) (by omega_arith)),
        q₅ k hk, hc.out k (by rw [hPdef]; exact hk')]
    · have hi : k - P < r := by omega_arith
      obtain e := d₇ (k - P) hi
      rw [show P + (k - P) = k by omega_arith] at e
      rw [e, d₅ k hk, uorig k hk (by omega_arith)]
      congr 1
      obtain k₆ : s₆.mem (Short.kp' s₀ + BitVec.ofNat 64 (k - P)) =
          s₃.mem (off (cx s₀) 128 + BitVec.ofNat 64 (k - P)) := by
        rw [m₆]
        obtain e₅ := k₅.frame.bytes (R := ⟨off (cx s₀) 128, 256⟩) (fun r hr => by
          simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (show 256 ≤ 2 ^ 64 by decide) (show k - P < 256 by omega_arith)
        rw [show Short.kp' s₀ = off (cx s₀) 128 from rfl, e₅]
        exact f₄.bytes (R := ⟨off (cx s₀) 128, 256⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (show 256 ≤ 2 ^ 64 by decide) (show k - P < 256 by omega_arith)
      obtain st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt u.mem (off (cx s₀) 64) := by
        rw [m₂]
        exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame (memIn_frame (s₀ := s₀) _ _ _) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      obtain hP64 : 64 * (o / 64 + 8 * T) = P := by rw [← hPdef]; omega_arith
      rw [k₆, ks₃ _ (by omega_arith), x0₂, st₂, hc.cnt,
        ks_shift _ hk (q := o / 64 + 8 * T) (by omega_arith), hP64]


/-- `(r - k) >> 63` is 1 iff `r < k`, for both below `2^63`. -/
theorem sub_shr63 {r k : Nat} (hr : r < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 r - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if r < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith : r < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega_arith : k < 2 ^ 64)]
  split
  · rw [Nat.mod_eq_of_lt (by omega_arith : 2 ^ 64 - k + r < 2 ^ 64), show (BitVec.ofNat 64 1).toNat = 1 from rfl]
    exact Nat.div_eq_of_lt_le (by omega_arith) (by omega_arith)
  · rw [show 2 ^ 64 - k + r = (r - k) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith : r - k < 2 ^ 64), Nat.div_eq_of_lt (by omega_arith)]
    rfl

/-- `TailO.test`: `x9 = 0` iff the rest is 65 to 256 bytes. -/
theorem test_ok (w : State) {r : Nat} (hr : r < 2 ^ 63) (hx : w.gpr .x23 = BitVec.ofNat 64 r) :
    WP isa (.block TailO.test) w fun u =>
      isa.eval (.zero .x .x9) u = some (decide (65 ≤ r ∧ r ≤ 256)) ∧ Kept [] w u ∧
      (∀ q, q ≠ .x9 → q ≠ .x10 → q ≠ .x11 → u.gpr q = w.gpr q) ∧
      ∀ v ∈ preservedV, (u.v v).extractLsb' 0 64 = (w.v v).extractLsb' 0 64 := by
  obtain core : WP isa (.block TailO.test) w fun u =>
      u.gpr .x9 = BitVec.ofNat 64 (if 65 ≤ r ∧ r ≤ 256 then 0 else 1) ∧
      (∀ q, q ≠ .x9 → q ≠ .x10 → q ≠ .x11 → u.gpr q = w.gpr q) ∧ u.mem = w.mem ∧ u.rd = w.rd ∧
      u.wr = w.wr := by
    unfold TailO.test
    refine wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
      wp_subImm (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ =>
      wp_addImm (by decide) fun s₆ u₆ => ?_
    simp only [List.replicate]
    refine wp_movz fun t₁ v₁ => wp_movz fun t₂ v₂ => wp_movz fun t₃ v₃ => wp_movz fun t₄ v₄ =>
      wp_movz fun t₅ v₅ => wp_movz fun t₆ v₆ => wp_movz fun t₇ v₇ => wp_movz fun t₈ v₈ =>
      wp_movz fun t₉ v₉ => WP.block_nil ⟨?_, fun q h9 h10 h11 => ?_, ?_, ?_, ?_⟩
    · have b₁ : s₂.gpr .x9 = BitVec.ofNat 64 (if r < 257 then 1 else 0) := by
        rw [u₂.gpr, u₁.gpr, hx, sub_shr63 hr (by decide)]
      obtain b₂ : s₄.gpr .x10 = BitVec.ofNat 64 (if r < 65 then 1 else 0) := by
        rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx, sub_shr63 hr (by decide)]
      rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide),
        v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
        v₁.other _ (by decide), u₆.gpr, u₅.gpr, b₂, u₄.other _ (by decide), u₃.other _ (by decide), b₁]
      by_cases h₁ : r < 65
      · simp only [h₁, show r < 257 by omega_arith, ite_true, show ¬ (65 ≤ r ∧ r ≤ 256) by omega_arith, ite_false]; rfl
      · by_cases h₂ : r < 257
        · simp only [h₁, h₂, ite_true, ite_false, show 65 ≤ r ∧ r ≤ 256 by omega_arith]; rfl
        · simp only [h₁, h₂, ite_false, show ¬ (65 ≤ r ∧ r ≤ 256) by omega_arith]; rfl
    · rw [v₉.other _ h11, v₈.other _ h11, v₇.other _ h11, v₆.other _ h11, v₅.other _ h11, v₄.other _ h11,
        v₃.other _ h11, v₂.other _ h11, v₁.other _ h11, u₆.other _ h9, u₅.other _ h9, u₄.other _ h10,
        u₃.other _ h10, u₂.other _ h9, u₁.other _ h9]
    · rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₆.mem, u₅.mem, u₄.mem,
        u₃.mem, u₂.mem, u₁.mem]
    · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, u₆.rd, u₅.rd, u₄.rd,
        u₃.rd, u₂.rd, u₁.rd]
    · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, u₆.wr, u₅.wr, u₄.wr,
        u₃.wr, u₂.wr, u₁.wr]
  refine WP.mono (WP.preservedV (WP.kept core (by rfl))
    (by rfl)) fun u ⟨⟨⟨h9, hg, hm, hrd, hwr⟩, hk, hsp⟩, hv⟩ =>
      ⟨?_, Kept.of hk hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hg, hv⟩
  rw [show isa.eval (.zero .x .x9) u = some (u.gpr .x9 == 0) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero u .x9, h9]
  by_cases h : 65 ≤ r ∧ r ≤ 256
  · simp only [h, and_self, ite_true, decide_true]; rfl
  · simp only [h, ite_false, decide_false]; rfl

/-- `Crypted` holds after code that writes only `x9`–`x11` (`TailO.test`). -/
theorem Crypted.keep {enc : Bool} {o : Nat} {s₀ s w u u' : State} {key msg : List Byte} {T : Nat}
    (hc : Crypted enc o s₀ s w key msg T u) (hk : Kept [] u u')
    (hg : ∀ q, q ≠ .x9 → q ≠ .x10 → q ≠ .x11 → u'.gpr q = u.gpr q)
    (hv : ∀ v ∈ preservedV, (u'.v v).extractLsb' 0 64 = (u.v v).extractLsb' 0 64) :
    Crypted enc o s₀ s w key msg T u' := by
  obtain hm : u'.mem = u.mem := by
    funext x; exact hk.frame x fun r hr => by simp at hr
  refine ⟨hc.inv.step hk (fun r hr => by simp at hr) (fun r hr => by simp at hr), hc.le, hc.lt,
    by rw [hg _ (by decide) (by decide) (by decide), hc.x0],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x1],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x2],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x3],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x22],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x23],
    by rw [hm]; exact hc.cnt, fun k hk' hk'' => by rw [hm]; exact hc.data k hk' hk'',
    fun k hk' => by rw [hm]; exact hc.out k hk',
    by rw [hm]; exact hc.frame, by rw [hm]; exact hc.mac, fun r hr => (hv r hr).trans (hc.vec r hr)⟩

end VG.Proof.ChaCha20Poly1305.AArch64.TailO
