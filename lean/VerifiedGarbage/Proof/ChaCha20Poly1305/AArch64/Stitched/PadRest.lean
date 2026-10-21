module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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

/-- The stream's arguments for `ctx[768, 1280)`. -/
theorem padArgs_ok {s₀ w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 512 0,
        .addImm .x .x3 .x21 128]) w fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 512 ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w u := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 512 0,
      .addImm .x .x3 .x21 128]) w fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 512 ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ => wp_movz fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hx21],
          by rw [u₄.other _ (by decide), u₃.gpr]; rfl,
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.kept core (by simp [clobbers, dstOf, preserved]))
    fun u ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `openRest`'s branch above the threshold: the data from `P` (fewer than 512
bytes) encrypted from the counter after `P / 64` blocks, through the keystream
of eight blocks at `ctx[768, 1280)`. -/
theorem padRest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hlt : L s₀ - P ≤ 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa (.seq (.block (Pad.zero ++ ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768,
        .movz .x .x2 512 0, .addImm .x .x3 .x21 128] : List Instr)))
      (.seq (.call v.callee.name v.callee.code) (.seq (Short.xorKsFrom 768) (.block Pad.zero)))) w
      fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hL
  have wc := hp.wrap_c
  have ts : Region.Sub (restR s₀ P) (dR s₀) := Offset.sub_base _ (by omega)
  -- The keystream's region zeroed, and the stream's arguments.
  refine WP.seq (WP.block_append (WP.mono (Pad.zero_ok hp hx21 hwr) fun s₁ ⟨k₁, z₁, v₁⟩ => ?_))
  refine WP.mono (WP.preservedV (padArgs_ok (s₀ := s₀) (by rw [k₁.cs _ (pres .x21) (pres30 .x21), hx21]))
    (by lit_decide)) fun s₂ ⟨⟨x0₂, x1₂, x2₂, x3₂, k₂⟩, v₂⟩ => ?_
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, k₁.wr, hwr]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨off (cx s₀) 768, 512⟩, ⟨off (cx s₀) 128, 320⟩] s₂.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 768, rfl, by show 768 + 512 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  -- The stream on the zeros.
  refine WP.seq (xor_call v x0₂ x1₂ x2₂ x3₂ (by decide)
    (sub_disj s₀ (a := 64) (n := 64) (b := 768) (m := 512) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := 512) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by decide)]; lit_omega) (Covers.right hw) hw fun s₃ v₃ k₃ data₃ => ?_)
  have ctxData : ∀ {a n : Nat}, a + n ≤ 1280 → ∀ k < L s₀,
      ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun h k hk hh => hp.c_d.sub_left (sub_ctx s₀ h) _ hh (data_in hk)
  have m₂ : ∀ k < L s₀, s₂.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => by
      rw [k₂.frame _ (fun r hr => absurd hr List.not_mem_nil), k₁.frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ctxData (by lit_omega) k hk)]
  have m₃ : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => by
      rw [k₃.frame _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxData (a := 64) (n := 64) (by lit_omega) k hk
        · exact ctxData (a := 768) (n := 512) (by lit_omega) k hk
        · exact ctxData (a := 128) (n := 320) (by lit_omega) k hk), m₂ k hk]
  have st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt w.mem (off (cx s₀) 64) := by
    rw [stateAt_frame k₂.frame (fun r hr => absurd hr List.not_mem_nil),
      stateAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))]
  -- The keystream from the counter after `P / 64` blocks.
  have ks₃ : ∀ i < 512, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) =
      (keystream (stateAt w.mem (off (cx s₀) 64)) 512).getD i 0 := fun i hi => by
    have x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₃ hi
    rw [x, st₂]
    have z : s₂.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) = 0 := by
      rw [k₂.frame _ (fun r hr => absurd hr List.not_mem_nil),
        show off (cx s₀) 768 + BitVec.ofNat 64 i = cx s₀ + BitVec.ofNat 64 (768 + i) from off_off _ _ _]
      exact z₁.byte (k := i) hi (by decide)
    rw [z]; simp
  -- The data XORed with it.
  have x21₃ : s₃.gpr .x21 = cx s₀ := by
    rw [k₃.cs _ (pres .x21) (pres30 .x21), k₂.cs _ (pres .x21) (pres30 .x21),
      k₁.cs _ (pres .x21) (pres30 .x21), hx21]
  have x22₃ : s₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 P := by
    rw [k₃.cs _ (pres .x22) (pres30 .x22), k₂.cs _ (pres .x22) (pres30 .x22),
      k₁.cs _ (pres .x22) (pres30 .x22), hx22]
  have x23₃ : s₃.gpr .x23 = BitVec.ofNat 64 (L s₀ - P) := by
    rw [k₃.cs _ (pres .x23) (pres30 .x23), k₂.cs _ (pres .x23) (pres30 .x23),
      k₁.cs _ (pres .x23) (pres30 .x23), hx23]
  have rd₃ : s₃.rd = s₀.rd := by rw [k₃.rd, k₂.rd, k₁.rd, hrd]
  have wr₃ : s₃.wr = s₀.wr := by rw [k₃.wr, wr₂]
  refine WP.seq (WP.mono (WP.preservedV (xorKsFromAt_ok hp (k := 768) (o := P) (n := L s₀ - P)
    (by omega) (by omega) x21₃ x22₃ x23₃ rd₃ wr₃) (by lit_decide)) fun s₄ ⟨⟨k₄, d₄, f₄, _⟩, v₄⟩ => ?_)
  -- The keystream zeroed again.
  refine WP.mono (Pad.zero_ok hp (by rw [k₄.cs _ (pres .x21) (pres30 .x21), x21₃])
    (by rw [k₄.wr, wr₃])) fun s₅ ⟨k₅, _, v₅⟩ => ?_
  have tgt : ∀ {rs : List Region}, (∀ r ∈ rs, ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512],
      Region.Sub r r') → ∀ r ∈ rs, ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun h => h
  have T768 : ∀ r ∈ [sub s₀ 768 512], ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have T3 : ∀ r ∈ [(⟨off (cx s₀) 64, 64⟩ : Region), ⟨off (cx s₀) 768, 512⟩, ⟨off (cx s₀) 128, 320⟩],
      ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨sub s₀ 768 512, by simp, fun _ h => h⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  have K : Kept [sub s₀ 64 384, dR s₀, sub s₀ 768 512] w s₅ :=
    ((((k₁.sub T768).trans (k₂.sub fun r hr => absurd hr List.not_mem_nil)).trans (k₃.sub T3)).trans
      (k₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩)).trans
      (k₅.sub T768)
  have F : Frame [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512] w.mem s₅.mem := by
    have T768' : ∀ r ∈ [sub s₀ 768 512], ∃ r' ∈ [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512],
        Region.Sub r r' :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    refine ((((k₁.frame.sub T768').trans (k₂.frame.sub fun r hr => absurd hr List.not_mem_nil)).trans
      (k₃.frame.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_)).trans (k₅.frame.sub T768')
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨sub s₀ 768 512, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨restR s₀ P, by simp, fun _ h => h⟩
  refine ⟨fun r hr => (v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))),
    K, F, ?_⟩
  -- The data encrypted.
  show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
  rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
    VG.Proof.Poly1305.length_bytesAt _ _ _]
  refine VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
  have m₅ : s₅.mem (dp s₀ + BitVec.ofNat 64 k) = s₄.mem (dp s₀ + BitVec.ofNat 64 k) :=
    k₅.frame _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ctxData (by lit_omega) k hk
  rw [m₅]
  by_cases hk' : k < P
  · rw [f₄ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact not_rest hk' hle),
      m₃ k hk, hdata k hk, ite_eq_left hk']
  · have hPL : P < L s₀ := by omega
    have h64 := hP hPL
    have x := d₄ (k - P) (by omega)
    rw [show P + (k - P) = k by omega, m₃ k hk, hdata k hk, ite_eq_right hk'] at x
    rw [x, show kpAt s₀ 768 = off (cx s₀) 768 from rfl, ks₃ (k - P) (by omega), hcnt hPL,
      VG.Proof.ChaCha20.keystream_getD _ (by omega), ks_shift _ hk (q := P / 64) (by omega),
      show 64 * (P / 64) = P by omega]

/-- `openRest`'s test: `x9 = 0` iff the rest is at most `Pad.threshold sve`. -/
theorem restSplit_ok (sve : Bool) (w : State) :
    WP isa (.block [.addImm .x .x9 .x23 (511 - Pad.threshold sve), .lsr .x .x9 .x9 9]) w fun u =>
      u.gpr .x9 = (w.gpr .x23 + BitVec.ofNat 64 (511 - Pad.threshold sve)) >>> 9 ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block [.addImm .x .x9 .x23 (511 - Pad.threshold sve), .lsr .x .x9 .x9 9]) w
      fun u => u.gpr .x9 = (w.gpr .x23 + BitVec.ofNat 64 (511 - Pad.threshold sve)) >>> 9 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_addImm (by cases sve <;> decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
      WP.block_nil ⟨by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
        by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.kept core (by cases sve <;> simp [clobbers, dstOf, preserved]))
    (by cases sve <;> lit_decide)) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
      ⟨h9, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hv⟩

/-- `openRest`: the data from `P` (fewer than 512 bytes) encrypted from the
counter after `P / 64` blocks, as a call of the stream would, but for
`ctx[768, 1280)`. -/
theorem openRest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hlt : L s₀ - P < 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa (openRest v.callee) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold openRest cryptRest
  refine WP.seq (WP.mono (restSplit_ok v.callee.sve w) fun w₁ ⟨x9₁, k₁, v₁⟩ => ?_)
  have mw := k₁.mem_eq
  have g₁ : ∀ r, r ∈ preserved → r ≠ .x30 → w₁.gpr r = w.gpr r := k₁.cs
  have hx21₁ : w₁.gpr .x21 = cx s₀ := by rw [g₁ _ (pres .x21) (pres30 .x21), hx21]
  have hx22₁ : w₁.gpr .x22 = dp s₀ + BitVec.ofNat 64 P := by rw [g₁ _ (pres .x22) (pres30 .x22), hx22]
  have hx23₁ : w₁.gpr .x23 = BitVec.ofNat 64 (L s₀ - P) := by rw [g₁ _ (pres .x23) (pres30 .x23), hx23]
  have hrd₁ : w₁.rd = s₀.rd := by rw [k₁.rd, hrd]
  have hwr₁ : w₁.wr = s₀.wr := by rw [k₁.wr, hwr]
  have hcnt₁ : P < L s₀ →
      stateAt w₁.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64) :=
    fun h => by rw [mw]; exact hcnt h
  have hdata₁ : ∀ k < L s₀, w₁.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by rw [mw]; exact hdata k hk
  have none : ∀ r ∈ ([] : List Region), ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun _ hr => absurd hr List.not_mem_nil
  refine WP.ite (decide (L s₀ - P ≤ Pad.threshold v.callee.sve))
    (by rw [show isa.eval (.zero .x .x9) w₁ = some (w₁.gpr .x9 == 0) from
      VG.Proof.ChaCha20.AArch64.Xor.eval_zero w₁ .x9, x9₁, hx23]
        exact congrArg some (Pad.splitVal_eq _ (by omega)))
    (fun _ => ?_) (fun _ => ?_)
  · -- The stream on the rest.
    refine WP.seq ((restArgs_ok hx21₁).mono fun w₂ ⟨⟨a0, a1, a2, a3, kw⟩, vw⟩ => ?_)
    have mw₂ := kw.mem_eq
    refine (rest_call v hp (s := s) (P := P) hle hP a0 (by rw [a1, hx22₁]) (by rw [a2, hx23₁]) a3
      (by rw [kw.wr, hwr₁]) (fun h => by rw [mw₂]; exact hcnt₁ h)
      (fun k hk => by rw [mw₂]; exact hdata₁ k hk)).mono fun u ⟨vu, ku, fu, pu⟩ =>
        ⟨fun r hr => (vu r hr).trans ((vw r hr).trans (v₁ r hr)),
          ((k₁.trans kw).sub none).trans (ku.sub fun r hr => ?_), ?_, pu⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · rw [← mw, ← mw₂]
      refine fu.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · -- Eight blocks of keystream.
    exact (padRest_ok v hp hle (by omega) hP hx21₁ hx22₁ hx23₁ hrd₁ hwr₁ hcnt₁ hdata₁).mono
      fun u ⟨vu, ku, fu, pu⟩ => ⟨fun r hr => (vu r hr).trans (v₁ r hr), (k₁.sub none).trans ku,
        by rw [← mw]; exact fu, pu⟩

end VG.Proof.ChaCha20Poly1305.AArch64
