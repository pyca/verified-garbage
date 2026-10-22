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

theorem setWidth_ofNat16 {n : Nat} (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The stream's arguments for `ctx[768, 768 + n)`. -/
theorem padArgs_ok {s₀ w : State} {n : Nat} (hn : n < 2 ^ 16) (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 (BitVec.ofNat 16 n) 0,
        .addImm .x .x3 .x21 128]) w fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 n ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w u := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 (BitVec.ofNat 16 n) 0,
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
  exact WP.mono (WP.kept core (by simp [clobbers, dstOf, preserved]))
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
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa (padRest v.callee n) w
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
  unfold padRest
  -- The keystream's region zeroed, and the stream's arguments.
  refine WP.seq (WP.block_append (WP.mono (Pad.zero_ok hp hx21 hwr) fun s₁ ⟨k₁, z₁, v₁⟩ => ?_))
  refine WP.mono (WP.preservedV (padArgs_ok (s₀ := s₀) (n := n) (by omega) (by rw [k₁.cs _ (pres .x21) (pres30 .x21), hx21]))
    (by simp [Code.allInstrs, keepsV, vdstOf])) fun s₂ ⟨⟨x0₂, x1₂, x2₂, x3₂, k₂⟩, v₂⟩ => ?_
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, k₁.wr, hwr]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨off (cx s₀) 768, n⟩, ⟨off (cx s₀) 128, 320⟩] s₂.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 768, rfl, by show 768 + n ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₂]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  -- The stream on the zeros.
  refine WP.seq (xor_call v x0₂ x1₂ x2₂ x3₂ (by omega)
    (sub_disj s₀ (a := 64) (n := 64) (b := 768) (m := n) (by omega) (by omega) (by omega))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := n) (b := 128) (m := 320) (by omega) (by omega) (by omega))
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
        · exact ctxData (a := 768) (n := n) (by omega) k hk
        · exact ctxData (a := 128) (n := 320) (by lit_omega) k hk), m₂ k hk]
  have st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt w.mem (off (cx s₀) 64) := by
    rw [stateAt_frame k₂.frame (fun r hr => absurd hr List.not_mem_nil),
      stateAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))]
  -- The keystream from the counter after `P / 64` blocks.
  have ks₃ : ∀ i < n, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) =
      (keystream (stateAt w.mem (off (cx s₀) 64)) n).getD i 0 := fun i hi => by
    have x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₃ hi
    rw [x, st₂]
    have z : s₂.mem (off (cx s₀) 768 + BitVec.ofNat 64 i) = 0 := by
      rw [k₂.frame _ (fun r hr => absurd hr List.not_mem_nil),
        show off (cx s₀) 768 + BitVec.ofNat 64 i = cx s₀ + BitVec.ofNat 64 (768 + i) from off_off _ _ _]
      exact z₁.byte (k := i) (by omega) (by decide)
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
  have T3 : ∀ r ∈ [(⟨off (cx s₀) 64, 64⟩ : Region), ⟨off (cx s₀) 768, n⟩, ⟨off (cx s₀) 128, 320⟩],
      ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨sub s₀ 768 512, by simp, sub_sub s₀ (Nat.le_refl _) (by omega) (by omega)⟩
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
      · exact ⟨sub s₀ 768 512, by simp, sub_sub s₀ (Nat.le_refl _) (by omega) (by omega)⟩
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

/-- `openRest`'s test of whole blocks: `x9 = 0` iff the rest is a multiple of 64. -/
theorem restWhole_ok (w : State) :
    WP isa (.block [.lsl .x .x9 .x23 58]) w fun u =>
      u.gpr .x9 = w.gpr .x23 <<< 58 ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block [.lsl .x .x9 .x23 58]) w
      fun u => u.gpr .x9 = w.gpr .x23 <<< 58 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_lsl (by decide) fun s₁ u₁ =>
      WP.block_nil ⟨u₁.gpr, u₁.mem, u₁.rd, u₁.wr⟩
  exact WP.mono (WP.preservedV (WP.kept core (by simp [clobbers, dstOf, preserved]))
    (by lit_decide)) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
      ⟨h9, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hv⟩

/-- `openRest`'s tests of a bound: `x9 = 0` iff the rest, at least 1, is at most `2^k`. -/
theorem restAtMost_ok (k : Nat) (hk : k < 64) (w : State) :
    WP isa (.block (atMost k)) w fun u =>
      u.gpr .x9 = (w.gpr .x23 - BitVec.ofNat 64 1) >>> k ∧ Kept [] w u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block (atMost k)) w
      fun u => u.gpr .x9 = (w.gpr .x23 - BitVec.ofNat 64 1) >>> k ∧ u.mem = w.mem ∧ u.rd = w.rd ∧
        u.wr = w.wr :=
    VG.Proof.ChaCha20.AArch64.Xor.wp_subImm (by decide) fun s₁ u₁ => wp_lsr hk fun s₂ u₂ =>
      WP.block_nil ⟨by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
        by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.kept core (by simp [atMost, clobbers, dstOf, preserved]))
    (by simp [atMost, Code.allInstrs, keepsV, vdstOf])) fun u ⟨⟨⟨h9, hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ =>
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
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [show (2 ^ 64 - 1 % 2 ^ 64 + r) % 2 ^ 64 = r - 1 by omega, Nat.div_eq_zero_iff_lt hp]
  omega

/-- `padRest` after code that kept everything but `x9`. -/
theorem padRest_after (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀)
    {s w w' : State} {P n : Nat} (hn : n ≤ 512) (hle : P ≤ L s₀) (hlt : L s₀ - P ≤ n)
    (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k))
    (k : Kept [] w w') (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) :
    WP isa (padRest v.callee n) w' fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have mw := k.mem_eq
  have none : ∀ r ∈ ([] : List Region), ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512], Region.Sub r r' :=
    fun _ hr => absurd hr List.not_mem_nil
  exact (padRest_ok v hp hn hle hlt hP (by rw [k.cs _ (pres .x21) (pres30 .x21), hx21])
    (by rw [k.cs _ (pres .x22) (pres30 .x22), hx22]) (by rw [k.cs _ (pres .x23) (pres30 .x23), hx23])
    (by rw [k.rd, hrd]) (by rw [k.wr, hwr]) (fun h => by rw [mw]; exact hcnt h)
    (fun i hi => by rw [mw]; exact hdata i hi)).mono
      fun u ⟨vu, ku, fu, pu⟩ => ⟨fun r hr => (vu r hr).trans (vw r hr), (k.sub none).trans ku,
        by rw [← mw]; exact fu, pu⟩

/-- `cryptRest` after code that kept everything but `x9`. -/
theorem cryptRest_after (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀)
    {s w w' : State} {P : Nat} (hle : P ≤ L s₀) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k))
    (k : Kept [] w w') (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) :
    WP isa (cryptRest v.callee) w' fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have mw := k.mem_eq
  have none : ∀ r ∈ ([] : List Region), ∃ r' ∈ [sub s₀ 64 384, dR s₀, sub s₀ 768 512],
      Region.Sub r r' := fun _ hr => absurd hr List.not_mem_nil
  unfold cryptRest
  refine WP.seq ((restArgs_ok (s₀ := s₀) (by rw [k.cs _ (pres .x21) (pres30 .x21), hx21])).mono
    fun w₃ ⟨⟨a0, a1, a2, a3, kw⟩, vw₃⟩ => ?_)
  have mw₃ := kw.mem_eq
  refine (rest_call v hp (s := s) (P := P) hle hP a0
    (by rw [a1, k.cs _ (pres .x22) (pres30 .x22), hx22])
    (by rw [a2, k.cs _ (pres .x23) (pres30 .x23), hx23]) a3
    (by rw [kw.wr, k.wr, hwr]) (fun h => by rw [mw₃, mw]; exact hcnt h)
    (fun i hi => by rw [mw₃, mw]; exact hdata i hi)).mono fun u ⟨vu, ku, fu, pu⟩ =>
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
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have pad := fun {w' : State} {n : Nat} (hn : n ≤ 512) (hlt' : L s₀ - P ≤ n) (k : Kept [] w w')
      (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) =>
    padRest_after (s := s) v hp hn hle hlt' hP hx21 hx22 hx23 hrd hwr hcnt hdata k vw
  have crypt := fun {w' : State} (k : Kept [] w w')
      (vw : ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) =>
    cryptRest_after (s := s) v hp hle hP hx21 hx22 hx23 hwr hcnt hdata k vw
  have x23k : ∀ {w' : State}, Kept [] w w' → w'.gpr .x23 = BitVec.ofNat 64 (L s₀ - P) :=
    fun k => by rw [k.cs _ (pres .x23) (pres30 .x23), hx23]
  have evz : ∀ (u : State), isa.eval (.zero .x .x9) u = some (u.gpr .x9 == 0) :=
    fun u => VG.Proof.ChaCha20.AArch64.Xor.eval_zero u .x9
  unfold openRest
  refine WP.seq (WP.mono (restSplit_ok v.callee.sve w) fun w₁ ⟨x9₁, k₁, v₁⟩ => ?_)
  refine WP.ite (decide (L s₀ - P ≤ Pad.threshold v.callee.sve))
    (by rw [evz, x9₁, hx23]; exact congrArg some (Pad.splitVal_eq _ (by omega)))
    (fun _ => ?_) (fun _ => pad (by omega) (by omega) k₁ v₁)
  -- At most the threshold: whole blocks through the stream.
  refine WP.seq (WP.mono (restWhole_ok w₁) fun w₂ ⟨x9₂, k₂, v₂⟩ => ?_)
  have k₂' : Kept [] w w₂ := k₁.trans k₂
  have v₂' : ∀ r ∈ preservedV, (w₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₂ r hr).trans (v₁ r hr)
  refine WP.ite (decide ((L s₀ - P) % 64 = 0))
    (by rw [evz, x9₂, x23k k₁]; exact congrArg some (whole_eq (by omega)))
    (fun _ => crypt k₂' v₂') (fun hwh => ?_)
  have h1 : 1 ≤ L s₀ - P := Nat.pos_of_ne_zero fun h => by
    rw [h] at hwh; exact absurd hwh (by decide)
  -- At most 64 bytes: one scalar block in the stream.
  refine WP.seq (WP.mono (restAtMost_ok 6 (by decide) w₂) fun w₃ ⟨x9₃, k₃, v₃⟩ => ?_)
  have k₃' : Kept [] w w₃ := k₂'.trans k₃
  have v₃' : ∀ r ∈ preservedV, (w₃.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₃ r hr).trans (v₂' r hr)
  refine WP.ite (decide (L s₀ - P ≤ 2 ^ 6))
    (by rw [evz, x9₃, x23k k₂']; exact congrArg some (atMost_eq h1 (by omega)))
    (fun _ => crypt k₃' v₃') (fun _ => ?_)
  -- Up to 256 bytes: four blocks of keystream; above, the stream.
  refine WP.seq (WP.mono (restAtMost_ok 8 (by decide) w₃) fun w₄ ⟨x9₄, k₄, v₄⟩ => ?_)
  have k₄' : Kept [] w w₄ := k₃'.trans k₄
  have v₄' : ∀ r ∈ preservedV, (w₄.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 :=
    fun r hr => (v₄ r hr).trans (v₃' r hr)
  refine WP.ite (decide (L s₀ - P ≤ 2 ^ 8))
    (by rw [evz, x9₄, x23k k₃']; exact congrArg some (atMost_eq h1 (by omega)))
    (fun h4 => pad (by decide) (by simpa using h4) k₄' v₄') (fun _ => crypt k₄' v₄')

end VG.Proof.ChaCha20Poly1305.AArch64
