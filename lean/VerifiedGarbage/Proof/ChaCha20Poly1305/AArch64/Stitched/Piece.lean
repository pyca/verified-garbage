module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64, stitched: 256 bytes of the rest

`Rest.piece` zeroes `ctx[128, 384)` and XORs into it the keystream of the
four blocks from the stream's counter (`Neon4.chunk`), and advances the
counter past them; `Rest.step` then XORs up to 256 bytes of the data with
it (`Short.xorKs`): `step_ok`, the data's first `Q + n` bytes encrypted from
the first `Q` (`Done`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

/-- The data's first `Q` bytes XORed with the keystream from counter 1, and
the others as in `s`. -/
def Done (s₀ s : State) (Q : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) =
    if k < Q then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)

/-- The keystream from block `q`. -/
theorem ks_shift (S : VG.Proof.ChaCha20.CState) {len q k : Nat} (hk : k < len) (hq : 64 * q ≤ k) :
    (Spec.ChaCha20.keystream S len).getD k 0 =
      (Spec.ChaCha20.serialize (Spec.ChaCha20.block (ctr (ctr S q) ((k - 64 * q) / 64)))).getD
        ((k - 64 * q) % 64) 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ hk, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show q + (k - 64 * q) / 64 = k / 64 by omega, show (k - 64 * q) % 64 = k % 64 by omega]

/-- The bytes `[Q, Q + n)` of the data do not hold byte `k` outside them. -/
theorem not_in {s₀ : State} {Q n k : Nat} (hk : k < Q ∨ Q + n ≤ k) (hQ : Q + n ≤ L s₀)
    (hkL : k < L s₀) :
    ¬ (⟨dp s₀ + BitVec.ofNat 64 Q, n⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- The context holds no byte of the data. -/
theorem ctx_not_data {s₀ : State} (hp : APre e s₀) {a n k : Nat} (h : a + n ≤ 1280)
    (hk : k < L s₀) : ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  fun hh => hp.c_d.sub_left (sub_ctx s₀ h) _ hh
    (Offset.contains_base _ (by omega) (by have h : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt; omega))

/-- `Rest.piece`: the keystream of the four blocks from the counter at
`ctx[128, 384)`, and the counter advanced past them. -/
theorem piece_ok {s₀ : State} (hp : APre e s₀) {w : State} (hx21 : w.gpr .x21 = cx s₀)
    (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr) :
    WP isa Rest.piece w fun u =>
      (∀ k < 256, u.mem (off (cx s₀) 128 + BitVec.ofNat 64 k) =
        (Spec.ChaCha20.serialize (Spec.ChaCha20.block
          (ctr (stateAt w.mem (off (cx s₀) 64)) (k / 64)))).getD (k % 64) 0) ∧
      stateAt u.mem (off (cx s₀) 64) = ctr (stateAt w.mem (off (cx s₀) 64)) 4 ∧
      Frame [sub s₀ 64 320] w.mem u.mem ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x4 → u.gpr r = w.gpr r) ∧ u.rd = w.rd ∧ u.wr = w.wr := by
  have oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  unfold Rest.piece
  refine WP.seq (WP.block_append ?_)
  rw [List.singleton_append]
  refine WP.mono (Short.zeroAt_ok (b := 128) (J := 16) (by decide) (by decide) hx21 fun a ha => by
    rw [hwr]; exact hp.in_ctx (a := 128 + a) (by omega)) fun s₁ ⟨g₁, rd₁, wr₁, _, _, z₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ u₂ => wp_addImm (by decide) fun s₃ u₃ => WP.block_nil ?_
  have x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by
    rw [u₃.other _ (by decide), u₂.gpr, g₁, hx21]
  have x1₃ : s₃.gpr .x1 = off (cx s₀) 128 := by rw [u₃.gpr, u₂.other _ (by decide), g₁, hx21]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, rd₁, hrd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, wr₁, hwr]
  have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Neon4.chunk_ok s₃
    (fun k => by rw [x0₃, oo, rd₃, wr₃]; exact hp.in_ctx' (by omega))
    (fun r j => by rw [x1₃, oo, wr₃]; exact hp.in_ctx (by omega))).mono
    fun s₄ ⟨ks₄, f₄, k₄⟩ => ?_)
  rw [x1₃] at ks₄ f₄
  have x0₄ : s₄.gpr .x0 = off (cx s₀) 64 := by rw [k₄.gpr _ (by decide), x0₃]
  have p48 : s₄.gpr .x0 + BitVec.ofNat 64 48 = off (cx s₀) 112 := by rw [x0₄, oo]
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.counter_ok s₄ (by decide) false
    (by rw [p48, k₄.rd, k₄.wr, rd₃, wr₃]; exact hp.in_ctx' (by lit_omega))
    (by rw [p48, k₄.wr, wr₃]; exact hp.in_ctx (by lit_omega))).mono
    fun s₅ ⟨m₅, g₅, rd₅, wr₅, _, _⟩ => ?_
  simp only [Bool.false_eq_true, ite_false] at m₅
  have f₅ : Frame [sub s₀ 112 4] s₄.mem s₅.mem := by
    rw [m₅, p48]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (contains_sub s₀ (by decide) (by decide)
      (by lit_omega))
  have z₁f : Frame [sub s₀ 128 256] w.mem s₁.mem := z₁.frame (by decide)
  have d64 : (⟨off (cx s₀) 64, 64⟩ : Region).Disjoint (sub s₀ 128 256) :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = stateAt w.mem (off (cx s₀) 64) := by
    rw [m₃]; exact stateAt_frame z₁f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d64
  refine ⟨fun k hk => ?_, ?_, ?_, fun r h0 h1 h4 => ?_, by rw [rd₅, k₄.rd, u₃.rd, u₂.rd, rd₁],
    by rw [wr₅, k₄.wr, u₃.wr, u₂.wr, wr₁]⟩
  · rw [f₅.bytes (R := sub s₀ 128 256) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (show 256 ≤ 2 ^ 64 by decide) hk,
      ks₄ k hk, x0₃, st₃, m₃, oo, z₁.byte (k := k) hk (by decide)]
    simp
  · rw [m₅, show off (cx s₀) 64 = s₄.gpr .x0 from x0₄.symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr, x0₄,
      stateAt_frame f₄ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact d64, st₃]
  · have fs : ∀ r ∈ [sub s₀ 128 256], ∃ r' ∈ [sub s₀ 64 320], Region.Sub r r' := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
    have f₁₃ : Frame [sub s₀ 64 320] w.mem s₃.mem := by rw [m₃]; exact z₁f.sub fs
    exact f₁₃.trans ((f₄.sub fs).trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩))
  · rw [g₅ r h4, k₄.gpr r h4, u₃.other r h1, u₂.other r h0, g₁]

/-- `Rest.step`: `n ≤ 256` bytes of the data from `Q`, XORed with the
keystream from counter `Q / 64`, and the counter advanced past four blocks. -/
theorem step_ok {s₀ : State} (hp : APre e s₀) {s w : State} {Q n : Nat} (hn : n ≤ 256)
    (hQ : Q + n ≤ L s₀) (h64 : Q % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 Q)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 n) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : stateAt w.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (Q / 64))
    (hd : Done s₀ s Q w.mem) :
    WP isa Rest.step w fun u => Done s₀ s (Q + n) u.mem ∧
      stateAt u.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (Q / 64 + 4) ∧
      Frame [sub s₀ 64 320, ⟨dp s₀ + BitVec.ofNat 64 Q, n⟩] w.mem u.mem ∧
      (∀ r, r ∉ [Reg.x0, .x1, .x4, .x9, .x10, .x11, .x12, .x13] → u.gpr r = w.gpr r) ∧
      u.rd = w.rd ∧ u.wr = w.wr := by
  unfold Rest.step
  refine WP.seq ((piece_ok hp hx21 hrd hwr).mono fun s₁ ⟨ks₁, st₁, f₁, g₁, rd₁, wr₁⟩ => ?_)
  refine (Short.xorKsAt_ok hp (o := Q) hn hQ (by rw [g₁ _ (by decide) (by decide) (by decide), hx21])
    (by rw [g₁ _ (by decide) (by decide) (by decide), hx22])
    (by rw [g₁ _ (by decide) (by decide) (by decide), hx23]) (by rw [rd₁, hrd]) (by rw [wr₁, hwr])).mono
    fun s₂ ⟨k₂, d₂, f₂, g₂⟩ => ?_
  rw [hcnt] at ks₁ st₁
  have dw : ∀ k < L s₀, s₁.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₁ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ctx_not_data hp (by lit_omega) hk
  refine ⟨fun k hk => ?_, ?_, ?_, fun r hr => ?_, by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁]⟩
  · by_cases hin : Q ≤ k ∧ k < Q + n
    · have x := d₂ (k - Q) (by omega)
      rw [show Q + (k - Q) = k by omega, dw k hk, hd k hk, ite_eq_right (by omega)] at x
      rw [x, ite_eq_left (by omega), ks_shift _ hk (q := Q / 64) (by omega),
        show 64 * (Q / 64) = Q by omega]
      exact congrArg _ (ks₁ (k - Q) (by omega))
    · rw [f₂ _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in (by omega) hQ hk,
        dw k hk, hd k hk]
      by_cases hk' : k < Q
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · rw [stateAt_frame k₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (data_ctx hp (by lit_omega)).symm,
      st₁, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add]
  · exact (f₁.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans
      (f₂.mono fun r hr => by simp [List.mem_singleton.mp hr])
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h4, h9, h10, h11, h12, h13⟩ := hr
    rw [g₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
      ⟨h9, h10, h11, h12, h13⟩), g₁ r h0 h1 h4]

end VG.Proof.ChaCha20Poly1305.AArch64
