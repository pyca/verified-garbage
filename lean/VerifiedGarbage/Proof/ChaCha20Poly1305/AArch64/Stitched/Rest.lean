module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Piece
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the rest of the data

The data after the first `P` bytes (the chunks, and when encrypting up to
256 bytes more), fewer than 512, XORed with the keystream from the counter
after them, 256 bytes at a time (`Rest.crypt`, `Piece.lean`): the whole data
encrypted from counter 1.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_mov wp_movz wp_lsr eval_zero
  ofNat_beq_zero sub_ofNat add_ofNat)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-- The data after its first `P` bytes. -/
abbrev restR (s₀ : State) (P : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 P, L s₀ - P⟩

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt; omega)

theorem not_rest {s₀ : State} {P k : Nat} (hk : k < P) (hP : P ≤ L s₀) :
    ¬ (restR s₀ P).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- The data before the rest is kept. -/
theorem prefix_rest {s₀ : State} (hp : APre e s₀) {m m' : Mem} {P n : Nat}
    (hf : Frame [sub s₀ 64 384, restR s₀ P] m m') (hn : n ≤ P) (hP : P ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 384) (by lit_omega)) _ hh
      (data_in (by omega))
  · exact not_rest (by omega) hP

theorem shr8 {r : Nat} (h : r < 2 ^ 64) : BitVec.ofNat 64 r >>> 8 = BitVec.ofNat 64 (r / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.ChaCha20.AArch64.toNat_ofNat_lt h,
    VG.Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem eval_zero' (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 k) :
    isa.eval (.zero .x r) s = some (decide (k = 0)) := by
  rw [show isa.eval (.zero .x r) s = some (s.gpr r == 0) from eval_zero s r, h, ofNat_beq_zero hk]

/-- `x9 = (r - 1) / 256`, from `r` in `x`. -/
theorem over_ok {is : List Instr} {s : State} {x : Reg} {r : Nat} (hr : 0 < r) (hr' : r < 2 ^ 64)
    (hx : s.gpr x = BitVec.ofNat 64 r) {Q : State → Prop}
    (k : ∀ u, u.gpr .x9 = BitVec.ofNat 64 ((r - 1) / 256) → (∀ q, q ≠ .x9 → u.gpr q = s.gpr q) →
      u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → WP isa (.block is) u Q) :
    WP isa (.block (.subImm .x .x9 x 1 :: .lsr .x .x9 .x9 8 :: is)) s Q :=
  wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => k s₂
    (by rw [u₂.gpr, u₁.gpr, hx, sub_ofNat (by omega), shr8 (by omega)])
    (fun q hq => by rw [u₂.other _ hq, u₁.other _ hq]) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

/-- `x23 = min r 256`. -/
theorem min256_ok {s : State} {r : Nat} (hr : 0 < r) (hr' : r < 512)
    (hx9 : s.gpr .x9 = BitVec.ofNat 64 ((r - 1) / 256)) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r) :
    WP isa (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x23 256 0])) s fun u =>
      u.gpr .x23 = BitVec.ofNat 64 (min r 256) ∧ (∀ q, q ≠ .x23 → u.gpr q = s.gpr q) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  refine WP.ite (decide ((r - 1) / 256 = 0)) (eval_zero' s .x9 (by omega) hx9) (fun h => ?_) (fun h => ?_)
  · have h' : r ≤ 256 := by have := of_decide_eq_true h; omega
    exact WP.block_nil ⟨by rw [hx23, Nat.min_eq_left h'], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h' : 256 ≤ r := by have := of_decide_eq_false h; omega
    exact wp_movz fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, Nat.min_eq_right h']; rfl,
      fun q hq => u₁.other _ hq, u₁.mem, u₁.rd, u₁.wr⟩

/-- What `Rest.crypt` leaves of the registers it uses. -/
abbrev cryptRegs : List Reg := [.x0, .x1, .x4, .x7, .x9, .x10, .x11, .x12, .x13]

theorem cryptRegs_preserved : ∀ r ∈ preserved, r ∉ cryptRegs := by decide

/-- `Rest.crypt`: the data after `P`, fewer than 512 bytes, encrypted from the
counter after `P / 64` blocks. -/
theorem restCrypt_ok {s₀ : State} (hp : APre e s₀) {s w : State} {P : Nat}
    (hle : P ≤ L s₀) (hlt : L s₀ - P < 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hd : Done s₀ s P w.mem) :
    WP isa Rest.crypt w fun u => Done s₀ s (L s₀) u.mem ∧
      Frame [sub s₀ 64 320, restR s₀ P] w.mem u.mem ∧
      (∀ q, q ∉ cryptRegs → u.gpr q = w.gpr q) ∧ u.rd = w.rd ∧ u.wr = w.wr := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wd := hp.wrap_d
  unfold Rest.crypt
  refine WP.ite (decide (L s₀ - P = 0)) (eval_zero' w .x23 (by omega) hx23) (fun h0 => ?_) (fun h0 => ?_)
  · have e : L s₀ = P := by have := of_decide_eq_true h0; omega
    exact WP.block_nil ⟨by rw [e]; exact hd, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  have hr0 : 0 < L s₀ - P := by have := of_decide_eq_false h0; omega
  have h64 := hP (by omega)
  have hc := hcnt (by omega)
  have fd : ∀ {Q n : Nat}, P ≤ Q → Q + n ≤ L s₀ → ∀ r ∈ [sub s₀ 64 320, ⟨dp s₀ + BitVec.ofNat 64 Q, n⟩],
      ∃ r' ∈ [sub s₀ 64 320, restR s₀ P], Region.Sub r r' := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨restR s₀ P, by simp, Offset.sub _ h₁ (by omega)⟩
  -- `x7 = r`, `x9 = (r - 1) / 256`.
  refine WP.seq (wp_mov fun s₁ u₁ => over_ok (x := .x23) hr0 (by omega)
    (by rw [u₁.other _ (by decide), hx23]) fun s₂ x9₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_)
  have g₂' : ∀ q, q ≠ .x7 → q ≠ .x9 → s₂.gpr q = w.gpr q := fun q h7 h9 => by
    rw [g₂ q h9, u₁.other _ h7]
  have x7₂ : s₂.gpr .x7 = BitVec.ofNat 64 (L s₀ - P) := by rw [g₂ _ (by decide), u₁.gpr, hx23]
  -- `x23 = min r 256`.
  refine WP.seq ((min256_ok hr0 hlt x9₂ (by rw [g₂' _ (by decide) (by decide), hx23])).mono
    fun s₃ ⟨x23₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have m₃' : s₃.mem = w.mem := by rw [m₃, m₂, u₁.mem]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, u₁.rd, hrd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, u₁.wr, hwr]
  have g₃' : ∀ q, q ≠ .x7 → q ≠ .x9 → q ≠ .x23 → s₃.gpr q = w.gpr q := fun q h7 h9 h23 => by
    rw [g₃ q h23, g₂' q h7 h9]
  -- The first 256 bytes, or fewer.
  refine WP.seq ((step_ok hp (s := s) (Q := P) (n := min (L s₀ - P) 256) (Nat.min_le_right _ _)
    (by omega) (by omega) (by rw [g₃' _ (by decide) (by decide) (by decide), hx21])
    (by rw [g₃' _ (by decide) (by decide) (by decide), hx22]) x23₃ rd₃' wr₃'
    (by rw [m₃', hc]) (by rw [m₃']; exact hd)).mono fun s₄ ⟨d₄, st₄, f₄, g₄, rd₄, wr₄⟩ => ?_)
  rw [m₃'] at f₄
  have g₄' : ∀ q, q ∉ cryptRegs → q ≠ .x23 → s₄.gpr q = w.gpr q := fun q hq h23 => by
    simp only [cryptRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨h0, h1, h4, h7, h9, h10, h11, h12, h13⟩ := hq
    rw [g₄ q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
      ⟨h0, h1, h4, h9, h10, h11, h12, h13⟩), g₃' q h7 h9 h23]
  have x7₄ : s₄.gpr .x7 = BitVec.ofNat 64 (L s₀ - P) := by
    rw [g₄ _ (by decide), g₃ _ (by decide), x7₂]
  -- Whether more follows, and `x23` restored.
  refine WP.seq (over_ok (x := .x7) hr0 (by omega) x7₄ fun s₅ x9₅ g₅ m₅ rd₅ wr₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ?_)
  have x23₆ : s₆.gpr .x23 = w.gpr .x23 := by rw [u₆.gpr, g₅ _ (by decide), x7₄, hx23]
  have g₆ : ∀ q, q ∉ cryptRegs → s₆.gpr q = w.gpr q := fun q hq => by
    by_cases h23 : q = .x23
    · subst h23; exact x23₆
    · rw [u₆.other _ h23, g₅ _ (fun h => hq (by simp [h])), g₄' q hq h23]
  have x9₆ : s₆.gpr .x9 = BitVec.ofNat 64 ((L s₀ - P - 1) / 256) := by
    rw [u₆.other _ (by decide), x9₅]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, m₅]
  refine WP.ite (decide ((L s₀ - P - 1) / 256 = 0)) (eval_zero' s₆ .x9 (by omega) x9₆)
    (fun h => ?_) (fun h => ?_)
  · -- Nothing more.
    have h' : L s₀ - P ≤ 256 := by have := of_decide_eq_true h; omega
    rw [show P + min (L s₀ - P) 256 = L s₀ by omega] at d₄
    refine WP.block_nil ⟨by rw [m₆]; exact d₄, by rw [m₆]; exact f₄.sub (fd (Nat.le_refl _) (by omega)),
      g₆, by rw [u₆.rd, rd₅, rd₄, rd₃', hrd], by rw [u₆.wr, wr₅, wr₄, wr₃', hwr]⟩
  · -- The bytes after the first 256.
    have h' : 256 < L s₀ - P := by have := of_decide_eq_false h; omega
    rw [Nat.min_eq_right (by omega)] at d₄ f₄
    refine WP.seq (wp_addImm (by decide) fun s₇ u₇ => wp_subImm (by decide) fun s₈ u₈ =>
      WP.block_nil ?_)
    have g₈ : ∀ q, q ≠ .x22 → q ≠ .x23 → s₈.gpr q = s₆.gpr q := fun q h22 h23 => by
      rw [u₈.other _ h23, u₇.other _ h22]
    have x22₆ : s₆.gpr .x22 = dp s₀ + BitVec.ofNat 64 P := by
      rw [g₆ _ (by decide), hx22]
    refine WP.seq ((step_ok hp (s := s) (Q := P + 256) (n := L s₀ - P - 256) (by omega) (by omega)
      (by omega) (by rw [g₈ _ (by decide) (by decide), g₆ _ (by decide), hx21])
      (by rw [u₈.other _ (by decide), u₇.gpr, x22₆, add_ofNat])
      (by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), x7₄,
        sub_ofNat (by omega)])
      (by rw [u₈.rd, u₇.rd, u₆.rd, rd₅, rd₄, rd₃']) (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅, wr₄, wr₃'])
      (by rw [u₈.mem, u₇.mem, m₆, st₄, show (P + 256) / 64 = P / 64 + 4 by omega])
      (by rw [u₈.mem, u₇.mem, m₆]; exact d₄)).mono fun s₉ ⟨d₉, _, f₉, g₉, rd₉, wr₉⟩ => ?_)
    refine wp_subImm (by decide) fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => WP.block_nil ?_
    rw [show P + 256 + (L s₀ - P - 256) = L s₀ by omega] at d₉
    have m₈ : s₈.mem = s₄.mem := by rw [u₈.mem, u₇.mem, m₆]
    rw [m₈] at f₉
    refine ⟨by rw [u₁₁.mem, u₁₀.mem]; exact d₉, by
        rw [u₁₁.mem, u₁₀.mem]
        exact (f₄.sub (fd (Nat.le_refl _) (by omega))).trans (f₉.sub (fd (by omega) (by omega))),
      fun q hq => ?_, by rw [u₁₁.rd, u₁₀.rd, rd₉, u₈.rd, u₇.rd, u₆.rd, rd₅, rd₄, rd₃', hrd],
      by rw [u₁₁.wr, u₁₀.wr, wr₉, u₈.wr, u₇.wr, u₆.wr, wr₅, wr₄, wr₃', hwr]⟩
    have hq' : q ∉ [Reg.x0, .x1, .x4, .x9, .x10, .x11, .x12, .x13] := fun h => hq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    by_cases h23 : q = .x23
    · subst h23
      rw [u₁₁.gpr, u₁₀.other _ (by decide), g₉ _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), x7₄, hx23]
    by_cases h22 : q = .x22
    · subst h22
      rw [u₁₁.other _ (by decide), u₁₀.gpr, g₉ _ (by decide), u₈.other _ (by decide), u₇.gpr, x22₆,
        hx22, BitVec.add_sub_cancel]
    rw [u₁₁.other _ h23, u₁₀.other _ h22, g₉ q hq', g₈ q h22 h23, g₆ q hq]

/-- The data encrypted, from all of it done. -/
theorem done_encrypt {s₀ s : State} {m : Mem} (h : Done s₀ s (L s₀) m) :
    bytesAt m (dp s₀) (L s₀) =
      Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
  rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
    VG.Proof.Poly1305.length_bytesAt _ _ _]
  exact VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => by
    rw [h k hk, ite_eq_left hk]

/-- What a call of the stream on the rest would leave, from `restCrypt_ok`'s. -/
theorem crypt_post {s₀ : State} {s w u : State} {P : Nat} (hle : P ≤ L s₀)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) (hsp : u.sp = w.sp)
    (hd : Done s₀ s (L s₀) u.mem) (hf : Frame [sub s₀ 64 320, restR s₀ P] w.mem u.mem)
    (hg : ∀ r ∈ preserved, u.gpr r = w.gpr r) (hrd : u.rd = w.rd) (hwr : u.wr = w.wr) :
    (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w u ∧ Frame [sub s₀ 64 384, restR s₀ P] w.mem u.mem ∧
      bytesAt u.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have f' : Frame [sub s₀ 64 384, restR s₀ P] w.mem u.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨hv, Kept.of hg hsp hrd hwr (f'.sub fun r hr => ?_), f', done_encrypt hd⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨dR s₀, by simp, Offset.sub_base _ (by omega)⟩

/-- `Rest.crypt` with what a call of the stream would leave. -/
theorem crypt_call {s₀ : State} (hp : APre e s₀) {s w : State} {P : Nat}
    (hle : P ≤ L s₀) (hlt : L s₀ - P < 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 P)
    (hx23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hd : Done s₀ s P w.mem) :
    WP isa Rest.crypt w fun u =>
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w u ∧ Frame [sub s₀ 64 384, restR s₀ P] w.mem u.mem ∧
      bytesAt u.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) :=
  (WP.withSp (WP.preservedV (restCrypt_ok hp hle hlt hP hx21 hx22 hx23 hrd hwr hcnt hd)
    (by lit_decide))).mono fun _ ⟨⟨⟨d, f, g, rd, wr⟩, v⟩, sp⟩ =>
      crypt_post hle v sp d f (fun r hr => g r (cryptRegs_preserved r hr)) rd wr

/-- `Rest.sealRest`: the stream's arguments' data encrypted, as a call of
the stream would. -/
theorem sealRest_call {s₀ : State} (hp : APre e s₀) {s w : State} {P : Nat}
    (hle : P ≤ L s₀) (hlt : L s₀ - P < 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 P)
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hd : Done s₀ s P w.mem) :
    WP isa Rest.sealRest w fun u =>
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w u ∧ Frame [sub s₀ 64 384, restR s₀ P] w.mem u.mem ∧
      bytesAt u.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  refine (WP.withSp (WP.preservedV (Q := fun u => Done s₀ s (L s₀) u.mem ∧
      Frame [sub s₀ 64 320, restR s₀ P] w.mem u.mem ∧ (∀ r ∈ preserved, u.gpr r = w.gpr r) ∧
      u.rd = w.rd ∧ u.wr = w.wr) ?_ (by lit_decide))).mono fun _ ⟨⟨⟨d, f, g, rd, wr⟩, v⟩, sp⟩ =>
    crypt_post hle v sp d f g rd wr
  unfold Rest.sealRest
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    WP.block_nil ?_)
  have g₄ : ∀ q, q ≠ .x14 → q ≠ .x15 → q ≠ .x22 → q ≠ .x23 → s₄.gpr q = w.gpr q :=
    fun q h14 h15 h22 h23 => by rw [u₄.other _ h23, u₃.other _ h22, u₂.other _ h15, u₁.other _ h14]
  have m₄ : s₄.mem = w.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq ((restCrypt_ok hp (s := s) hle hlt hP (by rw [g₄ _ (by decide) (by decide) (by decide)
      (by decide), hx21])
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx1])
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx2])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr])
    (by rw [m₄]; exact hcnt) (by rw [m₄]; exact hd)).mono fun s₅ ⟨d₅, f₅, g₅, rd₅, wr₅⟩ =>
      wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_)
  rw [m₄] at f₅
  have x14 : s₅.gpr .x14 = w.gpr .x22 := by
    rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have x15 : s₅.gpr .x15 = w.gpr .x23 := by
    rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine ⟨by rw [u₇.mem, u₆.mem]; exact d₅, by rw [u₇.mem, u₆.mem]; exact f₅, fun q hq => ?_,
    by rw [u₇.rd, u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₇.wr, u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  by_cases h23 : q = .x23
  · subst h23; rw [u₇.gpr, u₆.other _ (by decide), x15]
  by_cases h22 : q = .x22
  · subst h22; rw [u₇.other _ (by decide), u₆.gpr, x14]
  have hc := cryptRegs_preserved q hq
  rw [u₇.other _ h23, u₆.other _ h22, g₅ q hc, g₄ q (by rintro rfl; revert hq; decide)
    (by rintro rfl; revert hq; decide) h22 h23]

end VG.Proof.ChaCha20Poly1305.AArch64
