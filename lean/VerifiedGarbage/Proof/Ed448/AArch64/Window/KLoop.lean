import VerifiedGarbage.Proof.Ed448.AArch64.Window.Window
import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit

/-!
# Ed448 verification on AArch64: the windows of the challenge

Untrusted: everything here is checked by Lean. From `Q` the neutral point, each
byte of the challenge from the top (`kByte`) applies two windows, its high
and its low digit (`kByte_ok`); after the 57 bytes (`kLoop_ok`), `Q` is
`winQ P b 57` for the challenge's bytes `b`, and slots 0–2 are kept.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `Q` after the top `m` bytes of the challenge, byte `i` being `b i`. -/
def winQ (P : Point) (b : Nat → BitVec 8) : Nat → Point
  | 0 => ⟨0, 1, 1⟩
  | m + 1 => wstep P (wstep P (winQ P b m) (nibOf (b (56 - m)) 4)) (nibOf (b (56 - m)) 0)

/-- Before byte `j - 1` (`x19 = j`): `Q` after the bytes above it, slots 0–2 kept. -/
structure KInv (s₀ : State) (base : Addr) (P : Point) (S : Point) (j : Nat) (s : State) : Prop where
  bound : j ≤ 57
  ctx : WCtx s₀ base P s
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  q : VG.Proof.X448.AArch64.Base.pt (EV s.mem base) 3 4 5 = winQ P (fun i => s₀.mem (off base (KB + i))) (57 - j)
  sb : VG.Proof.X448.AArch64.Base.pt (EV s.mem base) 0 1 2 = S

private theorem dec_fact : ∀ j < 58, 0 < j →
    BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by decide +kernel

theorem dec19_ok (s : State) {j : Nat} (hj : 0 < j) (hj' : j < 58) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Keeps [.x19] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    dec_fact j hj' hj, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

theorem kByte_ok {s₀ s : State} {base : Addr} {P : Point} {S : Point} {j : Nat}
    (h : KInv s₀ base P S j s) (hj : 0 < j) :
    WP isa (.block kByte) s fun t => (t.gpr .x19 != 0) = decide (j - 1 ≠ 0) ∧ KInv s₀ base P S (j - 1) t := by
  rw [kByte, List.append_assoc, WP.block_append_iff]
  refine WP.mono (dec19_ok s hj (by have := h.bound; omega) h.counter) fun a ⟨a19, ka, ma⟩ => ?_
  have ha : WCtx s₀ base P a :=
    ⟨h.ctx.scr.of_keeps ka (by decide), by rw [ma]; exact h.ctx.env, by rw [ma]; exact h.ctx.zero,
      by rw [ma]; exact h.ctx.one, by rw [ma]; exact h.ctx.z5, by rw [ma]; exact h.ctx.tab,
      by rw [ka.1 _ (by decide)]; exact h.ctx.lr,
      by rw [ka.1 _ (by decide)]; exact h.ctx.chk, by rw [ka.2.1]; exact h.ctx.rd,
      by rw [ka.2.2]; exact h.ctx.wr, by rw [ma]; exact h.ctx.mem⟩
  have hb := h.bound
  rw [WP.block_append_iff]
  refine WP.mono (window_ok ha (by omega) a19 (Or.inr rfl))
    fun b ⟨hb', qb, sb, cb⟩ => ?_
  refine WP.mono (window_ok hb' (by omega) (cb.trans a19) (Or.inl rfl))
    fun t ⟨ht, qt, st, ct⟩ => ⟨?_, ⟨by omega, ht, ct.trans (cb.trans a19), ?_, ?_⟩⟩
  · rw [ct, cb, a19]
    have : BitVec.ofNat 64 (j - 1) = 0 ↔ j - 1 = 0 := by
      constructor
      · intro e; have := congrArg BitVec.toNat e; have h0 : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this; omega
      · intro e; rw [e]; rfl
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact not_congr this
  · rw [qt, qb, ma, h.q, show 57 - (j - 1) = (57 - j) + 1 by omega, winQ, show 56 - (57 - j) = j - 1 by omega]
  · rw [st, sb, ma, h.sb]

theorem kLoop_ok {s₀ : State} {base : Addr} {P : Point} {S : Point} :
    ∀ m, ∀ s, 1 ≤ m → m ≤ 57 → KInv s₀ base P S m s →
      WP isa (.loop (.block kByte) (.nonzero .x .x19)) s fun t => KInv s₀ base P S 0 t := by
  intro m s h1 h2 hi
  refine WP.loop (M := isa) (body := .block kByte) (c := .nonzero .x .x19)
    (Q := fun t => KInv s₀ base P S 0 t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 57 ∧ KInv s₀ base P S m s) ?_ m s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (kByte_ok hi (by omega)) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    exact .inl ⟨by decide, ht⟩
  · exact .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ht⟩

end VG.Proof.Ed448.AArch64.Window
