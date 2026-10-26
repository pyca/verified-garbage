module

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Window
import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Digit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ed448 verification on AArch64: the windows of the challenge

Untrusted: everything here is checked by Lean. From `Q` the neutral point, each
nibble of the challenge from the top (`kNib`, the nibbles expanded at `BITS`)
applies a window (`kNib_ok`); after the 114 nibbles (`kLoop_ok`), `Q` is
`winQN P N 114` for the nibbles `N`, which is `winQ P b 57` for the challenge's
bytes `b` (`winQN_eq`), and slots 0–2 are kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
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

/-- `Q` after the top `m` of the challenge's 114 nibbles, nibble `i` being `N i`. -/
def winQN (P : Point) (N : Nat → Nat) : Nat → Point
  | 0 => ⟨0, 1, 1⟩
  | m + 1 => wstep P (winQN P N m) (N (113 - m))

/-- The nibbles' windows are the bytes', two by two. -/
theorem winQN_eq (P : Point) {N : Nat → Nat} {b : Nat → BitVec 8}
    (hN : ∀ i < 57, N (2 * i) = nibOf (b i) 0 ∧ N (2 * i + 1) = nibOf (b i) 4) :
    ∀ m ≤ 57, winQN P N (2 * m) = winQ P b m
  | 0, _ => rfl
  | m + 1, hm => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, winQN, winQN, winQN_eq P hN m (by omega), winQ,
      show 113 - (2 * m + 1) = 2 * (56 - m) by omega, show 113 - 2 * m = 2 * (56 - m) + 1 by omega,
      (hN (56 - m) (by omega)).1, (hN (56 - m) (by omega)).2]

/-- After the windows: `Q` after the challenge's bytes, slots 0–2 kept. -/
structure KInv (s₀ : State) (base : Addr) (P : Point) (S : Point) (j : Nat) (s : State) : Prop where
  bound : j ≤ 57
  ctx : WCtx s₀ base P s
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  q : pt (EV s.mem base) 3 4 5 = winQ P (fun i => s₀.mem (off base (KB + i))) (57 - j)
  sb : pt (EV s.mem base) 0 1 2 = S

/-- The nibbles at the windows' start, as numbers. -/
def nibs (s₀ : State) (base : Addr) (i : Nat) : Nat := (s₀.mem (off base (BITS + i))).toNat

/-- Before nibble `j - 1` (`x19 = j`): `Q` after the nibbles above it, slots 0–2 kept. -/
structure KInvN (s₀ : State) (base : Addr) (P : Point) (S : Point) (j : Nat) (s : State) : Prop where
  bound : j ≤ 114
  ctx : WCtx s₀ base P s
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  q : pt (EV s.mem base) 3 4 5 = winQN P (nibs s₀ base) (114 - j)
  sb : pt (EV s.mem base) 0 1 2 = S
  nib : ∀ i < 114, nibs s₀ base i < 16

private theorem dec_fact : ∀ j < 115, 0 < j →
    BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by decide +kernel

theorem dec19_ok (s : State) {j : Nat} (hj : 0 < j) (hj' : j < 115) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Keeps [.x19] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    dec_fact j hj' hj, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

theorem kNib_ok {s₀ s : State} {base : Addr} {P : Point} {S : Point} {j : Nat}
    (h : KInvN s₀ base P S j s) (hj : 0 < j) :
    WP isa kNib s fun t => (t.gpr .x19 != 0) = decide (j - 1 ≠ 0) ∧ KInvN s₀ base P S (j - 1) t := by
  unfold kNib
  refine WP.seq (WP.mono (dec19_ok s hj (by have := h.bound; omega) h.counter) fun a ⟨a19, ka, ma⟩ => ?_)
  have ha : WCtx s₀ base P a :=
    ⟨h.ctx.scr.of_keeps ka (by decide), by rw [ma]; exact h.ctx.env, by rw [ma]; exact h.ctx.zero,
      by rw [ma]; exact h.ctx.one, by rw [ma]; exact h.ctx.z5, by rw [ma]; exact h.ctx.tab,
      by rw [ka.1 _ (by decide)]; exact h.ctx.chk, by rw [ka.2.1]; exact h.ctx.rd,
      by rw [ka.2.2]; exact h.ctx.wr, by rw [ma]; exact h.ctx.mem⟩
  have hb := h.bound
  refine WP.mono (window_ok ha (by omega) a19 (h.nib _ (by omega)))
    fun t ⟨ht, qt, st, ct⟩ => ⟨?_, ⟨by omega, ht, ct.trans a19, ?_, ?_, h.nib⟩⟩
  · rw [ct, a19]
    have : BitVec.ofNat 64 (j - 1) = 0 ↔ j - 1 = 0 := by
      constructor
      · intro e; have := congrArg BitVec.toNat e; have h0 : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this; omega
      · intro e; rw [e]; rfl
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact not_congr this
  · rw [qt, ma, h.q, show 114 - (j - 1) = (114 - j) + 1 by omega, winQN, show 113 - (114 - j) = j - 1 by omega]
    rfl
  · rw [st, ma, h.sb]

/-- **The windows**: from `KInvN` at 114, the nibbles of the challenge's copy at `KB` (`hN`) give
`KInv` at 0. -/
theorem kLoop_ok {s₀ : State} {base : Addr} {P : Point} {S : Point} (s : State) (hi : KInvN s₀ base P S 114 s)
    (hN : ∀ i < 57, nibs s₀ base (2 * i) = nibOf (s₀.mem (off base (KB + i))) 0 ∧
      nibs s₀ base (2 * i + 1) = nibOf (s₀.mem (off base (KB + i))) 4) :
    WP isa (.loop kNib (.nonzero .x .x19)) s fun t => KInv s₀ base P S 0 t := by
  refine WP.loop (M := isa) (body := kNib) (c := .nonzero .x .x19)
    (Q := fun t => KInv s₀ base P S 0 t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 114 ∧ KInvN s₀ base P S m s) ?_ 114 s ⟨by decide, by decide, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (kNib_ok hi (by omega)) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    refine .inl ⟨by decide, ⟨by decide, ht.ctx, ht.counter, ?_, ht.sb⟩⟩
    rw [ht.q, show 57 - 0 = 57 from rfl, ← winQN_eq P hN 57 (by decide)]
  · exact .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ht⟩

end VG.Proof.Ed448.AArch64.Window
