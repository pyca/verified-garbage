module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces
public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords
public import VerifiedGarbage.Proof.MillerRabin.Arm.Words

/-! ### `MillerRabin.Arm.Tab`, which only this module used -/

section

/-! ### `MillerRabin.Arm.Sq`, which only this module used -/

section

/-! # The Miller–Rabin round on ARMv7: a run of squarings

`SqS … q0 r st0 k`: a run of `q0` squarings from `st0` (`y` in `aY`, the
flag in `sF`), with the threshold `r` in `sR`, `k` of them left (in `sQ`):
`y` and the flag are `msqs … (q0 − k)` (`Proof/MillerRabin/Arm/Math.lean`).
One squaring goes from `k + 1` left to `k` (`sq_step`), and the loop from
`q0` to none (`sq_loop`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The witness, Montgomery one and minus one, from `σ`. -/
abbrev xOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 5
abbrev oOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 9
abbrev mOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 10

/-- A piece whose precondition is never met. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁ (h σ _)⟩

/-- A piece under a fact its stage implies. -/
theorem VP.of_imp {F G : State → State → Prop} {c : Prog isa} {p : Prop} (hp : ∀ σ s, F σ s → p)
    (h : p → VP F c G) : VP F c G :=
  ⟨fun σ s hs => (h (hp σ s hs)).wp σ s hs, fun s₁ s₂ t₁ t₂ s₁' s₂' hs e₁ e₂ =>
    match hs with
    | ⟨σ₁, σ₂, h₁, h₂⟩ => (h (hp _ _ h₁)).ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂⟩

/-- `y` and the flag after `n` squarings of the run. -/
abbrev sqst (P : MP) (q0 : Nat) (r : State → Nat) (st0 : State → Nat × Bool) (σ : State) (n : Nat) : Nat × Bool :=
  msqs (cOf P σ.mem) P.w (mOf P σ) (r σ) q0 (st0 σ) n

/-- The run's stage with `k` squarings left. -/
def SqS (P : MP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (q0 : Nat) (r : State → Nat) (st0 : State → Nat × Bool) (k : Nat) (σ s : State) : Prop :=
  k ≤ q0 ∧ St P E (fun σ => upd (A σ) aY (sqst P q0 r st0 σ (q0 - k)).1) (aY :: L)
    (fun σ => upd (upd (V σ) sF (sqst P q0 r st0 σ (q0 - k)).2.toNat) sQ k) LS σ s

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat} {q0 : Nat} {r : State → Nat} {st0 : State → Nat × Bool}

theorem sqst_lt (hE : ∀ σ, E σ → In P σ) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) :
    ∀ σ, E σ → ∀ n, (sqst P q0 r st0 σ n).1 < cOf P σ.mem := by
  intro σ e n
  have := (hE σ e).c3
  cases n with
  | zero => exact h0 σ e
  | succ n => exact mm_lt (by omega_using [this])

/-- One squaring. -/
theorem sq_step (hE : ∀ σ, E σ → In P σ) (hYL : aY ∉ L) (hM : aM1 ∈ L) (hX : aX ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L)
    (hF : sF ∈ LS) (hQ : sQ ∈ LS) (hR : sR ∈ LS) (hE2 : sE2 ∉ LS) (hT : sT ∉ LS)
    (vM : ∀ σ, E σ → A σ aM1 = mOf P σ) (vR : ∀ σ, E σ → V σ sR = r σ) (rl : ∀ σ, E σ → r σ < 2 ^ 31)
    (hq0 : q0 < 2 ^ 31) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) (k : Nat) (fios : Bool := false) :
    VP (SqS P E A L V LS q0 r st0 (k + 1)) (sqStep (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < k)) ∧ (k = 0 → SqS P E A L V LS q0 r st0 0 σ s) ∧
        (0 < k → SqS P E A L V LS q0 r st0 k σ s) := by
  by_cases hk : k + 1 ≤ q0
  swap
  · exact VP.of_false fun σ s h => hk h.1
  obtain lt := sqst_lt (q0 := q0) (r := r) hE h0
  let A1 := fun σ => upd (A σ) aY (sqst P q0 r st0 σ (q0 - (k + 1))).1
  let V1 := fun σ => upd (upd (V σ) sF (sqst P q0 r st0 σ (q0 - (k + 1))).2.toNat) sQ (k + 1)
  let A2 := fun σ => upd (A1 σ) aY (mm (cOf P σ.mem) P.w (A1 σ aY) (A1 σ aY))
  let V3 := fun σ => upd (V1 σ) sE2 (if A2 σ aY = A2 σ aM1 then 1 else 0)
  obtain a1Y : ∀ σ, A1 σ aY = (sqst P q0 r st0 σ (q0 - (k + 1))).1 := fun σ => upd_self _ _ _
  obtain a2Y : ∀ σ, A2 σ aY = (sqst P q0 r st0 σ (q0 - k)).1 := fun σ => by
    show mm _ _ (A1 σ aY) (A1 σ aY) = _
    rw [a1Y, show q0 - k = q0 - (k + 1) + 1 by omega_using [hk]]
    rfl
  obtain a2M : ∀ σ, E σ → A2 σ aM1 = mOf P σ := fun σ e => by
    show upd (upd (A σ) aY _) aY _ aM1 = _
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), vM σ e]
  refine VP.mono (F := St P E A1 (aY :: L) V1 LS) ?_ (fun σ s h => h.2) (fun _ _ h => h)
  simp only [sqStep, seqs]
  refine VP.seq (G := St P E A2 (aY :: L) V1 LS) ?_
    (VP.seq (G := St P E A2 (aY :: L) V3 (sE2 :: LS)) ?_ ?_)
  -- `y²`.
  · exact St.psqY (fios := fios) hYL h2 h3 (fun σ e => by rw [a1Y]; exact lt σ e _)
  -- `y = −1`.
  · exact St.peqS eq2_taint List.mem_cons_self (List.mem_cons_of_mem _ hM) (by decide) (by decide)
      (fun h => (List.mem_cons.mp h).elim (fun e => absurd e (by decide)) hX) hT (by decide)
  -- The flag and the count.
  · have vQ : ∀ σ, E σ → V3 σ sQ = k + 1 := fun σ _ => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sQ = _
      rw [upd_ne _ _ (by decide), upd_self]
    obtain vR3 : ∀ σ, E σ → V3 σ sR = r σ := fun σ e => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sR = _
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), vR σ e]
    obtain vE : ∀ σ, E σ → V3 σ sE2 =
        (decide (mm (cOf P σ.mem) P.w (sqst P q0 r st0 σ (q0 - (k + 1))).1
          (sqst P q0 r st0 σ (q0 - (k + 1))).1 = mOf P σ)).toNat := fun σ e => by
      show upd (V1 σ) sE2 (if A2 σ aY = A2 σ aM1 then 1 else 0) sE2 = _
      rw [upd_self, a2M σ e]
      show (if mm _ _ (A1 σ aY) (A1 σ aY) = _ then 1 else 0) = _
      rw [a1Y]
      split <;> simp_all
    obtain vF : ∀ σ, E σ → V3 σ sF = (sqst P q0 r st0 σ (q0 - (k + 1))).2.toNat := fun σ _ => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sF = _
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
    refine (St.psqFlag (k := k) (List.mem_cons_of_mem _ hQ) (List.mem_cons_of_mem _ hR) List.mem_cons_self
      (List.mem_cons_of_mem _ hF) vQ vR3 rl (by omega_using [hq0, hk]) vE vF).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
    obtain stage : SqS P E A L V LS q0 r st0 k σ s := by
      refine ⟨by omega_using [hk], h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)⟩
      · rcases List.mem_cons.mp hi with rfl | hi'
        · rw [a2Y]; exact (upd_self _ _ _).symm
        · have : i ≠ aY := fun x => hYL (x ▸ hi')
          show upd (upd (A σ) aY _) aY _ i = upd (A σ) aY _ i
          rw [upd_ne _ _ this, upd_ne _ _ this, upd_ne _ _ this]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
      · have e : sqst P q0 r st0 σ (q0 - k) = msq (cOf P σ.mem) P.w (mOf P σ) (decide (r σ < k + 1))
            (sqst P q0 r st0 σ (q0 - (k + 1))) := by
          rw [show q0 - k = q0 - (k + 1) + 1 by omega_using [hk]]
          show msq _ _ _ (decide (r σ < q0 - (q0 - (k + 1)))) _ = _
          rw [show q0 - (q0 - (k + 1)) = k + 1 by omega_using [hk]]
        by_cases dQ : d = sQ
        · subst dQ; simp only [upd_self]
        · by_cases dF : d = sF
          · subst dF
            simp only [upd_ne _ _ dQ, upd_self, e, msq]
          · have dE : d ≠ sE2 := fun x => hE2 (x ▸ hd)
            simp only [V3, V1, upd_ne _ _ dQ, upd_ne _ _ dF, upd_ne _ _ dE]
    refine ⟨?_, fun h0 => h0 ▸ stage, fun _ => stage⟩
    show some (!s.z) = _
    rw [z]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega_using [h0]

/-- The run. -/
theorem sq_loop (hE : ∀ σ, E σ → In P σ) (hYL : aY ∉ L) (hM : aM1 ∈ L) (hX : aX ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L)
    (hF : sF ∈ LS) (hQ : sQ ∈ LS) (hR : sR ∈ LS) (hE2 : sE2 ∉ LS) (hT : sT ∉ LS)
    (vM : ∀ σ, E σ → A σ aM1 = mOf P σ) (vR : ∀ σ, E σ → V σ sR = r σ) (rl : ∀ σ, E σ → r σ < 2 ^ 31)
    (hq0 : q0 < 2 ^ 31) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) (n : Nat) (fios : Bool := false) :
    VP (SqS P E A L V LS q0 r st0 (n + 1)) (sqLoop (fios := fios)) (SqS P E A L V LS q0 r st0 0) :=
  VP.loop (fun k => sq_step (fios := fios) hE hYL hM hX h2 h3 hF hQ hR hE2 hT vM vR rl hq0 h0 k) n

end

end VG.Proof.MillerRabin.Arm

end

end

/-! ### `MillerRabin.Arm.Scan`, which only this module used -/

section

/-! # The Miller–Rabin round on ARMv7: the scan and the table's shift

The scan (`St.pscan`): `T_d` into array 5 for the digit `d` at the top of
`sV`, through the masks of all 16 entries, the selection so far alternating
between arrays 8 and 5 (`hold`): before entry `j`, it is `T_d` if `d < j`,
else `T_0` (`selv`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The selection before entry `j`, for the digit `d`. -/
def selv (A : Nat → Nat) (d j : Nat) : Nat := if d < j then A (aT0 + d) else A aT0

theorem hold_mem (j : Nat) : hold j ∈ wJs := by unfold hold; split <;> decide
theorem hold_ne (j : Nat) : hold j ≠ hold (j + 1) := by unfold hold; split <;> split <;> first | decide | omega
theorem hold_two (j : Nat) : hold (j + 2) = hold j := by unfold hold; congr 1; simp only [Nat.add_mod_right]
theorem hold_lt (j : Nat) : hold j < aT0 := by unfold hold; split <;> decide
section
variable {P : MP} {σ s : State} {A : Nat → Nat} {L : List Nat} {V : Nat → Nat} {LS : List Nat}

/-- `maskJ j`: the mask of the digit at the top of `sV` being `j` into `sE1`. -/
theorem KS.mask_ok {j : Nat} (hj : j < 16) (h : KS P σ A L V LS s) (hw : Ws s P.B P.Z P.W nArr) (hv : sV ∈ LS)
    (vl : V sV < 2 ^ 32) :
    WP isa (.block (maskJ j)) s fun t =>
      KS P σ A L (upd V sE1 (decide (digitOf (V sV) = j)).toNat) (sE1 :: LS) t ∧ Ws t P.B P.Z P.W nArr := by
  simp only [maskJ]
  refine h.ldr hw hv (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (encodable_lt (by omega_using [hj]))) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  obtain r5 : Rest [.r1] s1 s5 :=
    (u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp))))
  obtain h5 := h1.of_rest r5 (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  obtain hw5 := hw1.rest r5
  refine h5.str hw5 (d := sE1) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨?_, hwt⟩
  obtain dl : digitOf (V sV) < 16 := by simp only [digitOf]; omega_using [vl]
  obtain g : (s5.gpr .r1).toNat = (decide (digitOf (V sV) = j)).toNat := by
    rw [u5.gpr, u4.gpr, dpVal, u3.gpr, dpVal, u2.gpr, u1.gpr, ofNat_shr32 vl]
    exact mask_eq _ dl _ hj
  rwa [g] at ht

/-- The entries `j, …, 15` of the scan, from the selection before entry `j`. -/
theorem scanFrom_ok {d : Nat} (hd : d < 16) (hT : ∀ k < 16, aT0 + k ∈ L) (hX : aX ∉ L) (hM : aM1 ∉ L)
    (hv : sV ∈ LS) (hE1 : sE1 ∉ LS) (dv : digitOf (V sV) = d) (vl : V sV < 2 ^ 32) :
    ∀ n j, j + n = 16 → 1 ≤ j → ∀ s, KS P σ (upd A (hold (j + 1)) (selv A d j)) (hold (j + 1) :: L) V LS s →
      Ws s P.B P.Z P.W nArr →
      WP isa (scanFrom j n) s fun t => KS P σ (upd A aX (A (aT0 + d))) (aX :: L) V LS t ∧ Ws t P.B P.Z P.W nArr
  | 0, j, hjn, _, s, h, hw => by
    have : j = 16 := by omega_using [hjn]
    subst this
    refine WP.block_nil ⟨?_, hw⟩
    obtain e : selv A d 16 = A (aT0 + d) := by simp only [selv, hd, ↓reduceIte]
    rw [e] at h
    exact h
  | n + 1, j, hjn, hj1, s, h, hw => by
    obtain hold_L : ∀ i, hold i ∉ L := fun i => by unfold hold; split; exacts [hX, hM]
    rw [scanFrom, WP.seq_iff]
    refine WP.mono (h.mask_ok (j := j) (by omega_using [hjn]) hw hv vl) fun s1 ⟨h1, hw1⟩ => ?_
    rw [WP.seq_iff]
    obtain hb : aT0 + j ∈ hold (j + 1) :: L := List.mem_cons_of_mem _ (hT j (by omega_using [hjn]))
    obtain ne1 : hold j ≠ aT0 + j := fun e => by have := hold_lt j; omega_using [e, this]
    refine WP.mono (h1.sel_ok hw1 (hold_mem j) List.mem_cons_self hb (hold_ne j) ne1 List.mem_cons_self
      (by rw [upd_self]; cases decide (digitOf (V sV) = j) <;> decide)) fun s2 ⟨h2, hw2, _⟩ => ?_
    refine scanFrom_ok hd hT hX hM hv hE1 dv vl n (j + 1) (by omega_using [hjn]) (by omega_using []) s2 ?_ hw2
    rw [hold_two]
    refine h2.mono (fun i hi => ⟨?_, ?_⟩) (fun e he => ⟨List.mem_cons_of_mem _ he, ?_⟩)
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
    · rcases List.mem_cons.mp hi with rfl | hi
      · have ne2 : aT0 + j ≠ hold (j + 1) := fun e => by have := hold_lt (j + 1); omega_using [e, this]
        simp only [upd_self]
        rw [upd_ne _ _ ne2, dv]
        unfold selv
        by_cases hdj : d = j
        · simp only [hdj, decide_true, Bool.toNat_true, Nat.one_ne_zero, ↓reduceIte, Nat.lt_succ_self]
        · simp only [hdj, decide_false, Bool.toNat_false, ↓reduceIte, show (d < j + 1) ↔ (d < j) by omega_using [hdj]]
      · have n1 : i ≠ hold j := fun e => hold_L j (e ▸ hi)
        obtain n2 : i ≠ hold (j + 1) := fun e => hold_L (j + 1) (e ▸ hi)
        rw [upd_ne _ _ n1, upd_ne _ _ n2, upd_ne _ _ n1]
    · have : e ≠ sE1 := fun x => hE1 (x ▸ he)
      rw [upd_ne _ _ this]

end

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- The scan: `[aX] := T_d` for the digit `d` at the top of `sV`. -/
theorem St.pscan (hT : ∀ k < 16, aT0 + k ∈ L) (hX : aX ∉ L) (hM : aM1 ∉ L) (hv : sV ∈ LS) (hE1 : sE1 ∉ LS)
    (vl : ∀ σ, E σ → V σ sV < 2 ^ 32) :
    VP (St P E A L V LS) scan
      (St P E (fun σ => upd (A σ) aX (A σ (aT0 + digitOf (V σ sV)))) (aX :: L) V LS) := by
  refine VP.kv scan_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  obtain dl : digitOf (V σ sV) < 16 := by have := vl σ e; simp only [digitOf]; omega_using [this]
  rw [scan, WP.seq_iff]
  obtain t0 : aT0 ∈ L := hT 0 (by decide)
  refine WP.mono (h.copy_ok hw (by decide) (h.live_lt _ t0) (by decide)) fun s1 ⟨h1, hw1, _⟩ => ?_
  refine WP.mono (scanFrom_ok (A := A σ) dl hT hX hM hv hE1 rfl (vl σ e) 15 1 rfl (Nat.le_refl _) s1 ?_ hw1)
    fun t ⟨ht, hwt⟩ => ⟨e, ht, hwt⟩
  rw [h.arrs aT0 t0] at h1
  obtain e1 : selv (A σ) (digitOf (V σ sV)) 1 = A σ aT0 := by
    unfold selv; split
    · rw [show digitOf (V σ sV) = 0 by omega_arith]; rfl
    · rfl
  rw [show hold (1 + 1) = aM1 from rfl, e1]
  exact h1

end

end VG.Proof.MillerRabin.Arm

end

end


/-! # The Miller–Rabin round on ARMv7: the table

`tv P σ k` is power `k` in Montgomery form. After `i` steps, entries
0 through `i + 1` are complete, and each remaining entry retains its input
value. Each product is copied once to its final public slot.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The table's entry `k`. -/
abbrev tv (P : MP) (σ : State) (k : Nat) : Nat := tp (cOf P σ.mem) P.w (xOf P σ) (oOf P σ) k

/-- Entry `k` of the table after `i` iterations. -/
def tabEnt (P : MP) (σ : State) (i k : Nat) : Nat :=
  if k = 0 then oOf P σ else if k = 1 then xOf P σ else
    if k ≤ i + 1 then tv P σ k else num σ.mem P.B P.W (aT0 + k)

/-- The arrays after `i` iterations. -/
def AT (P : MP) (i : Nat) (σ : State) (j : Nat) : Nat :=
  if j = aY then tv P σ (i + 1) else if j = aX then xOf P σ else tabEnt P σ i (j - aT0)

/-- `y`, `x` and the table. -/
abbrev LT : List Nat := [aY, aX, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The table's loop with `k` iterations left. -/
def TS (P : MP) (k : Nat) (σ s : State) : Prop :=
  k ≤ 14 ∧ St P (In P) (AT P (14 - k)) LT (fun _ => upd (fun _ => 0) sK k) [sK] σ s

theorem tv_lt {P : MP} {σ : State} (h : In P σ) (k : Nat) : tv P σ k < cOf P σ.mem := by
  have := h.c3
  exact tp_lt (by omega_using [this]) h.x5 (by show numAt σ.mem (State.addr P.ws) P.w 9 < _; rw [h.one]; exact Nat.mod_lt _ (by omega_using [this])) k

/-- A product and one final-slot copy advance the completed prefix. -/
theorem AT_step {P : MP} {σ : State} {i : Nat} (hi : i < 14) :
    ∀ j ∈ LT,
      upd (upd (AT P i σ) aY
        (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX)))
        (aT0 + i + 2) (tv P σ (i + 2)) j = AT P (i + 1) σ j := by
  have ey : mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX) = tv P σ (i + 2) := rfl
  rw [ey]
  have e0 : aT0 = 11 := rfl
  have eY : aY = 6 := rfl
  have eX : aX = 5 := rfl
  intro j hj
  obtain hj' : j = aY ∨ j = aX ∨ (aT0 ≤ j ∧ j < aT0 + 16) := by
    simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega_using [e0, hj]
  rcases hj' with rfl | rfl | hj
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · have hY : j ≠ aY := by omega_using [e0, eY, hj]
    obtain hX : j ≠ aX := by omega_using [e0, eX, hj]
    by_cases he : j = aT0 + i + 2
    · subst j
      obtain hsub : aT0 + i + 2 - aT0 = i + 2 := by omega_using []
      simp (disch := omega) only [upd, AT, tabEnt, hsub, ↓ite_eq_left, ↓ite_eq_right]
    · have hidx : j - aT0 ≠ i + 2 := by omega_using [he]
      obtain hbound : (j - aT0 ≤ i + 1) = (j - aT0 ≤ (i + 1) + 1) := by apply propext; omega_using [he]
      simp only [upd, he, hY, hX, AT, tabEnt, ↓reduceIte, hbound]


/-- The count addresses one final slot, then the existing copy loop preserves the stage. -/
private theorem tab_copy_store {P : MP} {σ s : State} {A : Nat → Nat} {L : List Nat}
    {V : Nat → Nat} {LS : List Nat} (h : KS P σ A L V LS s) (hw : Ws s P.B P.Z P.W nArr)
    (ha : aY ∈ L) (i : Nat) (hi : i<14) (count : s.gpr .lr=BitVec.ofNat 32 (14-i)) :
    WP isa tabCopyStore s fun t =>
      KS P σ (upd A (aT0+i+2) (num s.mem P.B P.W aY)) ((aT0+i+2)::L) V LS t ∧
      Ws t P.B P.Z P.W nArr := by
  rw [tabCopyStore,WP.seq_iff]
  simp only [tabCopyArgs,List.append_assoc,List.cons_append,List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  let s4 := s2.setReg .r0 (s2.gpr .r0*s2.gpr .r7+s2.gpr .r8)
  obtain u4 : Upd s2 s4 .r0 (s2.gpr .r0*s2.gpr .r7+s2.gpr .r8) := Upd.setReg _ _ _
  refine VG.Proof.X25519.Arm.WP.cons rfl ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  obtain index : s2.gpr .r0=BitVec.ofNat 32 (aT0+i+2) := by
    rw [u2.gpr,dpVal,u1.gpr,u1.other .lr (by decide),count]
    change BitVec.ofNat 32 27-BitVec.ofNat 32 (14-i)=_
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [])]
    congr 1
    simp only [aT0]
    omega_using [hi]
  obtain r5 : Rest [.r0] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u4.rest (by simp)).trans (u5.rest (by simp))))
  obtain mem5 : s5.mem=s.mem := by rw [u5.mem,u4.mem,u2.mem,u1.mem]
  obtain hw5 : Ws s5 P.B P.Z P.W nArr := hw.rest r5 (by decide) (by decide) (by decide)
  obtain p0 : s5.gpr .r0=P.B+BitVec.ofNat 32 (arr P.W (aT0+i+2)) := by
    rw [u5.gpr,dpVal,u4.gpr,index,
      u2.other .r8 (by decide),u1.other .r8 (by decide),
      u2.other .r7 (by decide),u1.other .r7 (by decide),hw.r7,hw.r8]
    exact ptr_val _ _ _
  refine ptr_ok hw5 (r := .r10) (by decide) (j := aY) (by decide) fun s6 p10 r6 mem6 hw6 => ?_
  refine ptr_ok hw6 (r := .r12) (by decide) (j := aY) (by decide) fun s7 p12 r7 mem7 hw7 => ?_
  refine wp_mov (op2_reg _ _) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u9 => WP.block_nil ?_
  obtain hu : Ws u P.B P.Z P.W nArr := (hw7.of_upd u8 (by decide) (by decide) (by decide)).of_upd u9 (by decide) (by decide) (by decide)
  obtain mu : u.mem=s.mem := by rw [u9.mem,u8.mem,mem7,mem6,mem5]
  obtain restU : Rest opRegs s u := (r5.mono (by simp)).trans ((r6.mono (by simp)).trans
    ((r7.mono (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))
  obtain ho : aT0+i+2<nArr := by simp only [aT0,nArr]; omega_using [hi]
  obtain ha' := h.live_lt _ ha
  obtain hoa : aT0+i+2≠aY := by simp only [aT0,aY]; omega_using []
  refine WP.mono (copyWords_ok u (hu.subCtx ho ha' ha' hoa hoa) hw.wpos
    (by rw [u9.other _ (by decide),u8.other _ (by decide),r7.gpr .r0 (by decide),r6.gpr .r0 (by decide),p0])
    (by rw [u9.other _ (by decide),u8.other _ (by decide),r7.gpr .r10 (by decide),p10])
    (by rw [u9.other _ (by decide),u8.other _ (by decide),p12])
    (by rw [u9.other _ (by decide),u8.gpr,hw7.r9])) ?_
  intro t inv
  have value := inv.value
  rw [mu] at value
  obtain keep : Keep P.B P.W [aT0+i+2] [] s.mem t.mem := Keep.of_arr (d := 0)
    (by simpa only [Nat.add_zero,mu] using inv.outside) (by simp only [S]; omega_using []) (by simp)
  obtain numeq : num t.mem P.B P.W (aT0+i+2)=num s.mem P.B P.W aY := by
    change val32 _ _ _ _=_
    rw [value]
    split <;> rfl
  obtain rest := restU.trans (inv.rest.mono (by simp))
  exact ⟨h.write1 keep (by simp [wJs,aT0]; omega_using [hi]) (by simp) rest.sp rest.rd rest.wr numeq (by simp),hu.rest inv.rest⟩

private theorem St.ptabCopy {P : MP} {E : State → Prop} {A : State → Nat → Nat}
    {L : List Nat} {V : State → Nat → Nat} {LS : List Nat} (i : Nat) (hi : i<14)
    (ha : aY ∈ L) (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK=14-i) :
    VP (St P E A L V LS) tabCopy
      (St P E (fun σ => upd (A σ) (aT0+i+2) (A σ aY)) ((aT0+i+2)::L) V LS) := by
  rw [tabCopy]
  refine VP.seq (G := fun σ s => St P E A L V LS σ s ∧ s.gpr .lr=BitVec.ofNat 32 (14-i)) ?_ ?_
  · refine VP.kv tabCopyLoad_taint (fun _ _ h => h.2.2) fun σ s ⟨e,h,hw⟩ => ?_
    refine h.ldr hw hk (r := .lr) (by decide) fun t ht hwt u => WP.block_nil ⟨⟨e,ht,hwt⟩,?_⟩
    rw [u.gpr,vk σ e]
  · refine VP.taint [.lr,.r7,.r8,.r9] tabCopyStore_taint ?_ ?_
    · intro σ₁ σ₂ s₁ s₂ h₁ h₂ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · rw [h₁.2,h₂.2]
      · rw [h₁.1.2.2.r7,h₂.1.2.2.r7]
      · rw [h₁.1.2.2.r8,h₂.1.2.2.r8]
      · rw [h₁.1.2.2.r9,h₂.1.2.2.r9]
    · intro σ s ⟨⟨e,h,hw⟩,count⟩
      exact WP.mono (tab_copy_store h hw ha i hi count)
        fun t ⟨ht,hwt⟩ => ⟨e,by rwa [h.arrs aY ha] at ht,hwt⟩

/-- One fixed, public entry index. -/
theorem tab_step {P : MP} (i : Nat) (hi : i < 14) (fios : Bool := false) :
    VP (TS P (14 - i)) (tabStep (fios := fios)) (fun σ s => TS P (13-i) σ s ∧ s.z=decide (13-i=0)) := by
  let V := fun (_ : State) => upd (fun _ => 0) sK (14 - i)
  refine VP.mono (F := St P (In P) (AT P i) LT V [sK]) ?_
    (fun σ s h => by simpa only [TS, Nat.sub_sub_self (by omega_using [hi] : i ≤ 14)] using h.2)
    (fun _ _ h => h)
  simp only [tabStep, seqs]
  refine VP.seq (St.pmulY (fios := fios) (P := P) (A := AT P i) (L := LT.tail) (.inr rfl)
    (by decide) (by decide) (by decide) (by decide) (fun σ e => tv_lt e _) (fun σ e => e.x5)) ?_
  refine VP.seq (St.ptabCopy i hi (by simp) (by simp) (fun _ _ => rfl)) ?_
  refine (St.pcnt (n := 13 - i) (by simp) (fun σ _ => by simp [V, upd]; omega_using [hi]) (by omega_using [])).mono
    (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  refine ⟨⟨by omega_using [], h.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩)
    (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], by
      simp only [List.mem_singleton] at hd; subst d; simp only [upd_self]⟩)⟩,z⟩
  change upd (upd (AT P i σ) aY _) (aT0 + i + 2) _ j = _
  rw [show (upd (AT P i σ) aY
      (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX))) aY = tv P σ (i + 2) from rfl]
  rw [AT_step hi j hj]
  congr 1
  omega_using [hi]

/-- The compact loop advances the completed prefix. -/
theorem tab_loop {P : MP} (fios : Bool := false) :
    VP (TS P 14) (tabBuild (fios := fios)) (TS P 0) := by
  refine VP.loop (fun n => ?_) 13
  by_cases hn : n+1 ≤ 14
  · have hi : 14-(n+1)<14 := by omega_using []
    obtain eq1 : 14-(14-(n+1))=n+1 := by omega_using [hn]
    obtain eq2 : 13-(14-(n+1))=n := by omega_using [hn]
    refine (tab_step (P := P) (14-(n+1)) hi (fios := fios)).mono ?_ ?_
    · intro σ s h
      simpa only [eq1] using h
    · intro σ s h
      obtain ts : TS P n σ s := by simpa only [eq2] using h.1
      refine ⟨?_,fun h0 => h0 ▸ ts,fun _ => ts⟩
      show some (!s.z) = _
      rw [h.2,eq2]
      by_cases h0 : n=0 <;> simp [h0] <;> omega_using [h0]
  · exact VP.of_false fun _ _ h => hn h.1

end VG.Proof.MillerRabin.Arm

end

end


/-! # The Miller–Rabin round on ARMv7: the windows

`wst P σ j`: `y` and the flag after `j` of the `16 w` windows (`mrun`).
`WI P m r`: in the word `m − 1` of `E` (`m` words left), `r` of its windows
left, the word shifted past the others (`svOf`); `WO P m`: `m` words left.
A window goes from `WI P m (n + 1)` to `WI P m n`, or `WO P (m − 1)` at the
word's end (`win_step`); a word from `WO P (n + 1)` to `WO P n` (`word_step`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- `y` and the flag after `j` windows. -/
abbrev wst (P : MP) (σ : State) (j : Nat) : Nat × Bool :=
  mrun (cOf P σ.mem) P.w (mOf P σ) (tv P σ) (eOf P σ) (16 * P.w) j

/-- The arrays during the windows. -/
def AW (P : MP) (j : Nat) (σ : State) (i : Nat) : Nat :=
  if i = aY then (wst P σ j).1 else if i = aM1 then mOf P σ else tv P σ (i - aT0)

/-- `y`, `−1` and the table. -/
abbrev LW : List Nat := [aY, aM1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The word `m − 1` of `E` shifted for `r` windows left. -/
abbrev svOf (P : MP) (σ : State) (m r : Nat) : Nat := (BitVec.ofNat 32 (ew P σ (m - 1)) <<< (4 * (8 - r))).toNat

/-- In the word `m − 1`, `r` of its windows left. -/
def WI (P : MP) (m r : Nat) (σ s : State) : Prop :=
  1 ≤ m ∧ m ≤ 2 * P.w ∧ r ≤ 8 ∧ St P (In P) (AW P (16 * P.w - (8 * (m - 1) + r))) LW
    (fun σ => upd (upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - (8 * (m - 1) + r))).2.toNat) sK
      (8 * (m - 1) + r)) sV (svOf P σ m r)) [sV, sK, sF] σ s

/-- `m` words left. -/
def WO (P : MP) (m : Nat) (σ s : State) : Prop :=
  m ≤ 2 * P.w ∧ St P (In P) (AW P (16 * P.w - 8 * m)) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * m)).2.toNat) sK (8 * m)) [sK, sF] σ s

section
variable {P : MP} {σ : State}

theorem wst_lt (h : In P σ) (j : Nat) : (wst P σ j).1 < cOf P σ.mem := by
  have := h.c3
  cases j with
  | zero => exact tv_lt h 0
  | succ j => exact mm_lt (by omega_arith)

/-- The digit at the top of the shifted word is the window's. -/
theorem digit_sv (h : In P σ) {m r : Nat} (hm1 : 1 ≤ m) (hm : m ≤ 2 * P.w) (hr1 : 1 ≤ r) (hr : r ≤ 8) :
    digitOf (svOf P σ m r) = eOf P σ / 16 ^ (16 * P.w - 1 - (16 * P.w - (8 * (m - 1) + r))) % 16 := by
  obtain lt : ew P σ (m - 1) < 2 ^ 32 := (σ.mem.readW _ 32).isLt
  obtain e := shl_shr28 (BitVec.ofNat 32 (ew P σ (m - 1))) (t := 8 - r) (by omega_arith)
  rw [ofNat_toNat32 lt] at e
  obtain e2 : (BitVec.ofNat 32 (ew P σ (m - 1)) <<< (4 * (8 - r)) >>> 28).toNat = digitOf (svOf P σ m r) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← e2, e, h.ew_val (by omega_arith), show 28 - 4 * (8 - r) = 4 * (r - 1) by omega_arith, digit_word _ _ _ (by omega_arith),
    show 16 * P.w - 1 - (16 * P.w - (8 * (m - 1) + r)) = 8 * (m - 1) + (r - 1) by omega_arith]

theorem svOf_next {m n : Nat} (hn : n < 8) :
    (BitVec.ofNat 32 (svOf P σ m (n + 1)) <<< 4).toNat = svOf P σ m n := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, shl4_succ32, show 8 - (n + 1) + 1 = 8 - n by omega_arith]

theorem svOf_lt (m r : Nat) : svOf P σ m r < 2 ^ 32 := BitVec.isLt _

theorem svOf_eight (m : Nat) : svOf P σ m 8 = ew P σ (m - 1) := by
  rw [svOf, show 4 * (8 - 8) = 0 from rfl, BitVec.shiftLeft_zero, ofNat_toNat32 (σ.mem.readW _ 32).isLt]

end


/-! ## A window's stages, `n + 1` windows left in the word `m − 1` -/

section
variable (P : MP) (m n : Nat)

/-- The windows done. -/
abbrev jw : Nat := 16 * P.w - (8 * (m - 1) + (n + 1))

/-- The header words at the window's start. -/
def V0w (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) sF (wst P σ (jw P m n)).2.toNat) sK (8 * (m - 1) + (n + 1))) sV (svOf P σ m (n + 1))

/-- After the four squarings. -/
abbrev st4 (σ : State) : Nat × Bool := sqst P 4 (fun _ => 0) (fun σ => wst P σ (jw P m n)) σ 4
def A2w (σ : State) : Nat → Nat := upd (AW P (jw P m n) σ) aY (st4 P m n σ).1
def V2w (σ : State) : Nat → Nat := upd (upd (upd (V0w P m n σ) sR 0) sF (st4 P m n σ).2.toNat) sQ 0

/-- The digit, and after the scan, `−1` and the product. -/
abbrev dgw (σ : State) : Nat := digitOf (svOf P σ m (n + 1))
def A3w (σ : State) : Nat → Nat := upd (A2w P m n σ) aX (tv P σ (dgw P m n σ))
def A4w (σ : State) : Nat → Nat := upd (A3w P m n σ) aM1 (mOf P σ)
abbrev Y5w (σ : State) : Nat := mm (cOf P σ.mem) P.w (st4 P m n σ).1 (tv P σ (dgw P m n σ))
def A5w (σ : State) : Nat → Nat := upd (A4w P m n σ) aY (Y5w P m n σ)

/-- After the comparisons. -/
def V7w (σ : State) : Nat → Nat :=
  upd (upd (V2w P m n σ) sE1 (decide (Y5w P m n σ = tv P σ 0)).toNat) sE2 (decide (Y5w P m n σ = mOf P σ)).toNat

end

/-- The table's entries. -/
abbrev Lt : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
abbrev LS4 : List Nat := [sQ, sR, sV, sK, sF]

theorem ite_toNat (p : Prop) [Decidable p] : (if p then 1 else 0) = (decide p).toNat := by
  by_cases h : p <;> simp [h]

theorem Lt_ne : ∀ i ∈ Lt, i ≠ aY ∧ i ≠ aX ∧ i ≠ aM1 := by decide

theorem AW_tab {P : MP} {j : Nat} {σ : State} {i : Nat} (hi : i ∈ Lt) : AW P j σ i = tv P σ (i - aT0) := by
  obtain ⟨h1, -, h3⟩ := Lt_ne i hi
  unfold AW; rw [ite_eq_right h1, ite_eq_right h3]

section
variable {P : MP} {m n : Nat} {σ : State}

theorem A5w_Y : A5w P m n σ aY = Y5w P m n σ := upd_self _ _ _
theorem A5w_M : A5w P m n σ aM1 = mOf P σ := by
  unfold A5w A4w; rw [upd_ne _ _ (by decide), upd_self]
theorem A5w_tab {i : Nat} (hi : i ∈ Lt) : A5w P m n σ i = tv P σ (i - aT0) := by
  obtain ⟨h1, h2, h3⟩ := Lt_ne i hi
  unfold A5w A4w A3w A2w; rw [upd_ne _ _ h1, upd_ne _ _ h3, upd_ne _ _ h2, upd_ne _ _ h1, AW_tab hi]
theorem A4w_Y : A4w P m n σ aY = (st4 P m n σ).1 := by
  unfold A4w A3w A2w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
theorem A4w_X : A4w P m n σ aX = tv P σ (dgw P m n σ) := by
  unfold A4w A3w; rw [upd_ne _ _ (by decide), upd_self]
theorem dgw_lt : dgw P m n σ < 16 := by
  have := svOf_lt (P := P) (σ := σ) m (n + 1); unfold dgw digitOf; omega_arith

theorem V2w_sV : V2w P m n σ sV = svOf P σ m (n + 1) := by
  unfold V2w V0w; simp only [upd, show sV ≠ sQ by decide, show sV ≠ sF by decide, show sV ≠ sR by decide, ↓reduceIte]
theorem V7w_sV : V7w P m n σ sV = svOf P σ m (n + 1) := by
  unfold V7w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), V2w_sV]
theorem V7w_sE1 : V7w P m n σ sE1 = (decide (Y5w P m n σ = tv P σ 0)).toNat := by
  unfold V7w; rw [upd_ne _ _ (by decide), upd_self]
theorem V7w_sE2 : V7w P m n σ sE2 = (decide (Y5w P m n σ = mOf P σ)).toNat := by
  unfold V7w; rw [upd_self]
theorem V7w_sF : V7w P m n σ sF = (st4 P m n σ).2.toNat := by
  unfold V7w V2w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
theorem V7w_sK : V7w P m n σ sK = 8 * (m - 1) + (n + 1) := by
  unfold V7w V2w V0w
  simp only [upd, show sK ≠ sE2 by decide, show sK ≠ sE1 by decide, show sK ≠ sQ by decide, show sK ≠ sF by decide,
    show sK ≠ sR by decide, show sK ≠ sV by decide, ↓reduceIte]

/-- The window's result. -/
theorem wst_next (h : In P σ) (hm1 : 1 ≤ m) (hm : m ≤ 2 * P.w) (hn : n + 1 ≤ 8) :
    wst P σ (jw P m n + 1) = (Y5w P m n σ, if dgw P m n σ = 0 then (st4 P m n σ).2 else
      (decide (Y5w P m n σ = tv P σ 0) || decide (Y5w P m n σ = mOf P σ))) := by
  obtain hd := digit_sv h hm1 hm (by omega_arith) hn
  show mwin _ _ _ _ (eOf P σ / 16 ^ (16 * P.w - 1 - jw P m n) % 16) (wst P σ (jw P m n)) = _
  rw [← hd]
  rfl

end

/-- One window. -/
theorem win_step {P : MP} {m : Nat} (n : Nat) (fios : Bool := false) :
    VP (WI P m (n + 1)) (win (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → WO P (m - 1) σ s) ∧ (0 < n → WI P m n σ s) := by
  by_cases hc : 1 ≤ m ∧ m ≤ 2 * P.w ∧ n + 1 ≤ 8
  swap
  · exact VP.of_false fun σ s h => hc ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨hm1, hm, hn⟩ := hc
  refine VP.of_imp (p := P.w ≤ 128) (fun σ s h => (h.2.2.2.1 : In P σ).w128) fun w128 => ?_
  refine VP.mono (F := St P (In P) (AW P (jw P m n)) LW (V0w P m n) [sV, sK, sF]) ?_ (fun σ s h => h.2.2.2)
    (fun _ _ h => h)
  simp only [win, seqs]
  -- The count and threshold of the squarings.
  refine VP.seq (G := SqS P (In P) (AW P (jw P m n)) LW.tail (fun σ => upd (V0w P m n σ) sR 0) LS4 4 (fun _ => 0)
    (fun σ => wst P σ (jw P m n)) 4) ?_ ?_
  · refine St.psqFour.mono (fun _ _ h => h) fun σ s h => ⟨Nat.le_refl _, h.mono (fun i hi => ⟨hi, ?_⟩)
      (fun d hd => ⟨hd, ?_⟩)⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · show AW P (jw P m n) σ aY = upd (AW P (jw P m n) σ) aY (wst P σ (jw P m n)).1 aY
        rw [upd_self]; rfl
      · exact (upd_ne _ _ ((by decide : ∀ i ∈ LW.tail, i ≠ aY) i hi)).symm
    · simp only [LS4, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl
  -- The squarings.
  refine VP.seq (G := St P (In P) (A2w P m n) (aY :: LW.tail) (V2w P m n) LS4)
    ((sq_loop (fios := fios) (fun σ e => e) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun σ _ => rfl) (fun σ _ => upd_self _ _ _)
      (fun _ _ => by decide) (by decide) (fun σ e => wst_lt e _) 3).mono (fun _ _ h => h)
      (fun σ s h => h.2)) ?_
  -- The scan.
  refine VP.seq (G := St P (In P) (A3w P m n) (aX :: aY :: Lt) (V2w P m n) LS4) ?_ ?_
  · refine VP.mono (F := St P (In P) (A2w P m n) (aY :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.pscan (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun σ _ => by rw [V2w_sV]; exact svOf_lt m (n + 1))).mono (fun _ _ h => h) fun σ s h => ?_
      refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
      rw [V2w_sV]
      show upd _ aX (A2w P m n σ (aT0 + dgw P m n σ)) i = upd _ aX (tv P σ (dgw P m n σ)) i
      have dl : dgw P m n σ < 16 := dgw_lt
      congr 1
      unfold A2w
      rw [upd_ne _ _ (by simp only [aT0, aY]; omega_arith), AW_tab (i := aT0 + dgw P m n σ) (by
        have : ∀ k < 16, aT0 + k ∈ Lt := by decide
        exact this _ dl), Nat.add_sub_cancel_left]
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: Lt, i ∈ aY :: LW.tail) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  -- `−1`.
  refine VP.seq (G := St P (In P) (A4w P m n) (aM1 :: aX :: aY :: Lt) (V2w P m n) LS4)
    (St.pcopyClr cM1_taint (by decide) (by decide) (by decide) (by decide)) ?_
  -- `y T_d`.
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: aX :: Lt) (V2w P m n) LS4) ?_ ?_
  · refine VP.mono (F := St P (In P) (A4w P m n) (aY :: aM1 :: aX :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.pmulY (fios := fios) (.inr rfl) (by decide) (by decide) (by decide) (by decide)
        (fun σ e => by rw [A4w_Y]; exact sqst_lt (q0 := 4) (fun σ e => e) (fun σ e => wst_lt e _) σ e 4)
        (fun σ e => by rw [A4w_X]; exact tv_lt e _)).mono (fun _ _ h => h) fun σ s h => ?_
      refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
      rw [A4w_Y, A4w_X]; rfl
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: aM1 :: aX :: Lt, i ∈ aM1 :: aX :: aY :: Lt) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  -- The comparisons.
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: Lt)
    (fun σ => upd (V2w P m n σ) sE1 (decide (Y5w P m n σ = tv P σ 0)).toNat) (sE1 :: LS4)) ?_ ?_
  · refine VP.mono (F := St P (In P) (A5w P m n) (aY :: aM1 :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.peqS eq1_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, ?_⟩)
      rw [A5w_Y, A5w_tab (i := aT0) (by decide), ite_toNat, Nat.sub_self]
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: aM1 :: Lt, i ∈ aY :: aM1 :: aX :: Lt) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: Lt) (V7w P m n) (sE2 :: sE1 :: LS4))
    ((St.peqS eq2_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, ?_⟩)) ?_
  · rw [A5w_Y, A5w_M, ite_toNat]; rfl
  -- The flag, the word and the count.
  refine (St.pwinEnd (K := 8 * (m - 1) + n) (v := fun σ => svOf P σ m (n + 1))
    (e1 := fun σ => decide (Y5w P m n σ = tv P σ 0)) (e2 := fun σ => decide (Y5w P m n σ = mOf P σ))
    (fb := fun σ => (st4 P m n σ).2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => V7w_sV) (fun σ _ => svOf_lt m (n + 1)) (fun σ _ => V7w_sE1) (fun σ _ => V7w_sE2)
    (fun σ _ => V7w_sF) (fun σ _ => V7w_sK) (by omega_arith)).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  have pre : In P σ := h.1
  obtain wn := wst_next pre hm1 hm hn
  obtain j1 : jw P m n + 1 = 16 * P.w - (8 * (m - 1) + n) := by have := pre.w4; simp only [jw]; omega_arith
  rw [j1] at wn
  obtain hA : ∀ i ∈ LW, A5w P m n σ i = AW P (16 * P.w - (8 * (m - 1) + n)) σ i := fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [A5w_Y]; unfold AW; rw [ite_eq_left rfl, wn]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [A5w_M]; unfold AW; rw [ite_eq_right (by decide), ite_eq_left rfl]
    · rw [A5w_tab hi, AW_tab hi]
  obtain hF : (if digitOf (svOf P σ m (n + 1)) = 0 then (st4 P m n σ).2 else
      (decide (Y5w P m n σ = tv P σ 0) || decide (Y5w P m n σ = mOf P σ))).toNat =
      (wst P σ (16 * P.w - (8 * (m - 1) + n))).2.toNat := by rw [wn]
  obtain hL : ∀ i ∈ LW, i ∈ aY :: aM1 :: Lt := by decide
  obtain stI : 0 < n → WI P m n σ s := fun hn0 => by
    refine ⟨hm1, hm, by omega_arith, h.mono (fun i hi => ⟨hL i hi, hA i hi⟩) (fun d hd => ⟨?_, ?_⟩)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · simp only [upd, show sV ≠ sK by decide, ↓reduceIte]; exact svOf_next (by omega_arith)
      · rw [upd_self, upd_ne _ _ (by decide : sK ≠ sV), upd_self]
      · simp only [upd, show sF ≠ sK by decide, show sF ≠ sV by decide, ↓reduceIte]; exact hF
  obtain stO : n = 0 → WO P (m - 1) σ s := fun hn0 => by
    subst hn0
    refine ⟨by omega_arith, h.mono (fun i hi => ⟨hL i hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)⟩
    · rw [hA i hi, show 16 * P.w - (8 * (m - 1) + 0) = 16 * P.w - 8 * (m - 1) by omega_arith]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · simp only [upd_self, Nat.add_zero]
      · simp only [upd, show sF ≠ sK by decide, show sF ≠ sV by decide, ↓reduceIte]
        rw [hF, show 16 * P.w - (8 * (m - 1) + 0) = 16 * P.w - 8 * (m - 1) by omega_arith]
  refine ⟨?_, stO, stI⟩
  show some (!s.z) = _
  rw [z]
  by_cases h0 : n = 0
  · subst h0; simp
  · have : (8 * (m - 1) + n) % 8 = n := by omega_arith
    rw [this]; simp [h0]; omega_arith

end VG.Proof.MillerRabin.Arm

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A word's windows. -/
theorem word_step {P : MP} (n : Nat) (fios : Bool := false) :
    VP (WO P (n + 1)) (word (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → WO P 0 σ s) ∧ (0 < n → WO P n σ s) := by
  by_cases hc : n + 1 ≤ 2 * P.w
  swap
  · exact VP.of_false fun σ s h => hc h.1
  refine VP.of_imp (p := P.w ≤ 128) (fun σ s h => (h.2.1 : In P σ).w128) fun w128 => ?_
  refine VP.mono (F := St P (In P) (AW P (16 * P.w - 8 * (n + 1))) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * (n + 1))).2.toNat) sK (8 * (n + 1))) [sK, sF]) ?_
    (fun σ s h => h.2) (fun _ _ h => h)
  simp only [Impl.MillerRabin.Arm.word, seqs]
  refine VP.seq (St.pwordK (K := 8 * (n + 1)) (by decide) (fun σ _ => by
    rw [upd_self])) (VP.seq (St.pwordLd (m := n + 1) (fun σ e => e) (by omega_arith) hc) ?_)
  refine VP.seq ((VP.loop (I := fun k => WI P (n + 1) k) (fun k => win_step (fios := fios) k) 7).mono (fun σ s h => ?_)
    (fun _ _ h => h)) ?_
  · refine ⟨by omega_arith, hc, by decide, ?_⟩
    refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
    · rw [show 16 * P.w - (8 * (n + 1 - 1) + 8) = 16 * P.w - 8 * (n + 1) by omega_arith]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · rw [upd_self, upd_self, svOf_eight, Nat.add_sub_cancel]
      · rw [upd_ne _ _ (by decide), upd_self, upd_ne _ _ (by decide), upd_self]; omega_arith
      · simp only [upd, show sF ≠ sV by decide, show sF ≠ sK by decide, ↓reduceIte]
        rw [show 16 * P.w - (8 * (n + 1 - 1) + (7 + 1)) = 16 * P.w - 8 * (n + 1) by omega_arith]
  · refine VP.mono (F := St P (In P) (AW P (16 * P.w - 8 * n)) LW
      (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * n)).2.toNat) sK (8 * n)) [sK, sF]) ?_
      (fun σ s h => by rw [Nat.add_sub_cancel] at h; exact h.2) (fun _ _ h => h)
    refine (St.pwordEnd (K := 8 * n) (by decide) (fun σ _ => upd_self _ _ _) (by omega_arith)).mono (fun _ _ h => h)
      fun σ s ⟨h, z⟩ => ⟨?_, fun h0 => ⟨by omega_arith, h0 ▸ h⟩, fun _ => ⟨by omega_arith, h⟩⟩
    show some (!s.z) = _
    rw [z]
    by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero, Nat.mul_eq_zero]

/-- The words. -/
theorem words_loop {P : MP} (fios : Bool := false) : VP (WO P (2 * P.w)) (.loop (word (fios := fios)) .ne) (WO P 0) := by
  refine VP.of_imp (p := 1 ≤ P.w) (fun σ s h => by have := (h.2.1 : In P σ).w4; omega_arith) fun w1 => ?_
  have := VP.loop (I := fun k => WO P k) (fun k => word_step (fios := fios) k) (2 * P.w - 1)
  rwa [show 2 * P.w - 1 + 1 = 2 * P.w by omega_arith] at this

end VG.Proof.MillerRabin.Arm
