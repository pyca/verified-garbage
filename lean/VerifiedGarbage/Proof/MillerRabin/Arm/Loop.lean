module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The Miller–Rabin round on ARMv7: one bit, and the loop

`Lp P k`: the stage with `k` bits left of the `64 w − 1`, after `j` bits:
`c`'s copy shifted left `j` bits, `y = yseq … j`, the flag `fseq … j` and
the count `k`. One bit goes from `Lp P (n + 1)` to `Lp P n` (`step_vp`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The witness, Montgomery one and minus one, from `σ`. -/
abbrev xOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 5
abbrev oOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 9
abbrev mOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 10

/-- `y` and the flag after `j` bits. -/
abbrev yv (P : MP) (σ : State) (j : Nat) : Nat := yseq (cOf P σ.mem) P.w (xOf P σ) (oOf P σ) j
abbrev fv (P : MP) (σ : State) (j : Nat) : Bool := fseq (cOf P σ.mem) P.w (xOf P σ) (oOf P σ) (mOf P σ) j

/-- The arrays after `j` bits. -/
def AL (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (upd (fun _ => 0) aE (cOf P σ.mem * 2 ^ j % P.R)) aB (xOf P σ)) aOne (oOf P σ))
    aM1 (mOf P σ)) aY (yv P σ j)

abbrev LL : List Nat := [aY, aM1, aOne, aB, aE]

/-- The header words after `j` bits. -/
def VL (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (upd (fun _ => 0) sF (fv P σ j).toNat) sK (64 * P.w - 1 - j)

abbrev LSL : List Nat := [sK, sF]

/-- The stage with `k` bits left. -/
def Lp (P : MP) (k : Nat) (σ s : State) : Prop :=
  k ≤ 64 * P.w - 1 ∧ St P (In P) (AL P (64 * P.w - 1 - k)) LL (VL P (64 * P.w - 1 - k)) LSL σ s

theorem mm_lt {c w x y : Nat} (hc : 0 < c) : mm c w x y < c := Nat.mod_lt _ hc

theorem yv_lt {P : MP} {σ : State} (h : In P σ) (j : Nat) : yv P σ j < cOf P σ.mem := by
  have c3 := h.c3
  cases j with
  | zero => show numAt σ.mem (State.addr P.ws) P.w 9 < _; rw [h.one]; exact Nat.mod_lt _ (by omega)
  | succ j => exact mm_lt (by omega)

/-- A piece whose precondition is never met. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁ (h σ _)⟩

/-! ## One bit's stages, after `j` bits -/

def A1 (P : MP) (j : Nat) (σ : State) : Nat → Nat := upd (AL P j σ) aE (2 * AL P j σ aE % P.R)
def V1 (P : MP) (j : Nat) (σ : State) : Nat → Nat := upd (VL P j σ) sBit (2 * AL P j σ aE / P.R)
abbrev LS1 : List Nat := sBit :: LSL
def A2 (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (A1 P j σ) aY (mm (cOf P σ.mem) P.w (A1 P j σ aY) (A1 P j σ aY))
def A3 (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (A2 P j σ) aX (if V1 P j σ sBit = 0 then A2 P j σ aOne else A2 P j σ aB)
abbrev L3 : List Nat := aX :: LL
abbrev L4 : List Nat := aY :: aX :: [aM1, aOne, aB, aE]
def A4 (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (A3 P j σ) aY (mm (cOf P σ.mem) P.w (A3 P j σ aY) (A3 P j σ aX))
def V5 (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (V1 P j σ) sE1 (if A4 P j σ aY = A4 P j σ aOne then 1 else 0)
abbrev LS5 : List Nat := sE1 :: LS1
def V6 (P : MP) (j : Nat) (σ : State) : Nat → Nat :=
  upd (V5 P j σ) sE2 (if A4 P j σ aY = A4 P j σ aM1 then 1 else 0)
abbrev LS6 : List Nat := sE2 :: LS5

theorem toNat_beq_one (b : Nat) : (b % 2 == 1).toNat = b % 2 := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h]

section
variable {P : MP} {j : Nat} {σ : State}

theorem AL_aE : AL P j σ aE = cOf P σ.mem * 2 ^ j % P.R := rfl
theorem AL_aB : AL P j σ aB = xOf P σ := rfl
theorem AL_aOne : AL P j σ aOne = oOf P σ := rfl
theorem AL_aM1 : AL P j σ aM1 = mOf P σ := rfl
theorem AL_aY : AL P j σ aY = yv P σ j := rfl
theorem VL_sF : VL P j σ sF = (fv P σ j).toNat := rfl
theorem VL_sK : VL P j σ sK = 64 * P.w - 1 - j := rfl

/-- The bit shifted out. -/
theorem V1_bit (hj : j < 64 * P.w) : V1 P j σ sBit = (ebit (cOf P σ.mem) P.w j).toNat := by
  simp only [V1, upd_self, AL_aE, MP.R]
  rw [shift_carry _ _ _ hj, ebit, toNat_beq_one]

theorem V1_le (hj : j < 64 * P.w) : V1 P j σ sBit ≤ 1 := by
  rw [V1_bit hj]; cases ebit (cOf P σ.mem) P.w j <;> decide

theorem A4_aE : A4 P j σ aE = cOf P σ.mem * 2 ^ (j + 1) % P.R := by
  show 2 * AL P j σ aE % P.R = _
  rw [AL_aE]; exact shift_val _ _ _

end

theorem A4_aY {P : MP} {j : Nat} {σ : State} (hj : j < 64 * P.w) : A4 P j σ aY = yv P σ (j + 1) := by
  show mm (cOf P σ.mem) P.w (A2 P j σ aY) (if V1 P j σ sBit = 0 then A2 P j σ aOne else A2 P j σ aB) = _
  rw [V1_bit hj]
  show _ = mm (cOf P σ.mem) P.w (mm (cOf P σ.mem) P.w (yv P σ j) (yv P σ j))
    (if ebit (cOf P σ.mem) P.w j then xOf P σ else oOf P σ)
  cases ebit (cOf P σ.mem) P.w j <;> rfl

theorem flag_logic (b F : Bool) (Y O M : Nat) :
    (if b.toNat = 1 then (decide ((if Y = O then 1 else 0) = 1) || decide ((if Y = M then 1 else 0) = 1))
      else (decide (F.toNat = 1) || decide ((if Y = M then 1 else 0) = 1))).toNat =
    (if b then (Y == O || Y == M) else (F || Y == M)).toNat := by
  rw [VG.Proof.RsaKeyGen.beq_dec Y O, VG.Proof.RsaKeyGen.beq_dec Y M]
  cases b <;> cases F <;> by_cases h1 : Y = O <;> by_cases h2 : Y = M <;> simp [h1, h2]

theorem flagv_V6 {P : MP} {j : Nat} {σ : State} (hj : j < 64 * P.w) : flagv (V6 P j σ) = (fv P σ (j + 1)).toNat := by
  have e6 : V6 P j σ sBit = (ebit (cOf P σ.mem) P.w j).toNat := V1_bit hj
  have e1 : V6 P j σ sE1 = if yv P σ (j + 1) = oOf P σ then 1 else 0 := by
    show (if A4 P j σ aY = A4 P j σ aOne then 1 else 0) = _
    rw [A4_aY hj]; rfl
  have e2 : V6 P j σ sE2 = if yv P σ (j + 1) = mOf P σ then 1 else 0 := by
    show (if A4 P j σ aY = A4 P j σ aM1 then 1 else 0) = _
    rw [A4_aY hj]; rfl
  have ef : V6 P j σ sF = (fv P σ j).toNat := rfl
  unfold flagv
  rw [e6, e1, e2, ef, flag_logic]
  rfl

theorem step_vp {P : MP} (n : Nat) :
    VP (Lp P (n + 1)) step fun σ s => isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → Lp P 0 σ s) ∧
      (0 < n → Lp P n σ s) := by
  by_cases hn : n + 1 ≤ 64 * P.w - 1
  swap
  · exact VP.of_false fun σ s h => hn h.1
  -- The bits done.
  obtain ⟨j, hj⟩ : ∃ j, j = 64 * P.w - 1 - (n + 1) := ⟨_, rfl⟩
  have hj1 : 64 * P.w - 1 - n = j + 1 := by omega
  have hjw : j < 64 * P.w := by omega
  refine VP.mono (F := St P (In P) (AL P j) LL (VL P j) LSL) ?_ (fun σ s h => hj ▸ h.2) (fun _ _ h => h)
  simp only [step, seqs]
  refine VP.seq (G := St P (In P) (A1 P j) LL (V1 P j) LS1) ?_
    (VP.seq (G := St P (In P) (A2 P j) LL (V1 P j) LS1) ?_
    (VP.seq (G := St P (In P) (A3 P j) L3 (V1 P j) LS1) ?_
    (VP.seq (G := St P (In P) (A4 P j) L4 (V1 P j) LS1) ?_
    (VP.seq (G := St P (In P) (A4 P j) L4 (V5 P j) LS5) ?_
    (VP.seq (G := St P (In P) (A4 P j) L4 (V6 P j) LS6) ?_ ?_)))))
  -- The bit.
  · exact St.pbitOut (by decide) fun σ _ => by rw [AL_aE]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- `y²`.
  · exact St.pmulY (L := [aM1, aOne, aB, aE]) (.inl rfl) (by decide) (by decide) (by decide) (by decide)
      (fun σ e => yv_lt e j) (fun σ e => yv_lt e j)
  -- The multiplicand.
  · exact St.psel sel_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun σ _ => V1_le hjw
  -- `y` times it.
  · refine (St.pmulY (L := [aX, aM1, aOne, aB, aE]) (.inr rfl) (by decide) (by decide) (by decide) (by decide)
      (fun σ e => by have := e.c3; exact mm_lt (by omega)) (fun σ e => ?_)).mono
      (fun σ s h => h.mono (fun i hi => ⟨(by decide : ∀ i ∈ L4, i ∈ L3) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)) (fun _ _ h => h)
    show (if V1 P j σ sBit = 0 then AL P j σ aOne else AL P j σ aB) < _
    rw [AL_aOne, AL_aB]
    have := e.c3
    split
    · show numAt σ.mem (State.addr P.ws) P.w 9 < _; rw [e.one]; exact Nat.mod_lt _ (by omega)
    · exact e.x5
  -- `y = 1`, `y = −1`.
  · exact St.peqS eq1_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact St.peqS eq2_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The flag and the count.
  · have vK : ∀ σ, V6 P j σ sK = n + 1 := fun σ => by
      show 64 * P.w - 1 - j = n + 1
      omega
    refine (St.pflag (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)
      (fun σ _ => ?_) (fun σ _ => ?_) (fun σ _ => by rw [vK]; omega) (fun σ e => ?_)).mono (fun _ _ h => h)
      (fun σ s ⟨h, z⟩ => ?_)
    · show V1 P j σ sBit ≤ 1; exact V1_le hjw
    · show (if A4 P j σ aY = A4 P j σ aOne then 1 else 0) ≤ 1; split <;> decide
    · show (if A4 P j σ aY = A4 P j σ aM1 then 1 else 0) ≤ 1; split <;> decide
    · show (fv P σ j).toNat ≤ 1; exact Bool.toNat_le _
    · rw [vK]; have := e.w128; omega
    · rw [vK, Nat.add_sub_cancel] at z
      have lp : Lp P n σ s := by
        refine ⟨by omega, ?_⟩
        rw [hj1]
        refine h.mono (fun i hi => ⟨(by decide : ∀ i ∈ LL, i ∈ L4) i hi, ?_⟩) (fun d hd => ⟨by
          simp only [LSL, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
          rcases hd with rfl | rfl <;> simp, ?_⟩)
        · simp only [LL, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl
          · exact A4_aY hjw
          · rfl
          · rfl
          · rfl
          · exact A4_aE
        · simp only [LSL, List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · show V6 P j σ sK - 1 = 64 * P.w - 1 - (j + 1)
            rw [vK]; omega
          · show flagv (V6 P j σ) = (fv P σ (j + 1)).toNat
            exact flagv_V6 hjw
      refine ⟨?_, fun h0 => h0 ▸ lp, fun _ => lp⟩
      show some (!s.z) = _
      rw [z]
      by_cases h0 : n = 0 <;> simp [h0] <;> omega

end VG.Proof.MillerRabin.Arm
