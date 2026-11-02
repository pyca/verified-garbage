module
public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces2

import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.RvKS

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
theorem tab_mem : ∀ k < 16, aT0 + k ∈ wJs := by decide

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
  refine wp_dp (op2_imm (encodable_lt (by omega))) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have r5 : Rest [.r1] s1 s5 :=
    (u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp))))
  have h5 := h1.of_rest r5 (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  have hw5 := hw1.rest r5
  refine h5.str hw5 (d := sE1) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨?_, hwt⟩
  have dl : digitOf (V sV) < 16 := by simp only [digitOf]; omega
  have g : (s5.gpr .r1).toNat = (decide (digitOf (V sV) = j)).toNat := by
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
    have : j = 16 := by omega
    subst this
    refine WP.block_nil ⟨?_, hw⟩
    have e : selv A d 16 = A (aT0 + d) := by simp only [selv, hd, ↓reduceIte]
    rw [e] at h
    exact h
  | n + 1, j, hjn, hj1, s, h, hw => by
    have hold_L : ∀ i, hold i ∉ L := fun i => by unfold hold; split; exacts [hX, hM]
    rw [scanFrom, WP.seq_iff]
    refine WP.mono (h.mask_ok (j := j) (by omega) hw hv vl) fun s1 ⟨h1, hw1⟩ => ?_
    rw [WP.seq_iff]
    have hb : aT0 + j ∈ hold (j + 1) :: L := List.mem_cons_of_mem _ (hT j (by omega))
    have ne1 : hold j ≠ aT0 + j := fun e => by have := hold_lt j; omega
    refine WP.mono (h1.sel_ok hw1 (hold_mem j) List.mem_cons_self hb (hold_ne j) ne1 List.mem_cons_self
      (by rw [upd_self]; cases decide (digitOf (V sV) = j) <;> decide)) fun s2 ⟨h2, hw2, _⟩ => ?_
    refine scanFrom_ok hd hT hX hM hv hE1 dv vl n (j + 1) (by omega) (by omega) s2 ?_ hw2
    rw [hold_two]
    refine h2.mono (fun i hi => ⟨?_, ?_⟩) (fun e he => ⟨List.mem_cons_of_mem _ he, ?_⟩)
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
    · rcases List.mem_cons.mp hi with rfl | hi
      · have ne2 : aT0 + j ≠ hold (j + 1) := fun e => by have := hold_lt (j + 1); omega
        simp only [upd_self]
        rw [upd_ne _ _ ne2, dv]
        unfold selv
        by_cases hdj : d = j
        · simp only [hdj, decide_true, Bool.toNat_true, Nat.one_ne_zero, ↓reduceIte, Nat.lt_succ_self]
        · simp only [hdj, decide_false, Bool.toNat_false, ↓reduceIte, show (d < j + 1) ↔ (d < j) by omega]
      · have n1 : i ≠ hold j := fun e => hold_L j (e ▸ hi)
        have n2 : i ≠ hold (j + 1) := fun e => hold_L (j + 1) (e ▸ hi)
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
  have dl : digitOf (V σ sV) < 16 := by have := vl σ e; simp only [digitOf]; omega
  rw [scan, WP.seq_iff]
  have t0 : aT0 ∈ L := hT 0 (by decide)
  refine WP.mono (h.copy_ok hw (by decide) (h.live_lt _ t0) (by decide)) fun s1 ⟨h1, hw1, _⟩ => ?_
  refine WP.mono (scanFrom_ok (A := A σ) dl hT hX hM hv hE1 rfl (vl σ e) 15 1 rfl (Nat.le_refl _) s1 ?_ hw1)
    fun t ⟨ht, hwt⟩ => ⟨e, ht, hwt⟩
  rw [h.arrs aT0 t0] at h1
  have e1 : selv (A σ) (digitOf (V σ sV)) 1 = A σ aT0 := by
    unfold selv; split
    · rw [show digitOf (V σ sV) = 0 by omega]; rfl
    · rfl
  rw [show hold (1 + 1) = aM1 from rfl, e1]
  exact h1

end

end VG.Proof.MillerRabin.Arm
