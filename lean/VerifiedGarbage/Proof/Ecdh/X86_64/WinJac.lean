module

public import VerifiedGarbage.Proof.Ecdh.X86_64.MulOk
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.AddConst
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages

/-!
# ECDH on x86-64: `[d]P` by 5-bit windows in Jacobian coordinates

For four or six words and a curve of prime order `n` with `n mod 32 ≥ 17`
(P-256, P-384), the slots of the Jacobian window method (`jwQ`, which
`WinJacA.lean` and `WinJacOdd.lean` run): numbered slots, its grid of 85 (the
table of 16 entries of five coordinates, then the selected entry) slots
`WT … WT + 84` past the tables of bits (`jwSlots_eq`), so they are apart as
the window method needs (`jwLayQ`); the bound on the recoded scalar
(`recodeJ_lt`); and what the window method and the power may write
(`mulQJW`, `mulQJ_w`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-! ## The slots -/

/-- The Jacobian window method's configuration for ECDH. -/
abbrev jwQ (c : Cfg) : JacWinCfg := Impl.Ecdh.X86_64.Cfg.jwinCfg c

/-- The indices of its slots: read only, written, and the grid. -/
def roJ : List Nat := [AP, B3P, ZERO, PX, PY, ONEP]
def otherJ : List Nat := [RX, RY, RZ, DX, DY, DZ, PT, T0, T1, T2, T3, T4, T5]
def gridJ : List Nat := (List.range 85).map (WT + ·)

theorem jwGrid_eq (c : Cfg) : jwGrid (jwQ c) = gridJ.map c.sl := by
  simp only [jwGrid, gridJ, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show c.sl WT + 8 * c.n * i = c.sl (WT + i)
  simp (disch := sl_ne) only [sl_eq]; rw [Nat.mul_add, Nat.add_assoc]

theorem jwSlots_eq (c : Cfg) : jwSlots (jwQ c) = (roJ ++ otherJ ++ gridJ).map c.sl := by
  rw [jwSlots, jwGrid_eq, List.map_append, List.map_append]; rfl

theorem jwW_eq (c : Cfg) : jwW (jwQ c) = slW c (otherJ ++ gridJ ++ [TMP]) := by
  rw [jwW, jwWs, jwGrid_eq]; simp only [slW, List.map_append, List.map_map]; rfl

theorem jwIdx_lt : ∀ i ∈ roJ ++ otherJ ++ gridJ, i < 169 ∧ i ≠ MP ∧ i ≠ TMP := by decide

/-- Every slot below `169` is in the working space, for four or six words. -/
theorem sl_le_jw (c : Cfg) (h46 : c.n = 4 ∨ c.n = 6) {i : Nat} (hi : i < 169) : c.sl i + 8 * c.n ≤ size := by
  have hix : ix c i < 169 := by
    have := tk_le c
    rcases ix_cases c i with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] <;> first | decide | omega
  rw [sl_eq']
  rcases h46 with h4 | h4 <;> rw [h4] <;> show _ ≤ 8192 <;> omega

theorem lay_jw (h46 : c.n = 4 ∨ c.n = 6) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 169 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le_jw c h46 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

theorem jwinJ_le (hc : CfgOk c) : Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ 13 * c.n + 1 := by
  unfold Impl.Ecdh.X86_64.Cfg.jwinJ; have := hc.len_hi; have := hc.nbits_le; omega_arith

theorem jwLayQ (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) : JacWinLay (jwQ c) size := by
  have hn := hc.n0
  have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  have hJle := jwinJ_le hc
  have hJ2 : 2 ≤ Impl.Ecdh.X86_64.Cfg.jwinJ c := by
    unfold Impl.Ecdh.X86_64.Cfg.jwinJ
    have := hc.len8
    by_cases h : c.nbits < 8 * c.C.len
    · have := (hc.mask h).1; omega_arith
    · omega_arith
  have hb : (jwQ c).bits = c.sl WB := rfl
  have hK : (jwQ c).tbl = c.sl WT := rfl
  have hMn : (jwQ c).M.n = c.n := rfl
  refine ⟨h46, ?_, ?_, ?_, ?_, rfl, ⟨by omega_arith, by omega_arith⟩, ?_, ?_, ?_⟩
  · rw [jwSlots_eq]; exact lay_jw h46 rfl rfl rfl jwIdx_lt
  · exact map_sl_disj hn (l₁ := roJ) (l₂ := otherJ) (by decide)
  · exact map_sl_nodup hn (l := otherJ) (by decide)
  · intro x hx
    have hx' : x ∈ (roJ ++ otherJ).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    have key : ∀ i ∈ roJ ++ otherJ, i < WT := by decide
    rw [hK, hMn]; exact Or.inl (sl_lt c (key i hi))
  · rw [hK]; simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WT <;> omega_arith
  · rw [hb, hJ]; simp (disch := sl_ne) only [sl_eq]
    rcases h46 with h4 | h4 <;> rw [h4] <;> show _ ≤ 8192 <;> unfold WB <;> omega_arith
  · intro w hw
    rw [jwW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [hb, hJ]
    have key : ∀ i ∈ otherJ ++ gridJ ++ [TMP], i < WB ∨ WT ≤ i := by decide
    rcases key i hi with h | h
    · by_cases h6 : i = TMP ∧ c.n = 6
      · obtain ⟨rfl, h6⟩ := h6
        refine Or.inl ?_
        dsimp only
        rw [sl_tmp6 c h6]; simp (disch := sl_ne) only [sl_eq]; unfold WB
        rw [h6] at hJle ⊢; omega
      · exact Or.inr (sl_lt c h (by
          by_cases ht : i = TMP
          · exact .inr (.inr ⟨fun e => h6 ⟨ht, e⟩, by decide⟩)
          · exact .inl ht))
    · refine Or.inl ?_
      dsimp only
      simp (disch := sl_ne) only [sl_eq]
      unfold WB; unfold WT at h
      rcases h46 with h4 | h4 <;> rw [h4] <;> omega_arith

/-! ## The recoded scalar -/

/-- `k + 16 Σ_{j<J} 32^j < 32^J` for `k < 2^b` and `J = ⌊(b + 6) / 5⌋`
(`Cfg.jwinJ`). -/
theorem recodeJ_lt {k b : Nat} (hk : k < 2 ^ b) :
    k + JacWinCfg.offset ((b + 6) / 5) < 32 ^ ((b + 6) / 5) := by
  rw [Weierstrass.X86_64.offset_eq]
  have hg := Window5.geom_mul ((b + 6) / 5)
  have h4 : 2 ^ b * 4 ≤ 32 ^ ((b + 6) / 5) := by
    rw [show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul, show 2 ^ b * 4 = 2 ^ (b + 2) by rw [Nat.pow_add]]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  omega_arith

/-! ## `[d]P` and `Z^(p-2)` -/

/-- What the window method writes, but its recoded scalar and bits and
the power's: `K` and the window method's slots. -/
def mulJI : List Nat := otherJ ++ gridJ ++ [TMP] ++ [K]

theorem mulJI_idx : ∀ i ∈ mulJI, i = TMP ∨ 12 ≤ i := by decide

/-- What the window method and the power may write. -/
abbrev mulQJW (c : Cfg) : List (Nat × Nat) := winX c ++ slW c mulJI ++ pwW c

theorem mulQJ_w (hc : CfgOk c) : MulW c (mulQJW c) where
  fixed := (fixedOk_winX.append (fixedOk_slW mulJI_idx)).append fixedOk_pwW
  d := apart_append (apart_append (apart_winX (by decide)) (apart_slW (by decide))) (apart_pwW (by decide) (by decide))
  flag := fun w hw => by
    have := hc.n0
    rcases apart_append (apart_append (apart_winX (c := c) (i := FLAG) (by decide))
      (apart_slW (l := mulJI) (by decide))) (apart_pwW (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h

end VG.Proof.Ecdh.X86_64
