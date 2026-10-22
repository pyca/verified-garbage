module

public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Group
import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# One-pass XTS-AES on AArch64: the setup

`enter_ok`: the arguments moved where the round code of
`vg_aes_encrypt_blocks_aes` expects them, and the tweak loaded into `x14` and
`x15`. `encSetup_ok`, `decSetup_ok`: the round keys loaded as `aes` and
`aesDec` need them (`Keys`, `DKeys`), as `Aese.encSetup_ok` and
`Aese.decSetup_ok` show for the block functions, from a state whose
schedule at `x0` is readable and `x3` the number of blocks: so `XInv … 0 0`
holds after `enter ++ setup` (`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt roundKey)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese (keysCommon encSetup decSetup kreg dreg)
open VG.Impl.AesXts.AArch64Aes (enter)

/-- What the key setups need of the state: the schedule at `x0` readable,
and `x1` a number of rounds. -/
structure KPre (s : State) : Prop where
  key_in : ∀ {o : Nat}, o + 16 ≤ 240 → InRegions (s.rd ++ s.wr) (bkp s + BitVec.ofNat 64 o) 16
  rounds : bnr s = 10 ∨ bnr s = 12 ∨ bnr s = 14

theorem common_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block keysCommon) s₀ (Common s₀) := by
  have hR := hp.rounds
  have hn : bnb s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (bnr s₀) := by simp [bnr]
  have hx3 : s₀.gpr .x3 = BitVec.ofNat 64 (bnb s₀) := by simp [bnb]
  rw [keysCommon, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => hp.key_in (by omega)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) := by
    rw [g, g, Proof.Aes.AArch64.shl4]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, f₁.rd, f₁.wr⟩
  · simp only [State.setV, State.write, (kreg_ne j).2, ite_false]
    rw [e₁ j hj]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx3]
    exact ushr3 (by omega)
  · simp only [State.setV, State.write, h1, h2, h3, h4, ite_false, g]
  · exact f₁.mem

/-- What a key setup leaves. -/
structure KPost (K : Nat → List Byte → State → Prop) (s₀ s : State) : Prop where
  keys : K (bnr s₀) (bsch s₀) s
  x13 : s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x13 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem encSetup_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block encSetup) s₀ (KPost Keys s₀) := by
  have hR := hp.rounds
  rw [encSetup, WP.block_append_iff]
  refine WP.mono (common_ok' hp) fun s₁ c₁ => ?_
  have e9' : bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) - BitVec.ofNat 64 16 =
      bkp s₀ + BitVec.ofNat 64 (16 * (bnr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega), show 16 * bnr s₀ - 16 = 16 * (bnr s₀ - 1) by omega]
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9,
      e9', BitVec.add_zero, c₁.rd, c₁.wr]
    exact hp.key_in (by omega)), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega
  refine ⟨⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, ite_false]
    rw [c₁.kreg j (by omega)]
    exact keyIs_readW _ _ (hL j (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9, e9',
      BitVec.add_zero, c₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x6]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x7]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x13]
  · simp only [State.setV, State.write, h1, ite_false]; exact c₁.gpr r h1 h2 h3 h4
  · simp only [State.setV, State.write, c₁.mem]
  · simp only [State.setV, State.write, c₁.rd]
  · simp only [State.setV, State.write, c₁.wr]

theorem decSetup_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block decSetup) s₀ (KPost DKeys s₀) := by
  have hR := hp.rounds
  rw [decSetup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (common_ok' hp) fun s₁ c₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 208) (by decide) (by
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide), c₁.rd, c₁.wr]
    exact hp.key_in (by omega)), WP.block_nil ?_⟩
  refine WP.mono (imcs_ok _ 13 (Nat.le_refl _)) fun s₂ ⟨e₂, o₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega
  have x0 : s₁.gpr .x0 = bkp s₀ := c₁.gpr _ (by decide) (by decide) (by decide) (by decide)
  have pre : ∀ j, 1 ≤ j → j ≤ 13 → j < bnr s₀ →
      KeyIs ((s₁.setV .v29 (s₁.mem.readW (s₁.gpr .x0 + BitVec.ofNat 64 208) 128)).v (dreg j))
        (roundKey (bsch s₀) j) := by
    intro j h1 h2 h3
    by_cases h13 : j = 13
    · subst h13
      simp only [Impl.Aes.AArch64.Aese.dreg, ite_true, setV_v_self, x0, c₁.mem]
      have := keyIs_readW s₀.mem (bkp s₀) (L := 16 * (bnr s₀ + 1)) (j := 13) (hL 13 (by omega))
      simpa using this
    · simp only [Impl.Aes.AArch64.Aese.dreg, h13, ite_false]
      rw [setV_v_of_ne _ _ (kreg_ne j).1, c₁.kreg j (by omega)]
      exact keyIs_readW _ _ (hL j (by omega))
  refine ⟨⟨hR, ?_, fun j h1 h2 => ?_, ?_, ?_, ?_⟩, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · rw [o₂ _ fun j hj => (dreg_ne j hj).1.symm, setV_v_of_ne _ _ (by decide), c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · have hj13 : j ≤ 13 := by omega
    have := e₂ (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, ite_eq_left (by omega)] at this
    rw [this]
    exact keyIs_aesimc (pre j h1 hj13 h2)
  · rw [o₂ _ fun j hj => (dreg_ne j hj).2.symm, setV_v_of_ne _ _ (by decide)]
    have := c₁.kreg 0 (by omega)
    simp only [Impl.Aes.AArch64.Aese.kreg] at this
    rw [this]
    exact keyIs_readW _ _ (hL 0 (by omega))
  · rw [g₂]; simp only [State.setV]; exact c₁.x6
  · rw [g₂]; simp only [State.setV]; exact c₁.x7
  · rw [g₂]; simp only [State.setV, c₁.x13]
  · rw [g₂]; simp only [State.setV]; exact c₁.gpr r h1 h2 h3 h4
  · rw [m₂]; simp only [State.setV, c₁.mem]
  · rw [rd₂]; simp only [State.setV, c₁.rd]
  · rw [wr₂]; simp only [State.setV, c₁.wr]

end VG.Proof.AesXts.AArch64.Aes
