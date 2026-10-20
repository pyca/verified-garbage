module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Short
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ChaCha20-Poly1305 on AArch64, 64 to 256 bytes: the kernel's output zeroed

`Short.zero` zeroes `ctx[64, 384)`, where the five-block kernel then XORs
its keystream.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Short

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Short

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off < 4096 * 16 by omega, ho, and_self, ite_true, Option.bind_some,
    State.store, h]

theorem off_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := off_off p a b

/-- `ctx[64, 64 + 16 j)` is zero, and `m` is `m₀` elsewhere. -/
def Zeroed (c : Addr) (j : Nat) (m₀ m : Mem) : Prop :=
  ∀ x, m x = if 64 ≤ (x - c).toNat ∧ (x - c).toNat < 64 + 16 * j then 0 else m₀ x

/-- What a store keeps. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : s'.v = s.v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Same.trans {s₁ s₂ s₃ : State} (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) : Same s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.v.trans h₁.v, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem zeroStores_step (j : Nat) :
    (List.range (j + 1)).map (fun i => Instr.strq .v0 .x21 (64 + 16 * i)) =
      (List.range j).map (fun i => Instr.strq .v0 .x21 (64 + 16 * i)) ++
        ([.strq .v0 .x21 (64 + 16 * j)] : List Instr) := by
  simp [List.range_succ]

/-- The first `j` stores of zeros. -/
theorem zeroStores_ok {c : Addr} {j : Nat} (hj : j ≤ 20) {s : State} (hx21 : s.gpr .x21 = c)
    (hv : s.v .v0 = 0) (hw : ∀ a, a + 16 ≤ 320 → InRegions s.wr (c + BitVec.ofNat 64 (64 + a)) 16) :
    WP isa (.block ((List.range j).map fun i => .strq .v0 .x21 (64 + 16 * i))) s fun s' =>
      Same s s' ∧ Zeroed c j s.mem s'.mem := by
  induction j with
  | zero =>
    refine WP.block_nil (M := isa) ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun x => ?_⟩
    rw [ite_eq_right_iff.mpr fun h => absurd h.2 (by omega)]
  | succ j ih =>
    rw [zeroStores_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, z₁⟩ => ?_)
    have ho : InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 (64 + 16 * j)) 16 := by
      rw [g₁.wr, g₁.gpr, hx21]; exact hw (16 * j) (by omega)
    refine WP.block_cons_iff.mpr ⟨_, exec_strq (by omega) ho, WP.block_nil ⟨⟨g₁.gpr, g₁.v, g₁.rd, g₁.wr,
      g₁.sp⟩, fun x => ?_⟩⟩
    show (if (x - (s₁.gpr .x21 + BitVec.ofNat 64 (64 + 16 * j))).toNat < 16 then
      (s₁.v .v0).extractLsb' (8 * (x - (s₁.gpr .x21 + BitVec.ofNat 64 (64 + 16 * j))).toNat) 8
      else s₁.mem x) = _
    rw [g₁.gpr, hx21, g₁.v, hv]
    by_cases h : (x - (c + BitVec.ofNat 64 (64 + 16 * j))).toNat < 16
    · have h' := (Offset.lt_iff x c (by omega)).mp h
      have h2 : 64 ≤ (x - c).toNat ∧ (x - c).toNat < 64 + 16 * (j + 1) := by omega
      simp only [h, h2, ite_true]
      ext i hi
      simp
    · have h' := mt (Offset.lt_iff x c (d := 64 + 16 * j) (n := 16) (by omega)).mpr h
      simp only [h, ite_false]
      rw [z₁ x]
      by_cases h'' : 64 ≤ (x - c).toNat ∧ (x - c).toNat < 64 + 16 * j
      · have h2 : 64 ≤ (x - c).toNat ∧ (x - c).toNat < 64 + 16 * (j + 1) := by omega
        simp only [h'', h2]
      · have h2 : ¬(64 ≤ (x - c).toNat ∧ (x - c).toNat < 64 + 16 * (j + 1)) := by omega
        simp only [h'', h2, ite_false]

/-- `Short.zero`: `ctx[64, 384)` zeroed. -/
theorem zero_ok {c : Addr} {s : State} (hx21 : s.gpr .x21 = c)
    (hw : ∀ a, a + 16 ≤ 320 → InRegions s.wr (c + BitVec.ofNat 64 (64 + a)) 16) :
    WP isa (.block zero) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .v0 → s'.v r = s.v r) ∧ Zeroed c 20 s.mem s'.mem := by
  unfold zero
  refine WP.block_cons_iff.mpr ⟨s.setV .v0 (s.v .v0 ^^^ s.v .v0), rfl, ?_⟩
  have hv : (s.setV .v0 (s.v .v0 ^^^ s.v .v0)).v .v0 = 0 := by
    rw [RegUpd.v_setV_self, BitVec.xor_self]; rfl
  refine WP.mono (zeroStores_ok (j := 20) (Nat.le_refl _) (by rw [RegUpd.gpr_setV]; exact hx21) hv
    (by rw [RegUpd.wr_setV]; exact hw)) fun s' ⟨g, z⟩ => ⟨by rw [g.gpr, RegUpd.gpr_setV],
      by rw [g.rd, RegUpd.rd_setV], by rw [g.wr, RegUpd.wr_setV], by rw [g.sp, RegUpd.sp_setV],
      fun r hr => by rw [g.v, RegUpd.v_setV_of_ne (s := s) _ hr], z⟩

/-- A zeroed region's bytes. -/
theorem Zeroed.byte {c : Addr} {m₀ m : Mem} (h : Zeroed c 20 m₀ m) {k : Nat} (hk : k < 320) :
    m (c + BitVec.ofNat 64 (64 + k)) = 0 := by
  have h2 : 64 ≤ 64 + k ∧ 64 + k < 64 + 16 * 20 := by omega
  rw [h, Mem.sub_ofNat_toNat c (by omega)]
  simp only [h2, and_self, ite_true]

/-- A zeroed region's frame. -/
theorem Zeroed.frame {c : Addr} {m₀ m : Mem} (h : Zeroed c 20 m₀ m) :
    Frame [⟨c + BitVec.ofNat 64 64, 320⟩] m₀ m := by
  intro x hx
  have hx' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hx'
  rw [h x]
  refine ite_eq_right_iff.mpr fun ⟨h₁, h₂⟩ => absurd ?_ hx'
  rw [Offset.toNat_sub_add x c (by omega),
    show 2 ^ 64 - 64 + (x - c).toNat = (x - c).toNat - 64 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

end VG.Proof.ChaCha20Poly1305.AArch64.Short
