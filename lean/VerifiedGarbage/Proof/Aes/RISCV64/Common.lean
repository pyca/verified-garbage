module

import VerifiedGarbage.Proof.Aes.RISCV64.Keys
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Aes.RISCV64.Encrypt
public import VerifiedGarbage.Proof.Framework.RISCV64.Align

/-!
# Facts the AES groups share, on RISC-V

Addresses and memory, the branch on the number of blocks left, and the
round keys and masks a group keeps, for the group loops of `vg_aes_ctr32`
(`Group.lean`) and of the block functions (`Ecb.lean`), as on PPC64LE
(`Proof/Aes/PPC64LE/Group.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega_arith)⟩

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem add_off8 (A : Addr) (x : Nat) :
    A + BitVec.ofNat 64 (x + 8) = A + BitVec.ofNat 64 x + 8 := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

theorem ofNat_sub_ofNat' {x y : Nat} (h : y ≤ x) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) := Offset.ofNat_sub_ofNat h

theorem off_add64 (D : Addr) (g : Nat) :
    D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 64 = D + BitVec.ofNat 64 (64 * (g + 1)) :=
  (Offset.add_add D _ 64).trans (by rw [show 64 * g + 64 = 64 * (g + 1) by omega_arith])

theorem ofNat_shr2 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 2 = BitVec.ofNat 64 (a / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The branch on `t0 := a4 >>> 2`: four blocks or more left. -/
theorem shr2_wp {s : State} {k : Nat} (hk : k < 2 ^ 64) (h7 : s.gpr .a4 = BitVec.ofNat 64 k)
    {c : Prog isa} {P : State → Prop}
    (h : ∀ s', Upd s s' t0 (BitVec.ofNat 64 (k / 4)) →
      isa.eval (.nonzero t0) s' = some (decide (4 ≤ k)) → WP isa c s' P) :
    WP isa (.seq (.block [shrI t0 .a4 2]) c) s P := by
  refine WP.seq (wp_srl (by decide) fun s' u => WP.block_nil ?_)
  rw [h7, ofNat_shr2 hk] at u
  refine h s' u ?_
  rw [Steps.eval_nonzero_ofNat s' t0 (by omega) u.gpr]
  congr 1; exact decide_eq_decide.mpr (by omega)

/-- `addi t0, a4, -k`, with `a4 = n`, `k ≤ n`. -/
theorem subA4_eval {s s' : State} {n k : Nat} (hk : k ≤ n)
    (h7 : s.gpr .a4 = BitVec.ofNat 64 n) (u : Upd s s' t0 (s.gpr .a4 - BitVec.ofNat 64 k)) :
    s'.gpr t0 = BitVec.ofNat 64 (n - k) := by
  rw [u.gpr, h7, ofNat_sub_ofNat' hk]

/-! ## What a group keeps -/

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region}
    (hR : R ≤ 14) (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + 1024, 960⟩ r)
    (h : KeysAt m (b + BitVec.ofNat 64 (1920 - 64 * R)) R w) :
    KeysAt m' (b + BitVec.ofNat 64 (1920 - 64 * R)) R w :=
  fun j hj => keyRel_congr (h j hj) fun k hk => hf.readW (key_contains _ hR hj hk) hd (by decide)

/-- The masks' slots: 52–57 and 64–75. -/
theorem allKs_in : ∀ p ∈ allKs, (52 ≤ p.1 ∧ p.1 < 58) ∨ (64 ≤ p.1 ∧ p.1 < 76) := by decide

/-- Memory outside both areas of masks keeps them. -/
theorem masks_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r) (h : MasksAt m b allKs) :
    MasksAt m' b allKs := by
  intro k v hk
  rw [← h k v hk]
  refine hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
  rcases allKs_in _ hk with hk' | hk'
  · exact (hd r hr).1.sub_left (Offset.sub b (by omega) (by omega))
  · exact (hd r hr).2.sub_left (Offset.sub b (by omega) (by omega))

/-- The scratch buffer's parts, at the rounded base `b = X + pad X`. -/
theorem scr_part (X : Addr) {d n : Nat} (h : d + n + 7 ≤ 2048) :
    Region.Sub ⟨X + BitVec.ofNat 64 (pad X) + BitVec.ofNat 64 d, n⟩ ⟨X, 2048⟩ := by
  rw [Offset.add_add]
  have := pad_lt X
  exact Offset.sub_base X (by omega)

theorem scr_base (X : Addr) {n : Nat} (h : n + 7 ≤ 2048) :
    Region.Sub ⟨X + BitVec.ofNat 64 (pad X), n⟩ ⟨X, 2048⟩ := by
  have := pad_lt X
  exact Offset.sub_base X (by omega)

end VG.Proof.Aes.RISCV64
