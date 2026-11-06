module

import VerifiedGarbage.Proof.Aes.RISCV64.Keys
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Aes.RISCV64.Encrypt
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64

/-!
# Facts the AES groups share, on RISC-V

Addresses and memory, the branch on the number of blocks left, and the
round keys and masks a group keeps, for the group loops of `vg_aes_ctr32`
(`Group.lean`) and of the block functions (`Ecb.lean`), as on x86-64
(`Proof/Aes/X86_64/Group.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## Doublewords of the data, a byte at a time or aligned -/

open VG.Impl.Words.RISCV64 (loadLE64W storeLE64W) in
/-- `loadLE64W w`: as `Bytes.loadLE64_ok`, the address a multiple of 8 when `w`. -/
theorem loadLE64W_ok {s : State} {w : Bool} {d tmp hi n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n)
    (hhn : hi ≠ n) (hdt : d ≠ tmp) (hdh : d ≠ hi) (hth : tmp ≠ hi) (ho : off + 7 < 2048)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (hal : w = true → (s.gpr n + BitVec.ofNat 64 off).toNat % 8 = 0) :
    WP isa (.block (loadLE64W w d tmp hi n off)) s fun s' =>
      s'.gpr d = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      (∀ r, r ≠ d → r ≠ tmp → r ≠ hi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases w with
  | false =>
    exact Bytes.loadLE64_ok hdn htn hhn hdt hdh hth ho (Words64.in_lo h8) (Words64.in_hi h8)
  | true =>
    exact wp_ld (by omega) rfl (hal rfl) h8 fun s' u =>
      WP.block_nil ⟨u.gpr, fun r h₁ _ _ => u.other r h₁, u.mem, u.rd, u.wr, u.sp⟩

open VG.Impl.Words.RISCV64 (loadLE64W storeLE64W) in
/-- `storeLE64W w`: as `Bytes.storeLE64_ok`, the address a multiple of 8 when `w`. -/
theorem storeLE64W_ok {s : State} {w : Bool} {v tmp hi n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (hhn : hi ≠ n) (hth : tmp ≠ hi) (ho : off + 7 < 2048)
    (h8 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8)
    (hal : w = true → (s.gpr n + BitVec.ofNat 64 off).toNat % 8 = 0) :
    WP isa (.block (storeLE64W w v tmp hi n off)) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32)).writeW
        (s.gpr n + BitVec.ofNat 64 (off + 4)) ((s.gpr v >>> 32).setWidth 32) ∧
      (∀ r, r ≠ tmp → r ≠ hi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases w with
  | false =>
    exact Bytes.storeLE64_ok htv htn hhn hth ho (Words64.in_lo h8) (Words64.in_hi h8)
  | true =>
    exact wp_sd (by omega) rfl (hal rfl) h8 fun s' u =>
      WP.block_nil ⟨by rw [u.mem, ← Offset.add_add, Words64.writeW64_split], fun r _ _ => by rw [u.gpr],
        u.rd, u.wr, u.sp⟩

/-- `x &&& 7`, the address modulo 8. -/
theorem and7 (x : BitVec 64) : x &&& BitVec.ofInt 64 7 = BitVec.ofNat 64 (x.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

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
