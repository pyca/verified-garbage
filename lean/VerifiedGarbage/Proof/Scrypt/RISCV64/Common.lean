module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.BlockMix
public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import all Init.Data.Nat.Power2.Basic

/-!
# scrypt on RISC-V: common lemmas

Untrusted: everything here is checked by Lean. The target-independent
lemmas about addresses and bytes are in `Proof/Scrypt/Memory.lean`; here are
the contracts of scryptBlockMix and scryptROMix, for both widths of their
accesses (`wide`: doublewords, which need the pointers to be multiples of 8;
otherwise bytes), and the 64-byte exclusive-or (`xor64_ok`).
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.RISCV64 in
/-- RISC-V contract for `vg_scrypt_blockmix(b = a0, r = a1, y = a2,
save = a3)` (`wide`) and `vg_scrypt_blockmix_bytes`: if `r > 0`, writes
scryptBlockMix of the `128 r` bytes at `b` to `y`. `save` (96 bytes, a
multiple of 8) is where it and Salsa20/8 save their callers' registers;
`b` and `y` must be multiples of 8 for `wide`. -/
def blockMixRISCV64 (wide : Bool) : Contract RISCV64.isa where
  pre s :=
    let r := (s.gpr .a1).toNat
    let b : Region := ⟨s.gpr .a0, r * 128⟩
    let y : Region := ⟨s.gpr .a2, r * 128⟩
    let save : Region := ⟨s.gpr .a3, 96⟩
    s.rd = [b] ∧ s.wr = [y, save] ∧
    y.Disjoint save ∧ b.Disjoint y ∧ b.Disjoint save ∧
    (s.gpr .a0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + r * 128 ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + 96 ≤ 2 ^ 64 ∧ 0 < r ∧ (s.gpr .a3).toNat % 8 = 0 ∧
    (wide = true → (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0)
  post s s' := let r := (s.gpr .a1).toNat
    bytesAt s'.mem (s.gpr .a2) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .a0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_scrypt_romix(b = a0, r = a1, v = a2, vlen = a3,
t = a4, save = a5)` (`wide`) and `vg_scrypt_romix_bytes`: if `r > 0` and
`vlen = N r` for a power of two `N`, replaces the `128 r` bytes at `b` by
their scryptROMix, with `t` (`128 r` bytes) as working space. `save` (168
bytes, a multiple of 8) is where it and the functions it calls save their
callers' registers; `b`, `v` and `t` must be multiples of 8 for `wide`. The
indices `j` of step 3 are public. -/
def roMixRISCV64 (wide : Bool) : Contract RISCV64.isa where
  pre s :=
    let r := (s.gpr .a1).toNat
    let b : Region := ⟨s.gpr .a0, r * 128⟩
    let v : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat * 128⟩
    let t : Region := ⟨s.gpr .a4, r * 128⟩
    let save : Region := ⟨s.gpr .a5, 168⟩
    s.rd = [] ∧ s.wr = [b, v, t, save] ∧
    b.Disjoint v ∧ b.Disjoint t ∧ b.Disjoint save ∧ v.Disjoint t ∧ v.Disjoint save ∧
    t.Disjoint save ∧
    (s.gpr .a0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 168 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .a3).toNat % r = 0 ∧ ((s.gpr .a3).toNat / r).isPowerOfTwo ∧
    (s.gpr .a5).toNat % 8 = 0 ∧
    (wide = true → (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a4).toNat % 8 = 0)
  post s s' := let r := (s.gpr .a1).toNat
    bytesAt s'.mem (s.gpr .a0) (128 * r) =
      roMix r ((s.gpr .a3).toNat / r) (bytesAt s.mem (s.gpr .a0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .a1).toNat ((s₁.gpr .a3).toNat / (s₁.gpr .a1).toNat)
        (bytesAt s₁.mem (s₁.gpr .a0) (128 * (s₁.gpr .a1).toNat)) =
      roMixIndices (s₂.gpr .a1).toNat ((s₂.gpr .a3).toNat / (s₂.gpr .a1).toNat)
        (bytesAt s₂.mem (s₂.gpr .a0) (128 * (s₂.gpr .a1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-- A unit of `xor64`: an 8-byte write of the XOR of two 8-byte reads, as
bytes. -/
theorem writeW_xor_byte (m m' : Mem) (d a b : Addr) :
    m.writeW d (((m' a).setWidth 64 ^^^ (m' b).setWidth 64).setWidth 8) =
      writeBytes m d (xorBytes (bytesAt m' a 1) (bytesAt m' b 1)) := by
  rw [VG.RISCV64.Bytes.xor_setWidth]
  simp only [Mem.writeW, show (8 : Nat) / 8 = 1 from rfl, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp [xorBytes, bytesAt, BitVec.extractLsb'_eq_self]

/-- The units' size is positive. -/
theorem unitB_pos (wide : Bool) : 0 < unitB wide := by cases wide <;> decide

/-- The number of units in 64 bytes. -/
abbrev units (wide : Bool) : Nat := if wide then 8 else 64

theorem units_mul (wide : Bool) : unitB wide * units wide = 64 := by cases wide <;> rfl

theorem xor64_eq (wide : Bool) (dst x src : Reg) :
    xor64 wide dst x src = (List.range (units wide)).flatMap (xorU wide dst x src) := rfl

/-- One unit `k` of `[dst] ← [x] xor [src]`: only memory, `t0` and `t1`
change, and the unit's bytes are the XOR. -/
theorem xorU_ok {wide : Bool} {dR xR sR : Reg} (hd : dR ≠ .t0 ∧ dR ≠ .t1)
    (hs : sR ≠ .t0 ∧ sR ≠ .t1) {d x y : Addr} {k : Nat}
    (hk : unitB wide * k < 2048) (s : State) (gd : s.gpr dR = d) (gx : s.gpr xR = x)
    (gy : s.gpr sR = y)
    (hal : wide = true → (x + BitVec.ofNat 64 (unitB wide * k)).toNat % 8 = 0 ∧
      (y + BitVec.ofNat 64 (unitB wide * k)).toNat % 8 = 0 ∧
      (d + BitVec.ofNat 64 (unitB wide * k)).toNat % 8 = 0)
    (hinx : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hiny : InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hout : InRegions s.wr (d + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    {rest : List Instr} {Q : State → Prop}
    (kQ : ∀ s', (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem (d + BitVec.ofNat 64 (unitB wide * k))
        (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
          (bytesAt s.mem (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xorU wide dR xR sR k ++ rest)) s Q := by
  cases wide with
  | true =>
    obtain ⟨ax, ay, ad⟩ := hal rfl
    simp only [xorU, unitW, unitB, ↓reduceIte, List.cons_append, List.nil_append] at ax ay ad hinx hiny hout kQ hk ⊢
    refine wp_ld hk (by rw [gx]) ax hinx fun s₂ u₂ => ?_
    refine wp_ld hk (by rw [u₂.other _ hs.1, gy]) ay (by rw [u₂.rd, u₂.wr]; exact hiny)
      fun s₃ u₃ => ?_
    refine wp_xor fun s₄ u₄ => ?_
    refine wp_sd hk (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, gd]) ad
      (by rw [u₄.wr, u₃.wr, u₂.wr]; exact hout) fun s₅ u₅ => ?_
    refine kQ s₅ (fun r h0 h1 => by rw [u₅.gpr, u₄.other r h0, u₃.other r h1, u₂.other r h0])
      (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr])
      (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]) ?_
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor]
  | false =>
    simp only [xorU, unitW, unitB, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append, Nat.one_mul] at hinx hiny hout kQ hk ⊢
    refine wp_lbu hk (by rw [gx]) hinx fun s₂ u₂ => ?_
    refine wp_lbu hk (by rw [u₂.other _ hs.1, gy]) (by rw [u₂.rd, u₂.wr]; exact hiny)
      fun s₃ u₃ => ?_
    refine wp_xor fun s₄ u₄ => ?_
    refine wp_sb hk (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, gd])
      (by rw [u₄.wr, u₃.wr, u₂.wr]; exact hout) fun s₅ u₅ => ?_
    refine kQ s₅ (fun r h0 h1 => by rw [u₅.gpr, u₄.other r h0, u₃.other r h1, u₂.other r h0])
      (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr])
      (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]) ?_
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem,
      writeW_xor_byte]

/-- The first `n` units of `[dst] ← [x] xor [src]`, for 64-byte blocks `d`,
`x`, `y` in memory, where `d` overlaps neither of the others. The code uses
`t0` and `t1`. -/
theorem xor64_ok {wide : Bool} {dR xR sR : Reg} (hd : dR ≠ .t0 ∧ dR ≠ .t1)
    (hx : xR ≠ .t0 ∧ xR ≠ .t1) (hs : sR ≠ .t0 ∧ sR ≠ .t1)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩)
    (hal : wide = true → x.toNat % 8 = 0 ∧ y.toNat % 8 = 0 ∧ d.toNat % 8 = 0) :
    ∀ n ≤ units wide, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < units wide,
      InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide)) →
    (∀ k < units wide,
      InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide)) →
    (∀ k < units wide, InRegions s.wr (d + BitVec.ofNat 64 (unitB wide * k)) (unitB wide)) →
    (∀ s', (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem d
        (xorBytes (bytesAt s.mem x (unitB wide * n)) (bytesAt s.mem y (unitB wide * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorU wide dR xR sR) ++ rest)) s Q := by
  have hu := unitB_pos wide
  have hum := units_mul wide
  have al : ∀ {p : Addr} {k : Nat}, (wide = true → p.toNat % 8 = 0) →
      wide = true → (p + BitVec.ofNat 64 (unitB wide * k)).toNat % 8 = 0 := by
    intro p k hp hw
    subst hw
    show (p + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0
    have := hp rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := p.isLt
    omega
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [Nat.mul_zero, bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    have hun : unitB wide * n + unitB wide ≤ 64 := by
      rw [← hum, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hn
    refine xorU_ok hd hs (k := n) (by omega) s₁ (by rw [g₁ _ hd.1 hd.2, gd])
      (by rw [g₁ _ hx.1 hx.2, gx]) (by rw [g₁ _ hs.1 hs.2, gy])
      (fun hw => ⟨al (fun h => (hal h).1) hw, al (fun h => (hal h).2.1) hw,
        al (fun h => (hal h).2.2) hw⟩)
      (by rw [rd₁, wr₁]; exact hinx n (by omega)) (by rw [rd₁, wr₁]; exact hiny n (by omega))
      (by rw [wr₁]; exact hout n (by omega))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => k s₂ (fun r h0 h1 => by rw [g₂ r h0 h1, g₁ r h0 h1])
        (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem x (unitB wide * n))
        (bytesAt s.mem y (unitB wide * n))).length = unitB wide * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (unitB wide * n), unitB wide⟩
        ⟨d, (xorBytes (bytesAt s.mem x (unitB wide * n)) (bytesAt s.mem y (unitB wide * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (unitB wide * n), unitB wide⟩
        ⟨d, (xorBytes (bytesAt s.mem x (unitB wide * n)) (bytesAt s.mem y (unitB wide * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [m₂, m₁, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (unitB wide * n))
      (unitB wide)) (bytesAt s.mem (y + BitVec.ofNat 64 (unitB wide * n)) (unitB wide)))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.RISCV64
