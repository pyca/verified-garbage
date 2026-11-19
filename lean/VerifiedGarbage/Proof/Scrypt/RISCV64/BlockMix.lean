module

public import VerifiedGarbage.Proof.Scrypt.BlockMix
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.Scrypt.RISCV64.BlockMix
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
import all Init.Data.Nat.Power2.Basic
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.BlockMix
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes

/-! ### `Scrypt.RISCV64.Common`, which this module and modules that import it used -/

section

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
    omega_arith
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [Nat.mul_zero, bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_using [hn]) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    have hun : unitB wide * n + unitB wide ≤ 64 := by
      rw [← hum, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hn
    refine xorU_ok hd hs (k := n) (by omega_using [hun]) s₁ (by rw [g₁ _ hd.1 hd.2, gd])
      (by rw [g₁ _ hx.1 hx.2, gx]) (by rw [g₁ _ hs.1 hs.2, gy])
      (fun hw => ⟨al (fun h => (hal h).1) hw, al (fun h => (hal h).2.1) hw,
        al (fun h => (hal h).2.2) hw⟩)
      (by rw [rd₁, wr₁]; exact hinx n (by omega_using [hn])) (by rw [rd₁, wr₁]; exact hiny n (by omega_using [hn]))
      (by rw [wr₁]; exact hout n (by omega_using [hn]))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => k s₂ (fun r h0 h1 => by rw [g₂ r h0 h1, g₁ r h0 h1])
        (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem x (unitB wide * n))
        (bytesAt s.mem y (unitB wide * n))).length = unitB wide * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (unitB wide * n), unitB wide⟩
        ⟨d, (xorBytes (bytesAt s.mem x (unitB wide * n)) (bytesAt s.mem y (unitB wide * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega_using [hun]) (by omega_using [hun]))).sub_right
        (Region.sub_prefix (by omega_using [hun]))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (unitB wide * n), unitB wide⟩
        ⟨d, (xorBytes (bytesAt s.mem x (unitB wide * n)) (bytesAt s.mem y (unitB wide * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega_using [hun]) (by omega_using [hun]))).sub_right
        (Region.sub_prefix (by omega_using [hun]))
    rw [m₂, m₁, bytesAt_writeBytes_sep _ _ sx (by omega_using [hun]), bytesAt_writeBytes_sep _ _ sy (by omega_using [hun])]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (unitB wide * n))
      (unitB wide)) (bytesAt s.mem (y + BitVec.ofNat 64 (unitB wide * n)) (unitB wide)))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_using [hun])
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.RISCV64

end

end

/-! ### `Scrypt.RISCV64.Salsa`, which only this module used -/

section

/-!
# The Salsa20/8 Core on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Scrypt/PPC64LE/BlockMix.lean`) and of RISC-V's ChaCha20 block
(`Proof/ChaCha20/RISCV64/Xor.lean`): the rounds on the low words of the
registers (`RI`), each line an addition, a rotation by two word shifts and
an `or`, and an XOR (`line_regs`); then the whole function (`correct`),
for both widths of its accesses (`wide`: `lw` and `sw`; otherwise the
byte-wise `loadLE32` and `storeLE32`), constant time, and `salsa_verified`
against `Proof.Scrypt.salsaRISCV64`.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.RISCV64 in
/-- RISC-V contract for `vg_salsa20_8(b = a0, save = a1)` (`wide`) and
`vg_salsa20_8_bytes`: replaces the 64 bytes at `b` by their Salsa20/8 Core.
`save` (40 bytes, a multiple of 8) is where the callee-saved registers are
saved; `b` must be a multiple of 4 for `wide`. The pointers are public; the
data is secret. -/
def salsaRISCV64 (wide : Bool) : Contract RISCV64.isa where
  pre s :=
    let b : Region := ⟨s.gpr .a0, 64⟩
    let sv : Region := ⟨s.gpr .a1, 40⟩
    s.rd = [] ∧ s.wr = [b, sv] ∧ b.Disjoint sv ∧ (s.gpr .a1).toNat % 8 = 0 ∧
      (wide = true → (s.gpr .a0).toNat % 4 = 0)
  post s s' := bytesAt s'.mem (s.gpr .a0) 64 = salsa (bytesAt s.mem (s.gpr .a0) 64)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Scrypt.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : Word := x.setWidth 32

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne {k : Nat} (hk : k < 16) :
    wreg k ≠ .t0 ∧ wreg k ≠ .t1 ∧ wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ .ra := by
  have key : ∀ k < 16, wreg k ≠ .t0 ∧ wreg k ≠ .t1 ∧ wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ .ra := by
    decide
  exact key k hk

/-- The registers that hold words, and the temporaries. -/
def Words (r : Reg) : Prop := (∃ k < 16, r = wreg k) ∨ r = .t0 ∨ r = .t1

theorem not_words {r : Reg} (h : ∀ k < 16, r ≠ wreg k) (h0 : r ≠ .t0) (h1 : r ≠ .t1) :
    ¬ Words r := by
  rintro (⟨k, hk, e⟩ | e | e)
  exacts [h k hk e, h0 e, h1 e]

theorem not_words_a0 : ¬ Words .a0 :=
  not_words (fun _ hk e => (wreg_ne hk).2.2.1 e.symm) (by decide) (by decide)
theorem not_words_a1 : ¬ Words .a1 :=
  not_words (fun _ hk e => (wreg_ne hk).2.2.2.1 e.symm) (by decide) (by decide)
theorem not_words_ra : ¬ Words .ra :=
  not_words (fun _ hk e => (wreg_ne hk).2.2.2.2 e.symm) (by decide) (by decide)

theorem saved_inj {i j : Nat} (hi : i < 5) (hj : j < 5) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 5, ∀ j < 5, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne_a1 {i : Nat} (hi : i < 5) : saved i ≠ .a1 := by
  have key : ∀ i < 5, saved i ≠ .a1 := by decide
  exact key i hi

/-- A preserved register is saved, or not a word register nor a temporary. -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) : (∃ i < 5, r = saved i) ∨ ¬ Words r := by
  have key : ∀ r ∈ preserved,
      (∃ i < 5, r = saved i) ∨ ((∀ k < 16, r ≠ wreg k) ∧ r ≠ .t0 ∧ r ≠ .t1) := by decide
  rcases key r hr with h | ⟨h, h0, h1⟩
  · exact .inl h
  · exact .inr (not_words h h0 h1)

/-! ## One line, on registers -/

/-- `a ^= R(b + c, n)`, through `t0` and `t1`, on the low words. -/
theorem line_regs {a b c : Reg} (ha0 : a ≠ .t0) (ha1 : a ≠ .t1) {n : Nat} (hn0 : 0 < n)
    (hn : n < 32) (s : State) :
    WP isa (.block [.addw .t0 b c, .shift .sll .w .t1 .t0 n, .shift .srl .w .t0 .t0 (32 - n),
        .logic .or .t0 .t0 .t1, .logic .xor a a .t0]) s fun s' =>
      lo (s'.gpr a) = lo (s.gpr a) ^^^ (lo (s.gpr b) + lo (s.gpr c)).rotateLeft n ∧
      (∀ r, r ≠ a → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' : 32 - n < 32 := by omega_using [hn0]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addw, exec_logic, exec_shift_w hn,
    exec_shift_w hn', Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, ha0, ha1, ite_false, lo32_xor, lo32_or, lo32_sext,
      show Reg.t0 ≠ Reg.t1 by decide, show Reg.t1 ≠ Reg.t0 by decide]
    rw [BitVec.or_comm, rotl_shifts _ hn]
  · simp only [RegUpd.gpr_write, h₁, h₂, h₃, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the low words of the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop := ∀ k (hk : k < 16), lo (s.gpr (wreg k)) = v[k]

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  refine WP.mono (line_regs (wreg_ne hi).1 (wreg_ne hi).2.1 (show 0 < n by omega_using [h1])
    (show n < 32 by omega_using [h2]) s) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, h.holds i hi, h.holds j hj, h.holds k hk]
    · simp only [e, ite_false]
      rw [hr _ (fun e' => e (wreg_inj hi hm' e'.symm)) (wreg_ne hm').1 (wreg_ne hm').2.1]
      exact h.holds m hm'
  · rw [hr r (fun e => hw (.inl ⟨i, hi, e⟩)) (fun e => hw (.inr (.inl e)))
      (fun e => hw (.inr (.inr e)))]
    exact h.keep r hw

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

/-- The lines of a double round in the RFC's order: each quarter-round's four
lines in turn (`lines` takes a line of each in turn). -/
def rfcLines : List (Nat × Nat × Nat × Nat) :=
  [(4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18), (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18), (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18), (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18)] ++
  [(1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18), (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18), (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18), (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

/-- The steps of a list of lines. -/
abbrev steps (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) : Vector Word 16 :=
  l.foldl (fun x (i, j, k, n) => stepN x i j k n) v

theorem doubleRound_rfc (v : Vector Word 16) : Spec.Scrypt.doubleRound v = steps rfcLines v := rfl

/-- Lines `a` and `b` touch disjoint words: neither writes a word the other
reads or writes. -/
def Indep : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Bool
  | (i, j, k, _), (i', j', k', _) =>
    decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ i' < 16 ∧ j' < 16 ∧ k' < 16 ∧
      i ≠ i' ∧ i ≠ j' ∧ i ≠ k' ∧ i' ≠ j ∧ i' ≠ k)

theorem stepN_comm {x : Vector Word 16} {i j k n i' j' k' n' : Nat}
    (h : Indep (i, j, k, n) (i', j', k', n') = true) :
    stepN (stepN x i j k n) i' j' k' n' = stepN (stepN x i' j' k' n') i j k n := by
  simp only [Indep, decide_eq_true_eq] at h
  obtain ⟨hi, hj, hk, hi', hj', hk', h1, h2, h3, h4, h5⟩ := h
  apply Vector.ext
  intro m hm
  simp only [stepN_get _ _ hi' hj' hk' _ hm, stepN_get _ _ hi hj hk _ hm, stepN_get _ _ hi hj hk _ hi',
    stepN_get _ _ hi hj hk _ hj', stepN_get _ _ hi hj hk _ hk', stepN_get _ _ hi' hj' hk' _ hi,
    stepN_get _ _ hi' hj' hk' _ hj, stepN_get _ _ hi' hj' hk' _ hk]
  have g1 : i' ≠ i := Ne.symm h1
  by_cases e : i = m
  · subst e; simp [g1, h4, h5]
  · by_cases e' : i' = m
    · subst e'; simp [e, h2, h3]
    · simp [e, e']

/-- `l` without its first `a`, if every line before it is independent of it. -/
def pull (a : Nat × Nat × Nat × Nat) : List (Nat × Nat × Nat × Nat) → Option (List (Nat × Nat × Nat × Nat))
  | [] => none
  | b :: l => if b = a then some l else if Indep b a then (pull a l).map (b :: ·) else none

/-- `l'` runs the lines of `l`, each moved only past lines independent of it. -/
def SameSteps : List (Nat × Nat × Nat × Nat) → List (Nat × Nat × Nat × Nat) → Bool
  | [], [] => true
  | a :: l', l => match pull a l with
    | some r => SameSteps l' r
    | none => false
  | [], _ :: _ => false

theorem steps_cons (a : Nat × Nat × Nat × Nat) (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) :
    steps (a :: l) v = steps l (stepN v a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  obtain ⟨i, j, k, n⟩ := a; rfl

theorem pull_ok {a : Nat × Nat × Nat × Nat} :
    ∀ {l r : List (Nat × Nat × Nat × Nat)}, pull a l = some r →
      ∀ v, steps l v = steps r (stepN v a.1 a.2.1 a.2.2.1 a.2.2.2)
  | [], _, h, _ => by simp [pull] at h
  | b :: l, r, h, v => by
    unfold pull at h
    by_cases e : b = a
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; exact steps_cons _ _ _
    · simp only [e, ite_false] at h
      by_cases hb : Indep b a = true
      · simp only [hb, ite_true] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [steps_cons, pull_ok hr', steps_cons]
        obtain ⟨i, j, k, n⟩ := b; obtain ⟨i', j', k', n'⟩ := a
        exact congrArg _ (stepN_comm hb)
      · simp only [hb, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem sameSteps_ok : ∀ {l' l : List (Nat × Nat × Nat × Nat)}, SameSteps l' l = true →
    ∀ v, steps l' v = steps l v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [SameSteps] at h
  | a :: l', l, h, v => by
    unfold SameSteps at h
    split at h
    · rename_i r hr
      rw [steps_cons, pull_ok hr, sameSteps_ok h]
    · simp at h

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v :=
  (doubleRound_rfc v).trans (sameSteps_ok (l' := lines) (l := rfcLines) (by decide) v).symm

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .a0
/-- `save`. -/
abbrev svp : Addr := s₀.gpr .a1
abbrev bR : Region := ⟨bp s₀, 64⟩
abbrev svR : Region := ⟨svp s₀, 40⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (wide : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, svR s₀]
  disj : (bR s₀).Disjoint (svR s₀)
  sv_al : (svp s₀).toNat % 8 = 0
  b_al : wide = true → (bp s₀).toNat % 4 = 0

theorem pre_of {wide : Bool} (s₀ : State) (h : (Proof.Scrypt.salsaRISCV64 wide).pre s₀) :
    Pre wide s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

/-- Word `k` of a 4-byte aligned pointer is 4-byte aligned. -/
theorem al4 {p : Addr} (h : p.toNat % 4 = 0) (k : Nat) :
    (p + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega_using [h]

/-- Doubleword `i` of an 8-byte aligned pointer is 8-byte aligned. -/
theorem al8 {p : Addr} (h : p.toNat % 8 = 0) (i : Nat) :
    (p + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega_using [h]

namespace Pre
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  simpa using hp.in_b hk []

theorem in_sav {i : Nat} (hi : i < 5) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (svp s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨svR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem out_sav {i : Nat} (hi : i < 5) : InRegions s₀.wr (svp s₀ + BitVec.ofNat 64 (8 * i)) 8 := by
  simpa using hp.in_sav hi []

end Pre

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega_using [h]) (by omega_using [hj]) (by omega_using [hk])) (by decide)

theorem readW_writeW_sav (m : Mem) (p : Addr) (v : BitVec 64) {i j : Nat} (hi : i < 5) (hj : j < 5)
    (h : i ≠ j) :
    (m.writeW (p + BitVec.ofNat 64 (8 * j)) v).readW (p + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * i)) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hi]) (by omega_using [hj])) (by decide)

/-! ## Words of `b` -/

/-- `loadWord`: the low word of `d` is the word read, and only `d` and `t1`
change. -/
theorem loadWord_ok {wide : Bool} {s : State} {d : Reg} {off : Nat} (hd0 : d ≠ .a0) (hd1 : d ≠ .t1)
    (ho : off + 3 < 2048) (ha : wide = true → (s.gpr .a0 + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (loadWord wide d off)) s fun s' =>
      lo (s'.gpr d) = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 off) 32 ∧
      (∀ r, r ≠ d → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases wide with
  | true =>
    apply WP.of_runBlock
    simp only [loadWord, ↓reduceIte]
    rw [runBlock_cons, exec_load_w (by omega_using [ho]) (ha rfl) h, runStep_some,
      runBlock_nil]
    refine ⟨_, rfl, ?_, fun r h₁ _ => RegUpd.gpr_write_of_ne _ _ h₁, rfl, rfl, rfl⟩
    dsimp only [lo]
    rw [RegUpd.gpr_write_self, lo32_ext]
  | false =>
    simp only [loadWord, Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (loadLE32_ok hd0 (by decide) hd1 ho h) fun s' e => ?_
    subst e
    refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
    · dsimp only [lo]
      rw [RegUpd.gpr_write_self, lo32_ext]
    · rw [RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]

/-- `storeWord`: the low word of `v` is written, and only `t1` changes. -/
theorem storeWord_ok {wide : Bool} {s : State} {v : Reg} {off : Nat} (hv1 : v ≠ .t1)
    (ho : off + 3 < 2048) (ha : wide = true → (s.gpr .a0 + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions s.wr (s.gpr .a0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (storeWord wide v off)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .a0 + BitVec.ofNat 64 off) (lo (s.gpr v)) ∧
      (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases wide with
  | true =>
    apply WP.of_runBlock
    simp only [storeWord, ↓reduceIte]
    rw [runBlock_cons, exec_store_w (by omega_using [ho]) (ha rfl) h, runStep_some,
      runBlock_nil]
    exact ⟨_, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
  | false =>
    simp only [storeWord, Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (storeLE32_ok (Ne.symm hv1) (by decide) ho h) fun s' e => ?_
    subst e
    exact ⟨rfl, fun r h₁ => RegUpd.gpr_write_of_ne _ _ h₁, rfl, rfl⟩

/-! ## Saving the callee-saved registers -/

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [svR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (svp s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {n : Nat} (hn : n < 5) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .a1 (8 * n)]) s (SI s₀ (n + 1)) := by
  have ha1 : s.gpr .a1 = svp s₀ := by rw [h.gpr]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_d (by omega_using [hn]) (by rw [ha1]; exact al8 hp.sv_al n)
    (by rw [h.wr, ha1]; exact hp.out_sav hn), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ ?_,
    fun i hi => ?_⟩
  · rw [ha1]; exact Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn])
  · simp only [ha1]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_sav _ _ _ (by omega_arith) hn (by omega_using [hi])]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-! ## Loading the input -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → lo (s.gpr (wreg j)) = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {n : Nat} (hn : n < 16) {s : State}
    (h : LI s₀ n s) : WP isa (.block (loadWord wide (wreg n) (4 * n))) s (LI s₀ (n + 1)) := by
  have hr0 : s.gpr .a0 = bp s₀ := h.keep _ not_words_a0
  refine WP.mono (loadWord_ok (wreg_ne hn).2.2.1 (wreg_ne hn).2.1 (by omega_using [hn])
    (fun hw => by rw [hr0]; exact al4 (hp.b_al hw) n)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_b hn _)) fun s' ⟨hd, hr, hm, hrd, hwr⟩ => ?_
  refine ⟨fun j hj hjn => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [hr _ (fun e => absurd (wreg_inj hj hn e) (by omega_using [hjn])) (wreg_ne hj).2.1]
      exact h.loaded j hj hjn
    · rw [hd, hr0, h.mem, V_get _ hj]
  · rw [hr r (fun e => hw (.inl ⟨n, hn, e⟩)) (fun e => hw (.inr (.inr e)))]
    exact h.keep r hw

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums, the
others still hold the input, and words `i … 15` of the rounds' result `R` are
still in their registers. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j] + (V s₀)[j] else (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → lo (s.gpr (wreg j)) = R[j]
  frame : Frame [bR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem finish_step {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {R : Vector Word 16} {i : Nat}
    (hi : i < 16) {s : State} (h : FI s₀ R i s) :
    WP isa (.block (finishWord wide i)) s (FI s₀ R (i + 1)) := by
  have hr0 : s.gpr .a0 = bp s₀ := h.keep _ not_words_a0
  have hne := wreg_ne hi
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * i)) 32 = (V s₀)[i] := by
    rw [h.out i hi, ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl i)]
  unfold finishWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWord_ok (d := .t0) (by decide) (by decide) (by omega_using [hi])
    (fun hw => by rw [hr0]; exact al4 (hp.b_al hw) i)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_b hi _)) fun s₁ ⟨t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [List.singleton_append]
  refine Steps.WP.cons exec_addw ?_
  have hb₁ : s₁.gpr .a0 = bp s₀ := by rw [g₁ _ (by decide) (by decide), hr0]
  have hw : lo (sext32 (lo (s₁.gpr (wreg i)) + lo (s₁.gpr .t0))) = R[i] + (V s₀)[i] := by
    dsimp only [lo] at t₁ ⊢
    rw [lo32_sext, t₁, hr0, hv, g₁ _ hne.1 hne.2.1]
    have := h.rest i hi (Nat.le_refl _)
    dsimp only [lo] at this
    rw [this]
  refine WP.mono (storeWord_ok (s := s₁.write (wreg i) _) (v := wreg i) hne.2.1 (by omega_using [hi])
    (fun hwd => by rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm hne.2.2.1), hb₁]; exact al4 (hp.b_al hwd) i)
    (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ (Ne.symm hne.2.2.1), hb₁, wr₁, h.wr]
        exact hp.out_b hi)) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have hm : s'.mem = s.mem.writeW (bp s₀ + BitVec.ofNat 64 (4 * i)) (R[i] + (V s₀)[i]) := by
    rw [m', RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ (Ne.symm hne.2.2.1), hb₁,
      RegUpd.gpr_write_self, hw, m₁]
  have g₂ : ∀ r, r ≠ wreg i → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₃, RegUpd.gpr_write_of_ne _ _ h₁, g₁ r h₂ h₃]
  have hfr : Frame [bR s₀] s₀.mem s'.mem := by
    rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  have hrd : s'.rd = s₀.rd := by rw [rd', RegUpd.rd_write, rd₁, h.rd]
  have hwr : s'.wr = s₀.wr := by rw [wr', RegUpd.wr_write, wr₁, h.wr]
  refine ⟨fun j hj => ?_, fun j hj hij => ?_, hfr, hrd, hwr, fun r hw' => ?_⟩
  · rw [hm]
    by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h,
          ite_eq_left_iff.mpr fun h => absurd (by omega_using [hji]) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji,
          ite_eq_right_iff.mpr fun h => absurd h (by omega_using [e, hji])]
  · rw [g₂ _ (fun e => absurd (wreg_inj hj hi e) (by omega_using [hij])) (wreg_ne hj).1 (wreg_ne hj).2.1]
    exact h.rest j hj (by omega_using [hij])
  · rw [g₂ r (fun e => hw' (.inl ⟨i, hi, e⟩)) (fun e => hw' (.inr (.inl e)))
      (fun e => hw' (.inr (.inr e)))]
    exact h.keep r hw'

/-! ## Restoring the callee-saved registers -/

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 5, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {wide : Bool} {s₀ sB : State} (hp : Pre wide s₀) (ha1 : sB.gpr .a1 = svp s₀)
    (hsav : ∀ i < 5, sB.mem.readW (svp s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 5) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .a1 (8 * n)]) s (RI' s₀ sB (n + 1)) := by
  have ha1' : s.gpr .a1 = svp s₀ := by
    rw [h.others _ fun i hi e => saved_ne_a1 hi e.symm, ha1]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_d (by omega_using [hn]) (by rw [ha1']; exact al8 hp.sv_al n)
    (by rw [h.rd, h.wr, ha1']; exact hp.in_sav hn _), runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ fun e => absurd (saved_inj (by omega_arith) hn e) (by omega_using [hi])]
      exact h.restored i hi
    · rw [RegUpd.gpr_write_self, ha1', h.mem, hsav i hn]
  · rw [RegUpd.gpr_write_of_ne _ _ (hr n hn)]; exact h.others r hr

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega_using [])]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj]

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {wide : Bool} {s₁ : State} (hp : Pre wide s₁) :
    WP isa (main wide) s₁ fun s' =>
      (∀ j (hj : j < 16), s'.mem.readW (bp s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [bR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega_using []), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block (load wide)) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _)
      s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂ 4) fun s₃ h₃ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun j hj => by
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j), h₃.mem, h₂.mem, V_get _ hj],
      fun j hj _ => h₃.holds j hj, by rw [h₃.mem, h₂.mem]; exact Frame.refl _ _,
      h₃.rd.trans h₂.rd, h₃.wr.trans h₂.wr, fun r hw => (h₃.keep r hw).trans (h₂.keep r hw)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => finish_step hp hi h) 16
    (Nat.le_refl _) s₃ hf₃) fun s' h =>
      ⟨fun j hj => by rw [h.out j hj, ite_eq_left_iff.mpr fun e => absurd hj e],
        h.frame, h.rd, h.wr, h.keep⟩

theorem correct {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (salsa wide) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      (Proof.Scrypt.salsaRISCV64 wide).post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 5) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 5 (Nat.le_refl _)
      s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hb : bp s₁ = bp s₀ := by simp only [bp, h₁.gpr]
  have hs : svp s₁ = svp s₀ := by simp only [svp, h₁.gpr]
  have hp₁ : Pre wide s₁ := ⟨by rw [h₁.rd, hp.rd], by rw [h₁.wr, hp.wr, bR, bR, svR, svR, hb, hs],
    by simpa only [bR, svR, hb, hs] using hp.disj, by rw [hs]; exact hp.sv_al,
    fun hw => by rw [hb]; exact hp.b_al hw⟩
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    rw [V_get _ hj, V_get _ hj, hb]
    exact h₁.frame.readW (r := bR s₀) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (by simpa using hp.disj) (by decide)
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have ha1 : s₃.gpr .a1 = svp s₀ := by rw [hk _ not_words_a1, h₁.gpr]
  have hsav : ∀ i < 5, s₃.mem.readW (svp s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf.readW (r := svR s₀) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
        (by simpa [bR, hb] using hp.disj.symm) (by decide)]
      exact h₁.saved i hi
  have hr₀ : RI' s₀ s₃ 0 s₃ :=
    ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, hrd.trans h₁.rd, hwr.trans h₁.wr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ s₃)
    (fun k s hk h => restore_step hp ha1 hsav hk h) 5 (Nat.le_refl _) s₃ hr₀) fun s' h =>
      ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | hw
    · exact h.restored i hi
    · rw [h.others r fun i hi e => ?_, hk r hw, h₁.gpr]
      have key : ∀ i < 5, ∃ k < 16, saved i = wreg k := by decide
      obtain ⟨k, hk', e'⟩ := key i hi
      exact hw (.inl ⟨k, hk', e.trans e'⟩)
  · rw [h.others _ fun i hi e => ?_, hk _ not_words_ra, h₁.gpr]
    have key : ∀ i < 5, saved i ≠ .ra := by decide
    exact key i hi e.symm
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    rw [h.mem]
    refine post_of fun j hj => ?_
    rw [← hb, hout j hj, Rs, hV]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 40⟩]

theorem salsa_ct (wide : Bool) :
    ConstantTime isa (Proof.Scrypt.salsaRISCV64 wide).pre (Proof.Scrypt.salsaRISCV64 wide).pub
      (Impl.Scrypt.RISCV64.salsa wide) := by
  have agree : ∀ s₁ s₂ : State, (Proof.Scrypt.salsaRISCV64 wide).pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ Taint.ofRegs [.a0, .a1], s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h1, h2]
  cases wide
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1])
      (fun s₁ s₂ _ _ h => agree s₁ s₂ h) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1])
      (fun s₁ s₂ _ _ h => agree s₁ s₂ h) (by taint_decide)

theorem salsa_verified (wide : Bool) :
    Verified RISCV64.target (Impl.Scrypt.RISCV64.salsa wide) (Proof.Scrypt.salsaRISCV64 wide) := by
  refine ⟨fun s hs => ?_, salsa_ct wide, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · exact ⟨satState, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, fun _ => by decide⟩

end VG.Proof.Scrypt.RISCV64

end

end

/-!
# scryptBlockMix on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Scrypt/PPC64LE/BlockMix.lean`), for both widths of the
accesses: the calls of Salsa20/8 by `WP.call` from its proof
(`salsaCall_ok`), the loop over the pairs (`Inv`), and the registers saved
in `save` (`Spill`). There is no stack frame: the return address is saved
with the callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.BlockMix

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt blk salsa blockMix)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ blockMix_eq flatMap_congr)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt
  bytesAt_add bytesAt_blocks bytesAt_congr)

/-! ## A call of Salsa20/8 -/

theorem salsa_noFrames (wide : Bool) : (Impl.Scrypt.RISCV64.salsa wide).noFrames = true := by
  cases wide <;> lit_decide

/-- A call of Salsa20/8 on the block at `a0`, saving registers at `a1`. -/
theorem salsaCall_ok (wide : Bool) {s : State} {d sv : Addr} (hd : s.gpr .a0 = d)
    (hs : s.gpr .a1 = sv) (hds : Region.Disjoint ⟨d, 64⟩ ⟨sv, 40⟩) (hsa : sv.toNat % 8 = 0)
    (hda : wide = true → d.toNat % 4 = 0) (hind : InRegions s.wr d 64) (hins : InRegions s.wr sv 40)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨d, 64⟩, ⟨sv, 40⟩] s.mem s'.mem →
      bytesAt s'.mem d 64 = salsa (bytesAt s.mem d 64) → Q s') :
    WP isa (.call (salsaName wide) (Impl.Scrypt.RISCV64.salsa wide)) s Q := by
  obtain c0 : s.callEntry.gpr .a0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  obtain c1 : s.callEntry.gpr .a1 = sv := (State.callEntry_gpr _ (by decide)).trans hs
  obtain hw : Covers [⟨d, 64⟩, ⟨sv, 40⟩] s.wr := Covers.pair (Covers.one hind) (Covers.one hins)
  refine WP.call (k := Proof.Scrypt.salsaRISCV64 wide) (salsa_verified wide).1
    (rd := []) (wr := [⟨d, 64⟩, ⟨sv, 40⟩]) ?_ ?_ hw ?_ (salsa_noFrames wide)
  · simp only [Proof.Scrypt.salsaRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hds, hsa, hda⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .a0
abbrev rr : Nat := (s₀.gpr .a1).toNat
abbrev yP : Addr := s₀.gpr .a2
abbrev sv : Addr := s₀.gpr .a3
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev svR : Region := ⟨sv s₀, 96⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- Our return address and our caller's `s5`–`s10` are saved in `save`. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sv s₀) s₀.gpr bmSaved m

/-- Where Salsa20/8 saves its caller's registers. -/
abbrev ssv : Addr := sv s₀ + BitVec.ofNat 64 56

end

/-- The callee-saved registers the code never writes. -/
def others : List Reg := [.s0, .s1, .s2, .s3, .s4, .s11]

structure Pre (wide : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, svR s₀]
  y_s : (yR s₀).Disjoint (svR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (svR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sv s₀).toNat + 96 ≤ 2 ^ 64
  pos : 0 < rr s₀
  s_al : (sv s₀).toNat % 8 = 0
  al : wide = true → (bP s₀).toNat % 8 = 0 ∧ (yP s₀).toNat % 8 = 0

theorem pre_of {wide : Bool} {s₀ : State} (h : (Proof.Scrypt.blockMixRISCV64 wide).pre s₀) :
    Pre wide s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- An offset that is a multiple of 8 of an address that is one. -/
theorem al8 {p : Addr} (hp : p.toNat % 8 = 0) {o : Nat} (ho : o % 8 = 0) :
    (p + BitVec.ofNat 64 o).toNat % 8 = 0 := Spill.al8 hp ho

section
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

/-- `y` is not the whole address space, since `save` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sv s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
  simp only [Region.Contains]
  have := (sv s₀ - yP s₀).isLt
  omega_using [hc]

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 96) :
    (svR s₀).Contains (sv s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega_using [h])

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 96) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 o, n⟩ (svR s₀) :=
  sub_off h (by omega_using [h])

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s5 : s.gpr .s5 = bB s₀ k
  s6 : s.gpr .s6 = yE s₀ k
  s7 : s.gpr .s7 = yO s₀ k
  s10 : s.gpr .s10 = sv s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (rr s₀ - k)
  s9 : s.gpr .s9 = xP s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, svR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `save`. -/
theorem b_frame {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {m : Mem}
    (hf : Frame [yR s₀, svR s₀] s₀.mem m) {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_using [ho, this])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_using [hi])

/-! ## A call of Salsa20/8 on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .t0 ∧ r ≠ .t1 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

/-- Where Salsa20/8 saves registers. -/
abbrev ssvR (s₀ : State) : Region := ⟨ssv s₀, 40⟩

theorem ssv_sub (s₀ : State) : Region.Sub (ssvR s₀) (svR s₀) := s_sub s₀ (by decide)

theorem salsaAt_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (ho8 : o % 8 = 0)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o)
    (h9 : s.gpr .s10 = sv s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ssvR s₀] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yP s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt wide dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mv fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  obtain e₁ : s₂.gpr .a0 = yP s₀ + BitVec.ofNat 64 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  obtain e₂ : s₂.gpr .a1 = ssv s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h9]
  obtain e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (pres_ne r hr).2.1, u₁.other _ (pres_ne r hr).1]
  obtain hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  obtain hw₂ : s₂.wr = [yR s₀, svR s₀] := by rw [u₂.wr, u₁.wr, hwr, hp.wr]
  obtain hin₁ : InRegions s₂.wr (yP s₀ + BitVec.ofNat 64 o) 64 := by
    rw [hw₂]; exact InRegions.of_mem (by simp) (in_y hp ho)
  obtain hin₂ : InRegions s₂.wr (ssv s₀) 40 := by
    rw [hw₂]; exact InRegions.of_mem (by simp) (in_s s₀ (by decide))
  refine salsaCall_ok wide e₁ e₂ (hp.y_s.sub_left hsub |>.sub_right (ssv_sub s₀))
    (al8 hp.s_al (by decide))
    (fun hw => by have := al8 (hp.al hw).2 ho8; omega_using [this]) hin₁ hin₂
    fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr => by rw [hcs r hr, e₃ r hr])
      (by rw [u₂.mem, u₁.mem] at hf; exact hf) (by rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint (ssvR s₀) :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (ssv_sub s₀)

/-- Where `X` is. -/
theorem xP_in {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, svR s₀]) :
    ∀ i < units wide, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (unitB wide * i))
      (unitB wide) := by
  intro i hi
  obtain hu := units_mul wide
  obtain hle : unitB wide * i + unitB wide ≤ 64 := by
    rw [← hu, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega_using [hle, hk]))
  | succ j =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_y hp (by omega_using [hle, hk]))

theorem xP_disj {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀) :
    Region.Disjoint (slot s₀ (64 * k)) ⟨xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact yb_disj hp (by omega_using [hk]) (by have := hp.pos; omega_using [hk])
  | succ j => exact y_disj hp (by omega_using [hk]) (by omega_using [hk]) (by omega_using [hk]) (by omega_using []) (by omega_using [])

theorem xP_al {wide : Bool} {s₀ : State} (hp : Pre wide s₀) (hw : wide = true) (k : Nat) :
    (xP s₀ k).toNat % 8 = 0 := by
  cases k with
  | zero =>
    simp only [xP]
    exact al8 (hp.al hw).1 (by omega_using [])
  | succ j =>
    simp only [xP]
    exact al8 (hp.al hw).2 (by omega_using [])

/-- What a call keeps: our caller's saved registers. -/
theorem saved_keep {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {m m' : Mem} (hf : Frame [slot s₀ o, ssvR s₀] m m') (h : Saved s₀ m) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  obtain hp8 : p.2 + 8 ≤ 56 := by revert p; decide
  obtain hsub : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (svR s₀) := s_sub s₀ (by omega_using [hp8])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · exact disj_off (sv s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 56) (n₂ := 40) (by omega_using [hp8]) (by omega_using [hp8])
      (by omega_using []) (by omega_using [hp8]) (by omega_using [])

/-- What a call keeps: the other blocks of `y`. -/
theorem slot_keep {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ssvR s₀] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_using [])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho (by omega_using []) (by omega_using [])
  · exact slot_s hp ho'

theorem frame_big {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {m m' : Mem} (hf : Frame [slot s₀ o, ssvR s₀] m m') : Frame [yR s₀, svR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨svR s₀, List.mem_cons_of_mem _ List.mem_cons_self, ssv_sub s₀⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {dR xR sR : Reg}
    (hd : dR ≠ .t0 ∧ dR ≠ .t1) (hx : xR ≠ .t0 ∧ xR ≠ .t1) (hs : sR ≠ .t0 ∧ sR ≠ .t1)
    {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (ho8 : o % 8 = 0)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) (hob8 : ob % 8 = 0) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, svR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 64 ob) (h9 : s.gpr .s10 = sv s₀)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x, 64⟩) (hxa : wide = true → x.toNat % 8 = 0)
    (hinx : ∀ i < units wide,
      InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (unitB wide * i)) (unitB wide))
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ssvR s₀] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 wide dR xR sR)) s fun s' => WP isa (.seq (salsaAt wide dR) P) s' Q := by
  obtain lt := r_lt hp
  obtain hu := units_mul wide
  obtain hle : ∀ i < units wide, unitB wide * i + unitB wide ≤ 64 := fun i hi => by
    rw [← hu, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [← List.append_nil (xor64 wide dR xR sR), xor64_eq]
  refine xor64_ok hd hx hs hdx (yb_disj hp ho hob)
    (fun hw => ⟨hxa hw, al8 (hp.al hw).1 hob8, al8 (hp.al hw).2 ho8⟩) (units wide)
    (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]
      exact InRegions.of_mem (by simp) (in_b hp (by have := hle i hi; omega_using [hob, this])))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by have := hle i hi; omega_using [ho, this])))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  rw [hu] at m₁
  obtain l1 : (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)).length
      = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  obtain f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  obtain hw := bytesAt_writeBytes_self s.mem (yP s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega_using [])
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hp ho ho8 (by rw [g₁ _ hd.1 hd.2, gd])
    (by rw [g₁ _ (by decide) (by decide), h9]) (by rw [wr₁, hwr, hp.wr])
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (pres_ne r hr).2.2.1 (pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s5 : s.gpr .s5 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  s6 : s.gpr .s6 = yE s₀ k
  s7 : s.gpr .s7 = yO s₀ k
  s10 : s.gpr .s10 = sv s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, svR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀)
    {s s₂ s₅ : State} (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ssvR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ssvR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, svR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  obtain lt := r_lt hp
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  obtain F₂ := h.frame.trans (frame_big hp oE f₂)
  obtain yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_using [hk] : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_using [], ← blk_B s₀ (by omega_using [hk]), yAt_eq]
  obtain hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_using [hk])]
    exact b_frame hp F₂ (by omega_using [hk])
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_using [hk]) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_using [hi, hik]
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_using [hk, hi]) (by omega_using [hk, hi]) f₅, slot_keep hp oE (by omega_using [hk, hi]) (by omega_using [hik]) f₂, d₁]
    · rw [slot_keep hp oO (by omega_using [hk, hi]) (by omega_using [hik]) f₅, slot_keep hp oE (by omega_using [hk, hi]) (by omega_using [hk]) f₂, d₂]

theorem others_pres : ∀ r ∈ others, r ∈ preserved ∧ r ≠ .s5 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 wide .s6 .s9 .s5)) <| .seq (salsaAt wide .s6) <|
      .seq (.block (.addi .s5 .s5 64 :: xor64 wide .s7 .s6 .s5)) <| .seq (salsaAt wide .s7) P)
      s Q := by
  obtain lt := r_lt hp
  obtain hrd : s.rd = [bR s₀] := by rw [h.rd, hp.rd]
  obtain hwr : s.wr = [yR s₀, svR s₀] := by rw [h.wr, hp.wr]
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  refine WP.seq (half_ok hp (by decide) (by decide) (by decide) oE (by omega_using []) (ob := 128 * k)
    (by omega_using [hk]) (by omega_using []) hrd hwr h.s6 h.s9 h.s5 h.s10 (xP_disj hp hk)
    (fun hw => xP_al hp hw k) (xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₃ u₃ => ?_)
  obtain k3 : ∀ r, r ≠ .s5 → r ∈ preserved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  obtain e3 : s₃.gpr .s5 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide), h.s5, add_ofNat, show 128 * k + 64 = 64 * (2 * k + 1) by omega_using []]
  obtain hrd₃ : s₃.rd = [bR s₀] := by rw [u₃.rd, rd₂, hrd]
  obtain hwr₃ : s₃.wr = [yR s₀, svR s₀] := by rw [u₃.wr, wr₂, hwr]
  obtain e5 : s₃.gpr .s6 = yE s₀ k := by rw [k3 _ (by decide) (by decide), h.s6]
  obtain hu := units_mul wide
  refine half_ok hp (by decide) (by decide) (by decide) oO (by omega_using []) (ob := 64 * (2 * k + 1))
    (by omega_using [hk]) (by omega_using []) hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide), h.s7]) e5 e3
    (by rw [k3 _ (by decide) (by decide), h.s10])
    (y_disj hp (by omega_using [hk]) oO oE (by omega_using []) (by omega_using []))
    (fun hw => al8 (hp.al hw).2 (by omega_using []))
    (fun i hi => by
      obtain hle : unitB wide * i + unitB wide ≤ 64 := by
        rw [← hu, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
      rw [hrd₃, hwr₃, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega_using [hk, hle])))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  obtain k5 : ∀ r, r ≠ .s5 → r ∈ preserved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide), e3],
    by rw [k5 _ (by decide) (by decide), h.s6],
    by rw [k5 _ (by decide) (by decide), h.s7],
    by rw [k5 _ (by decide) (by decide), h.s10],
    by rw [k5 _ (by decide) (by decide), h.s8],
    fun r hr => by
      rw [k5 r (others_pres r hr).2 (others_pres r hr).1, h.keep r hr],
    F, S, D⟩

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64 := by omega) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} {wide : Bool} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀)
    {s : State} (h : Mid s₀ k s) :
    WP isa (.block [mov .s9 .s7, .addi .s5 .s5 64, .addi .s6 .s6 64,
      .addi .s7 .s7 64, .addi .s8 .s8 (-1)]) s (Inv s₀ (k + 1)) := by
  obtain lt := r_lt hp
  refine wp_mv fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ =>
    wp_addi (by decide) fun s₉ u₉ => wp_subi (imm := 1) (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  obtain g : ∀ r, r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s.gpr r :=
    fun r h4 h5 h6 h7 h8 => by
      rw [u₁₀.other _ h7, u₉.other _ h6, u₈.other _ h5, u₇.other _ h4, u₆.other _ h8]
  refine ⟨(by omega_using [hk]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.s5, add_ofNat, show 64 * (2 * k + 1) + 64 = 128 * (k + 1) by omega_using []]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.s6, add_ofNat, show 64 * k + 64 = 64 * (k + 1) by omega_using []]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.s7, add_ofNat,
      show 64 * (rr s₀ + k) + 64 = 64 * (rr s₀ + (k + 1)) by omega_using []]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.s10]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.s8, sub_ofNat' (by omega_using [hk])]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.s7]
    rfl
  · intro r hr
    have : r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .s8 ∧ r ≠ .s9 := by
      revert r; decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega_using [])).2]
    rfl

theorem body_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) : WP isa (bmBody wide) s (Inv s₀ (k + 1)) :=
  halves_ok hp hk h fun _ hm => regs_ok hp hk hm

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [svR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .a3 bmSaved ++
    ([mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .s9 .a0 .t1, .addi .s9 .s9 (-64)] : List Instr) := rfl

theorem save_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .a3 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok hp.s_al (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega_using [h], BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .s9 .a0 .t1, .addi .s9 .s9 (-64)]) s₁ (Inv s₀ 0) := by
  obtain lt : 128 * (s₀.gpr .a1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mv fun a ua => wp_mv fun b ub => wp_mv fun c uc => wp_mv fun d ud =>
    wp_sll (by decide) fun e ue => wp_add fun f uf => wp_sll (by decide) fun g' ug =>
    wp_add fun h uh => wp_subi (imm := 64) (by decide) fun i ui => WP.block_nil ?_
  obtain r1 : d.gpr .a1 = s₀.gpr .a1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  obtain e1 : e.gpr .t1 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, r1, shl_eq (by simp; omega_using [lt]), Nat.mul_comm]
  obtain g1 : g'.gpr .t1 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), r1, shl_eq (by simp; omega_using [lt]),
      Nat.mul_comm]
  obtain hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  obtain k : ∀ r, r ≠ .t1 → r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s10 → r ≠ .s8 → r ≠ .s9 →
      i.gpr r = s₀.gpr r := fun r h1 h4 h5 h6 h9 h7 h8 => by
    rw [ui.other _ h8, uh.other _ h8, ug.other _ h1, uf.other _ h6, ue.other _ h1,
      ud.other _ h9, uc.other _ h5, ub.other _ h4, ua.other _ h7, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => absurd hi (by omega_using []), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e1,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g1, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega_using [pos])]
    rfl
  · intro r hr
    have : r ≠ .t1 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .s10 ∧ r ≠ .s8 ∧ r ≠ .s9 := by
      revert r; decide
    obtain ⟨h1, h4, h5, h6, h9, h7, h8⟩ := this
    exact k r h1 h4 h5 h6 h9 h7 h8
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_using [pos]), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_using []]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega_using [pos]))

/-! ## The loop -/

theorem loop_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody wide) (.nonzero .s8)) s (Inv s₀ (rr s₀)) := by
  obtain lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' hi' => ?_
  obtain hz : isa.eval (.nonzero .s8) s' = some (decide (rr s₀ - (k + 1) ≠ 0)) :=
    eval_nonzero_ofNat s' .s8 (by omega_using [lt]) hi'.s8
  by_cases hl : rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = rr s₀ by omega_using [hk, hl]] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], rr s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hl], hi'⟩

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ∈ bmSaved.map Prod.fst ∨ r ∈ others := by
  decide

theorem restore_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra :=
  WP.mono (Spill.restore_wp (b := .s10) hp.s_al h.s10 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, h'.sp, fun r hr =>
      h'.gpr_of ((preserved_cases r hr).imp id (h.keep r)), h'.gpr_of (.inl (by decide))⟩

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_using [], bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correct {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (Impl.Scrypt.RISCV64.blockMix wide) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ s'.gpr .ra = s₀.gpr .ra ∧
      bytesAt s'.mem (yP s₀) (128 * rr s₀) = Spec.Scrypt.blockMix (rr s₀) (B s₀) := by
  unfold Impl.Scrypt.RISCV64.blockMix
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hsp hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hsp hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg', hra⟩ =>
    ⟨hg', hsp'.trans h₃.sp, hra, ?_⟩
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

theorem blockMix_correct {wide : Bool} (s : State) (hs : (Proof.Scrypt.blockMixRISCV64 wide).pre s) :
    ∃ t s', Exec isa (Impl.Scrypt.RISCV64.blockMix wide) s t s' ∧ abiPreserved s s' ∧
      (Proof.Scrypt.blockMixRISCV64 wide).post s s' := by
  obtain ⟨t, s', he, hk, hsp, hra, hpost⟩ := correct (pre_of hs)
  exact ⟨t, s', he, ⟨hk, hsp, hra⟩, hpost⟩

theorem agree₀ {wide : Bool} {s₁ s₂ : State} (hpub : (Proof.Scrypt.blockMixRISCV64 wide).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem blockMix_ct (wide : Bool) : ConstantTime isa (Proof.Scrypt.blockMixRISCV64 wide).pre
    (Proof.Scrypt.blockMixRISCV64 wide).pub (Impl.Scrypt.RISCV64.blockMix wide) := by
  cases wide
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data). -/
def bmSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 96⟩]

theorem blockMix_verified (wide : Bool) :
    Verified RISCV64.target (Impl.Scrypt.RISCV64.blockMix wide)
      (Proof.Scrypt.blockMixRISCV64 wide) :=
  ⟨blockMix_correct, blockMix_ct wide, ⟨bmSat, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide,
    by decide, by decide, by decide, fun _ => by decide⟩⟩

end VG.Proof.Scrypt.RISCV64.BlockMix
