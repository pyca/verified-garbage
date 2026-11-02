module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.RoMix
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Scrypt.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset

/-!
# scryptROMix on RISC-V: the small loops

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/Scrypt/PPC64LE/RoMix.lean`), for both widths of the accesses (`u`
bytes at a time, `unitB wide`): the copy (`copyLoop`), the exclusive-or
(`xorLoop`) and the computation of `2 N` by doubling (`nLoop`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.RoMix

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat)

/-! ## Arithmetic -/

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- A pointer advanced by one unit. -/
theorem next_ptr (p : Addr) (u k : Nat) :
    p + BitVec.ofNat 64 (u * k) + BitVec.ofNat 64 u = p + BitVec.ofNat 64 (u * (k + 1)) := by
  rw [add_ofNat, Nat.mul_succ]

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - BitVec.ofNat 64 1 =
    BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel, BitVec.add_sub_cancel]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [ofNat_pred (by omega), Nat.sub_sub]

theorem dec_ne {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1)) != 0) = decide (k + 1 ≠ n) := by
  rw [bne, ofNat_beq_zero (by omega)]
  by_cases h : k + 1 = n
  · simp only [h, Nat.sub_self, decide_true, Bool.not_true, ne_eq, not_true_eq_false, decide_false]
  · simp only [show n - (k + 1) ≠ 0 by omega, decide_false, Bool.not_false, ne_eq, h,
      not_false_eq_true, decide_true]

theorem ofNat_zero_add (p : Addr) (u : Nat) : p + BitVec.ofNat 64 (u * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    omega

/-- A unit of a pointer that is a multiple of 8 is one, for `wide`. -/
theorem unit_al {wide : Bool} {p : Addr} (hp : wide = true → p.toNat % 8 = 0) (hw : wide = true)
    (k : Nat) : (p + BitVec.ofNat 64 (unitB wide * k)).toNat % 8 = 0 := by
  subst hw
  exact Spill.al8 (hp rfl) (by show 8 * k % 8 = 0; omega)

/-- A byte, as the 8-bit word at its address. -/
theorem byte_readW (m : Mem) (a : Addr) : (((m a).setWidth 64).setWidth 8 : BitVec 8) = m.readW a 8 := by
  show _ = ((0#0 : BitVec 0) ++ m a).setWidth 8
  rw [BitVec.zero_width_append]
  simp

/-! ## Counted loops -/

/-- A do-while loop on `bnez cr` that runs its body `n > 0` times: the
register is zero exactly after the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr cr != 0) = decide (k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero cr) s' = some (decide (k + 1 ≠ n)) := by
    rw [eval_nonzero, hc]
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- The body of `copyLoop`. -/
def copyBody (wide : Bool) : List Instr :=
  [.load (unitW wide) .t3 .t0 0, .store (unitW wide) .t3 .t1 0, .addi .t0 .t0 (unitB wide),
    .addi .t1 .t1 (unitB wide), .addi .t2 .t2 (-1)]

theorem copyLoop_eq (wide : Bool) : copyLoop wide = .loop (.block (copyBody wide)) (.nonzero .t2) := by
  cases wide <;> rfl

/-- After `k` units of `copyLoop`. -/
structure CopyInv (wide : Bool) (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → t.gpr r = s.gpr r
  t0 : t.gpr .t0 = src + BitVec.ofNat 64 (unitB wide * k)
  t1 : t.gpr .t1 = dst + BitVec.ofNat 64 (unitB wide * k)
  t2 : t.gpr .t2 = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (unitB wide * k))

theorem copy_step {wide : Bool} {s : State} {src dst : Addr} {n : Nat}
    (hlt : unitB wide * n < 2 ^ 64)
    (hal : wide = true → src.toNat % 8 = 0 ∧ dst.toNat % 8 = 0)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hsep : Region.Disjoint ⟨src, unitB wide * n⟩ ⟨dst, unitB wide * n⟩) {k : Nat} (hk : k < n)
    {t : State} (h : CopyInv wide s src dst n k t) :
    WP isa (.block (copyBody wide)) t
      fun t' => CopyInv wide s src dst n (k + 1) t' ∧ (t'.gpr .t2 != 0) = decide (k + 1 ≠ n) := by
  have hu := unitB_pos wide
  have hle : unitB wide * k + unitB wide ≤ unitB wide * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
  have hn64 : n < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left n hu) hlt
  have hsep' : Mem.Sep src (unitB wide * k + unitB wide) dst (unitB wide * k + unitB wide) :=
    hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  have hlt' : unitB wide * k + unitB wide < 2 ^ 64 := by omega
  -- The two accesses, then the same additions.
  suffices key : WP isa (.block (copyBody wide)) t fun t' =>
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → t'.gpr r = t.gpr r) ∧
      t'.gpr .t0 = t.gpr .t0 + BitVec.ofNat 64 (unitB wide) ∧
      t'.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 (unitB wide) ∧
      t'.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
      t'.mem = t.mem.writeW (dst + BitVec.ofNat 64 (unitB wide * k))
        (t.mem.readW (src + BitVec.ofNat 64 (unitB wide * k)) (8 * unitB wide)) by
    refine WP.mono key fun t' ⟨rd', wr', sp', o', e0, e1, e2, m'⟩ => ?_
    have e2' : t'.gpr .t2 = BitVec.ofNat 64 (n - (k + 1)) := by rw [e2, h.t2, dec_count hk]
    refine ⟨⟨by rw [rd', h.rd], by rw [wr', h.wr], by rw [sp', h.sp],
      fun r a b c d => by rw [o' r a b c d, h.other r a b c d],
      by rw [e0, h.t0, next_ptr], by rw [e1, h.t1, next_ptr], e2', ?_⟩, ?_⟩
    · rw [m', h.mem, Nat.mul_succ]
      exact Proof.Scrypt.Memory.copy_mem s.mem src dst k (unitB wide) hsep' hlt'
    · rw [e2', dec_ne hk hn64]
  have hi := hin k hk
  have ho := hout k hk
  have g0 := h.t0
  have g1 := h.t1
  have grd := h.rd
  have gwr := h.wr
  clear hin hout hsep hsep' hlt' hle
  cases wide with
  | true =>
    have ha := hal rfl
    simp only [copyBody, unitW, unitB, ↓reduceIte] at hi ho g0 g1 ⊢
    refine wp_ld (a := src + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [g0, add_zero'])
      (unit_al (wide := true) (fun _ => ha.1) rfl k) (by rw [grd, gwr]; exact hi) fun t₁ u₁ => ?_
    refine wp_sd (a := dst + BitVec.ofNat 64 (8 * k)) (by decide)
      (by rw [u₁.other _ (by decide), g1, add_zero']) (unit_al (wide := true) (fun _ => ha.2) rfl k)
      (by rw [u₁.wr, gwr]; exact ho) fun t₂ u₂ => ?_
    refine wp_addi (by decide) fun t₃ u₃ => wp_addi (by decide) fun t₄ u₄ =>
      wp_subi (imm := 1) (by decide) fun t₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .t3 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
    refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], fun r a b c d => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other r c, u₄.other r b, u₃.other r a, g r d]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide)]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide)]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide)]
    · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
      rfl
  | false =>
    simp only [copyBody, unitW, unitB, Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at hi ho g0 g1 ⊢
    refine wp_lbu (a := src + BitVec.ofNat 64 k) (by decide) (by rw [g0, add_zero'])
      (by rw [grd, gwr]; exact hi) fun t₁ u₁ => ?_
    refine wp_sb (a := dst + BitVec.ofNat 64 k) (by decide)
      (by rw [u₁.other _ (by decide), g1, add_zero'])
      (by rw [u₁.wr, gwr]; exact ho) fun t₂ u₂ => ?_
    refine wp_addi (by decide) fun t₃ u₃ => wp_addi (by decide) fun t₄ u₄ =>
      wp_subi (imm := 1) (by decide) fun t₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .t3 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
    refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], fun r a b c d => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other r c, u₄.other r b, u₃.other r a, g r d]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide)]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide)]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide)]
    · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, byte_readW]
      rfl

/-- `copyLoop` copies `u n` bytes from `t0` to `t1` (`t2 = n > 0` units). -/
theorem copyLoop_ok {wide : Bool} {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n)
    (hlt : unitB wide * n < 2 ^ 64) (hal : wide = true → src.toNat % 8 = 0 ∧ dst.toNat % 8 = 0)
    (h0 : s.gpr .t0 = src) (h1 : s.gpr .t1 = dst) (h2 : s.gpr .t2 = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hsep : Region.Disjoint ⟨src, unitB wide * n⟩ ⟨dst, unitB wide * n⟩) :
    WP isa (copyLoop wide) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (unitB wide * n)) := by
  rw [copyLoop_eq]
  refine WP.mono (count_loop hn (CopyInv wide s src dst n)
    (fun k hk t h => copy_step hlt hal hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add, h0], by rw [ofNat_zero_add, h1],
    by rw [h2, Nat.sub_zero], by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- The body of `xorLoop`. -/
def xorBody (wide : Bool) : List Instr :=
  [.load (unitW wide) .t4 .t0 0, .load (unitW wide) .t5 .t1 0,
    .logic .xor .t4 .t4 .t5, .store (unitW wide) .t4 .t2 0, .addi .t0 .t0 (unitB wide),
    .addi .t1 .t1 (unitB wide), .addi .t2 .t2 (unitB wide), .addi .t3 .t3 (-1)]

theorem xorLoop_eq (wide : Bool) : xorLoop wide = .loop (.block (xorBody wide)) (.nonzero .t3) := rfl

/-- After `k` units of `xorLoop`. -/
structure XorInv (wide : Bool) (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → t.gpr r = s.gpr r
  t0 : t.gpr .t0 = x + BitVec.ofNat 64 (unitB wide * k)
  t1 : t.gpr .t1 = y + BitVec.ofNat 64 (unitB wide * k)
  t2 : t.gpr .t2 = d + BitVec.ofNat 64 (unitB wide * k)
  t3 : t.gpr .t3 = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem d
    (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k)))

theorem xor_step {wide : Bool} {s : State} {x y d : Addr} {n : Nat} (hlt : unitB wide * n < 2 ^ 64)
    (hal : wide = true → x.toNat % 8 = 0 ∧ y.toNat % 8 = 0 ∧ d.toNat % 8 = 0)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hdx : Region.Disjoint ⟨d, unitB wide * n⟩ ⟨x, unitB wide * n⟩)
    (hdy : Region.Disjoint ⟨d, unitB wide * n⟩ ⟨y, unitB wide * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv wide s x y d n k t) :
    WP isa (.block (xorBody wide)) t
      fun t' => XorInv wide s x y d n (k + 1) t' ∧ (t'.gpr .t3 != 0) = decide (k + 1 ≠ n) := by
  have hu := unitB_pos wide
  have hle : unitB wide * k + unitB wide ≤ unitB wide * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
  have hn64 : n < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left n hu) hlt
  have hl : (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k))).length =
      unitB wide * k := by
    rw [Proof.Scrypt.Memory.xorBytes_length _ _ (by simp [bytesAt]), Proof.Scrypt.Memory.bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (unitB wide * k), unitB wide⟩
      ⟨d, (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (Proof.Scrypt.Memory.sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (unitB wide * k), unitB wide⟩
      ⟨d, (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (Proof.Scrypt.Memory.sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  -- The memory after one more unit, from the unit written.
  have mem_next : ∀ m', m' = writeBytes (writeBytes s.mem d
        (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k))))
        (d + BitVec.ofNat 64 (unitB wide * k))
        (xorBytes (bytesAt (writeBytes s.mem d
            (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k))))
            (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
          (bytesAt (writeBytes s.mem d
            (xorBytes (bytesAt s.mem x (unitB wide * k)) (bytesAt s.mem y (unitB wide * k))))
            (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))) →
      m' = writeBytes s.mem d
        (xorBytes (bytesAt s.mem x (unitB wide * (k + 1))) (bytesAt s.mem y (unitB wide * (k + 1)))) := by
    intro m' hm'
    rw [hm', Proof.Scrypt.Memory.bytesAt_writeBytes_sep _ _ sx (by omega),
      Proof.Scrypt.Memory.bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (unitB wide * k))
      (unitB wide)) (bytesAt s.mem (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide)))
      (by rw [hl, Proof.Scrypt.Memory.xorBytes_length _ _ (by simp [bytesAt]),
        Proof.Scrypt.Memory.bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, Proof.Scrypt.Memory.bytesAt_add, Proof.Scrypt.Memory.bytesAt_add, xorBytes,
      xorBytes, xorBytes, List.zipWith_append (by simp [bytesAt])]
  suffices key : WP isa (.block (xorBody wide)) t fun t' =>
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → t'.gpr r = t.gpr r) ∧
      t'.gpr .t0 = t.gpr .t0 + BitVec.ofNat 64 (unitB wide) ∧
      t'.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 (unitB wide) ∧
      t'.gpr .t2 = t.gpr .t2 + BitVec.ofNat 64 (unitB wide) ∧
      t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
      t'.mem = writeBytes t.mem (d + BitVec.ofNat 64 (unitB wide * k))
        (xorBytes (bytesAt t.mem (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
          (bytesAt t.mem (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))) by
    refine WP.mono key fun t' ⟨rd', wr', sp', o', e0, e1, e2, e3, m'⟩ => ?_
    have e3' : t'.gpr .t3 = BitVec.ofNat 64 (n - (k + 1)) := by rw [e3, h.t3, dec_count hk]
    refine ⟨⟨by rw [rd', h.rd], by rw [wr', h.wr], by rw [sp', h.sp],
      fun r a b c d' e f => by rw [o' r a b c d' e f, h.other r a b c d' e f],
      by rw [e0, h.t0, next_ptr], by rw [e1, h.t1, next_ptr], by rw [e2, h.t2, next_ptr], e3',
      mem_next _ (by rw [m', h.mem])⟩, ?_⟩
    rw [e3', dec_ne hk hn64]
  have hix := hinx k hk
  have hiy := hiny k hk
  have ho := hout k hk
  have g0 := h.t0
  have g1 := h.t1
  have g2 := h.t2
  have grd := h.rd
  have gwr := h.wr
  clear mem_next sx sy hl hinx hiny hout hdx hdy hle
  cases wide with
  | true =>
    have ha := hal rfl
    simp only [xorBody, unitW, unitB, ↓reduceIte] at hix hiy ho g0 g1 g2 ⊢
    refine wp_ld (a := x + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [g0, add_zero'])
      (unit_al (wide := true) (fun _ => ha.1) rfl k) (by rw [grd, gwr]; exact hix) fun t₁ u₁ => ?_
    refine wp_ld (a := y + BitVec.ofNat 64 (8 * k)) (by decide)
      (by rw [u₁.other _ (by decide), g1, add_zero']) (unit_al (wide := true) (fun _ => ha.2.1) rfl k)
      (by rw [u₁.rd, u₁.wr, grd, gwr]; exact hiy) fun t₂ u₂ => ?_
    refine wp_xor fun t₃ u₃ => ?_
    refine wp_sd (a := d + BitVec.ofNat 64 (8 * k)) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g2, add_zero'])
      (unit_al (wide := true) (fun _ => ha.2.2) rfl k)
      (by rw [u₃.wr, u₂.wr, u₁.wr, gwr]; exact ho) fun t₄ u₄ => ?_
    refine wp_addi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ =>
      wp_addi (by decide) fun t₇ u₇ => wp_subi (imm := 1) (by decide) fun t₈ u₈ => WP.block_nil ?_
    have g : ∀ r, r ≠ .t4 → r ≠ .t5 → t₄.gpr r = t.gpr r := fun r h4 h5 => by
      rw [u₄.gpr, u₃.other r h4, u₂.other r h5, u₁.other r h4]
    refine ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
      fun r a b c d' e f => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₈.other r d', u₇.other r c, u₆.other r b, u₅.other r a, g r e f]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
        g _ (by decide) (by decide)]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
        g _ (by decide) (by decide)]
    · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        g _ (by decide) (by decide)]
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        g _ (by decide) (by decide)]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other .t4 (by decide), u₂.gpr,
        u₂.mem, u₁.gpr, u₁.mem, Proof.Scrypt.Memory.writeW_xor]
  | false =>
    simp only [xorBody, unitW, unitB, Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at hix hiy ho g0 g1 g2 ⊢
    refine wp_lbu (a := x + BitVec.ofNat 64 k) (by decide) (by rw [g0, add_zero'])
      (by rw [grd, gwr]; exact hix) fun t₁ u₁ => ?_
    refine wp_lbu (a := y + BitVec.ofNat 64 k) (by decide)
      (by rw [u₁.other _ (by decide), g1, add_zero'])
      (by rw [u₁.rd, u₁.wr, grd, gwr]; exact hiy) fun t₂ u₂ => ?_
    refine wp_xor fun t₃ u₃ => ?_
    refine wp_sb (a := d + BitVec.ofNat 64 k) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g2, add_zero'])
      (by rw [u₃.wr, u₂.wr, u₁.wr, gwr]; exact ho) fun t₄ u₄ => ?_
    refine wp_addi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ =>
      wp_addi (by decide) fun t₇ u₇ => wp_subi (imm := 1) (by decide) fun t₈ u₈ => WP.block_nil ?_
    have g : ∀ r, r ≠ .t4 → r ≠ .t5 → t₄.gpr r = t.gpr r := fun r h4 h5 => by
      rw [u₄.gpr, u₃.other r h4, u₂.other r h5, u₁.other r h4]
    refine ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
      fun r a b c d' e f => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₈.other r d', u₇.other r c, u₆.other r b, u₅.other r a, g r e f]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
        g _ (by decide) (by decide)]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
        g _ (by decide) (by decide)]
    · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        g _ (by decide) (by decide)]
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        g _ (by decide) (by decide)]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other .t4 (by decide), u₂.gpr,
        u₂.mem, u₁.gpr, u₁.mem, Proof.Scrypt.RISCV64.writeW_xor_byte]

/-- `xorLoop` writes `[t0] xor [t1]` to `t2`, `u n` bytes (`t3 = n > 0` units). -/
theorem xorLoop_ok {wide : Bool} {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n)
    (hlt : unitB wide * n < 2 ^ 64)
    (hal : wide = true → x.toNat % 8 = 0 ∧ y.toNat % 8 = 0 ∧ d.toNat % 8 = 0)
    (h0 : s.gpr .t0 = x) (h1 : s.gpr .t1 = y) (h2 : s.gpr .t2 = d)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (unitB wide * k)) (unitB wide))
    (hdx : Region.Disjoint ⟨d, unitB wide * n⟩ ⟨x, unitB wide * n⟩)
    (hdy : Region.Disjoint ⟨d, unitB wide * n⟩ ⟨y, unitB wide * n⟩) :
    WP isa (xorLoop wide) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem d
        (xorBytes (bytesAt s.mem x (unitB wide * n)) (bytesAt s.mem y (unitB wide * n))) := by
  rw [xorLoop_eq]
  refine WP.mono (count_loop hn (XorInv wide s x y d n)
    (fun k hk t h => xor_step hlt hal hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add, h0],
    by rw [ofNat_zero_add, h1], by rw [ofNat_zero_add, h2], by rw [h3, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .t0 → r' ≠ .t1 → r' ≠ .t3 → t.gpr r' = s.gpr r'
  t0 : t.gpr .t0 = BitVec.ofNat 64 (r * 2 ^ k)
  t1 : t.gpr .t1 = BitVec.ofNat 64 (2 ^ k)

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.add .t0 .t0 .t0, .add .t1 .t1 .t1, .sub .t3 .t0 .t2]) t
      fun t' => NInv s r (k + 1) t' ∧ (t'.gpr .t3 != 0) = decide (k + 1 ≠ e + 1) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_sub fun t₃ u₃ => WP.block_nil ?_
  have ax : t₂.gpr .t0 = BitVec.ofNat 64 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.t0, Proof.Scrypt.Memory.dbl_pow]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₃.mem, u₂.mem, u₁.mem, h.mem],
    fun r' h0 h1 h3 => ?_, by rw [u₃.other _ (by decide), ax], ?_⟩, ?_⟩
  · rw [u₃.other r' h3, u₂.other r' h1, u₁.other r' h0, h.other r' h0 h1 h3]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.t1, ← Nat.one_mul (2 ^ k),
      Proof.Scrypt.Memory.dbl_pow, Nat.one_mul]
  · rw [u₃.gpr, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide) (by decide), h2, bne, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, Bool.not_false, ne_eq, hh, not_false_eq_true, decide_true]

/-- `nLoop` doubles `t0` (from `r`) and `t1` (from 1) until `t0 = t2 = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (h0 : s.gpr .t0 = BitVec.ofNat 64 r) (h1 : s.gpr .t1 = 1)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .t0 → r' ≠ .t1 → r' ≠ .t3 → s'.gpr r' = s.gpr r') ∧
      s'.gpr .t1 = BitVec.ofNat 64 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h2 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.sp, h.mem, h.other, h.t1⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, by rw [h0, Nat.pow_zero, Nat.mul_one],
    by rw [h1]; rfl⟩

end VG.Proof.Scrypt.RISCV64.RoMix
