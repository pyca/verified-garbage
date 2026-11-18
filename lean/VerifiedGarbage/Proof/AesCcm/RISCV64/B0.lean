module

import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesCcm.Rev64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.Cmac

/-! ### `AesCcm.RISCV64.Header`, which this module and modules that import it used -/

section

/-! ### `AesCcm.RISCV64.Ctrs`, which this module and modules that import it used -/

section

/-!
# AES-CCM on RISC-V: `Ctr₀` (`ctrs`) and the tag out (`tagOut`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesCcm/PPC64LE/Ctrs.lean`): `ctrs` zeroes `W + 48`, writes
`q − 1 = 14 − n` in its first byte and copies the `n`-byte nonce after it:
`Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3, `ctrs_wp`). `tagOut` copies the first
`tag_len` bytes of the tag at `W` to `tag` (`tagOut_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- Sixteen zero bytes, as two doublewords. -/
theorem zeros16_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 =
      Spec.Ccm.zeros 16 := by
  rw [Proof.AesCcm.bytesAt_writeW64_at _ _ (o := 8) _ (by decide) (by decide),
    Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide)]
  simp only [Proof.Cmac.le8_zero, List.drop_append, List.take_append, List.drop_drop]
  simp [Spec.Ccm.zeros, Spec.Cmac.zeros, length_bytesAt]

/-- `Ctr₀` at `W + 48`, from the `n`-byte nonce at `N` (`a2`, `a3`). -/
theorem ctrs_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {N : Addr} (hN : Buf c s N c.nl)
    (h2 : s.gpr .a2 = N) (h3 : s.gpr .a3 = BitVec.ofNat 64 c.nl) :
    WP isa ctrs s fun s' => PK s s' ∧ Frame [⟨c.W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
  have h7 := L.h7
  have h13 := L.h13
  unfold ctrs ctrsSeg zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 48) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => ?_
  refine wp_sb (a := c.W + BitVec.ofNat 64 48) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  have pk₉ : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have E₉ := E.of_pk pk₉
  have g₄ : ∀ r, r ≠ .t0 → r ≠ .t1 → s₅.gpr r = s.gpr r := fun r h0 h1 => by
    rw [u₅.other _ h1, u₄.other _ h1, u₃.gpr, u₂.gpr, u₁.other _ h0]
  -- The memory before the copy.
  have m₉ : s₉.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 48)
      (BitVec.ofNat 8 (15 - c.nl - 1) : Byte)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₄.gpr, u₄.other .a3 (by decide), u₃.gpr, u₂.gpr,
      u₁.other .a3 (by decide), h3, Proof.AesCcm.sub_low_byte (by omega_using [h13]), u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem,
      u₁.mem, u₁.gpr]
    rfl
  have hb : BytesPre s₉ N (c.W + BitVec.ofNat 64 49) c.nl :=
    { a0 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, g₄ .a2 (by decide) (by decide), h2]
      a1 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr,
        g₄ .s1 (by decide) (by decide), E.s1]; rfl
      a2 := by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₄ .a3 (by decide) (by decide), h3]
      pos := by omega_using [h7]
      lt := by omega_using [h13]
      rd := by rw [pk₉.rd, pk₉.wr]; exact hN.rd
      wr := E₉.perm.wC (by omega_using [h13])
      disj := hN.wd (by omega_using [h13]) }
  refine WP.mono (copy_wp s₉ hb) fun s₁₀ ⟨hm, _, k₁₀⟩ => ⟨pk₉.trans (PK.ofKeeps k₁₀), ?_, ?_⟩
  · rw [hm, m₉]
    have cB : ∀ d k, 48 ≤ d → d + k ≤ 64 →
        (⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
      fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega_using [h₂]) (by decide)
    refine ((Proof.Cmac.frame_store2 _ _ _).writeW (List.mem_singleton_self _) _ (cB 48 1 (by decide) (by decide))).trans
      (writeBytes_frame _ _ _ ?_)
    rw [length_bytesAt]; exact cB 49 c.nl (by decide) (by omega_using [h13])
  · have hx : bytesAt s₉.mem N c.nl = bytesAt s.mem N c.nl := by
      rw [m₉]
      refine Proof.Cmac.bytesAt_frame (rs := [⟨c.W + BitVec.ofNat 64 48, 16⟩])
        (((Proof.Cmac.frame_store2 _ _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains c.W (Nat.le_refl _) (by decide) (by decide)))) (fun r hr => ?_) (by omega_using [h13])
      simp only [List.mem_singleton] at hr; subst hr; exact hN.wd (by decide)
    have hz : bytesAt ((s.mem.writeW (c.W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
        (c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8) (0 : BitVec 64)) (c.W + BitVec.ofNat 64 48) 16 =
        Spec.Ccm.zeros 16 := zeros16_bytes _ _
    rw [hm, hx, m₉, show c.W + BitVec.ofNat 64 49 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 from
        (Offset.add_add c.W 48 1).symm,
      Proof.AesCcm.bytesAt_writeBytes_at _ _ (o := 1) (n := 16) _ (by rw [length_bytesAt]; omega_using [h13]) (by decide),
      Proof.AesCcm.bytesAt_writeW8_base _ _ _ (by decide) (by decide), hz, length_bytesAt]
    simp only [Spec.Ccm.ctrBlock, length_bytesAt, Proof.AesCcm.be_zero, Spec.Ccm.zeros, List.take_succ_cons,
      List.take_zero, List.drop_replicate, List.cons_append, List.nil_append]
    rw [Nat.add_comm 1 c.nl, List.drop_succ_cons, List.drop_replicate]

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
theorem tagOut_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (hT : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa tagOut s fun s' => PK s s' ∧ Frame [⟨c.T, c.tl⟩] s.mem s'.mem ∧
      bytesAt s'.mem c.T c.tl = bytesAt s.mem c.W c.tl := by
  have ht4 := L.t4
  have ht16 := L.t16
  unfold tagOut
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s1]; rfl)
    (L.alW (by decide) (by decide)) (E.perm.wR (by decide)) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ =>
      WP.block_nil ?_)
  have pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hwt : (⟨c.W, c.tl⟩ : Region).Disjoint ⟨c.T, c.tl⟩ :=
    (L.t_w.sub_right (Region.sub_prefix (by omega_using [ht16]))).symm.sub_left (Region.sub_prefix (Nat.le_refl _))
  have hb : BytesPre s₃ c.W c.T c.tl :=
    { a0 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1]
      a1 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, S.tag]
      a2 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s2]
      pos := by omega_using [ht4]
      lt := by omega_using [ht16]
      rd := by
        rw [pk₃.rd, pk₃.wr]
        have h := E.perm.wCR (d := 0) (n := c.tl) (by omega_using [ht16])
        rw [BitVec.add_zero] at h
        exact h
      wr := by rw [pk₃.wr]; exact hT
      disj := hwt }
  refine WP.mono (copy_wp s₃ hb) fun s₄ ⟨hm, _, k₄⟩ => ⟨pk₃.trans (PK.ofKeeps k₄), ?_, ?_⟩
  · rw [hm, m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  · rw [hm, m₃]
    have := Proof.AesCcm.bytesAt_writeBytes_base s.mem c.T (bytesAt s.mem c.W c.tl) (n := c.tl)
      (by rw [length_bytesAt]) (by have := L.tw; omega_using [ht16])
    rw [this, length_bytesAt, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil]

end VG.Proof.AesCcm.RISCV64

end

end

/-! ### `AesCcm.RISCV64.Absorb`, which this module and modules that import it used -/

section

/-!
# AES-CCM on RISCV64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`, on none if
there are none, then its last `len mod 16` bytes copied into the zeroed
block `B` (`absTail_wp`); together, the blocks of the padded string
(`absorbPad_wp`, `Proof.AesCcm.blocks_pad16`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Proof.CmacAes.Stream.RISCV64 (upd_call)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt bytesAt_prefix bytesAt_suffix bytesAt_writeBytes_base)

/-! ## Arithmetic -/

theorem ofNat_lsl4 {a : Nat} (ha : a < 2 ^ 60) :
    BitVec.ofNat 64 a <<< 4 = BitVec.ofNat 64 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_using [ha]),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using [ha]), Nat.mod_eq_of_lt (by omega_using [ha])]
  omega_using []

theorem ofNat_and15 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 15 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_using []),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-! ## What the pieces leave -/

/-- The regions the CBC-MAC's pieces write: the MAC state at `W + y`, `B`
and the working space of the functions called. -/
abbrev macR (W : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

/-- What a piece of the CBC-MAC leaves: the MAC state `Y` at `W + y`. -/
structure Absorbed (c : Cx) (y : Nat) (s : State) (Y : List Byte) (s' : State) : Prop where
  pk : PK s s'
  frame : Frame (macR c.W y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y

theorem macR_mut {c : Cx} {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ macR c.W y, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by omega_using [hy])
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

/-- The cipher of the key schedule, which the pieces keep. -/
theorem ciph_keep {c : Cx} (L : Lay c) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (macR c.W y) m m') : Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R :=
  ciph_mut L (hf.sub (macR_mut hy))

/-- A buffer apart from `W` is kept. -/
theorem buf_keep {c : Cx} {s : State} {P : Addr} {len : Nat} (hP : Buf c s P len) {y : Nat} (hy : y = 0 ∨ y = 96)
    {m m' : Mem} (hf : Frame (macR c.W y) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.wd (by omega_using [hy])
    · exact hP.wd (by decide)
    · exact hP.wd (by decide)) (by have := hP.lt; omega_using [this])

/-! ## The last bytes -/

theorem le8_zero : Proof.Cmac.le8 (0 : BitVec 64) = Spec.Ccm.zeros 8 := by decide

/-- The last `len mod 16` (not 0) bytes of the `len` bytes at `P`, padded
with zeros in `B` and chained into the MAC state at `W + y`. -/
theorem absTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (hs5 : s.gpr .s5 = P) (hs6 : s.gpr .s6 = BitVec.ofNat 64 len)
    (hs8 : s.gpr .s8 = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    WP isa (absTail y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [(bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16)])) := by
  have hl := hP.lt
  unfold absTail zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 32) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide)) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 40) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide)) (by rw [u₂.wr, u₁.wr]; exact E.perm.wW (by decide))
    fun s₃ u₃ => ?_
  refine wp_srl (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
    wp_addi (by decide) fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  obtain pk₈ : PK s s₈ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))))
  obtain E₈ := E.of_pk pk₈
  obtain hm₈ : s₈.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr, Offset.add_add]
    rfl
  obtain f₈ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₈.mem := by
    rw [hm₈]; exact Proof.Cmac.frame_store2 _ _ _
  obtain hz₈ : bytesAt s₈.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₈, Proof.AesCcm.bytesAt_writeW64_at _ _ (o := 8) _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide)]
    simp only [le8_zero, List.drop_append, List.take_append, List.drop_drop]
    simp [Spec.Ccm.zeros, length_bytesAt]
  -- The tail's address, length and copy.
  obtain hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  obtain hq := hP.drop hw
  rw [show len - 16 * (len / 16) = len % 16 by omega_using []] at hq
  obtain a0₈ : s₈.gpr .a0 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs5, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs6,
      ofNat_lsr4 hl, ofNat_lsl4 (by omega_using [hl])]
  obtain hb : BytesPre s₈ (P + BitVec.ofNat 64 (16 * (len / 16)))
      (c.W + BitVec.ofNat 64 32) (len % 16) :=
    { a0 := a0₈
      a1 := by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl
      a2 := by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs8]
      pos := by omega_using [h0]
      lt := by omega_using []
      rd := by rw [pk₈.rd, pk₈.wr]; exact hq.rd
      wr := covers_prefix (E₈.perm.wC (d := 32) (n := 16) (by decide)) (by omega_using [])
      disj := (hq.wd (d := 32) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega_using [])) }
  refine WP.seq (WP.mono (copy_wp s₈ hb) fun s₉ ⟨hm₉, _, k₉⟩ => ?_)
  obtain pk₉ := pk₈.trans (PK.ofKeeps k₉)
  obtain E₉ := E.of_pk pk₉
  obtain htail : bytesAt s₈.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
      (bytesAt s.mem P len).drop (16 * (len / 16)) := by
    rw [Proof.Cmac.bytesAt_frame f₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hq.wd (by decide)) (by omega_using []),
      show len % 16 = len - 16 * (len / 16) by omega_using [], bytesAt_suffix _ _ hw]
  obtain hB : bytesAt s₉.mem (c.W + BitVec.ofNat 64 32) 16 =
      (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
    rw [hm₉, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega_using []) (by decide), hz₈, htail,
      List.length_drop, length_bytesAt]
    simp only [Spec.Ccm.zeros, List.drop_replicate]
    congr 2
    omega_using []
  obtain f₉ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₉.mem := by
    rw [hm₉]
    refine f₈.trans (writeBytes_frame _ _ _ ?_)
    rw [length_bytesAt]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
    omega_using []
  -- The block chained.
  unfold updBlock updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ => wp_addi (by omega_using [hy]) fun s₁₂ u₁₂ =>
    wp_addi (by decide) fun s₁₃ u₁₃ => wp_addi (by decide) fun s₁₄ u₁₄ =>
    wp_li (by decide) fun s₁₅ u₁₅ => WP.block_nil ?_)
  obtain pk₁₅ : PK s₉ s₁₅ := (PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅)))))
  obtain E₁₅ := E₉.of_pk pk₁₅
  obtain m₁₅ : s₁₅.mem = s₉.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  obtain U := uargs L E₁₅ (y := y) (by omega_using [hy]) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₁₅.perm (by decide)) (L.w_w (by omega_using [hy]) (by decide) (by omega_using [hy])) (by decide)
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.gpr, E₉.s3])
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.gpr, u₁₀.other _ (by decide), E₉.s4])
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr,
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), E₉.s1])
    (by rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), E₉.s1]; rfl)
    (by rw [u₁₅.gpr])
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), E₉.s1]; rfl)
  refine WP.mono (upd_call U) fun s₁₆ U₁₆ => ?_
  obtain f₁₆' : Frame (macR c.W y) s₉.mem s₁₆.mem := by
    rw [← m₁₅]
    exact U₁₆.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  obtain f₁₆ : Frame (macR c.W y) s.mem s₁₆.mem :=
    (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans f₁₆'
  refine ⟨pk₉.trans (pk₁₅.trans (PK.ofSaved U₁₆.rd U₁₆.wr U₁₆.sp U₁₆.saved)), f₁₆, ?_⟩
  obtain hY : bytesAt s₉.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_using [hy]) (by omega_using [hy]) (by decide)) (by decide)
  obtain hK : Spec.Ccm.ctxCiph s₉.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R :=
    ciph_keep L hy (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  rw [U₁₆.out, m₁₅, Proof.Cmac.Stream.blocksAt_eq, hY, show 16 * 1 = 16 from rfl, hB,
    Proof.Cmac.Stream.blocks_single (by simp [length_bytesAt, Spec.Ccm.zeros]; omega_using []), ← hK]
  rfl

/-- The `len` bytes at `P` (`s5`, `s6`), padded with zeros to whole blocks,
chained into the MAC state at `W + y`. -/
theorem absorbPad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (hs5 : s.gpr .s5 = P) (hs6 : s.gpr .s6 = BitVec.ofNat 64 len) :
    WP isa (absorbPad y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  have hl := hP.lt
  obtain hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  unfold absorbPad updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by omega_using [hy]) fun s₃ u₃ =>
    wp_addi (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ =>
    WP.block_nil ?_)
  obtain pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  obtain E₆ := E.of_pk pk₆
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hq := hP.take hw
  obtain U := uargs L E₆ (y := y) (by omega_using [hy]) (Q := P) (k := len / 16) (hq.of_eq pk₆.rd pk₆.wr).src
    (hq.wd (by omega_using [hy])) (by omega_using [hl])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.s3])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.s4])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hs5])
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hs6, ofNat_lsr4 hl])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
  refine WP.seq (WP.mono (upd_call U) fun s₇ U₇ => ?_)
  obtain f₇ : Frame (macR c.W y) s.mem s₇.mem := by
    rw [← m₆]
    exact U₇.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  obtain Y₇ : bytesAt s₇.mem (c.W + BitVec.ofNat 64 y) 16 =
      Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))) := by
    rw [U₇.out, Proof.Cmac.Stream.blocksAt_eq, m₆, ← bytesAt_prefix _ _ hw]
    rfl
  refine WP.seq (wp_andi (by decide) fun s₉ u₉ => WP.block_nil ?_)
  obtain pk₉ : PK s s₉ := pk₆.trans ((PK.ofSaved U₇.rd U₇.wr U₇.sp U₇.saved).trans (PK.ofUpd u₉))
  obtain m₉ : s₉.mem = s₇.mem := by rw [u₉.mem]
  obtain s6₈ : s₇.gpr .s6 = BitVec.ofNat 64 len := by
    rw [U₇.saved _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hs6]
  obtain s8₉ : s₉.gpr .s8 = BitVec.ofNat 64 (len % 16) := by
    rw [u₉.gpr, s6₈, show BitVec.ofInt 64 15 = BitVec.ofNat 64 15 from rfl, ofNat_and15 hl]
  obtain hb : Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len)) =
      Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16))) ++
        (if len % 16 = 0 then [] else
          [(bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16)]) := by
    rw [Proof.AesCcm.blocks_pad16, length_bytesAt]
  refine WP.ite (decide (len % 16 = 0)) (eval_z s8₉ (by omega_using [])) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₉, by rw [m₉]; exact f₇, ?_⟩
    rw [m₉, Y₇, hb, ite_eq_left h0, List.append_nil]
  · have h0 : len % 16 ≠ 0 := by simpa using hf
    obtain f₉ : Frame (macR c.W y) s.mem s₉.mem := by rw [m₉]; exact f₇
    refine WP.mono (absTail_wp L (E.of_pk pk₉) hy (hP.of_eq pk₉.rd pk₉.wr)
      (by rw [u₉.other _ (by decide), U₇.saved _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hs5])
      (by rw [u₉.other _ (by decide), s6₈]) s8₉ h0) fun s' A => ⟨pk₉.trans A.pk, f₉.trans A.frame, ?_⟩
    rw [A.out, ciph_keep L hy f₉, buf_keep hP hy f₉, m₉, Y₇, hb, ite_eq_right h0, Proof.Cmac.chain_append]

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISC-V: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesCcm/PPC64LE/Header.lean`): `header` zeroes `B` and writes the
encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by shifting `a` and storing
it big-endian a byte at a time (`storeBE`), which is storing it
byte-reversed (`wp_storeBE8`), so its blocks are the shared ones
(`Proof.AesCcm.enc_lo`, …) (`header_wp`); its length is in `s7`. And the
weakest preconditions of `storeBE 8` and `loadBE64`, as a doubleword
byte-reversed.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (hdrLen length_bytesAt)
open VG.Proof.CmacAes.Stream.RISCV64 (upd_call)
open VG.Impl.AesCbc.RISCV64 (mov)

/-! ## Big-endian doublewords -/

/-- `li` of any immediate. -/
theorem wp_li_int {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

/-- `storeBE 8 v tmp n off`: the doubleword `v` byte-reversed at `a`, and
`tmp` then `v`. -/
theorem wp_storeBE8 {is : List Instr} {s : State} {Q : State → Prop} {v tmp n : Reg} {off : Nat} {a : Addr}
    (htv : tmp ≠ v) (htn : tmp ≠ n) (ho : off + 8 ≤ 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hout : InRegions s.wr a 8)
    (k : ∀ s₁ s', Mupd s s₁ (s.mem.writeW a (byteRev64 (s.gpr v))) → Upd s₁ s' tmp (s.gpr v) →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.storeBE 8 v tmp n off ++ is)) s Q := by
  rw [WP.block_append_iff]
  obtain hin : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8 := by rw [ha]; exact hout
  refine WP.mono (ByteLoad.storeBE_ok htv htn (by decide) (by decide) ho
    (fun j hj => ByteLoad.in_byte' hin hj)) fun s' e => ?_
  subst e
  rw [writeBytes_beBytes, ha]
  exact k { s with mem := s.mem.writeW a (byteRev64 (s.gpr v)) } _ ⟨rfl, rfl, rfl, rfl, rfl⟩ (Upd.write _ _ _)

/-- `loadBE64 d tmp n off`: the doubleword at `a` byte-reversed in `d`. -/
theorem wp_loadBE64 {is : List Instr} {s : State} {Q : State → Prop} {d tmp n : Reg} {off : Nat} {a : Addr}
    (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp) (ho : off + 7 < 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s₁ s', Upd s s₁ tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 7))).setWidth 64) →
      Upd s₁ s' d (byteRev64 (s.mem.readW a 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 d tmp n off ++ is)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok hdn htn hdt ho (by rw [ha]; exact hin)) fun s' e => ?_
  subst e
  rw [be64_eq, ha]
  exact k _ _ (Upd.write _ _ _) (Upd.write _ _ _)

theorem m2_shl : byteRev64 (BitVec.ofInt 64 (-2) <<< 48) = BitVec.ofNat 64 0xfeff := by decide

/-! ## The encoding -/

/-- What `header` leaves. -/
structure HdrPost (c : Cx) (a : Nat) (s s' : State) : Prop where
  pk : PK s s'
  s5 : s'.gpr .s5 = s.gpr .s5
  s6 : s'.gpr .s6 = s.gpr .s6
  s7 : s'.gpr .s7 = BitVec.ofNat 64 (hdrLen a)
  frame : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a)

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`s6`) at its start, and its length in `s7`. -/
theorem header_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {a : Nat} (ha : a < 2 ^ 64)
    (hs6 : s.gpr .s6 = BitVec.ofNat 64 a) : WP isa header s (HdrPost c a s) := by
  unfold header zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 32) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_srl (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans (PK.ofUpd u₄)))
  obtain E₄ := E.of_pk pk₄
  obtain hm₄ : s₄.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr]; rfl
  obtain f₄ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [hm₄]; exact Proof.Cmac.frame_store2 _ _ _
  obtain z₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by rw [hm₄]; exact zeros16_bytes _ _
  obtain s5₄ : s₄.gpr .s5 = s.gpr .s5 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  obtain s6₄ : s₄.gpr .s6 = BitVec.ofNat 64 a := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs6]
  obtain t1₄ : s₄.gpr .t1 = BitVec.ofNat 64 (a / 2 ^ 32) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs6, ofNat_lsr ha]
  -- Storing a doubleword at the start of the zeroed `B`.
  obtain stB : ∀ {t : State} (v : BitVec 64), t.mem = s₄.mem.writeW (c.W + BitVec.ofNat 64 32) v →
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧
        bytesAt t.mem (c.W + BitVec.ofNat 64 32) 16 = Proof.Cmac.le8 v ++ Spec.Ccm.zeros 8 := by
    intro t v hm
    obtain hc : Region.Contains ⟨c.W + BitVec.ofNat 64 32, 16⟩ (c.W + BitVec.ofNat 64 32) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    refine ⟨f₄.trans ?_, ?_⟩
    · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
    rw [hm, Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide), z₄]
    simp [Spec.Ccm.zeros]
  obtain inB : ∀ {t : State}, PK s₄ t → InRegions t.wr (c.W + BitVec.ofNat 64 32) 8 := fun k => by
    rw [k.wr]; exact E₄.perm.wW (by decide)
  refine WP.ite (decide (a / 2 ^ 32 = 0)) (eval_z t1₄ (by omega_using [ha])) (fun ht => ?_) (fun hf => ?_)
  · have h₂ : a < 2 ^ 32 := by have := of_decide_eq_true ht; omega_using [this]
    refine WP.seq (wp_srl (by decide) fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ =>
      wp_sltu fun s₇ u₇ => WP.block_nil ?_)
    obtain pk₇ : PK s₄ s₇ := (PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇))
    obtain t1₇ : s₇.gpr .t1 = BitVec.ofNat 64 (if a / 2 ^ 8 < 255 then 1 else 0) := by
      rw [u₇.gpr, u₆.other .t1 (by decide), u₆.gpr, u₅.gpr, s6₄, ofNat_lsr ha,
        ofNat_ult (by omega_using [ha]) (by decide)]
    obtain m₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
    obtain s6₇ : s₇.gpr .s6 = BitVec.ofNat 64 a := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), s6₄]
    obtain s5₇ : s₇.gpr .s5 = s.gpr .s5 := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), s5₄]
    refine WP.ite (decide ((if a / 2 ^ 8 < 255 then 1 else 0) = 0)) (eval_z t1₇ (by split <;> decide))
      (fun ht' => ?_) (fun hf' => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      obtain h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_true ht'; split at this <;> simp_all <;> omega_arith
      refine wp_sll (by decide) fun s₈ u₈ => wp_li_int (by decide) fun s₉ u₉ => wp_sll (by decide) fun s₁₀ u₁₀ =>
        wp_or fun s₁₁ u₁₁ => ?_
      obtain pk₁₁ : PK s₇ s₁₁ := (PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁)))
      refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide) (by decide)
        (by rw [(pk₇.trans pk₁₁).gpr .s1 (by decide), E₄.s1]; rfl) (inB (pk₇.trans pk₁₁))
        fun s₁₂ s₁₃ u₁₂ u₁₃ => wp_li (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
      obtain pk : PK s₄ s₁₄ := pk₇.trans (pk₁₁.trans ((PK.ofMupd u₁₂).trans ((PK.ofUpd u₁₃).trans (PK.ofUpd u₁₄))))
      obtain hv : s₁₄.mem = s₄.mem.writeW (c.W + BitVec.ofNat 64 32)
          (byteRev64 (BitVec.ofNat 64 a) >>> 16 ||| BitVec.ofNat 64 0xfeff) := by
        rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₀.other .t1 (by decide), u₁₀.gpr, u₉.gpr,
          u₉.other .t1 (by decide), u₈.gpr, s6₇, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇,
          Proof.AesCcm.byteRev64_or, show (16 : Nat) = 8 * 2 from rfl, Proof.AesCcm.byteRev64_shl _ (by decide),
          m2_shl]
      obtain ⟨hf₁, hb₁⟩ := stB _ hv
      obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .s7 → s₁₄.gpr r = s₇.gpr r := fun r h1 h2 h7 => by
        rw [u₁₄.other _ h7, u₁₃.other _ h2, u₁₂.gpr, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ h2, u₈.other _ h1]
      refine ⟨pk₄.trans pk, by rw [g _ (by decide) (by decide) (by decide), s5₇],
        by rw [g _ (by decide) (by decide) (by decide), s6₇, hs6],
        by rw [u₁₄.gpr, Proof.AesCcm.hdrLen_mid h₁ h₂], hf₁, ?_⟩
      rw [hb₁]; exact Proof.AesCcm.enc_mid h₁ h₂ _ rfl
    · -- `[a]₁₆`.
      obtain h₁ : a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_false hf'; split at this <;> simp_all <;> omega_arith
      refine wp_sll (by decide) fun s₈ u₈ => ?_
      refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide) (by decide)
        (by rw [(pk₇.trans (PK.ofUpd u₈)).gpr .s1 (by decide), E₄.s1]; rfl) (inB (pk₇.trans (PK.ofUpd u₈)))
        fun s₉ s₁₀ u₉ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => WP.block_nil ?_
      obtain pk : PK s₄ s₁₁ := pk₇.trans ((PK.ofUpd u₈).trans ((PK.ofMupd u₉).trans ((PK.ofUpd u₁₀).trans
        (PK.ofUpd u₁₁))))
      obtain hv : s₁₁.mem = s₄.mem.writeW (c.W + BitVec.ofNat 64 32) (byteRev64 (BitVec.ofNat 64 a) >>> 48) := by
        rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.gpr, s6₇, u₈.mem, m₇,
          show (48 : Nat) = 8 * 6 from rfl, Proof.AesCcm.byteRev64_shl _ (by decide)]
      obtain ⟨hf₁, hb₁⟩ := stB _ hv
      obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .s7 → s₁₁.gpr r = s₇.gpr r := fun r h1 h2 h7 => by
        rw [u₁₁.other _ h7, u₁₀.other _ h2, u₉.gpr, u₈.other _ h1]
      refine ⟨pk₄.trans pk, by rw [g _ (by decide) (by decide) (by decide), s5₇],
        by rw [g _ (by decide) (by decide) (by decide), s6₇, hs6],
        by rw [u₁₁.gpr, Proof.AesCcm.hdrLen_lo h₁], hf₁, ?_⟩
      rw [hb₁]; exact Proof.AesCcm.enc_lo h₁ _ rfl
  · -- `0xff ‖ 0xff ‖ [a]₆₄`.
    obtain h₂ : ¬ a < 2 ^ 32 := by have := of_decide_eq_false hf; omega_using [this]
    obtain h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by omega_using [h₂]
    refine wp_li (by decide) fun s₅ u₅ => ?_
    refine wp_sb (a := c.W + BitVec.ofNat 64 32) (by decide)
      (by rw [u₅.other _ (by decide), E₄.s1]; rfl) (by rw [u₅.wr]; exact E₄.perm.wW (by decide)) fun s₆ u₆ => ?_
    refine wp_sb (a := c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 1) (by decide)
      (by rw [u₆.gpr, u₅.other _ (by decide), E₄.s1, Offset.add_add]; rfl)
      (by rw [u₆.wr, u₅.wr, Offset.add_add]; exact E₄.perm.wW (by decide)) fun s₇ u₇ => ?_
    refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2) (by decide) (by decide) (by decide)
      (by rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), E₄.s1, Offset.add_add]; rfl)
      (by rw [u₇.wr, u₆.wr, u₅.wr, Offset.add_add]; exact E₄.perm.wW (by decide))
      fun s₈ s₉ u₈ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain pk : PK s₄ s₁₀ := (PK.ofUpd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofMupd u₈).trans
      ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))))
    obtain s6₇ : s₇.gpr .s6 = BitVec.ofNat 64 a := by
      rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), s6₄]
    obtain hb : ((BitVec.ofNat 64 255).setWidth 8 : Byte) = 0xff := by decide
    obtain hm : s₁₀.mem = ((s₄.mem.writeW (c.W + BitVec.ofNat 64 32) (0xff : Byte)).writeW
        (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 1) (0xff : Byte)).writeW
        (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2) (byteRev64 (BitVec.ofNat 64 a)) := by
      rw [u₁₀.mem, u₉.mem, u₈.mem, s6₇, u₇.mem, u₆.mem, u₆.gpr, u₅.gpr, u₅.mem, hb]
    obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .s7 → s₁₀.gpr r = s₄.gpr r := fun r h1 h2 h7 => by
      rw [u₁₀.other _ h7, u₉.other _ h2, u₈.gpr, u₇.gpr, u₆.gpr, u₅.other _ h1]
    refine ⟨pk₄.trans pk, by rw [g _ (by decide) (by decide) (by decide), s5₄],
      by rw [g _ (by decide) (by decide) (by decide), s6₄, hs6],
      by rw [u₁₀.gpr, Proof.AesCcm.hdrLen_hi h₁ h₂], ?_, ?_⟩
    · rw [hm]
      refine f₄.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW
        (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_) <;>
        simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.sub_self, BitVec.toNat_zero] <;> decide
    · rw [hm, Proof.AesCcm.bytesAt_writeW64_at _ _ (o := 2) _ (by decide) (by decide),
        Proof.AesCcm.bytesAt_writeW8_at _ _ (o := 1) _ (by decide) (by decide),
        Proof.AesCcm.bytesAt_writeW8_base _ _ _ (by decide) (by decide), z₄,
        Proof.AesCcm.le8_byteRev64_ofNat ha, Proof.AesCcm.encodeLen_hi h₁ h₂, Proof.AesCcm.hdrLen_hi h₁ h₂]
      simp [Spec.Ccm.zeros, List.replicate]

/-! ## A block chained -/

/-- `B` chained into the MAC state at `W + y`. -/
theorem updBlock_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock y) s fun s' => Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16]) s' ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r := by
  unfold updBlock updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by omega_using [hy]) fun s₃ u₃ =>
    wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_li (by decide) fun s₆ u₆ => WP.block_nil ?_)
  obtain pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  obtain E₆ := E.of_pk pk₆
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain U := uargs L E₆ (y := y) (by omega_using [hy]) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₆.perm (by decide)) (L.w_w (by omega_using [hy]) (by decide) (by omega_using [hy])) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.s3])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.s4])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₆.gpr])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
  refine WP.mono (upd_call U) fun s₇ U₇ => ⟨⟨pk₆.trans (PK.ofSaved U₇.rd U₇.wr U₇.sp U₇.saved), ?_, ?_⟩, ?_⟩
  rotate_left 2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [U₇.saved _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [← m₆]
    exact U₇.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [U₇.out, m₆, Proof.Cmac.Stream.blocksAt_eq, show 16 * 1 = 16 from rfl,
      Proof.Cmac.Stream.blocks_single (length_bytesAt _ _ _)]
    rfl

/-! ## `min (16 − h, a)` -/

/-- The end of `minK`: `s8 := min (b, 16 − h)` for `b ≤ 16` in `t1`. -/
theorem minRest_wp {s : State} {h b : Nat} (hs7 : s.gpr .s7 = BitVec.ofNat 64 h)
    (ht1 : s.gpr .t1 = BitVec.ofNat 64 b) (hh : h ≤ 16) (hb : b ≤ 16) :
    WP isa (.seq (.block [.li .t2 16, .sub .t2 .t2 .s7, .sltu .t3 .t1 .t2])
      (.ite (.zero .t3) (.block [mov .s8 .t2]) (.block [mov .s8 .t1]))) s fun s' =>
      PK s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = BitVec.ofNat 64 (min b (16 - h)) ∧
        ∀ r ∈ [Reg.s5, .s6, .s7], s'.gpr r = s.gpr r := by
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_sltu fun s₃ u₃ => WP.block_nil ?_)
  obtain pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain t2₃ : s₃.gpr .t2 = BitVec.ofNat 64 (16 - h) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hs7, ofNat_sub_ofNat' hh (by decide)]
  obtain t1₃ : s₃.gpr .t1 = BitVec.ofNat 64 b := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht1]
  obtain t3₃ : s₃.gpr .t3 = BitVec.ofNat 64 (if b < 16 - h then 1 else 0) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .t1 (by decide), u₁.gpr, u₁.other .t1 (by decide), u₁.other .s7 (by decide),
      ht1, hs7, ofNat_sub_ofNat' hh (by decide), ofNat_ult (by omega_using [hb]) (by omega_using [])]
  obtain keep₃ : ∀ r ∈ [Reg.s5, .s6, .s7], s₃.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine WP.ite (decide ((if b < 16 - h then 1 else 0) = 0)) (eval_z t3₃ (by split <;> decide))
    (fun ht => ?_) (fun hf => ?_)
  · have hge : ¬ b < 16 - h := by have := of_decide_eq_true ht; split at this <;> simp_all
    refine wp_mv fun s₅ u₅ => WP.block_nil ⟨pk₃.trans (PK.ofUpd u₅), by rw [u₅.mem, m₃], ?_, fun r hr => ?_⟩
    · rw [u₅.gpr, t2₃, Nat.min_eq_right (by omega_using [hge])]
    · rw [u₅.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
        keep₃ r hr]
  · have hlt : b < 16 - h := by have := of_decide_eq_false hf; split at this <;> simp_all
    refine wp_mv fun s₅ u₅ => WP.block_nil ⟨pk₃.trans (PK.ofUpd u₅), by rw [u₅.mem, m₃], ?_, fun r hr => ?_⟩
    · rw [u₅.gpr, t1₃, Nat.min_eq_left (by omega_using [hlt])]
    · rw [u₅.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
        keep₃ r hr]

/-- `minK`: `s8 = min (a, 16 − h)` for `h ≤ 16` in `s7` and `a` in `s6`. -/
theorem minK_wp {s : State} {h a : Nat} (hs7 : s.gpr .s7 = BitVec.ofNat 64 h)
    (hs6 : s.gpr .s6 = BitVec.ofNat 64 a) (hh : h ≤ 16) (ha : a < 2 ^ 64) :
    WP isa minK s fun s' =>
      PK s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = BitVec.ofNat 64 (min a (16 - h)) ∧
        ∀ r ∈ [Reg.s5, .s6, .s7], s'.gpr r = s.gpr r := by
  unfold minK
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain t1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (a / 2 ^ 4) := by
    rw [u₁.gpr, hs6, ofNat_lsr ha]
  obtain k₁ : ∀ r ∈ [Reg.s5, .s6, .s7], s₁.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [u₁.other _ (by decide)]
  obtain fin : ∀ {t : State} {b : Nat}, PK s t → t.mem = s.mem → (∀ r ∈ [Reg.s5, .s6, .s7], t.gpr r = s.gpr r) →
      t.gpr .t1 = BitVec.ofNat 64 b → b = min a 16 →
      WP isa (.seq (.block [.li .t2 16, .sub .t2 .t2 .s7, .sltu .t3 .t1 .t2])
        (.ite (.zero .t3) (.block [mov .s8 .t2]) (.block [mov .s8 .t1]))) t fun s' =>
        PK s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = BitVec.ofNat 64 (min a (16 - h)) ∧
          ∀ r ∈ [Reg.s5, .s6, .s7], s'.gpr r = s.gpr r := by
    intro t b pk hm hk ht1 hb
    refine WP.mono (minRest_wp (by rw [hk .s7 (by simp), hs7]) ht1 hh (by omega_using [hb])) fun s' ⟨pk', hm', hs8, hk'⟩ =>
      ⟨pk.trans pk', by rw [hm', hm], by rw [hs8, hb]; congr 1; omega_using [], fun r hr => by rw [hk' r hr, hk r hr]⟩
  refine WP.seq (WP.ite (decide (a / 2 ^ 4 = 0)) (eval_z t1₁ (by omega_using [ha])) (fun ht => ?_) (fun hf => ?_))
  · have h16 : a < 16 := by have := of_decide_eq_true ht; omega_using [this]
    refine wp_mv fun s₂ u₂ => WP.block_nil ?_
    exact fin ((PK.ofUpd u₁).trans (PK.ofUpd u₂)) (by rw [u₂.mem, u₁.mem])
      (fun r hr => by
        rw [u₂.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
          k₁ r hr])
      (by rw [u₂.gpr, u₁.other _ (by decide), hs6]) (by omega_using [h16])
  · have h16 : 16 ≤ a := by have := of_decide_eq_false hf; omega_using [this]
    refine wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_
    exact fin ((PK.ofUpd u₁).trans (PK.ofUpd u₂)) (by rw [u₂.mem, u₁.mem])
      (fun r hr => by
        rw [u₂.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
          k₁ r hr])
      u₂.gpr (by rw [Nat.min_eq_right h16])

/-! ## The first block of the associated data -/

theorem hdrLen_ge (a : Nat) : 2 ≤ hdrLen a := by
  unfold hdrLen; split <;> [omega_using []; split <;> omega_using []]

/-- What `aadHead` leaves: its block chained, and the rest of the data. -/
structure HeadPost (c : Cx) (y : Nat) (P : Addr) (a : Nat) (s : State) (Y : List Byte) (s' : State) : Prop where
  abs : Absorbed c y s Y s'
  s5 : s'.gpr .s5 = P + BitVec.ofNat 64 (Proof.AesCcm.headLen a)
  s6 : s'.gpr .s6 = BitVec.ofNat 64 (a - Proof.AesCcm.headLen a)

/-- The first block of the `a > 0` bytes of associated data at `P`: the
encoding of its length followed by its first `headLen a` bytes, padded,
chained into the MAC state at `W + y`. -/
theorem aadHead_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {a : Nat} (hP : Buf c s P a) (hs5 : s.gpr .s5 = P) (hs6 : s.gpr .s6 = BitVec.ofNat 64 a)
    (ha0 : 0 < a) :
    WP isa (aadHead y) s (HeadPost c y P a s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem P a).take (Proof.AesCcm.headLen a))])) := by
  have hl := hP.lt
  obtain hh := Proof.AesCcm.hdrLen_le a
  obtain hh2 := hdrLen_ge a
  generalize hk : Proof.AesCcm.headLen a = k
  have hk' : k = min a (16 - hdrLen a) := hk.symm
  obtain hk1 : 1 ≤ k := by omega_using [ha0, hh, hk']
  obtain hkh : hdrLen a + k ≤ 16 := by omega_using [hh, hk']
  unfold aadHead
  refine WP.seq (WP.mono (header_wp L E hl hs6) fun s₁ H => ?_)
  obtain E₁ := E.of_pk H.pk
  refine WP.seq (WP.mono (minK_wp H.s7 (by rw [H.s6, hs6]) (by omega_using [hh]) hl)
    fun s₂ ⟨pk₂, m₂, s8₂, k₂⟩ => ?_)
  obtain E₂ := E₁.of_pk pk₂
  refine WP.seq (wp_add fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_)
  obtain pk₆ : PK s₂ s₆ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))
  obtain E₆ := E₂.of_pk pk₆
  obtain m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
  obtain hd : (⟨P, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 (32 + hdrLen a), k⟩ :=
    (hP.take (by omega_using [hk'])).wd (by omega_using [hh, hk'])
  obtain hb : BytesPre s₆ P (c.W + BitVec.ofNat 64 (32 + hdrLen a)) k :=
    { a0 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        k₂ .s5 (by simp), H.s5, hs5]
      a1 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, k₂ .s7 (by simp), H.s7, E₂.s1,
          Offset.add_add]
        congr 2
        unfold bO; omega_using []
      a2 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), s8₂, hk']
      pos := hk1
      lt := by omega_using [hk']
      rd := by rw [pk₆.rd, pk₂.rd, H.pk.rd, pk₆.wr, pk₂.wr, H.pk.wr]; exact (hP.take (by omega_using [hk'])).rd
      wr := E₆.perm.wC (by omega_using [hh, hk'])
      disj := hd }
  refine WP.seq (WP.mono (copy_wp s₆ hb) fun s₇ ⟨hm₇, _, k₇⟩ => ?_)
  obtain hx : bytesAt s₆.mem P k = (bytesAt s.mem P a).take k := by
    rw [m₆, Proof.Cmac.bytesAt_frame H.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hP.take (by omega_using [hk'])).wd (by decide)) (by omega_using [hk']),
      bytesAt_prefix _ _ (by omega_using [hk'] : k ≤ a)]
  refine WP.seq (wp_add fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_)
  obtain pk₉ : PK s s₉ := H.pk.trans (pk₂.trans (pk₆.trans ((PK.ofKeeps k₇).trans ((PK.ofUpd u₈).trans
    (PK.ofUpd u₉)))))
  obtain m₉ : s₉.mem = writeBytes s₁.mem (c.W + BitVec.ofNat 64 (32 + hdrLen a)) ((bytesAt s.mem P a).take k) := by
    rw [u₉.mem, u₈.mem, hm₇, hx, m₆]
  obtain hxl : ((bytesAt s.mem P a).take k).length = k := by rw [List.length_take, length_bytesAt]; omega_using [hk']
  -- `B` holds the encoding of the length, then the data, then zeros.
  obtain hB : bytesAt s₉.mem (c.W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem P a).take k) := by
    obtain he := Proof.AesCcm.length_encodeLen a
    rw [m₉, show c.W + BitVec.ofNat 64 (32 + hdrLen a) = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a)
        from (Offset.add_add _ _ _).symm,
      Proof.AesCcm.bytesAt_writeBytes_at _ _ (o := hdrLen a) (n := 16) _ (by rw [hxl]; omega_using [hh, hk']) (by decide), H.out,
      hxl]
    obtain e1 : (Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a)).take (hdrLen a) = Spec.Ccm.encodeLen a :=
      List.take_left' he
    obtain e2 : (Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a)).drop (hdrLen a + k) =
        Spec.Ccm.zeros (16 - (hdrLen a + k)) := by
      rw [show hdrLen a + k = (Spec.Ccm.encodeLen a).length + k by rw [he], List.drop_append]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by omega_using []), List.nil_append, he]
      congr 1; omega_using []
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem P a).take k)
      (by rw [List.length_append, he, hxl]; omega_using [hh, hk']) with e | e
    · rw [e1, e2, e, List.length_append, he, hxl, List.append_assoc]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, he]; simp; omega_using [hh2])
  obtain f₉ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₉.mem := by
    rw [m₉]
    refine H.frame.trans (writeBytes_frame _ _ _ ?_)
    rw [hxl]
    simp only [Region.Contains]
    rw [← Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hh])]
    omega_using [hh, hk']
  obtain E₉ := E.of_pk pk₉
  refine WP.mono (updBlock_wp L E₉ hy) fun s' ⟨A, ka⟩ => ⟨⟨pk₉.trans A.pk, ?_, ?_⟩, ?_, ?_⟩
  · exact (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans A.frame
  · have hY : bytesAt s₉.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
      Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_using [hy]) (by omega_using [hy]) (by decide)) (by decide)
    obtain hK : Spec.Ccm.ctxCiph s₉.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R :=
      ciph_keep L hy (f₉.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    rw [A.out, hY, hK, hB]
  · have s8₇ : s₇.gpr .s8 = BitVec.ofNat 64 k := by
      rw [k₇.gpr _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), s8₂, hk']
    rw [ka .s5 (by simp), u₉.other _ (by decide), u₈.gpr, s8₇, k₇.gpr _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ .s5 (by simp), H.s5, hs5, hk]
  · have s8₈ : s₈.gpr .s8 = BitVec.ofNat 64 k := by
      rw [u₈.other _ (by decide), k₇.gpr _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), s8₂, hk']
    rw [ka .s6 (by simp), u₉.gpr, s8₈, u₈.other _ (by decide), k₇.gpr _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ .s6 (by simp), H.s6, hs6,
      ofNat_sub_ofNat' (by omega_using [hk']) hl, hk]

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISCV64: `B₀` (`b0 y`) and the counter blocks (`ctrAt`)

Untrusted: everything here is checked by Lean. `flagsSeg` computes the flags
`4 (t − 2) + q − 1 + 64 [a > 0]` (which is A.2.1's for an even `t`,
`flags_wp`); `b0Seg y` writes `B₀` to `W + 32` from `Ctr₀` and zeroes the
MAC state at `W + y` (`b0Seg_wp`); `b0 y` then chains `B₀` into it
(`b0_wp`). `ctrAt` writes `Ctrᵢ` to `W + 64` from `Ctr₀` (`ctrAt_wp`). The
last 8 bytes of a block are read and written byte-reversed (`ldbrx`,
`stdbrx`), so ORing `[i]₆₄` into them is AArch64's `ctr_or`
(`Proof.AesCcm.ctr_or`): `rev (rev w ||| i) = w ||| rev i`.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)
open VG.Proof.Cmac (le8)

/-- `rev (rev w ||| v)`: `w` with `rev v` ORed into it. -/
theorem rev_or_rev (w v : BitVec 64) : byteRev64 (byteRev64 w ||| v) = w ||| byteRev64 v := by
  rw [Proof.AesCcm.byteRev64_or, Proof.Gcm.byteRev64_byteRev64]

/-- The first 8 and the last 8 bytes of `Ctr₀`. -/
theorem ctr0_lo {m : Mem} {W : Addr} {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (hc0 : bytesAt m (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    le8 (m.readW (W + BitVec.ofNat 64 48) 64) = BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
  obtain h8 : bytesAt m (W + BitVec.ofNat 64 48) 8 = (bytesAt m (W + BitVec.ofNat 64 48) 16).take 8 := by
    rw [Proof.Cmac.bytesAt_split, List.take_left' (length_bytesAt _ _ _)]
  rw [Proof.Cmac.le8_readW, h8, hc0, Proof.AesCcm.ctrBlock_take8 h7]

theorem ctr0_hi {m : Mem} {W : Addr} {nonce : List Byte}
    (hc0 : bytesAt m (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    le8 (m.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
  rw [show W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 from (Offset.add_add W 48 8).symm,
    Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, List.drop_left' (length_bytesAt _ _ _)]

theorem ctr0_take8 {m : Mem} {W : Addr} {nonce : List Byte}
    (hc0 : bytesAt m (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    le8 (m.readW (W + BitVec.ofNat 64 48) 64) = (Spec.Ccm.ctrBlock nonce 0).take 8 := by
  rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, List.take_left' (length_bytesAt _ _ _)]

theorem ofNat_lsl2 {a : Nat} (ha : a < 2 ^ 62) : BitVec.ofNat 64 a <<< 2 = BitVec.ofNat 64 (4 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_using [ha]),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using [ha]), Nat.mod_eq_of_lt (by omega_using [ha])]
  omega_using []

/-! ## The counter blocks -/

/-- `ctrAt`: `Ctrᵢ` at `W + 64`, for `i` in `t3`. -/
theorem ctrAt_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - c.nl)) (ht3 : s.gpr .t3 = BitVec.ofNat 64 i) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r ∈ [Reg.s5, .s6, .s7, .s8, .t3], s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem →
      bytesAt s'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i → WP isa (.block is) s' Q) :
    WP isa (.block (ctrAt ++ is)) s Q := by
  have h7 := L.h7
  have h13 := L.h13
  unfold ctrAt
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ld (a := c.W + BitVec.ofNat 64 48) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 64) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_loadBE64 (a := c.W + BitVec.ofNat 64 56) (by decide) (by decide) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₃ s₄ u₃ u₄ => ?_
  refine wp_or fun s₅ u₅ => ?_
  obtain pk₅ : PK s s₅ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (by decide) (by decide) (by decide)
    (by rw [pk₅.gpr .s1 (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [pk₅.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₆ s₇ u₆ u₇ => ?_
  obtain hk : ∀ r ∈ [Reg.s5, .s6, .s7, .s8, .t3], s₇.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]
  -- The two doublewords written.
  obtain hv : s₇.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 64) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
      (c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 i)) := by
    obtain hr : s₂.mem.readW (c.W + BitVec.ofNat 64 56) 64 = s.mem.readW (c.W + BitVec.ofNat 64 56) 64 := by
      rw [u₂.mem, u₁.gpr, u₁.mem]
      exact Mem.readW_writeW_sep ((L.w_w (a := 64) (n := 8) (d := 56) (k := 8) (.inr (by decide)) (by decide)
        (by decide)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
    rw [u₇.mem, u₆.mem, u₅.gpr, u₄.gpr, u₄.other .t3 (by decide), u₃.other .t3 (by decide),
      u₂.gpr, u₁.other .t3 (by decide), ht3, u₅.mem, u₄.mem, u₃.mem, hr, rev_or_rev, u₂.mem, u₁.gpr, u₁.mem]
  refine k s₇ (pk₅.trans ((PK.ofMupd u₆).trans (PK.ofUpd u₇))) hk
    (by rw [hv]; exact Proof.Cmac.frame_store2 _ _ _) ?_
  rw [hv, Proof.Cmac.bytesAt_store2, ctr0_take8 hc0,
    Proof.AesCcm.ctr_or (by omega_using [hnl, h7]) (by omega_using [hnl, h13]) (ctr0_hi hc0) (by rw [hnl]; exact hi),
    Proof.AesCcm.ctrBlock_take8 (by omega_using [hnl, h7]) 0, ← Proof.AesCcm.ctrBlock_take8 (by omega_using [hnl, h7]) i, List.take_append_drop]

/-! ## The flags -/

/-- The flags, from the tag length, the nonce length in its slot and the
length of the associated data in `s6`. -/
theorem flags_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (hs6 : s.gpr .s6 = BitVec.ofNat 64 c.al) :
    WP isa flagsSeg s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .t3 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64) ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r := by
  have ht4 := L.t4
  have ht16 := L.t16
  have h13 := L.h13
  unfold flagsSeg
  refine WP.seq (wp_subi (imm := 2) (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => ?_)
  refine wp_ld (a := c.W + BitVec.ofNat 64 232) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₃ u₃ => ?_
  refine wp_li (imm := 14) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_
  obtain pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain k₆ : ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s₆.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain t3₆ : s₆.gpr .t3 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl)) := by
    rw [u₆.gpr, u₅.gpr, u₅.other .t3 (by decide), u₄.gpr, u₄.other .t1 (by decide), u₄.other .t3 (by decide),
      u₃.gpr, u₃.other .t3 (by decide), u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, E.s2, S.nlen, ofNat_sub_ofNat' (by omega_using [ht4]) (by omega_using [ht16]),
      ofNat_lsl2 (by omega_using [ht16]), ofNat_sub_ofNat' (by omega_using [h13]) (by decide), BitVec.ofNat_add_ofNat]
  refine WP.ite (decide (c.al = 0)) (eval_z (by rw [k₆ .s6 (by simp), hs6]) L.al_lt)
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₆, m₆, by rw [t3₆, h0]; rfl, k₆⟩
  · have h0 : c.al ≠ 0 := by simpa using hf
    refine wp_addi (by decide) fun s₇ u₇ => WP.block_nil ⟨pk₆.trans (PK.ofUpd u₇),
      by rw [u₇.mem, m₆], ?_, fun r hr => ?_⟩
    · rw [u₇.gpr, t3₆, BitVec.ofNat_add_ofNat, ite_eq_right h0]
    · have ht3 : r ≠ .t3 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [u₇.other _ ht3, k₆ r hr]

/-! ## `B₀` -/

theorem flags_byte {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) :
    ((BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags c.tl (15 - nonce.length) c.al := by
  rw [hnl, Proof.AesCcm.flags_val L.t4 L.t16 L.te L.h7 L.h13]

/-- `B₀` at `W + 32` from `Ctr₀` and the flags in `t3`, and the MAC state at
`W + y` zeroed. -/
theorem b0Seg_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (ht3 : s.gpr .t3 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64))
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (b0Seg y)) s fun s' => PK s s' ∧ (∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r) ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Spec.Ccm.zeros 16 ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
  have h7 := L.h7
  have h13 := L.h13
  obtain hy8 : y % 8 = 0 := by omega_using [hy]
  unfold b0Seg zero16
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ld (a := c.W + BitVec.ofNat 64 48) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 56) (by decide) (by rw [u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 32) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 40) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ u₄ => ?_
  refine wp_sb (a := c.W + BitVec.ofNat 64 32) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  obtain pk₅ : PK s s₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    (PK.ofMupd u₅))))
  refine wp_loadBE64 (a := c.W + BitVec.ofNat 64 40) (by decide) (by decide) (by decide) (by decide)
    (by rw [pk₅.gpr .s1 (by decide), E.s1]; rfl)
    (by rw [pk₅.rd, pk₅.wr]; exact E.perm.wR (by decide)) fun s₆ s₇ u₆ u₇ => wp_or fun s₈ u₈ => ?_
  obtain pk₈ : PK s s₈ := pk₅.trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))
  refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 40) (by decide) (by decide) (by decide)
    (by rw [pk₈.gpr .s1 (by decide), E.s1]; rfl)
    (by rw [pk₈.wr]; exact E.perm.wW (by decide)) fun s₉ s₉' u₉ u₉' => ?_
  obtain pk₉ : PK s s₉' := pk₈.trans ((PK.ofMupd u₉).trans (PK.ofUpd u₉'))
  refine wp_li (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 y) (by omega_using [hy])
    (by rw [u₁₀.other _ (by decide), pk₉.gpr .s1 (by decide), E.s1]) (L.alW hy8 (by omega_using [hy]))
    (by rw [u₁₀.wr, pk₉.wr]; exact E.perm.wW (by omega_using [hy])) fun s₁₁ u₁₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8) (by omega_using [hy])
    (by rw [u₁₁.gpr, u₁₀.other _ (by decide), pk₉.gpr .s1 (by decide), E.s1, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_using [hy]) (by omega_using [hy]))
    (by rw [u₁₁.wr, u₁₀.wr, pk₉.wr, Offset.add_add]; exact E.perm.wW (by omega_using [hy])) fun s₁₂ u₁₂ => WP.block_nil ?_
  obtain pk₁₂ : PK s s₁₂ := pk₉.trans ((PK.ofUpd u₁₀).trans ((PK.ofMupd u₁₁).trans (PK.ofMupd u₁₂)))
  -- `B₀` as written.
  obtain s10₇ : s₇.gpr .s10 = BitVec.ofNat 64 c.n := by
    rw [(pk₅.trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇))).gpr .s10 (by decide), E.s10]
  obtain hr : s₅.mem.readW (c.W + BitVec.ofNat 64 40) 64 = s.mem.readW (c.W + BitVec.ofNat 64 56) 64 := by
    rw [u₅.mem, Mem.readW_writeW_sep ((L.w_w (a := 40) (n := 8) (d := 32) (k := 1) (.inr (by decide))
      (by decide) (by decide)).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), u₄.mem,
      Mem.readW_writeW_self64, u₃.gpr, u₂.gpr, u₁.mem]
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = (((s.mem.writeW (c.W + BitVec.ofNat 64 32)
      (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64)).writeW (c.W + BitVec.ofNat 64 32)
      ((s.gpr .t3).setWidth 8 : Byte)).writeW (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 c.n)) := ⟨_, rfl⟩
  obtain hm₉ : s₉'.mem = mB := by
    rw [hmB, u₉'.mem, u₉.mem, u₈.gpr, u₇.gpr, s10₇, hr, rev_or_rev, u₈.mem, u₇.mem, u₆.mem, u₅.mem,
      u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.other .t3 (by decide), u₂.gpr, u₂.mem, u₂.other .t1 (by decide), u₁.other .t3 (by decide),
      u₁.gpr, u₁.mem, Offset.add_add]
  obtain hm₁₂ : s₁₂.mem = (mB.writeW (c.W + BitVec.ofNat 64 y) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, u₁₀.gpr, u₁₀.mem, hm₉]; rfl
  obtain cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega_using [h₂]) (by decide)
  obtain fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB, Offset.add_add]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  obtain fY : Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩] mB s₁₂.mem := by
    rw [hm₁₂]; exact Proof.Cmac.frame_store2 _ _ _
  obtain dYB : (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain hB : bytesAt mB (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
    obtain hlo := ctr0_lo (by omega_using [hnl, h7]) hc0
    obtain hhi := Proof.AesCcm.ctr_or (by omega_using [hnl, h7]) (by omega_using [hnl, h13]) (ctr0_hi hc0) (by rw [hnl]; exact L.hn)
    rw [hmB, Proof.AesCcm.bytesAt_writeW64_at _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW8_base _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_at _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hhi, ht3, flags_byte L hnl,
      Proof.AesCcm.ctrBlock_drop8 (by omega_using [hnl, h7])]
    simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons,
      List.append_assoc]
    obtain ht7 : (nonce.take 7).length = 7 := by simp; omega_using [hnl, h7]
    obtain e1 : List.take 7 (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16)) =
        nonce.take 7 := List.take_left' ht7
    rw [e1, List.take_left' ht7]
    obtain hd1 : List.drop (8 + 8) (BitVec.ofNat 8 (15 - nonce.length - 1) ::
        (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16))) = [] :=
      List.drop_eq_nil_of_le (by simp [length_bytesAt]; omega_using [])
    rw [hd1, List.append_nil]
    obtain hd2 : List.drop (8 + 8) (Spec.Ccm.flags c.tl (15 - nonce.length) c.al ::
        (List.take 7 nonce ++ le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64))) = [] :=
      List.drop_eq_nil_of_le (by simp [Proof.Cmac.length_le8]; omega_using [])
    rw [hd2, List.append_nil, ← List.append_assoc, List.take_append_drop]
  refine ⟨pk₁₂, fun r hr => ?_, ?_, by rw [hm₁₂]; exact zeros16_bytes _ _, ?_⟩
  · have h1 : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ h1.1, u₉'.other _ h1.2.2, u₉.gpr, u₈.other _ h1.2.1, u₇.other _ h1.2.1,
      u₆.other _ h1.2.2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ h1.2.2, u₁.other _ h1.2.1]
  · exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  · rw [Proof.Cmac.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB)
      (by decide), hB]

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
theorem b0_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (hs6 : s.gpr .s6 = BitVec.ofNat 64 c.al) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 y) s fun s' => Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Ccm.zeros 16) [Spec.Ccm.b0 c.tl nonce c.al c.n]) s' ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r := by
  unfold b0
  refine WP.seq (WP.mono (flags_wp L E S hs6) fun s₁ ⟨pk₁, m₁, r9₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (b0Seg_wp L (E.of_pk pk₁) hnl (by rw [m₁]; exact hc0) r9₁ hy)
    fun s₂ ⟨pk₂, k₂, f₂, z₂, b₂⟩ => ?_)
  rw [m₁] at f₂
  obtain f₂' : Frame (macR c.W y) s.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  refine WP.mono (updBlock_wp L (E.of_pk (pk₁.trans pk₂)) hy) fun s₃ ⟨A, k₃⟩ =>
    ⟨⟨pk₁.trans (pk₂.trans A.pk), f₂'.trans A.frame, ?_⟩, fun r hr => by rw [k₃ r (by simp at hr ⊢; omega),
      k₂ r hr, k₁ r hr]⟩
  rw [A.out, z₂, b₂, ciph_keep L hy f₂']

end VG.Proof.AesCcm.RISCV64
