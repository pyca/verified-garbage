module

import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.Cmac

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
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ofNat_and15 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 15 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega),
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
  · exact sub_lo (by omega)
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
    · exact hP.wd (by omega)
    · exact hP.wd (by decide)
    · exact hP.wd (by decide)) (by have := hP.lt; omega)

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
  have pk₈ : PK s s₈ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))))
  have E₈ := E.of_pk pk₈
  have hm₈ : s₈.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr, Offset.add_add]
    rfl
  have f₈ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₈.mem := by
    rw [hm₈]; exact Proof.Cmac.frame_store2 _ _ _
  have hz₈ : bytesAt s₈.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₈, Proof.AesCcm.bytesAt_writeW64_at _ _ (o := 8) _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide)]
    simp only [le8_zero, List.drop_append, List.take_append, List.drop_drop]
    simp [Spec.Ccm.zeros, length_bytesAt]
  -- The tail's address, length and copy.
  have hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := hP.drop hw
  rw [show len - 16 * (len / 16) = len % 16 by omega] at hq
  have a0₈ : s₈.gpr .a0 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs5, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs6,
      ofNat_lsr4 hl, ofNat_lsl4 (by omega)]
  have hb : BytesPre s₈ (P + BitVec.ofNat 64 (16 * (len / 16)))
      (c.W + BitVec.ofNat 64 32) (len % 16) :=
    { a0 := a0₈
      a1 := by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl
      a2 := by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs8]
      pos := by omega
      lt := by omega
      rd := by rw [pk₈.rd, pk₈.wr]; exact hq.rd
      wr := covers_prefix (E₈.perm.wC (d := 32) (n := 16) (by decide)) (by omega)
      disj := (hq.wd (d := 32) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega)) }
  refine WP.seq (WP.mono (copy_wp s₈ hb) fun s₉ ⟨hm₉, _, k₉⟩ => ?_)
  have pk₉ := pk₈.trans (PK.ofKeeps k₉)
  have E₉ := E.of_pk pk₉
  have htail : bytesAt s₈.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
      (bytesAt s.mem P len).drop (16 * (len / 16)) := by
    rw [Proof.Cmac.bytesAt_frame f₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hq.wd (by decide)) (by omega),
      show len % 16 = len - 16 * (len / 16) by omega, bytesAt_suffix _ _ hw]
  have hB : bytesAt s₉.mem (c.W + BitVec.ofNat 64 32) 16 =
      (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
    rw [hm₉, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega) (by decide), hz₈, htail,
      List.length_drop, length_bytesAt]
    simp only [Spec.Ccm.zeros, List.drop_replicate]
    congr 2
    omega
  have f₉ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₉.mem := by
    rw [hm₉]
    refine f₈.trans (writeBytes_frame _ _ _ ?_)
    rw [length_bytesAt]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
    omega
  -- The block chained.
  unfold updBlock updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ => wp_addi (by omega) fun s₁₂ u₁₂ =>
    wp_addi (by decide) fun s₁₃ u₁₃ => wp_addi (by decide) fun s₁₄ u₁₄ =>
    wp_li (by decide) fun s₁₅ u₁₅ => WP.block_nil ?_)
  have pk₁₅ : PK s₉ s₁₅ := (PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅)))))
  have E₁₅ := E₉.of_pk pk₁₅
  have m₁₅ : s₁₅.mem = s₉.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  have U := uargs L E₁₅ (y := y) (by omega) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₁₅.perm (by decide)) (L.w_w (by omega) (by decide) (by omega)) (by decide)
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
  have f₁₆' : Frame (macR c.W y) s₉.mem s₁₆.mem := by
    rw [← m₁₅]
    exact U₁₆.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have f₁₆ : Frame (macR c.W y) s.mem s₁₆.mem :=
    (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans f₁₆'
  refine ⟨pk₉.trans (pk₁₅.trans (PK.ofSaved U₁₆.rd U₁₆.wr U₁₆.sp U₁₆.saved)), f₁₆, ?_⟩
  have hY : bytesAt s₉.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by omega) (by decide)) (by decide)
  have hK : Spec.Ccm.ctxCiph s₉.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R :=
    ciph_keep L hy (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  rw [U₁₆.out, m₁₅, Proof.Cmac.Stream.blocksAt_eq, hY, show 16 * 1 = 16 from rfl, hB,
    Proof.Cmac.Stream.blocks_single (by simp [length_bytesAt, Spec.Ccm.zeros]; omega), ← hK]
  rfl

/-- The `len` bytes at `P` (`s5`, `s6`), padded with zeros to whole blocks,
chained into the MAC state at `W + y`. -/
theorem absorbPad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (hs5 : s.gpr .s5 = P) (hs6 : s.gpr .s6 = BitVec.ofNat 64 len) :
    WP isa (absorbPad y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  have hl := hP.lt
  have hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  unfold absorbPad updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by omega) fun s₃ u₃ =>
    wp_addi (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ =>
    WP.block_nil ?_)
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hq := hP.take hw
  have U := uargs L E₆ (y := y) (by omega) (Q := P) (k := len / 16) (hq.of_eq pk₆.rd pk₆.wr).src
    (hq.wd (by omega)) (by omega)
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
  have f₇ : Frame (macR c.W y) s.mem s₇.mem := by
    rw [← m₆]
    exact U₇.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have Y₇ : bytesAt s₇.mem (c.W + BitVec.ofNat 64 y) 16 =
      Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))) := by
    rw [U₇.out, Proof.Cmac.Stream.blocksAt_eq, m₆, ← bytesAt_prefix _ _ hw]
    rfl
  refine WP.seq (wp_andi (by decide) fun s₉ u₉ => WP.block_nil ?_)
  have pk₉ : PK s s₉ := pk₆.trans ((PK.ofSaved U₇.rd U₇.wr U₇.sp U₇.saved).trans (PK.ofUpd u₉))
  have m₉ : s₉.mem = s₇.mem := by rw [u₉.mem]
  have s6₈ : s₇.gpr .s6 = BitVec.ofNat 64 len := by
    rw [U₇.saved _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hs6]
  have s8₉ : s₉.gpr .s8 = BitVec.ofNat 64 (len % 16) := by
    rw [u₉.gpr, s6₈, show BitVec.ofInt 64 15 = BitVec.ofNat 64 15 from rfl, ofNat_and15 hl]
  have hb : Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len)) =
      Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16))) ++
        (if len % 16 = 0 then [] else
          [(bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16)]) := by
    rw [Proof.AesCcm.blocks_pad16, length_bytesAt]
  refine WP.ite (decide (len % 16 = 0)) (eval_z s8₉ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₉, by rw [m₉]; exact f₇, ?_⟩
    rw [m₉, Y₇, hb, ite_eq_left h0, List.append_nil]
  · have h0 : len % 16 ≠ 0 := by simpa using hf
    have f₉ : Frame (macR c.W y) s.mem s₉.mem := by rw [m₉]; exact f₇
    refine WP.mono (absTail_wp L (E.of_pk pk₉) hy (hP.of_eq pk₉.rd pk₉.wr)
      (by rw [u₉.other _ (by decide), U₇.saved _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hs5])
      (by rw [u₉.other _ (by decide), s6₈]) s8₉ h0) fun s' A => ⟨pk₉.trans A.pk, f₉.trans A.frame, ?_⟩
    rw [A.out, ciph_keep L hy f₉, buf_keep hP hy f₉, m₉, Y₇, hb, ite_eq_right h0, Proof.Cmac.chain_append]

end VG.Proof.AesCcm.RISCV64
