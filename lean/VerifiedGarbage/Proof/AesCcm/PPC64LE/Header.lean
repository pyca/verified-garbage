module

public import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesCcm.Rev64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Callee
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.Cmac

/-! ### `AesCcm.PPC64LE.Absorb`, which this module and modules that import it used -/

section

/-!
# AES-CCM on PPC64LE: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`, on none if
there are none, then its last `len mod 16` bytes copied into the zeroed
block `B` (`absTail_wp`); together, the blocks of the padded string
(`absorbPad_wp`, `Proof.AesCcm.blocks_pad16`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li wp_and wp_add wp_lsl wp_lsr wp_std)
open VG.Proof.Gather.PPC64LE (eval_zero BytesPre copyBytes_wp)
open VG.Proof.CmacAes.Stream.PPC64LE (upd_call)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt bytesAt_prefix bytesAt_suffix bytesAt_writeBytes_base)

/-! ## Arithmetic -/

theorem ofNat_lsl4 {a : Nat} (ha : a < 2 ^ 60) :
    BitVec.ofNat 64 a <<< 4 = BitVec.ofNat 64 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem ofNat_and15 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 15 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_arith),
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
  · exact sub_lo (by omega_arith)
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
    · exact hP.wd (by omega_arith)
    · exact hP.wd (by decide)
    · exact hP.wd (by decide)) (by have := hP.lt; omega_arith)

/-! ## The last bytes -/

theorem le8_zero : Proof.Cmac.le8 (0 : BitVec 64) = Spec.Ccm.zeros 8 := by decide

/-- The last `len mod 16` (not 0) bytes of the `len` bytes at `P`, padded
with zeros in `B` and chained into the MAC state at `W + y`. -/
theorem absTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (h18 : s.gpr .r18 = P) (h19 : s.gpr .r19 = BitVec.ofNat 64 len)
    (h21 : s.gpr .r21 = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    WP isa (absTail y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [(bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16)])) := by
  have hl := hP.lt
  unfold absTail zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_std (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]; rfl) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 40) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14]; rfl) (by rw [u₂.wr, u₁.wr]; exact E.perm.wW (by decide))
    fun s₃ u₃ => ?_
  refine wp_lsr (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
    wp_addi (by decide) (by decide) fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
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
  rw [show len - 16 * (len / 16) = len % 16 by omega_arith] at hq
  obtain r3₈ : s₈.gpr .r3 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), h18, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h19,
      VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat hl, ofNat_lsl4 (by omega_arith)]
  obtain hb : VG.Proof.Gather.PPC64LE.BytesPre s₈ (P + BitVec.ofNat 64 (16 * (len / 16)))
      (c.W + BitVec.ofNat 64 32) (len % 16) :=
    { r3 := r3₈
      r9 := by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.r14]; rfl
      r4 := by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h21]
      pos := by omega_arith
      lt := by omega_arith
      rd := by rw [pk₈.rd, pk₈.wr]; exact hq.rd
      wr := VG.Proof.Gather.PPC64LE.covers_prefix (E₈.perm.wC (d := 32) (n := 16) (by decide)) (by omega_arith)
      disj := (hq.wd (d := 32) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega_arith)) }
  refine WP.seq (WP.mono (copyBytes_wp s₈ hb) fun s₉ ⟨hm₉, _, k₉⟩ => ?_)
  obtain pk₉ := pk₈.trans (PK.ofKeeps k₉)
  obtain E₉ := E.of_pk pk₉
  obtain htail : bytesAt s₈.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
      (bytesAt s.mem P len).drop (16 * (len / 16)) := by
    rw [Proof.Cmac.bytesAt_frame f₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hq.wd (by decide)) (by omega_arith),
      show len % 16 = len - 16 * (len / 16) by omega_arith, bytesAt_suffix _ _ hw]
  obtain hB : bytesAt s₉.mem (c.W + BitVec.ofNat 64 32) 16 =
      (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
    rw [hm₉, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega_arith) (by decide), hz₈, htail,
      List.length_drop, length_bytesAt]
    simp only [Spec.Ccm.zeros, List.drop_replicate]
    congr 2
    omega_arith
  obtain f₉ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₉.mem := by
    rw [hm₉]
    refine f₈.trans (writeBytes_frame _ _ _ ?_)
    rw [length_bytesAt]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
    omega_arith
  -- The block chained.
  unfold updBlock updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ => wp_addi (by decide) (by omega_arith) fun s₁₂ u₁₂ =>
    wp_addi (by decide) (by decide) fun s₁₃ u₁₃ => wp_addi (by decide) (by decide) fun s₁₄ u₁₄ =>
    wp_li (by decide) fun s₁₅ u₁₅ => WP.block_nil ?_)
  obtain pk₁₅ : PK s₉ s₁₅ := (PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅)))))
  obtain E₁₅ := E₉.of_pk pk₁₅
  obtain m₁₅ : s₁₅.mem = s₉.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  obtain U := uargs L E₁₅ (y := y) (by omega_arith) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₁₅.perm (by decide)) (L.w_w (by omega_arith) (by decide) (by omega_arith)) (by decide)
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.gpr, E₉.r16])
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.gpr, u₁₀.other _ (by decide), E₉.r17])
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr,
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), E₉.r14])
    (by rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), E₉.r14]; rfl)
    (by rw [u₁₅.gpr])
    (by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), E₉.r14]; rfl)
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
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) (by omega_arith) (by decide)) (by decide)
  obtain hK : Spec.Ccm.ctxCiph s₉.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R :=
    ciph_keep L hy (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  rw [U₁₆.out, m₁₅, Proof.Cmac.Stream.blocksAt_eq, hY, show 16 * 1 = 16 from rfl, hB,
    Proof.Cmac.Stream.blocks_single (by simp [length_bytesAt, Spec.Ccm.zeros]; omega_arith), ← hK]
  rfl

/-- The `len` bytes at `P` (`r18`, `r19`), padded with zeros to whole blocks,
chained into the MAC state at `W + y`. -/
theorem absorbPad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (h18 : s.gpr .r18 = P) (h19 : s.gpr .r19 = BitVec.ofNat 64 len) :
    WP isa (absorbPad y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  have hl := hP.lt
  obtain hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  unfold absorbPad updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by decide) (by omega_arith) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ =>
    WP.block_nil ?_)
  obtain pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  obtain E₆ := E.of_pk pk₆
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hq := hP.take hw
  obtain U := uargs L E₆ (y := y) (by omega_arith) (Q := P) (k := len / 16) (hq.of_eq pk₆.rd pk₆.wr).src
    (hq.wd (by omega_arith)) (by omega_arith)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.r16])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.r17])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h18])
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h19, VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat hl])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
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
  refine WP.seq (wp_li (by decide) fun s₈ u₈ => wp_and fun s₉ u₉ => WP.block_nil ?_)
  obtain pk₉ : PK s s₉ := pk₆.trans ((PK.ofSaved U₇.rd U₇.wr U₇.sp U₇.saved).trans
    ((PK.ofUpd u₈).trans (PK.ofUpd u₉)))
  obtain m₉ : s₉.mem = s₇.mem := by rw [u₉.mem, u₈.mem]
  obtain r19₈ : s₈.gpr .r19 = BitVec.ofNat 64 len := by
    rw [u₈.other _ (by decide), U₇.saved _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h19]
  obtain r21₉ : s₉.gpr .r21 = BitVec.ofNat 64 (len % 16) := by
    rw [u₉.gpr, r19₈, u₈.gpr, ofNat_and15 hl]
  obtain hb : Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len)) =
      Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16))) ++
        (if len % 16 = 0 then [] else
          [(bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16)]) := by
    rw [Proof.AesCcm.blocks_pad16, length_bytesAt]
  refine WP.ite (decide (len % 16 = 0)) (eval_zero r21₉ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₉, by rw [m₉]; exact f₇, ?_⟩
    rw [m₉, Y₇, hb, ite_eq_left h0, List.append_nil]
  · have h0 : len % 16 ≠ 0 := by simpa using hf
    obtain f₉ : Frame (macR c.W y) s.mem s₉.mem := by rw [m₉]; exact f₇
    refine WP.mono (absTail_wp L (E.of_pk pk₉) hy (hP.of_eq pk₉.rd pk₉.wr)
      (by rw [u₉.other _ (by decide), u₈.other _ (by decide), U₇.saved _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h18])
      (by rw [u₉.other _ (by decide), r19₈]) r21₉ h0) fun s' A => ⟨pk₉.trans A.pk, f₉.trans A.frame, ?_⟩
    rw [A.out, ciph_keep L hy f₉, buf_keep hP hy f₉, m₉, Y₇, hb, ite_eq_right h0, Proof.Cmac.chain_append]

end VG.Proof.AesCcm.PPC64LE

end

end

/-!
# AES-CCM on PPC64LE: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by shifting `a` and storing
it byte-reversed (`stdbrx`), which is AArch64's `rev` and a shift the other
way (`Proof.AesCcm.byteRev64_shl`), so its blocks are the shared ones
(`Proof.AesCcm.enc_lo`, …) (`header_wp`); its length is in `r20`.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_lis wp_and wp_or wp_lsl wp_lsr wp_std wp_stb
  wp_sub wp_add)
open VG.Proof.Gather.PPC64LE (eval_zero copyBytes_wp)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (hdrLen length_bytesAt)
open VG.Proof.CmacAes.Stream.PPC64LE (upd_call)

theorem rev64_eq (a : BitVec 64) : rev64 a = byteRev64 a := rfl

/-- 16 bytes zeroed a doubleword at a time. -/
theorem zeros16_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 =
      Spec.Ccm.zeros 16 := by
  rw [Proof.AesCcm.bytesAt_writeW64_at _ _ (o := 8) _ (by decide) (by decide),
    Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide)]
  simp only [le8_zero, List.drop_append, List.take_append, List.drop_drop]
  simp [Spec.Ccm.zeros, length_bytesAt]

theorem lis_fffe : byteRev64 ((((0xfffe : BitVec 16) ++ (0 : BitVec 16)).signExtend 64) <<< 32) =
    BitVec.ofNat 64 0xfeff := by decide

/-- What `header` leaves. -/
structure HdrPost (c : Cx) (a : Nat) (s s' : State) : Prop where
  pk : PK s s'
  r18 : s'.gpr .r18 = s.gpr .r18
  r19 : s'.gpr .r19 = s.gpr .r19
  r20 : s'.gpr .r20 = BitVec.ofNat 64 (hdrLen a)
  frame : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a)

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`r19`) at its start, and its length in `r20`. -/
theorem header_wp {c : Cx} {s : State} (E : Env c s) {a : Nat} (ha : a < 2 ^ 64)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 a) : WP isa header s (HdrPost c a s) := by
  unfold header zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_std (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]; rfl) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add]; rfl)
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans (PK.ofUpd u₄)))
  obtain E₄ := E.of_pk pk₄
  obtain hm₄ : s₄.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr]; rfl
  obtain f₄ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [hm₄]; exact Proof.Cmac.frame_store2 _ _ _
  obtain z₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by rw [hm₄]; exact zeros16_bytes _ _
  obtain r18₄ : s₄.gpr .r18 = s.gpr .r18 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  obtain r19₄ : s₄.gpr .r19 = BitVec.ofNat 64 a := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h19]
  obtain r9₄ : s₄.gpr .r9 = BitVec.ofNat 64 (a / 2 ^ 32) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h19, VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat ha]
  -- Storing a doubleword at the start of the zeroed `B`.
  obtain stB : ∀ {t : State} (v : BitVec 64), PK s₄ t → t.mem = s₄.mem.writeW (c.W + BitVec.ofNat 64 32) v →
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧
        bytesAt t.mem (c.W + BitVec.ofNat 64 32) 16 = Proof.Cmac.le8 v ++ Spec.Ccm.zeros 8 := by
    intro t v _ hm
    obtain hc : Region.Contains ⟨c.W + BitVec.ofNat 64 32, 16⟩ (c.W + BitVec.ofNat 64 32) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    refine ⟨f₄.trans ?_, ?_⟩
    · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
    rw [hm, Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide), z₄]
    simp [Spec.Ccm.zeros]
  obtain inB : ∀ {t : State}, PK s₄ t → InRegions t.wr (c.W + BitVec.ofNat 64 32) 8 := fun k => by
    rw [k.wr]; exact E₄.perm.wW (by decide)
  refine WP.ite (decide (a / 2 ^ 32 = 0)) (eval_zero r9₄ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h₂ : a < 2 ^ 32 := by have := of_decide_eq_true ht; omega_arith
    refine WP.seq (wp_lsr (by decide) fun s₅ u₅ => wp_subi (by decide) (by decide) fun s₆ u₆ =>
      wp_lsr (by decide) fun s₇ u₇ => WP.block_nil ?_)
    obtain pk₇ : PK s₄ s₇ := (PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇))
    obtain r9₇ : s₇.gpr .r9 = BitVec.ofNat 64 (if a / 256 < 255 then 1 else 0) := by
      rw [u₇.gpr, u₆.gpr, u₅.gpr, r19₄, VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat ha,
        sub_sign (by omega_arith) (by decide)]
    obtain m₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
    obtain r19₇ : s₇.gpr .r19 = BitVec.ofNat 64 a := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), r19₄]
    obtain r18₇ : s₇.gpr .r18 = s.gpr .r18 := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), r18₄]
    refine WP.ite (decide ((if a / 256 < 255 then 1 else 0) = 0)) (eval_zero r9₇ (by split <;> decide))
      (fun ht' => ?_) (fun hf' => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      obtain h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_true ht'; split at this <;> simp_all <;> omega_arith
      refine wp_lsl (by decide) fun s₈ u₈ => wp_lis fun s₉ u₉ => wp_lsl (by decide) fun s₁₀ u₁₀ =>
        wp_or fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ => ?_
      obtain pk₁₂ : PK s₇ s₁₂ := (PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans
        ((PK.ofUpd u₁₁).trans (PK.ofUpd u₁₂))))
      refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 32) (by decide)
        (by rw [(pk₇.trans pk₁₂).gpr .r14 (by decide), E₄.r14, u₁₂.gpr]; rfl) (inB (pk₇.trans pk₁₂))
        fun s₁₃ u₁₃ => wp_li (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
      obtain pk : PK s₄ s₁₄ := pk₇.trans (pk₁₂.trans ((PK.ofMupd u₁₃).trans (PK.ofUpd u₁₄)))
      obtain hv : s₁₄.mem = s₄.mem.writeW (c.W + BitVec.ofNat 64 32)
          (byteRev64 (BitVec.ofNat 64 a) >>> 16 ||| BitVec.ofNat 64 0xfeff) := by
        rw [u₁₄.mem, u₁₃.mem, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₁₀.gpr, u₉.gpr,
          u₉.other _ (by decide), u₈.gpr, r19₇, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇, rev64_eq,
          Proof.AesCcm.byteRev64_or, show (16 : Nat) = 8 * 2 from rfl, Proof.AesCcm.byteRev64_shl _ (by decide),
          lis_fffe]
      obtain ⟨hf₁, hb₁⟩ := stB _ pk hv
      refine ⟨pk₄.trans pk, by rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
          u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), r18₇],
        by rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), r19₇, h19],
        by rw [u₁₄.gpr, Proof.AesCcm.hdrLen_mid h₁ h₂], hf₁, ?_⟩
      rw [hb₁]; exact Proof.AesCcm.enc_mid h₁ h₂ _ rfl
    · -- `[a]₁₆`.
      obtain h₁ : a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_false hf'; split at this <;> simp_all <;> omega_arith
      refine wp_lsl (by decide) fun s₈ u₈ => wp_li (by decide) fun s₉ u₉ => ?_
      obtain pk₉ : PK s₇ s₉ := (PK.ofUpd u₈).trans (PK.ofUpd u₉)
      refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 32) (by decide)
        (by rw [(pk₇.trans pk₉).gpr .r14 (by decide), E₄.r14, u₉.gpr]; rfl) (inB (pk₇.trans pk₉))
        fun s₁₀ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => WP.block_nil ?_
      obtain pk : PK s₄ s₁₁ := pk₇.trans (pk₉.trans ((PK.ofMupd u₁₀).trans (PK.ofUpd u₁₁)))
      obtain hv : s₁₁.mem = s₄.mem.writeW (c.W + BitVec.ofNat 64 32) (byteRev64 (BitVec.ofNat 64 a) >>> 48) := by
        rw [u₁₁.mem, u₁₀.mem, u₉.other _ (by decide), u₈.gpr, r19₇, u₉.mem, u₈.mem, m₇, rev64_eq,
          show (48 : Nat) = 8 * 6 from rfl, Proof.AesCcm.byteRev64_shl _ (by decide)]
      obtain ⟨hf₁, hb₁⟩ := stB _ pk hv
      refine ⟨pk₄.trans pk, by rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
          u₈.other _ (by decide), r18₇],
        by rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), r19₇, h19],
        by rw [u₁₁.gpr, Proof.AesCcm.hdrLen_lo h₁], hf₁, ?_⟩
      rw [hb₁]; exact Proof.AesCcm.enc_lo h₁ _ rfl
  · -- `0xff ‖ 0xff ‖ [a]₆₄`.
    obtain h₂ : ¬ a < 2 ^ 32 := by have := of_decide_eq_false hf; omega_arith
    obtain h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by omega_arith
    refine wp_li (by decide) fun s₅ u₅ => ?_
    refine wp_stb (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide)
      (by rw [u₅.other _ (by decide), E₄.r14]; rfl) (by rw [u₅.wr]; exact E₄.perm.wW (by decide)) fun s₆ u₆ => ?_
    refine wp_stb (a := c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 1) (by decide) (by decide)
      (by rw [u₆.gpr, u₅.other _ (by decide), E₄.r14, Offset.add_add]; rfl)
      (by rw [u₆.wr, u₅.wr, Offset.add_add]; exact E₄.perm.wW (by decide)) fun s₇ u₇ => ?_
    refine wp_li (by decide) fun s₈ u₈ => ?_
    refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2) (by decide)
      (by rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), E₄.r14, u₈.gpr, Offset.add_add]; rfl)
      (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, Offset.add_add]; exact E₄.perm.wW (by decide))
      fun s₉ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain pk : PK s₄ s₁₀ := (PK.ofUpd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofUpd u₈).trans
      ((PK.ofMupd u₉).trans (PK.ofUpd u₁₀)))))
    obtain r19₈ : s₈.gpr .r19 = BitVec.ofNat 64 a := by
      rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), r19₄]
    obtain hb : ((BitVec.ofNat 64 255).setWidth 8 : Byte) = 0xff := by decide
    obtain hm : s₁₀.mem = ((s₄.mem.writeW (c.W + BitVec.ofNat 64 32) (0xff : Byte)).writeW
        (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 1) (0xff : Byte)).writeW
        (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2) (byteRev64 (BitVec.ofNat 64 a)) := by
      rw [u₁₀.mem, u₉.mem, r19₈, u₈.mem, u₇.mem, u₆.mem, u₆.gpr, u₅.gpr, u₅.mem, hb, rev64_eq]
    refine ⟨pk₄.trans pk, by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr,
        u₅.other _ (by decide), r18₄],
      by rw [u₁₀.other _ (by decide), u₉.gpr, r19₈, h19],
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
      ∀ r ∈ [Reg.r18, .r19, .r20, .r21], s'.gpr r = s.gpr r := by
  unfold updBlock updArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by decide) (by omega_arith) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ =>
    wp_li (by decide) fun s₆ u₆ => WP.block_nil ?_)
  obtain pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  obtain E₆ := E.of_pk pk₆
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain U := uargs L E₆ (y := y) (by omega_arith) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₆.perm (by decide)) (L.w_w (by omega_arith) (by decide) (by omega_arith)) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.r16])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.r17])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₆.gpr])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
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

/-- The end of `minK`: `r21 := min (b, 16 − h)` for `b ≤ 16` in `r10`. -/
theorem minRest_wp {s : State} {h b : Nat} (h20 : s.gpr .r20 = BitVec.ofNat 64 h)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 b) (hh : h ≤ 16) (hb : b ≤ 16) :
    WP isa (.seq (.block [.li .r9 16, .sub .r9 .r9 .r20, .sub .r11 .r10 .r9, .lsr .d .r11 .r11 63])
      (.ite (.zero .d .r11) (.block [Impl.AesCbc.PPC64LE.mov .r21 .r9])
        (.block [Impl.AesCbc.PPC64LE.mov .r21 .r10]))) s fun s' =>
      PK s s' ∧ s'.mem = s.mem ∧ s'.gpr .r21 = BitVec.ofNat 64 (min b (16 - h)) ∧
        ∀ r ∈ [Reg.r18, .r19, .r20], s'.gpr r = s.gpr r := by
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_sub fun s₃ u₃ =>
    wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_)
  obtain pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r9₄ : s₄.gpr .r9 = BitVec.ofNat 64 (16 - h) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h20,
      ofNat_sub_ofNat' hh (by decide)]
  obtain r10₄ : s₄.gpr .r10 = BitVec.ofNat 64 b := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h10]
  obtain r11₄ : s₄.gpr .r11 = BitVec.ofNat 64 (if b < 16 - h then 1 else 0) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h10, h20, ofNat_sub_ofNat' hh (by decide), sub_sign (by omega_arith) (by omega_arith)]
  obtain keep₄ : ∀ r ∈ [Reg.r18, .r19, .r20], s₄.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine WP.ite (decide ((if b < 16 - h then 1 else 0) = 0)) (eval_zero r11₄ (by split <;> decide))
    (fun ht => ?_) (fun hf => ?_)
  · have hge : ¬ b < 16 - h := by have := of_decide_eq_true ht; split at this <;> simp_all
    refine wp_mv fun s₅ u₅ => WP.block_nil ⟨pk₄.trans (PK.ofUpd u₅), by rw [u₅.mem, m₄], ?_, fun r hr => ?_⟩
    · rw [u₅.gpr, r9₄, Nat.min_eq_right (by omega_arith)]
    · rw [u₅.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
        keep₄ r hr]
  · have hlt : b < 16 - h := by have := of_decide_eq_false hf; split at this <;> simp_all
    refine wp_mv fun s₅ u₅ => WP.block_nil ⟨pk₄.trans (PK.ofUpd u₅), by rw [u₅.mem, m₄], ?_, fun r hr => ?_⟩
    · rw [u₅.gpr, r10₄, Nat.min_eq_left (by omega_arith)]
    · rw [u₅.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
        keep₄ r hr]

/-- `minK`: `r21 = min (a, 16 − h)` for `h ≤ 16` in `r20` and `a` in `r19`. -/
theorem minK_wp {s : State} {h a : Nat} (h20 : s.gpr .r20 = BitVec.ofNat 64 h)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 a) (hh : h ≤ 16) (ha : a < 2 ^ 64) :
    WP isa minK s fun s' =>
      PK s s' ∧ s'.mem = s.mem ∧ s'.gpr .r21 = BitVec.ofNat 64 (min a (16 - h)) ∧
        ∀ r ∈ [Reg.r18, .r19, .r20], s'.gpr r = s.gpr r := by
  unfold minK
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain r10₁ : s₁.gpr .r10 = BitVec.ofNat 64 (a / 2 ^ 4) := by
    rw [u₁.gpr, h19, VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat ha]
  obtain k₁ : ∀ r ∈ [Reg.r18, .r19, .r20], s₁.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [u₁.other _ (by decide)]
  obtain fin : ∀ {t : State} {b : Nat}, PK s t → t.mem = s.mem → (∀ r ∈ [Reg.r18, .r19, .r20], t.gpr r = s.gpr r) →
      t.gpr .r10 = BitVec.ofNat 64 b → b = min a 16 →
      WP isa (.seq (.block [.li .r9 16, .sub .r9 .r9 .r20, .sub .r11 .r10 .r9, .lsr .d .r11 .r11 63])
        (.ite (.zero .d .r11) (.block [Impl.AesCbc.PPC64LE.mov .r21 .r9])
          (.block [Impl.AesCbc.PPC64LE.mov .r21 .r10]))) t fun s' =>
        PK s s' ∧ s'.mem = s.mem ∧ s'.gpr .r21 = BitVec.ofNat 64 (min a (16 - h)) ∧
          ∀ r ∈ [Reg.r18, .r19, .r20], s'.gpr r = s.gpr r := by
    intro t b pk hm hk h10 hb
    refine WP.mono (minRest_wp (by rw [hk .r20 (by simp), h20]) h10 hh (by omega_arith)) fun s' ⟨pk', hm', h21, hk'⟩ =>
      ⟨pk.trans pk', by rw [hm', hm], by rw [h21, hb]; congr 1; omega_arith, fun r hr => by rw [hk' r hr, hk r hr]⟩
  refine WP.seq (WP.ite (decide (a / 2 ^ 4 = 0)) (eval_zero r10₁ (by omega_arith)) (fun ht => ?_) (fun hf => ?_))
  · have h16 : a < 16 := by have := of_decide_eq_true ht; omega_arith
    refine wp_mv fun s₂ u₂ => WP.block_nil ?_
    exact fin ((PK.ofUpd u₁).trans (PK.ofUpd u₂)) (by rw [u₂.mem, u₁.mem])
      (fun r hr => by
        rw [u₂.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
          k₁ r hr])
      (by rw [u₂.gpr, u₁.other _ (by decide), h19]) (by omega_arith)
  · have h16 : 16 ≤ a := by have := of_decide_eq_false hf; omega_arith
    refine wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_
    exact fin ((PK.ofUpd u₁).trans (PK.ofUpd u₂)) (by rw [u₂.mem, u₁.mem])
      (fun r hr => by
        rw [u₂.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
          k₁ r hr])
      u₂.gpr (by omega_arith)

/-! ## The first block of the associated data -/

theorem hdrLen_ge (a : Nat) : 2 ≤ hdrLen a := by
  unfold hdrLen; split <;> [omega_arith; split <;> omega_arith]

/-- What `aadHead` leaves: its block chained, and the rest of the data. -/
structure HeadPost (c : Cx) (y : Nat) (P : Addr) (a : Nat) (s : State) (Y : List Byte) (s' : State) : Prop where
  abs : Absorbed c y s Y s'
  r18 : s'.gpr .r18 = P + BitVec.ofNat 64 (Proof.AesCcm.headLen a)
  r19 : s'.gpr .r19 = BitVec.ofNat 64 (a - Proof.AesCcm.headLen a)

/-- The first block of the `a > 0` bytes of associated data at `P`: the
encoding of its length followed by its first `headLen a` bytes, padded,
chained into the MAC state at `W + y`. -/
theorem aadHead_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {a : Nat} (hP : Buf c s P a) (h18 : s.gpr .r18 = P) (h19 : s.gpr .r19 = BitVec.ofNat 64 a)
    (ha0 : 0 < a) :
    WP isa (aadHead y) s (HeadPost c y P a s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem P a).take (Proof.AesCcm.headLen a))])) := by
  have hl := hP.lt
  obtain hh := Proof.AesCcm.hdrLen_le a
  obtain hh2 := hdrLen_ge a
  generalize hk : Proof.AesCcm.headLen a = k
  have hk' : k = min a (16 - hdrLen a) := hk.symm
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hkh : hdrLen a + k ≤ 16 := by omega_arith
  unfold aadHead
  refine WP.seq (WP.mono (header_wp E hl h19) fun s₁ H => ?_)
  obtain E₁ := E.of_pk H.pk
  refine WP.seq (WP.mono (minK_wp H.r20 (by rw [H.r19, h19]) (by omega_arith) hl)
    fun s₂ ⟨pk₂, m₂, r21₂, k₂⟩ => ?_)
  obtain E₂ := E₁.of_pk pk₂
  refine WP.seq (wp_add fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_)
  obtain pk₆ : PK s₂ s₆ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))
  obtain E₆ := E₂.of_pk pk₆
  obtain m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
  obtain hd : (⟨P, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 (32 + hdrLen a), k⟩ :=
    (hP.take (by omega_arith)).wd (by omega_arith)
  obtain hb : VG.Proof.Gather.PPC64LE.BytesPre s₆ P (c.W + BitVec.ofNat 64 (32 + hdrLen a)) k :=
    { r3 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        k₂ .r18 (by simp), H.r18, h18]
      r9 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, k₂ .r20 (by simp), H.r20, E₂.r14,
          Offset.add_add]
        congr 2
        unfold bO; omega_arith
      r4 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r21₂, hk']
      pos := hk1
      lt := by omega_arith
      rd := by rw [pk₆.rd, pk₂.rd, H.pk.rd, pk₆.wr, pk₂.wr, H.pk.wr]; exact (hP.take (by omega_arith)).rd
      wr := E₆.perm.wC (by omega_arith)
      disj := hd }
  refine WP.seq (WP.mono (copyBytes_wp s₆ hb) fun s₇ ⟨hm₇, _, k₇⟩ => ?_)
  obtain hx : bytesAt s₆.mem P k = (bytesAt s.mem P a).take k := by
    rw [m₆, Proof.Cmac.bytesAt_frame H.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hP.take (by omega_arith)).wd (by decide)) (by omega_arith),
      bytesAt_prefix _ _ (by omega_arith : k ≤ a)]
  refine WP.seq (wp_add fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_)
  obtain pk₉ : PK s s₉ := H.pk.trans (pk₂.trans (pk₆.trans ((PK.ofKeeps k₇).trans ((PK.ofUpd u₈).trans
    (PK.ofUpd u₉)))))
  obtain m₉ : s₉.mem = writeBytes s₁.mem (c.W + BitVec.ofNat 64 (32 + hdrLen a)) ((bytesAt s.mem P a).take k) := by
    rw [u₉.mem, u₈.mem, hm₇, hx, m₆]
  obtain hxl : ((bytesAt s.mem P a).take k).length = k := by rw [List.length_take, length_bytesAt]; omega_arith
  -- `B` holds the encoding of the length, then the data, then zeros.
  obtain hB : bytesAt s₉.mem (c.W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem P a).take k) := by
    obtain he := Proof.AesCcm.length_encodeLen a
    rw [m₉, show c.W + BitVec.ofNat 64 (32 + hdrLen a) = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a)
        from (Offset.add_add _ _ _).symm,
      Proof.AesCcm.bytesAt_writeBytes_at _ _ (o := hdrLen a) (n := 16) _ (by rw [hxl]; omega_arith) (by decide), H.out,
      hxl]
    obtain e1 : (Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a)).take (hdrLen a) = Spec.Ccm.encodeLen a :=
      List.take_left' he
    obtain e2 : (Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a)).drop (hdrLen a + k) =
        Spec.Ccm.zeros (16 - (hdrLen a + k)) := by
      rw [show hdrLen a + k = (Spec.Ccm.encodeLen a).length + k by rw [he], List.drop_append]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by omega_arith), List.nil_append, he]
      congr 1; omega_arith
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem P a).take k)
      (by rw [List.length_append, he, hxl]; omega_arith) with e | e
    · rw [e1, e2, e, List.length_append, he, hxl, List.append_assoc]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, he]; simp; omega_arith)
  obtain f₉ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₉.mem := by
    rw [m₉]
    refine H.frame.trans (writeBytes_frame _ _ _ ?_)
    rw [hxl]
    simp only [Region.Contains]
    rw [← Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  obtain E₉ := E.of_pk pk₉
  refine WP.mono (updBlock_wp L E₉ hy) fun s' ⟨A, ka⟩ => ⟨⟨pk₉.trans A.pk, ?_, ?_⟩, ?_, ?_⟩
  · exact (f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans A.frame
  · have hY : bytesAt s₉.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
      Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) (by omega_arith) (by decide)) (by decide)
    obtain hK : Spec.Ccm.ctxCiph s₉.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R :=
      ciph_keep L hy (f₉.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    rw [A.out, hY, hK, hB]
  · have r21₇ : s₇.gpr .r21 = BitVec.ofNat 64 k := by
      rw [k₇.gpr _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), r21₂, hk']
    rw [ka .r18 (by simp), u₉.other _ (by decide), u₈.gpr, r21₇, k₇.gpr _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ .r18 (by simp), H.r18, h18, hk]
  · have r21₈ : s₈.gpr .r21 = BitVec.ofNat 64 k := by
      rw [u₈.other _ (by decide), k₇.gpr _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), r21₂, hk']
    rw [ka .r19 (by simp), u₉.gpr, r21₈, u₈.other _ (by decide), k₇.gpr _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ .r19 (by simp), H.r19, h19,
      ofNat_sub_ofNat' (by omega_arith) hl, hk]

end VG.Proof.AesCcm.PPC64LE
