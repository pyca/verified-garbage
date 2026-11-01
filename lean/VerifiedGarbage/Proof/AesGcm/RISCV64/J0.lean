module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCtr.Inc
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Spec.Ctr
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesCtr.RISCV64.Words
import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/J0.lean`): `j0` writes `J₀` for the `r25`-byte nonce at
`r24` to the state: its words and `0x00000001` for a 12-byte nonce
(`j012_ok`), and otherwise GHASH of the nonce padded with zeros and the
lengths block, with `absorb`, `flush` and `lens` on the accumulator at the
state's first block (`j0hash_ok`), the nonce's length in `r18`. `initState`
then zeroes the accumulator and writes the first counter block `inc₃₂(J₀)`
(`initState_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem ww32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- The bytes of a list, read back. -/
theorem bytesAt_of_get {m : Mem} {p : Addr} {l : List Byte}
    (h : ∀ j < l.length, m (p + BitVec.ofNat 64 j) = l.getD j 0) : bytesAt m p l.length = l := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h i h₂]
  simp [List.getD_eq_getElem?_getD, h₂]

/-- The bytes of a word copied with `ld`/`sd`. -/
theorem bytesAt_writeW64 (m m' : Mem) (a b : Addr) :
    bytesAt (m.writeW a (m'.readW b 64)) a 8 = bytesAt m' b 8 := by
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  exact writeW_readW_byte m m' a b (List.mem_range.mp hj)

/-- The bytes of a word copied with `lwu`/`sw`. -/
theorem bytesAt_writeW32 (m m' : Mem) (a b : Addr) :
    bytesAt (m.writeW a (((m'.readW b 32).setWidth 64).setWidth 32)) a 4 = bytesAt m' b 4 := by
  rw [ww32]
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [Mem.readW_byte (m.writeW a (m'.readW b 32)) a hj, Mem.readW_writeW_self32, ← Mem.readW_byte m' b hj]

/-- The bytes `storeBE 4` stores: the word's, big-endian. -/
theorem beBytes4_eq (x : BitVec 64) : ByteLoad.beBytes 4 x = Spec.Ctr.ofNat x.toNat 4 := by
  unfold ByteLoad.beBytes Spec.Ctr.ofNat
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- `inc₃₂` of a block: its first 12 bytes, and its last 32 bits plus one,
big-endian. -/
theorem inc32_bytes {t : List Byte} (ht : t.length = 16) {w : BitVec 32}
    (hw : Proof.AesCtr.lo32 t = w.toNat) :
    ofBytes (t.take 12 ++ ByteLoad.beBytes 4 (w.setWidth 64 + BitVec.ofNat 64 1)) = inc32 (ofBytes t) := by
  have ht' : t = t.take 12 ++ t.drop 12 := (List.take_append_drop 12 t).symm
  have hA : Spec.Ctr.toNat (t.take 12) < 256 ^ (t.take 12).length := Proof.AesCcm.beVal_lt _
  have hB : Spec.Ctr.toNat (t.drop 12) < 256 ^ (t.drop 12).length := Proof.AesCcm.beVal_lt _
  simp only [List.length_take, List.length_drop, ht] at hA hB
  have hT : Spec.Ctr.toNat t = Spec.Ctr.toNat (t.take 12) * 2 ^ 32 + Spec.Ctr.toNat (t.drop 12) := by
    conv => lhs; rw [ht']
    rw [Proof.AesCtr.toNat_append, List.length_drop, ht]
  have hW : Spec.Ctr.toNat (t.drop 12) = w.toNat := by
    rw [← hw, Proof.AesCtr.lo32, hT]; omega_arith
  have hx : (w.setWidth 64 + BitVec.ofNat 64 1).toNat = w.toNat + 1 := by
    have := w.isLt
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show w.toNat < 2 ^ 64 by omega)]
    show (w.toNat + 1) % 2 ^ 64 = _
    omega_arith
  apply BitVec.eq_of_toNat_eq
  rw [Proof.AesCcm.toNat_inc32]
  show (BitVec.ofNat 128 (Spec.Ctr.toNat _)).toNat =
    (BitVec.ofNat 128 (Spec.Ctr.toNat t)).toNat / 2 ^ 32 * 2 ^ 32 +
      ((BitVec.ofNat 128 (Spec.Ctr.toNat t)).toNat % 2 ^ 32 + 1) % 2 ^ 32
  rw [Proof.AesCtr.toNat_append, beBytes4_eq, Proof.AesCtr.length_ofNat, Proof.AesCtr.toNat_ofNat, hx,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, hT, hW]
  have := w.isLt
  omega_arith

/-- The regions `j0` writes. -/
abbrev j0Frame (st w sp : Addr) : List Region :=
  [⟨st, 80⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩, below sp 2048]

/-- Before `j0`: the `n`-byte nonce at `Np`, its length also in `s7`. -/
structure J0In (V : Reg → BitVec 64) (sp : Addr) (H : Block) (Np : Addr) (n : Nat) (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  s4 : s.gpr .s4 = Np
  s5 : s.gpr .s5 = BitVec.ofNat 64 n
  s7 : V .s7 = BitVec.ofNat 64 n
  data : DataOk (V .s1) (V .s0) s Np n

/-- `J₀` written, from `m₀`. -/
structure J0Mid (V : Reg → BitVec 64) (sp : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (V .s1) = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame (V .s1) (V .s0) sp) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (V : Reg → BitVec 64) (sp : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (V .s1) = Spec.Gcm.j0 H iv
  y : blockAt s.mem (V .s1 + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame (V .s1) (V .s0) sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨V .s1 + BitVec.ofNat 64 d, k⟩] m m')
    (hk : d + k ≤ 80) : Frame (j0Frame (V .s1) (V .s0) sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

omit L in
theorem cont_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (h₃ : e + k < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n :=
  Offset.contains p h₁ h₂ h₃

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : Addr} {s : State} (h : J0In V sp H Np 12 s) :
    WP isa (.block j012) s (J0Mid V sp H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have hst := he.s1
  have hd := h.data
  have h24 := h.s4
  refine WP.block_append (WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s4) (dst := .s1) (soff := 0)
    (doff := 0) (n := 12) (by decide) (by decide) (by decide) (by decide) (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi hc => ?_)) fun s₁ c => ?_)
  · rw [h24, Nat.zero_add]; exact in_off hd.rd (d := i) (n := 1) (by omega) (by decide)
  · rw [hst, Nat.zero_add]; exact he.perm.stW (by omega)
  · rw [hst, h24, Nat.zero_add, add_ofNat_zero] at hc
    refine hd.st (Np + BitVec.ofNat 64 i) (Offset.contains_base Np (by omega) (by omega)) ?_
    exact Lay.stSub (S := V .s1) (d := 0) (n := 12) (by decide) _ (by rw [add_ofNat_zero]; exact hc)
  have g1 : s₁.gpr .s1 = V .s1 := (c.gpr _ (by decide)).trans hst
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t0) (dst := .s1) (doff := 12) (bs := [0, 0, 0, 1])
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₂ c₂ => ?_
  · rw [g1, c.wr]; simp only [List.length_cons, List.length_nil] at hi; exact he.perm.stW (by omega)
  have c₂f : Frame [⟨V .s1 + BitVec.ofNat 64 12, 4⟩] s₁.mem s₂.mem := by
    have := c₂.frame; rwa [g1] at this
  have c₂s : ∀ j < 4, s₂.mem (V .s1 + BitVec.ofNat 64 (12 + j)) = BitVec.ofNat 8 ([0, 0, 0, 1].getD j 0) :=
    fun j hj => by have := c₂.stored j hj; rwa [g1] at this
  have f₁ : Frame [⟨V .s1 + BitVec.ofNat 64 0, 80⟩] s.mem s₂.mem := by
    have a := c.frame; have b := c₂f
    rw [hst] at a
    refine (a.sub fun r hr => ?_).trans (b.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hb₁ : bytesAt s₂.mem (V .s1) 12 = bytesAt s.mem Np 12 := by
    rw [bytesAt_frame c₂f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.st_st (st := V .s1) (a := 0) (n := 12) (d := 12) (k := 4) (.inl (by decide))
        (by decide) (by decide)) (by decide)]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := c.copied i (List.mem_range.mp hi)
    simp only [hst, h24, Nat.zero_add] at this; exact this
  have hb₂ : bytesAt s₂.mem (V .s1 + BitVec.ofNat 64 12) 4 = [0, 0, 0, 1] := by
    refine bytesAt_of_get (l := [0, 0, 0, 1]) fun j hj => ?_
    rw [add_ofNat_assoc, c₂s j hj]
    have e : ∀ j < 4, BitVec.ofNat 8 ([0, 0, 0, 1].getD j 0) = ([0, 0, 0, 1] : List Byte).getD j 0 := by
      decide
    exact e j hj
  refine ⟨he.keep (fun r hr => (c₂.gpr r (by revert r; decide)).trans (c.gpr r (by revert r; decide)))
      (c₂.sp.trans c.sp) (c₂.rd.trans c.rd) (c₂.wr.trans c.wr), ?_, ?_, st_j0Frame f₁ (by decide)⟩
  · rw [blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, show (16 : Nat) = 12 + 4 from rfl, bytesAt_add,
      hb₁, hb₂]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : J0Mid V sp H iv m₀ s) :
    WP isa (.block initState) s (J0Out V sp H iv m₀) := by
  have he := h.env
  have hst := he.s1
  simp only [initState, List.append_assoc, List.cons_append, List.nil_append]
  refine Steps.wp_ld (off := 0) (a := V .s1 + BitVec.ofNat 64 0) (by decide) (by rw [hst])
    (L.stal (by decide) (by decide)) (he.perm.stR (by decide)) fun s₁ u₁ => ?_
  have g₁ : s₁.gpr .s1 = V .s1 := (u₁.other _ (by decide)).trans hst
  refine Steps.wp_sd (off := 48) (a := V .s1 + BitVec.ofNat 64 48) (by decide) (by rw [g₁])
    (L.stal (by decide) (by decide)) (by rw [u₁.wr]; exact he.perm.stW (by decide)) fun s₂ u₂ => ?_
  have g₂ : s₂.gpr .s1 = V .s1 := by rw [u₂.gpr]; exact g₁
  refine Steps.wp_lwu (off := 8) (a := V .s1 + BitVec.ofNat 64 8) (by decide) (by rw [g₂])
    (L.stal4 (by decide) (by decide)) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact he.perm.stR (by decide))
    fun s₃ u₃ => ?_
  have g₃ : s₃.gpr .s1 = V .s1 := (u₃.other _ (by decide)).trans g₂
  refine Steps.wp_sw (off := 56) (a := V .s1 + BitVec.ofNat 64 56) (by decide) (by rw [g₃])
    (L.stal4 (by decide) (by decide)) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact he.perm.stW (by decide))
    fun s₄ u₄ => ?_
  have g₄ : s₄.gpr .s1 = V .s1 := by rw [u₄.gpr]; exact g₃
  have k₄ : s₄.rd = s.rd ∧ s₄.wr = s.wr ∧ s₄.sp = s.sp :=
    ⟨by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
      by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩
  have hm₄ : s₄.mem = (s.mem.writeW (V .s1 + BitVec.ofNat 64 48) (s.mem.readW (V .s1 + BitVec.ofNat 64 0) 64)).writeW
      (V .s1 + BitVec.ofNat 64 56) ((((s.mem.writeW (V .s1 + BitVec.ofNat 64 48)
        (s.mem.readW (V .s1 + BitVec.ofNat 64 0) 64)).readW (V .s1 + BitVec.ofNat 64 8) 32).setWidth 64).setWidth 32) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE32_ok (d := .a0) (tmp := .t0) (n := .s1) (off := 12) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₄, k₄.1, k₄.2.1]; exact he.perm.stR (show 12 + 4 ≤ 80 by decide)))
    fun s₅ e₅ => ?_
  subst e₅
  rw [g₄]
  refine Steps.wp_addi (imm := 1) (by decide) fun s₆ u₆ => ?_
  have g₆ : s₆.gpr .s1 = V .s1 := by
    rw [u₆.other _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), g₄]
  have a₆ : s₆.gpr .a0 = (ByteLoad.beWord s₄.mem (V .s1) 12).setWidth 64 + BitVec.ofNat 64 1 := by
    rw [u₆.gpr, RegUpd.gpr_write_self]
  have w₆ : s₆.wr = s.wr := by rw [u₆.wr]; exact k₄.2.1
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (v := .a0) (tmp := .t0) (n := .s1) (off := 60) (w := 4) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun j hj => by
      rw [g₆, w₆]; exact he.perm.stW (d := 60 + j) (n := 1) (by omega)) fun s₇ e₇ => ?_
  have g₇ : s₇.gpr .s1 = V .s1 := by rw [e₇, RegUpd.gpr_write_of_ne _ _ (by decide)]; exact g₆
  have w₇ : s₇.wr = s.wr := by rw [e₇]; exact w₆
  refine Steps.wp_li (imm := 0) (by decide) fun s₈ u₈ => ?_
  have g₈ : s₈.gpr .s1 = V .s1 := (u₈.other _ (by decide)).trans g₇
  refine Steps.wp_sd (off := 16) (a := V .s1 + BitVec.ofNat 64 16) (by decide) (by rw [g₈])
    (L.stal (by decide) (by decide)) (by rw [u₈.wr, w₇]; exact he.perm.stW (by decide)) fun s₉ u₉ => ?_
  refine Steps.wp_sd (off := 24) (a := V .s1 + BitVec.ofNat 64 24) (by decide) (by rw [u₉.gpr, g₈])
    (L.stal (by decide) (by decide)) (by rw [u₉.wr, u₈.wr, w₇]; exact he.perm.stW (by decide))
    fun s₁₀ u₁₀ => WP.block_nil ?_
  -- The memories.
  generalize hM2 : s.mem.writeW (V .s1 + BitVec.ofNat 64 48) (s.mem.readW (V .s1 + BitVec.ofNat 64 0) 64) = M2
    at hm₄
  generalize hx : (ByteLoad.beWord s₄.mem (V .s1) 12).setWidth 64 + BitVec.ofNat 64 1 = x at a₆
  have m₇ : s₇.mem = writeBytes s₄.mem (V .s1 + BitVec.ofNat 64 60) (ByteLoad.beBytes 4 x) := by
    rw [e₇, RegUpd.mem_write]
    show writeBytes s₆.mem (s₆.gpr .s1 + BitVec.ofNat 64 60) (ByteLoad.beBytes 4 (s₆.gpr .a0)) = _
    rw [g₆, a₆, u₆.mem]; rfl
  have m₁₀ : s₁₀.mem = (s₇.mem.writeW (V .s1 + BitVec.ofNat 64 16) (0 : BitVec 64)).writeW
      (V .s1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₀.mem, u₉.gpr, u₉.mem, u₈.gpr, u₈.mem, add_ofNat_assoc]; rfl
  have c48 : (⟨V .s1 + BitVec.ofNat 64 48, 16⟩ : Region).Contains (V .s1 + BitVec.ofNat 64 48) 8 :=
    cont_off _ (by decide) (by decide) (by decide)
  have f₂ : Frame [⟨V .s1 + BitVec.ofNat 64 48, 16⟩] s.mem M2 := by
    rw [← hM2]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c48
  have f₂₄ : Frame [⟨V .s1 + BitVec.ofNat 64 56, 4⟩] M2 s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₄₇ : Frame [⟨V .s1 + BitVec.ofNat 64 60, 4⟩] s₄.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (Region.contains_self _ _)
  have f₇ : Frame [⟨V .s1 + BitVec.ofNat 64 16, 16⟩] s₇.mem s₁₀.mem := by
    rw [m₁₀]; exact Proof.Cmac.frame_store2 _ _ _
  have f₄ : Frame [⟨V .s1 + BitVec.ofNat 64 48, 16⟩] s.mem s₄.mem :=
    f₂.trans (f₂₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
  have ff : Frame [⟨V .s1 + BitVec.ofNat 64 0, 80⟩] s.mem s₁₀.mem := by
    have h₁ : Frame [⟨V .s1 + BitVec.ofNat 64 0, 80⟩] s.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have h₂ : Frame [⟨V .s1 + BitVec.ofNat 64 0, 80⟩] s₄.mem s₇.mem := f₄₇.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have h₃ : Frame [⟨V .s1 + BitVec.ofNat 64 0, 80⟩] s₇.mem s₁₀.mem := f₇.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    exact (h₁.trans h₂).trans h₃
  have dst : ∀ {a n d k : Nat}, a + n ≤ d ∨ d + k ≤ a → a + n ≤ 80 → d + k ≤ 80 →
      ∀ r ∈ [(⟨V .s1 + BitVec.ofNat 64 d, k⟩ : Region)], (⟨V .s1 + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r :=
    fun h₁ h₂ h₃ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st h₁ h₂ h₃
  have dst0 : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 80 →
      ∀ r ∈ [(⟨V .s1 + BitVec.ofNat 64 d, k⟩ : Region)], (⟨V .s1, 16⟩ : Region).Disjoint r :=
    fun h₁ h₂ r hr => by
      have := dst (a := 0) (n := 16) (.inl h₁) (by decide) h₂ r hr
      rwa [add_ofNat_zero] at this
  have hJ : blockAt s₁₀.mem (V .s1) = blockAt s.mem (V .s1) := by
    rw [blockAt_frame f₇ (dst0 (by decide) (by decide)), blockAt_frame f₄₇ (dst0 (by decide) (by decide)),
      blockAt_frame f₄ (dst0 (by decide) (by decide))]
  have hg : ∀ r, r ≠ .t0 → r ≠ .a0 → s₁₀.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ h₁, e₇, RegUpd.gpr_write_of_ne _ _ h₁]
    show s₆.gpr r = _
    rw [u₆.other _ h₂, RegUpd.gpr_write_of_ne _ _ h₂, RegUpd.gpr_write_of_ne _ _ h₁, u₄.gpr, u₃.other _ h₁,
      u₂.gpr, u₁.other _ h₁]
  have hw : ByteLoad.beWord s₄.mem (V .s1) 12 = ByteLoad.beWord s.mem (V .s1) 12 := by
    rw [Proof.Aes.RISCV64.beWord_eq, Proof.Aes.RISCV64.beWord_eq,
      f₄.readW (Region.contains_self _ _) (dst (by decide) (by decide) (by decide)) (by decide)]
  have hb₄ : bytesAt s₄.mem (V .s1 + BitVec.ofNat 64 48) 12 = bytesAt s.mem (V .s1) 12 := by
    rw [show (12 : Nat) = 8 + 4 from rfl, bytesAt_add, bytesAt_add, add_ofNat_assoc,
      bytesAt_frame f₂₄ (dst (by decide) (by decide) (by decide)) (by decide), hm₄, bytesAt_writeW32, ← hM2,
      bytesAt_writeW64, add_ofNat_zero,
      bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c48)
        (dst (by decide) (by decide) (by decide)) (by decide)]
  have hcb : bytesAt s₁₀.mem (V .s1 + BitVec.ofNat 64 48) 16 =
      (bytesAt s.mem (V .s1) 16).take 12 ++ ByteLoad.beBytes 4 x := by
    rw [bytesAt_frame f₇ (dst (by decide) (by decide) (by decide)) (by decide),
      show (16 : Nat) = 12 + 4 from rfl, bytesAt_add, bytesAt_add, add_ofNat_assoc,
      bytesAt_frame f₄₇ (dst (by decide) (by decide) (by decide)) (by decide), hb₄, m₇,
      bytesAt_writeBytes_self' _ _ (ByteLoad.beBytes_length _ _) (by decide),
      List.take_left' (length_bytesAt _ _ _)]
  refine ⟨he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
      (by rw [u₁₀.sp, u₉.sp, u₈.sp, e₇]; show s₆.sp = _; rw [u₆.sp]; exact k₄.2.2)
      (by rw [u₁₀.rd, u₉.rd, u₈.rd, e₇]; show s₆.rd = _; rw [u₆.rd]; exact k₄.1)
      (by rw [u₁₀.wr, u₉.wr, u₈.wr, w₇]), ?_, by rw [hJ, h.j0], ?_, ?_, h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, m₁₀, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · rw [blockAt, hcb, ← hx, hw, inc32_bytes (length_bytesAt _ _ _)
      (Proof.AesCtr.RISCV64.lo32_beWord s.mem (V .s1)), ← blockAt, h.j0]

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame (V .s1) (V .s0) 0 sp) m m') :
    Frame (j0Frame (V .s1) (V .s0) sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame (V .s1) (V .s0) 0 sp) m m') :
    Frame (j0Frame (V .s1) (V .s0) sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- The first block of `j0hash`: the accumulator at the state zeroed. -/
theorem j0zero_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) :
    WP isa (.block [.li .t0 0, .store .d .t0 .s1 0, .store .d .t0 .s1 8, .li .s6 0]) s
      (fun s' => AbsIn V sp 0 H [] Np n s' ∧
        blockAt s'.mem (V .s1 + BitVec.ofNat 64 0) = 0 ∧
        bytesAt s'.mem Np n = bytesAt s.mem Np n ∧
        Frame [⟨V .s1 + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem) := by
  have he := h.env
  have hd := h.data
  have h30 := he.s1
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have a₀ := L.stal (d := 0) (by decide) (by decide)
  have a₁ := L.stal (d := 8) (by decide) (by decide)
  have hrun : WP isa (.block [.li .t0 0, .store .d .t0 .s1 0, .store .d .t0 .s1 8, .li .s6 0]) s
      fun s' => s'.mem = (s.mem.writeW (V .s1 + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
          (V .s1 + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s'.gpr .s6 = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .t0 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
    simp only [add_ofNat_zero] at z₀ a₀ ⊢
    crun [Int.reduceNatCast', h30, z₀, z₁, a₀, a₁, write_8]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl⟩⟩
  refine WP.mono hrun fun s₁ ⟨hm₁, h26, hg₁, hk₁⟩ => ?_
  have f₁ : Frame [⟨V .s1 + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ r ∈ [(⟨V .s1 + BitVec.ofNat 64 0, 16⟩ : Region)], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hd.st.sub_right (Lay.stSub (by decide))
  refine ⟨⟨he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr,
    by rw [hg₁ _ (by decide) (by decide), h.s4], by rw [hg₁ _ (by decide) (by decide), h.s5],
    by rw [h26]; rfl, hd.of_eq hk₁.rd hk₁.wr hk₁.sp, ?_⟩, ?_, bytesAt_frame f₁ dD (by have := hd.lt; omega), f₁⟩
  · rw [blockAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) (hn : n ≠ 12) :
    WP isa j0hash s (J0Mid V sp H (bytesAt s.mem Np n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt
  refine WP.seq (WP.mono (j0zero_ok L h) fun s₁ ⟨hai, hY₁, hiv, f₁⟩ => ?_)
  refine WP.seq (WP.mono (absorb_ok L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  have hab₂ := ho.abs (Proof.Gcm.absorbed_nil H hY₁)
  have he₂ := ho.env
  have hH₂ : blockAt s₂.mem (V .s2 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inl rfl) hai.env.stk'), hai.hH]
  have h18 : s₂.gpr .s7 = BitVec.ofNat 64 n := he₂.fr _ (by decide) |>.trans h.s7
  have h₃ : WP isa (.block [.logicImm .and .s6 .s7 15]) s₂ fun s₃ =>
      s₃.gpr .s6 = BitVec.ofNat 64 (n % 16) ∧ (∀ r, r ≠ .s6 → s₃.gpr r = s₂.gpr r) ∧
        Keeps s₂ s₃ := by
    have hand := and15 (BitVec.ofNat 64 n)
    rw [toNat64 hlt] at hand
    crun [Int.reduceNatCast', h18, hand]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h26₃, hg₃, hk₃⟩ => ?_)
  have he₃ := he₂.keep (fun r hr => hg₃ r (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 0) (.inl rfl) (x := bytesAt s.mem Np n) ⟨he₃, by
    rw [hk₃.mem, hH₂]⟩ (by rw [h26₃, length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  have h18₄ : s₄.gpr .s7 = BitVec.ofNat 64 n := he₄.fr _ (by decide) |>.trans h.s7
  have h₅ : WP isa (.block [.li .s4 0, mov .s6 .s7]) s₄ fun s₅ =>
      s₅.gpr .s4 = BitVec.ofNat 64 0 ∧ s₅.gpr .s6 = BitVec.ofNat 64 n ∧
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    crun [Int.reduceNatCast', h18₄, mov]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := he₄.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (lens_ok L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hk₅.mem]; exact hf.hH))
    fun s₆ ⟨he₆, hH₆, hY₆, _, f₆⟩ => ?_
  refine ⟨he₆, hH₆, ?_, ?_⟩
  · have hw := (hf.abs (by rw [hk₃.mem]; exact hab₂)).whole_eq (by
      simp only [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [length_bytesAt, add_ofNat_zero] at hw
    rw [h24₅, h26₅, toNat64 (by decide), toNat64 hlt, hk₅.mem, add_ofNat_zero, hw] at hY₆
    rw [Proof.Gcm.j0_eq H (by rw [length_bytesAt]; exact hn), length_bytesAt, ← hY₆]
  · have g₁ : Frame (j0Frame (V .s1) (V .s0) sp) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    have g₄ := t_j0Frame hf.frame
    have g₆ := t_j0Frame f₆
    rw [hk₃.mem] at g₄
    rw [hk₅.mem] at g₆
    exact ((g₁.trans (abs_j0Frame ho.frame)).trans g₄).trans g₆

omit L in
/-- Branching on `r - k`, for `r` holding `a`. -/
theorem eval_subk {s : State} {r : Reg} {a k : Nat}
    (h : s.gpr r = BitVec.ofNat 64 a - BitVec.ofNat 64 k) (ha : a < 2 ^ 64) (hk : k < 2 ^ 64) :
    isa.eval (.zero r) s = some (decide (a = k)) := by
  rw [Steps.eval_zero, h]
  congr 1
  by_cases hak : a = k
  · subst hak; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 k ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, toNat64 ha, toNat64 hk] at this
      simp at this; omega
    simp only [hak, decide_false, beq_eq_false_iff_ne.mpr this]

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) :
    WP isa j0 s (J0Out V sp H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  have h₁ : WP isa (.block [.addi .a2 .s5 (-12)]) s fun s₁ =>
      s₁.gpr .a2 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ (∀ r, r ≠ .a2 → s₁.gpr r = s.gpr r) ∧
        Keeps s s₁ := by
    crun [Int.reduceNatCast', h.s5]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨h6, hg₁, hk₁⟩ => ?_)
  have hi : J0In V sp H Np n s₁ :=
    ⟨h.env.keep (fun r hr => hg₁ r (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, by rw [hk₁.mem]; exact h.hH,
      by rw [hg₁ _ (by decide)]; exact h.s4, by rw [hg₁ _ (by decide)]; exact h.s5, h.s7,
      h.data.of_eq hk₁.rd hk₁.wr hk₁.sp⟩
  rw [← hk₁.mem]
  refine WP.seq (WP.ite (decide (n = 12)) (eval_subk h6 hlt (by decide)) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L hi) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok L hi (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.AesGcm.RISCV64
