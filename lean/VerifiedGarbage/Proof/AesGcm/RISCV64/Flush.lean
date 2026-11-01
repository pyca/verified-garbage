module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Flush.lean`): `flush yo` pads the `s6` buffered bytes
with zeros in `T` and absorbs them (`flush_ok`); `lens yo` stores the
lengths block of `s4` and `s6` bytes in `T`, a byte at a time, and absorbs
it (`lens_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write, with the stack below `sp` that
`vg_ghash`'s frame uses. -/
abbrev tFrame (st w : Addr) (yo : Nat) (sp : Addr) : List Region :=
  [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩,
    below sp 2048]

theorem gh_tFrame {st w : Addr} {yo : Nat} {sp : Addr} {m m' : Mem}
    (h : Frame [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩, below sp 2048] m m') :
    Frame (tFrame st w yo sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem tFrame_T {st w : Addr} {yo : Nat} {sp : Addr} {m m' : Mem}
    (h : Frame [⟨w + BitVec.ofNat 64 96, 16⟩] m m') : Frame (tFrame st w yo sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

theorem write_8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW]; exact congrArg (m.write a 8) (BitVec.setWidth_eq _).symm

/-- The 16 bytes after zeroing. -/
theorem zeroT_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 = zeros 16 := by
  rw [Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- Before `flush yo` (or `lens yo`). -/
structure FlIn (V : Reg → BitVec 64) (sp : Addr) (H : Block) (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `x₀` absorbed in `m₀`. -/
structure FlOut (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x
  frame : Frame (tFrame (V .s1) (V .s0) yo sp) m₀ s.mem

/-- After the copy of the `o` buffered bytes to `T`, padded with zeros. -/
structure FlMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (o : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  hT : bytesAt s.mem (V .s0 + BitVec.ofNat 64 96) 16 =
    bytesAt m₀ (V .s1 + BitVec.ofNat 64 32) o ++ zeros (16 - o)
  hY : blockAt s.mem (V .s1 + BitVec.ofNat 64 yo) = blockAt m₀ (V .s1 + BitVec.ofNat 64 yo)
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame (hk : StkOk (V .s2) (V .s1) (V .s0) sp) : ∀ r ∈ tFrame (V .s1) (V .s0) yo sp,
    (⟨V .s2 + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega_arith)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact hk.c.sub_left (Lay.ctxSub (by decide))

omit hyo in
/-- `T` zeroed. -/
theorem zeroT_ok {s : State} (he : Env V sp s) :
    WP isa (.block [.li .t0 0, .store .d .t0 .s0 tO, .store .d .t0 .s0 (tO + 8)]) s fun s' =>
      s'.mem = (s.mem.writeW (V .s0 + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (V .s0 + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h31 := he.s0
  have w₀ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have a₀ := L.wal8 (d := 96) (by decide) (by decide)
  have a₁ := L.wal8 (d := 104) (by decide) (by decide)
  crun [tO, h31, w₀, w₁, a₀, a₁, write_8]
  exact ⟨by rw [add_ofNat_assoc], fun r a => by simp [a]⟩

/-- The `o` buffered bytes copied to `T`, padded with zeros. -/
theorem flushCopy_ok {H : Block} {o : Nat} {s : State} (h : FlIn V sp H s)
    (h26 : s.gpr .s6 = BitVec.ofNat 64 o) (ho : o < 16) (h0 : o ≠ 0) :
    WP isa (.seq (.block flushPre) copyLoop) s (FlMid V sp yo H o s.mem) := by
  have he := h.env
  have h30 := he.s1; have h31 := he.s0
  refine WP.seq (WP.block_append (WP.mono (zeroT_ok L he) fun s₁ ⟨hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_))
  have e30 : s₁.gpr .s1 = V .s1 := (hg₁ _ (by decide)).trans h30
  have e31 : s₁.gpr .s0 = V .s0 := (hg₁ _ (by decide)).trans h31
  have e26 : s₁.gpr .s6 = BitVec.ofNat 64 o := (hg₁ _ (by decide)).trans h26
  have h₂ : WP isa (.block [.addi .a0 .s1 32, .addi .a1 .s0 tO, mov .a2 .s6]) s₁ (fun s₂ : State =>
      s₂.gpr .a0 = V .s1 + BitVec.ofNat 64 32 ∧ s₂.gpr .a1 = V .s0 + BitVec.ofNat 64 96 ∧
      s₂.gpr .a2 = BitVec.ofNat 64 o ∧ (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂) := by
    crun [tO, e30, e31, e26, mov, BitVec.or_self, Int.reduceNatCast']
    exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₂ fun s₂ ⟨h3, h4, h5, hg₂, hk₂⟩ => ?_
  have lp : LoopPre s₂ (V .s1 + BitVec.ofNat 64 32) (V .s0 + BitVec.ofNat 64 96) o := by
    refine ⟨h3, h4, h5, by omega_arith, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂.rd, hk₂.wr, hrd₁, hwr₁]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂.wr, hwr₁]; exact he.perm.wC (by omega_arith)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by omega_arith⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [hk₂.mem] at hm₃
  -- The memory so far.
  have fz : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hB₁ : bytesAt s₁.mem (V .s1 + BitVec.ofNat 64 32) o = bytesAt s.mem (V .s1 + BitVec.ofNat 64 32) o :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
      (by omega_arith)
  have hlen := length_bytesAt s₁.mem (V .s1 + BitVec.ofNat 64 32) o
  have fc : Frame [⟨V .s0 + BitVec.ofNat 64 96, o⟩] s₁.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  have f₃ : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine ⟨he.keep (fun r hr => by
      rw [lo.other r (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide),
        hg₁ r (by revert r; decide)])
      (by rw [lo.keeps.2.2, hk₂.sp, hsp₁]) (by rw [lo.keeps.1, hk₂.rd, hrd₁])
      (by rw [lo.keeps.2.1, hk₂.wr, hwr₁]), ?_, ?_, ?_, f₃⟩
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
  · rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hB₁]
    congr 1
    have := zeroT_bytes s.mem (V .s0 + BitVec.ofNat 64 96)
    rw [← hm₁, show (16 : Nat) = o + (16 - o) by omega_arith, bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega_arith, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · exact blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)

/-- The padded buffer absorbed. -/
theorem flushGh_ok {H : Block} {x : List Byte} {m₀ : Mem} {s : State}
    (h : FlMid V sp yo H (x.length % 16) m₀ s) (h0 : x.length % 16 ≠ 0) :
    WP isa (ghash1 yo .s0 tO) s (FlOut V sp yo H x (x ++ zeros (padLen x.length)) m₀) := by
  have he := h.env
  refine WP.mono (ghash1_ok L hyo he .s0 96 (.inr rfl) (by decide) (P := V .s0 + BitVec.ofNat 64 96)
    (by rw [he.s0]) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide))
    (he.stk'.w.sub_left (Lay.wSub (d := 96) (n := 16) (by decide))) (L.w_fit (by decide) (by decide))
    (covers_left (he.perm.wC (by decide))))
    fun s₄ g => ?_
  refine ⟨g.env he, ?_, ?_, ?_⟩
  · rw [blockAt_frame (he.sp ▸ g.frame) (ctx_ghFrame L hyo he.stk'), h.hH]
  · intro ha
    refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s.mem (V .s0 + BitVec.ofNat 64 96) 16) h.hT ?_
    rw [g.out, h.hY, h.hH]; rfl
  · exact (tFrame_T h.frame).trans (gh_tFrame (he.sp ▸ g.frame))

/-- `flush yo`. -/
theorem flush_ok {H : Block} {x : List Byte} {s : State} (h : FlIn V sp H s)
    (h26 : s.gpr .s6 = BitVec.ofNat 64 (x.length % 16)) :
    WP isa (flush yo) s (FlOut V sp yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  refine WP.ite (decide (x.length % 16 = 0)) (eval_zero h26 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨h.env, h.hH, fun ha => by simpa [zeros] using ha, Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (flushCopy_ok L hyo (o := x.length % 16) h h26 hlt h0) fun s₃ hm =>
      flushGh_ok L hyo hm h0)

end

/-- The bytes `storeBE 8` stores of a 64-bit word, as GCM's `[x]₆₄`. -/
theorem beBytes_be64 (v : BitVec 64) : ByteLoad.beBytes 8 v = Spec.Gcm.be64 v.toNat := by
  simp only [ByteLoad.beBytes, Spec.Gcm.be64]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 - 1 - j) = 8 * (7 - j) by omega, Nat.pow_mul]

/-- The 8 bytes of `[8 r]₆₄`. -/
theorem beBytes_lens (x : BitVec 64) : ByteLoad.beBytes 8 (x <<< 3) = Spec.Gcm.be64 (8 * x.toNat) := by
  have : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [Nat.reducePow, Nat.mul_comm]
  rw [beBytes_be64, this, BitVec.toNat_ofNat, Proof.Gcm.be64_mod]

/-- `[8 s4]₆₄ ‖ [8 s6]₆₄`, the lengths block, stored in `T` a byte at a time. -/
theorem lensStore_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    WP isa (.block Impl.AesGcm.RISCV64.lensBlock) s fun s' =>
      s'.mem = writeBytes (writeBytes s.mem (V .s0 + BitVec.ofNat 64 96)
          (ByteLoad.beBytes 8 (s.gpr .s4 <<< 3)))
        (V .s0 + BitVec.ofNat 64 104) (ByteLoad.beBytes 8 (s.gpr .s6 <<< 3)) ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .t0 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
  have h31 := he.s0
  rw [Impl.AesGcm.RISCV64.lensBlock, List.append_assoc, WP.block_append_iff]
  refine Steps.wp_sll (by decide) fun s₁ u₁ => Steps.wp_sll (by decide) fun s₂ u₂ => WP.block_nil ?_
  rw [WP.block_append_iff]
  have hw : ∀ off, off + 8 ≤ 2560 → ∀ j < 8,
      InRegions s₂.wr (s₂.gpr .s0 + BitVec.ofNat 64 (off + j)) 1 := fun off ho j hj => by
    rw [u₂.wr, u₁.wr, u₂.other _ (by decide), u₁.other _ (by decide), h31]
    exact he.perm.wW (by omega)
  refine WP.mono (ByteLoad.storeBE_ok (s := s₂) (v := .a0) (tmp := .t0) (n := .s0) (off := tO) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (hw 96 (by decide))) fun s₃ e₃ => ?_
  subst e₃
  refine WP.mono (ByteLoad.storeBE_ok (v := .a1) (tmp := .t0) (n := .s0) (off := tO + 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa [RegUpd.gpr_write, RegUpd.wr_write] using hw (tO + 8) (by decide))) fun s₄ e₄ => ?_
  subst e₄
  have a0 : s₂.gpr .a0 = s.gpr .s4 <<< 3 := by rw [u₂.other _ (by decide), u₁.gpr]
  have a1 : s₂.gpr .a1 = s.gpr .s6 <<< 3 := by rw [u₂.gpr, u₁.other _ (by decide)]
  have b0 : s₂.gpr .s0 = V .s0 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h31]
  have m2 : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨?_, fun r a b c d e => ?_, ⟨?_, ?_, ?_⟩⟩
  · simp only [RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ (show Reg.s0 ≠ .t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .t0 by decide), a0, a1, b0, m2, tO, Nat.reduceAdd]
  · simp only [RegUpd.gpr_write_of_ne _ _ e]; rw [u₂.other _ b, u₁.other _ a]
  · simp only [RegUpd.rd_write]; exact u₂.rd.trans u₁.rd
  · simp only [RegUpd.wr_write]; exact u₂.wr.trans u₁.wr
  · simp only [RegUpd.sp_write]; exact u₂.sp.trans u₁.sp

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The lengths block of `s4` and `s6` bytes, absorbed. -/
theorem lens_ok {H : Block} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) :
    WP isa (lens yo) s fun s' => Env V sp s' ∧
      blockAt s'.mem (V .s2 + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (V .s1 + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (V .s1 + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .s4).toNat (s.gpr .s6).toNat)] ∧
      (∀ r, r ∈ preserved → s'.gpr r = s.gpr r) ∧
      Frame (tFrame (V .s1) (V .s0) yo sp) s.mem s'.mem := by
  refine WP.seq (WP.mono (lensStore_ok he) fun s₂ ⟨hm₂, hg₂, hk₂⟩ => ?_)
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have hlen := ByteLoad.beBytes_length 8 (s.gpr .s4 <<< 3)
  have hcat := writeBytes_append s.mem (V .s0 + BitVec.ofNat 64 96) (ByteLoad.beBytes 8 (s.gpr .s4 <<< 3))
    (ByteLoad.beBytes 8 (s.gpr .s6 <<< 3)) (by simp [ByteLoad.beBytes_length])
  rw [hlen, add_ofNat_assoc] at hcat
  rw [hcat] at hm₂
  have fT : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact writeBytes_frame' _ (by simp [ByteLoad.beBytes_length])
  have hT : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 96) 16 =
      lensBlock (s.gpr .s4).toNat (s.gpr .s6).toNat := by
    rw [hm₂, bytesAt_writeBytes_self' _ _ (by simp [ByteLoad.beBytes_length]) (by decide), beBytes_lens,
      beBytes_lens]; rfl
  have hY₂ : blockAt s₂.mem (V .s1 + BitVec.ofNat 64 yo) = blockAt s.mem (V .s1 + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (V .s2 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  refine WP.mono (ghash1_ok L hyo he₂ .s0 96 (.inr rfl) (by decide) (P := V .s0 + BitVec.ofNat 64 96)
    (by rw [he₂.s0]) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide))
    (he₂.stk'.w.sub_left (Lay.wSub (d := 96) (n := 16) (by decide))) (L.w_fit (by decide) (by decide))
    (covers_left (he₂.perm.wC (by decide))))
    fun s₃ g => ?_
  refine ⟨g.env he₂, ?_, ?_, fun r hr => by
      rw [g.saved r hr]; exact hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide), ?_⟩
  · rw [blockAt_frame (he₂.sp ▸ g.frame) (ctx_ghFrame L hyo he₂.stk'), hH₂]
  · have hb : blockAt s₂.mem (V .s0 + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .s4).toNat (s.gpr .s6).toNat) := by
      rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, hb]
  · have := g.frame; rw [he₂.sp] at this; exact (tFrame_T fT).trans (gh_tFrame this)

end

end VG.Proof.AesGcm.RISCV64
