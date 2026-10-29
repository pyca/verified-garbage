module

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Flush.lean`): `flush yo` pads the `r26` buffered bytes
with zeros in `T` and absorbs them (`flush_ok`); `lens yo` stores the
lengths block of `r24` and `r26` bytes in `T` and absorbs it (`lens_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (st w : Addr) (yo : Nat) : List Region :=
  [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩]

theorem gh_tFrame {st w : Addr} {yo : Nat} {m m' : Mem}
    (h : Frame [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩] m m') :
    Frame (tFrame st w yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

theorem tFrame_T {st w : Addr} {yo : Nat} {m m' : Mem} (h : Frame [⟨w + BitVec.ofNat 64 96, 16⟩] m m') :
    Frame (tFrame st w yo) m m' :=
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
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `x₀` absorbed in `m₀`. -/
structure FlOut (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .r30 + BitVec.ofNat 64 yo) (V .r30 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .r30 + BitVec.ofNat 64 yo) (V .r30 + BitVec.ofNat 64 32) H x
  frame : Frame (tFrame (V .r30) (V .r31) yo) m₀ s.mem

/-- After the copy of the `o` buffered bytes to `T`, padded with zeros. -/
structure FlMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (o : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  hT : bytesAt s.mem (V .r31 + BitVec.ofNat 64 96) 16 =
    bytesAt m₀ (V .r30 + BitVec.ofNat 64 32) o ++ zeros (16 - o)
  hY : blockAt s.mem (V .r30 + BitVec.ofNat 64 yo) = blockAt m₀ (V .r30 + BitVec.ofNat 64 yo)
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ tFrame (V .r30) (V .r31) yo,
    (⟨V .r29 + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega_arith)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)

omit L hyo in
/-- `T` zeroed. -/
theorem zeroT_ok {s : State} (he : Env V sp s) :
    WP isa (.block [.li .r0 0, .store .d .r0 .r31 tO, .store .d .r0 .r31 (tO + 8)]) s fun s' =>
      s'.mem = (s.mem.writeW (V .r31 + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (V .r31 + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  have h31 := he.r31
  have w₀ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  crun [tO, h31, w₀, w₁, write_8]
  exact ⟨by rw [add_ofNat_assoc], fun r a => by simp [a]⟩

/-- The `o` buffered bytes copied to `T`, padded with zeros. -/
theorem flushCopy_ok {H : Block} {o : Nat} {s : State} (h : FlIn V sp H s)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 o) (ho : o < 16) (h0 : o ≠ 0) :
    WP isa (.seq (.block flushPre) copyLoop) s (FlMid V sp yo H o s.mem) := by
  have he := h.env
  have h30 := he.r30; have h31 := he.r31
  refine WP.seq (WP.block_append (WP.mono (zeroT_ok he) fun s₁ ⟨hm₁, hg₁, hrd₁, hwr₁, hsp₁, _⟩ => ?_))
  have e30 : s₁.gpr .r30 = V .r30 := (hg₁ _ (by decide)).trans h30
  have e31 : s₁.gpr .r31 = V .r31 := (hg₁ _ (by decide)).trans h31
  have e26 : s₁.gpr .r26 = BitVec.ofNat 64 o := (hg₁ _ (by decide)).trans h26
  have h₂ : WP isa (.block [.addi .r3 .r30 32, .addi .r4 .r31 tO, mov .r5 .r26]) s₁ (fun s₂ : State =>
      s₂.gpr .r3 = V .r30 + BitVec.ofNat 64 32 ∧ s₂.gpr .r4 = V .r31 + BitVec.ofNat 64 96 ∧
      s₂.gpr .r5 = BitVec.ofNat 64 o ∧ (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂) := by
    crun [tO, e30, e31, e26, mov, BitVec.or_self]
    exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₂ fun s₂ ⟨h3, h4, h5, hg₂, hk₂⟩ => ?_
  have lp : LoopPre s₂ (V .r30 + BitVec.ofNat 64 32) (V .r31 + BitVec.ofNat 64 96) o := by
    refine ⟨h3, h4, h5, by omega_arith, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂.rd, hk₂.wr, hrd₁, hwr₁]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂.wr, hwr₁]; exact he.perm.wC (by omega_arith)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by omega_arith⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [hk₂.mem] at hm₃
  -- The memory so far.
  have fz : Frame [⟨V .r31 + BitVec.ofNat 64 96, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hB₁ : bytesAt s₁.mem (V .r30 + BitVec.ofNat 64 32) o = bytesAt s.mem (V .r30 + BitVec.ofNat 64 32) o :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
      (by omega_arith)
  have hlen := length_bytesAt s₁.mem (V .r30 + BitVec.ofNat 64 32) o
  have fc : Frame [⟨V .r31 + BitVec.ofNat 64 96, o⟩] s₁.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  have f₃ : Frame [⟨V .r31 + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine ⟨he.keep (fun r hr => by
      rw [lo.other r (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide),
        hg₁ r (by revert r; decide)])
      (by rw [lo.keeps.2.2.1, hk₂.sp, hsp₁]) (by rw [lo.keeps.1, hk₂.rd, hrd₁])
      (by rw [lo.keeps.2.1, hk₂.wr, hwr₁]), ?_, ?_, ?_, f₃⟩
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
  · rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hB₁]
    congr 1
    have := zeroT_bytes s.mem (V .r31 + BitVec.ofNat 64 96)
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
    WP isa (ghash1 yo .r31 tO) s (FlOut V sp yo H x (x ++ zeros (padLen x.length)) m₀) := by
  have he := h.env
  refine WP.mono (ghash1_ok L hyo he .r31 96 (.inr rfl) (by decide) (P := V .r31 + BitVec.ofNat 64 96)
    (by rw [he.r31]) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide)) (covers_left (he.perm.wC (by decide))))
    fun s₄ g => ?_
  refine ⟨g.env he, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (ctx_ghFrame L hyo), h.hH]
  · intro ha
    refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s.mem (V .r31 + BitVec.ofNat 64 96) 16) h.hT ?_
    rw [g.out, h.hY, h.hH]; rfl
  · exact (tFrame_T h.frame).trans (gh_tFrame g.frame)

/-- `flush yo`. -/
theorem flush_ok {H : Block} {x : List Byte} {s : State} (h : FlIn V sp H s)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 (x.length % 16)) :
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

theorem rev64_eq : VG.PPC64LE.rev64 = byteRev64 := rfl

/-- The 8 bytes of `[8 r]₆₄`. -/
theorem le8_lens (x : BitVec 64) :
    Proof.Cmac.le8 (VG.PPC64LE.rev64 (x <<< 3)) = Spec.Gcm.be64 (8 * x.toNat) := by
  have : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [Nat.reducePow, Nat.mul_comm]
  rw [rev64_eq, Proof.Gcm.le8_byteRev64, this, BitVec.toNat_ofNat, Proof.Gcm.be64_mod]

/-- `[8 r24]₆₄ ‖ [8 r26]₆₄`, the lengths block, stored in `T`. -/
theorem lensStore_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    WP isa (.block Impl.AesGcm.PPC64LE.lensBlock) s fun s' =>
      s'.mem = (s.mem.writeW (V .r31 + BitVec.ofNat 64 96) (VG.PPC64LE.rev64 (s.gpr .r24 <<< 3))).writeW
        (V .r31 + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (VG.PPC64LE.rev64 (s.gpr .r26 <<< 3)) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
  have h31 := he.r31
  have w₀ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have w₁' : InRegions s.wr (V .r31 + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 8 := by
    rw [add_ofNat_assoc]; exact w₁
  crun [Impl.AesGcm.PPC64LE.lensBlock, tO, h31, w₀, w₁', write_8, addrX]
  exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl⟩⟩

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The lengths block of `r24` and `r26` bytes, absorbed. -/
theorem lens_ok {H : Block} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H) :
    WP isa (lens yo) s fun s' => Env V sp s' ∧
      blockAt s'.mem (V .r29 + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (V .r30 + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (V .r30 + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .r24).toNat (s.gpr .r26).toNat)] ∧
      (∀ r, r ∈ preserved → s'.gpr r = s.gpr r) ∧
      Frame (tFrame (V .r30) (V .r31) yo) s.mem s'.mem := by
  refine WP.seq (WP.mono (lensStore_ok he) fun s₂ ⟨hm₂, hg₂, hk₂⟩ => ?_)
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have fT : Frame [⟨V .r31 + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (V .r31 + BitVec.ofNat 64 96) 16 =
      lensBlock (s.gpr .r24).toNat (s.gpr .r26).toNat := by
    rw [hm₂, Proof.Cmac.bytesAt_store2, le8_lens, le8_lens]; rfl
  have hY₂ : blockAt s₂.mem (V .r30 + BitVec.ofNat 64 yo) = blockAt s.mem (V .r30 + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (V .r29 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  refine WP.mono (ghash1_ok L hyo he₂ .r31 96 (.inr rfl) (by decide) (P := V .r31 + BitVec.ofNat 64 96)
    (by rw [he₂.r31]) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide)) (covers_left (he₂.perm.wC (by decide))))
    fun s₃ g => ?_
  refine ⟨g.env he₂, ?_, ?_, fun r hr => by
      rw [g.saved r hr]; exact hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide), ?_⟩
  · rw [blockAt_frame g.frame (ctx_ghFrame L hyo), hH₂]
  · have hb : blockAt s₂.mem (V .r31 + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .r24).toNat (s.gpr .r26).toNat) := by
      rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, hb]
  · exact (tFrame_T fT).trans (gh_tFrame g.frame)

end

end VG.Proof.AesGcm.PPC64LE
