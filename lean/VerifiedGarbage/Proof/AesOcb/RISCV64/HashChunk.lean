module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.RISCV64.PadTo
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
import VerifiedGarbage.Proof.AesOcb.RISCV64.LNtz
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.AesOcb.RISCV64

/-!
# AES-OCB on RISC-V: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`s4` points at block `j`, `s6` is `j + 1`, and `m − j` is in `t1` and at
`W + hlO`. `hashChunk` takes `c = min(8, m − j)` blocks (`chunkHead_ok`):
fills the buffer with each block XORed with its offset (`fill_ok`),
enciphers the buffer, adds it to the sum (`hashSum_ok`), and leaves `HInv`
at `j + c` (`hashChunk_ok`). Each step of the fill (`hashFill_ok`)
computes the next offset, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}`
(`lNtz_ok`, `xorB_ok`), copies the next block of the associated data a byte
at a time (AES-GCM's `copyLoop`) to the next slot of the buffer at
`W + bufO`, and XORs the offset into it there. As on PPC64LE
(`Proof/AesOcb/PPC64LE/HashFill.lean`, `HashChunk.lean`), but the associated
data need not be aligned.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

section Fill

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (in_left in_off copyLoop_ok)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a2, .a3, .a5, .a7, .s4, .s5, .s6]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  s4 : t'.gpr .s4 = A + BitVec.ofNat 64 (16 * (j + i + 1))
  s6 : t'.gpr .s6 = BitVec.ofNat 64 (j + i + 2)
  a7 : t'.gpr .a7 = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  s5 : t'.gpr .s5 = BitVec.ofNat 64 (c - (i + 1))
  gpr : ∀ r, r ∉ fillRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

/-- The block written at `p`. -/
theorem blockAtMem_writeBytes (m : Mem) (p : Addr) {xs : List Byte} (h : xs.length = 16) :
    blockAtMem (writeBytes m p xs) p = Spec.Ocb.ofBytes xs := by
  rw [blockAtMem, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by omega) (by decide), h,
    List.drop_eq_nil_of_le (by rw [Proof.Ocb.length_bytesAt]), List.append_nil]

theorem hashFill_ok {K W : Addr} (L : Lay K W) {t : State} (hs0 : t.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {A : Addr} {l : Block} {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (hs6 : t.gpr .s6 = BitVec.ofNat 64 (j + i + 1)) (hs4 : t.gpr .s4 = A + BitVec.ofNat 64 (16 * (j + i)))
    (ha7 : t.gpr .a7 = W + BitVec.ofNat 64 (384 + 16 * i)) (hs5 : t.gpr .s5 = BitVec.ofNat 64 (c - i))
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa hashFill t (FillPost W A l j i c t) := by
  have hW := L.wal
  unfold hashFill xorW
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) hs0 hW hw (by omega) (by omega) hs6 hl0) fun t₁ P₁ => ?_)
  have hs0₁ : t₁.gpr .s0 = W := by rw [P₁.gpr _ (by decide), hs0]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  refine WP.seq (WP.block_append (WP.mono (xorB_ok (s := t₁) (pd := ohO) (qd := lO) (cd := ohO) hW hW hW
    (by decide) (by decide) (by decide) hs0₁ hs0₁ hs0₁ (by decide) (by decide) (by decide)
    (in_left (ww (by decide))) (in_left (ww (by decide))) (in_left (ww (by decide))) (in_left (ww (by decide)))
    (ww (by decide)) (ww (by decide)) (Offset.sep W (by decide) (by decide) (by decide))
    (Offset.sep W (by decide) (by decide) (by decide))) fun t₂ B₂ => ?_))
  refine wp_mv fun t₂a u₂a => wp_mv fun t₂b u₂b => wp_li (imm := 16) (by decide) fun t₂c u₂c => WP.block_nil ?_
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])),
      P₁.gpr r hr]
  have gc : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → t₂c.gpr r = t₂.gpr r := fun r h0 h1 h2 => by
    rw [u₂c.other _ h2, u₂b.other _ h1, u₂a.other _ h0]
  have mc : t₂c.mem = t₂.mem := by rw [u₂c.mem, u₂b.mem, u₂a.mem]
  have rdc : t₂c.rd = t.rd := by rw [u₂c.rd, u₂b.rd, u₂a.rd, B₂.rd, P₁.rd]
  have wrc : t₂c.wr = t.wr := by rw [u₂c.wr, u₂b.wr, u₂a.wr, B₂.wr, P₁.wr]
  have spc : t₂c.sp = t.sp := by rw [u₂c.sp, u₂b.sp, u₂a.sp, B₂.sp, P₁.sp]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have hb : 384 + 16 * i + 16 ≤ 2560 := by omega
  have dS : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩ := hAW.sub_right (Lay.wSub hb)
  have eA : bytesAt t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) 16 =
      bytesAt t.mem (A + BitVec.ofNat 64 (16 * (j + i))) 16 :=
    Proof.Cmac.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hAW.sub_right (Lay.wSub (by decide))) (by decide)
  have pre : Proof.AesGcm.RISCV64.LoopPre t₂c (A + BitVec.ofNat 64 (16 * (j + i)))
      (W + BitVec.ofNat 64 (384 + 16 * i)) 16 :=
    ⟨by rw [u₂c.other _ (by decide), u₂b.other _ (by decide), u₂a.gpr, g₂ _ (by decide), hs4],
      by rw [u₂c.other _ (by decide), u₂b.gpr, u₂a.other _ (by decide), g₂ _ (by decide), ha7],
      u₂c.gpr, by decide, by decide, by rw [rdc, wrc]; exact hA,
      by rw [wrc]; exact Proof.AesGcm.RISCV64.covers_off hw (by omega) (by decide), dS⟩
  refine WP.seq (WP.mono (copyLoop_ok t₂c pre) fun t₃ ⟨hm₃, o₃⟩ => ?_)
  obtain ⟨rd₃, wr₃, sp₃⟩ := o₃.keeps
  have fs₃ : Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t₂c.mem t₃.mem := by
    rw [hm₃]; exact writeBytes_frame _ _ _ (by rw [Proof.Ocb.length_bytesAt]; exact Region.contains_self _ _)
  have v₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
      blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) := by
    rw [hm₃, blockAtMem_writeBytes _ _ (Proof.Ocb.length_bytesAt _ _ _), mc, eA]; rfl
  have dOB : (⟨W + BitVec.ofNat 64 ohO, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩ :=
    L.w_w (a := ohO) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by simp only [ohO]; omega)) (by decide)
      (by omega)
  have oh₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [blockAtMem_frame fs₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dOB), mc, oh₂]
  have g₃ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → t₃.gpr r = t₂.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [o₃.other r h0 h1 h2 h3 h4, gc r h1 h2 h3]
  have hs0₃ : t₃.gpr .s0 = W := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), hs0]
  have hB : (W + BitVec.ofNat 64 (384 + 16 * i)).toNat % 8 = 0 := L.alW (by omega)
  have ha7₃ : t₃.gpr .a7 = W + BitVec.ofNat 64 (384 + 16 * i) := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), ha7]
  have hS0 : W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * i) :=
    BitVec.add_zero _
  have hWl := L.ww
  have sp₁ : Mem.Sep (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 (0 + 8)) 8
      (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 0) 8 := by
    rw [hS0, Offset.add_add]; exact Offset.sep _ (.inr (by omega)) (by omega) (by omega)
  have sq₁ : Mem.Sep (W + BitVec.ofNat 64 (ohO + 8)) 8
      (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 0) 8 := by
    rw [hS0]; exact Offset.sep _ (.inl (by simp only [ohO]; omega)) (by simp only [ohO]; omega) (by omega)
  refine WP.block_append (WP.mono (xorB_ok (s := t₃) (P := W + BitVec.ofNat 64 (384 + 16 * i)) (Q := W)
    (C := W + BitVec.ofNat 64 (384 + 16 * i)) (pd := 0) (qd := ohO) (cd := 0) hB hW hB (by decide) (by decide)
    (by decide) ha7₃ hs0₃ ha7₃
    (by decide) (by decide) (by decide)
    (by rw [rd₃, wr₃, rdc, wrc, hS0]; exact in_left (in_off hw (by omega) (by decide)))
    (by rw [rd₃, wr₃, rdc, wrc, Offset.add_add]; exact in_left (in_off hw (by omega) (by decide)))
    (by rw [rd₃, wr₃, rdc, wrc]; exact in_left (in_off hw (by decide) (by decide)))
    (by rw [rd₃, wr₃, rdc, wrc]; exact in_left (in_off hw (by decide) (by decide)))
    (by rw [wr₃, wrc, hS0]; exact in_off hw (by omega) (by decide))
    (by rw [wr₃, wrc, Offset.add_add]; exact in_off hw (by omega) (by decide))
    sp₁ sq₁) fun t₄ B₄ => ?_)
  have v₄ := B₄.val
  rw [hS0] at v₄
  refine wp_addi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ =>
    wp_addi (by decide) fun t₇ u₇ => wp_subi (imm := 1) (by decide) fun t₈ u₈ => WP.block_nil ?_
  have g₄ : ∀ r, r ∉ fillRegs → t₄.gpr r = t.gpr r := fun r hr => by
    simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [B₄.gpr r (by simp [hr.2.1, hr.2.2.1]), g₃ r hr.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1
      hr.2.2.2.2.2.2.2.2.1, g₂ r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.1])]
  have fs : Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t₃.mem t₄.mem := by
    have := B₄.frame; rwa [hS0] at this
  have r4 : ∀ r, r ≠ .t1 → r ≠ .t2 → t₄.gpr r = t₃.gpr r := fun r h1 h2 =>
    B₄.gpr r (by simp [h1, h2])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem]
    refine (fr₂.mono (by simp)).trans ?_
    rw [← mc]
    exact (fs₃.mono (by simp)).trans (fs.mono (by simp))
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, blockAtMem_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dOB), oh₃]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, v₄, v₃, oh₃]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      r4 _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), hs4, Offset.add_add, show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      r4 _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), hs6, ← BitVec.ofNat_add]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      r4 _ (by decide) (by decide), ha7₃, Offset.add_add, show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      r4 _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), hs5, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · have hr' := hr
    simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [u₈.other _ hr'.2.2.2.2.2.2.2.2.2.2.2.2.1, u₇.other _ hr'.2.2.2.2.2.2.2.2.2.2.2.2.2,
      u₆.other _ hr'.2.2.2.2.2.2.2.2.2.2.2.1, u₅.other _ hr'.2.2.2.2.2.2.2.2.2.2.1, g₄ r hr]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, B₄.sp, sp₃, spc]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, B₄.rd, rd₃, rdc]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, B₄.wr, wr₃, wrc]

end Fill


open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.RegUpd VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (in_left in_off Keeps)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, its offset, the counts of
blocks at `[296, 312)`, and the buffer and the working space of the
functions called. -/
abbrev hashR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩,
    ⟨W + BitVec.ofNat 64 296, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

theorem hashR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (hashR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)

/-- A part of `W` that `HASH` writes, within its part at `W + e`. -/
theorem in_hashR {W : Addr} {d k e n : Nat} (he : (⟨W + BitVec.ofNat 64 e, n⟩ : Region) ∈ hashR W)
    (h₁ : e ≤ d) (h₂ : d + k ≤ e + n) : ∃ r' ∈ hashR W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, he, Offset.sub W h₁ h₂⟩

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (V : Reg → BitVec 64) (sp : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : Env V sp s
  frame : Frame (hashR (V .s0)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ohO) = offAt 0 l j
  s4 : s.gpr .s4 = A + BitVec.ofNat 64 (16 * j)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (j + 1)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (a.length / 16 - j)
  hl : s.mem.readW (V .s0 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - j)
  l0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0

/-- What a chunk of `HASH` needs of its start, `s₀`: the key context's
cipher and `L_*`, the associated data (apart from `W` and the data at `D`). -/
structure HCtx (K W D : Addr) (n R : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) : Prop where
  lay : Lay K W
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ciph : ctxCiph s₀.mem K R = ciph
  lstar : ctxLstar s₀.mem K = l
  buf : Buf W s₀ A a.length
  aad : bytesAt s₀.mem A a.length = a
  ad : (⟨A, a.length⟩ : Region).Disjoint ⟨D, n⟩
  kd : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace HCtx

variable {K W D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}
  (C : HCtx K W D n R ciph l A a s₀)
include C

theorem short : a.length < 2 ^ 64 := C.buf.lt

/-- The associated data misses the parts the pieces write. -/
theorem a_mut : ∀ r ∈ mutR W D n, (⟨A, a.length⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact C.buf.w.sub_right (Region.sub_prefix (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.ad

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (mutR W D n) s₀.mem m) {i : Nat} (hi : i < a.length / 16) :
    blockAtMem m (A + BitVec.ofNat 64 (16 * i)) = blockAt a i := by
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega), blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))]

theorem ciph' {m : Mem} (h : Frame (mutR W D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [← C.ciph]
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases C.rounds with h | h | h <;> omega
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut C.lay C.kd r hr).sub_left (Region.sub_prefix hRb))
    (by omega)]

theorem lstar' {m : Mem} (h : Frame (mutR W D n) s₀.mem m) : ctxLstar m K = l := by
  rw [← C.lstar]
  show blockAtMem m (K + BitVec.ofNat 64 240) = blockAtMem s₀.mem (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut C.lay C.kd r hr).sub_left (Lay.kSub (by decide))

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (V : Reg → BitVec 64) (sp : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env V sp t
  frame : Frame (hashR (V .s0)) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  s4 : t.gpr .s4 = A + BitVec.ofNat 64 (16 * (j + i))
  s6 : t.gpr .s6 = BitVec.ofNat 64 (j + i + 1)
  a7 : t.gpr .a7 = V .s0 + BitVec.ofNat 64 (384 + 16 * i)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (c - i)
  cn : t.mem.readW (V .s0 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c
  hl : t.mem.readW (V .s0 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - (j + c))
  oh : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (V .s0 + BitVec.ofNat 64 (384 + 16 * k)) =
    blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 sumO) = hsum ciph l a j
  l0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .s2) (V .s0) D n R ciph l A a s₀) {j c : Nat}
    (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16) {t : State} {i : Nat} (hi : i < c)
    (F : FillInv V sp ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => FillInv V sp ciph l A a s₀ j c t' (i + 1) := by
  have L := C.lay
  have hs := C.short
  have hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).rd
  have hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).w
  refine WP.mono (hashFill_ok L F.env.s0 F.env.perm.w hi hc (by omega) F.s6 F.s4 F.a7 F.s5 F.l0 F.oh hA hAW)
    fun t' P => ?_
  have hfr : ∀ r ∈ [(⟨V .s0 + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 ohO, 16⟩,
      ⟨V .s0 + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ hashR (V .s0), Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact in_hashR (e := 96) (n := 16) (by simp) (by decide) (by decide)
    · exact in_hashR (e := 272) (n := 16) (by simp) (by decide) (by decide)
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by omega) (by omega)
  have keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 272) ∨ (288 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem t.mem (V .s0 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 272) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)
  have keepW : ∀ {d : Nat}, (288 ≤ d ∧ d + 8 ≤ 384) →
      t'.mem.readW (V .s0 + BitVec.ofNat 64 d) 64 = t.mem.readW (V .s0 + BitVec.ofNat 64 d) 64 := fun h =>
    P.frame.readW (r := ⟨V .s0 + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (d := 96) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (d := 272) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (d := 384 + 16 * i) (k := 16) (by omega) (by omega) (by omega)) (by decide)
  refine
    { env := F.env.others P.gpr P.sp P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      s4 := by rw [P.s4, show j + i + 1 = j + (i + 1) by omega]
      s6 := by rw [P.s6, show j + i + 2 = j + (i + 1) + 1 by omega]
      a7 := P.a7
      s5 := P.s5
      cn := by rw [keepW (by simp only [cnO]; omega), F.cn]
      hl := by rw [keepW (by simp only [hlO]; omega), F.hl]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega) (by decide), F.sum]
      l0 := by rw [keepB (by simp only [l0O]; omega) (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega) (by omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (hashR_mut F.frame) (by omega)]

theorem fill_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .s2) (V .s0) D n R ciph l A a s₀) {j c : Nat}
    (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16) {t : State}
    (F : FillInv V sp ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill (.nonzero .s5)) t fun t' => FillInv V sp ciph l A a s₀ j c t' c := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ FillInv V sp ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (fill_step C hc hjc hi F) fun u' F' => ?_
  have ev := eval_nonzero F'.s5 (by omega)
  by_cases he : i + 1 = c
  · left; exact ⟨ev.trans (by simp; omega), he ▸ F'⟩
  · right; exact ⟨ev.trans (by simp; omega), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

/-- The registers the sum loop writes. -/
abbrev sumRegs : List Reg := [.t1, .t2, .a7, .s5]

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {K W : Addr} (L : Lay K W) {t : State} (hs0 : t.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {k c : Nat} (hk : k < c) (hc : c ≤ 8) (ha7 : t.gpr .a7 = W + BitVec.ofNat 64 (384 + 16 * k))
    (hs5 : t.gpr .s5 = BitVec.ofNat 64 (c - k)) :
    WP isa (.block (xorB .s0 .a7 .s0 sumO 0 sumO ++ ([.addi .a7 .a7 16, .addi .s5 .s5 (-1)] : List Instr))) t
      fun t' => BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) sumRegs t t' ∧
      t'.gpr .a7 = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .s5 = BitVec.ofNat 64 (c - (k + 1)) := by
  have e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  have e8 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 (0 + 8) = W + BitVec.ofNat 64 (384 + 16 * k + 8) :=
    Offset.add_add _ _ _
  have sq₁ : Mem.Sep (W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 (0 + 8)) 8
      (W + BitVec.ofNat 64 sumO) 8 := by
    rw [e8]; exact Offset.sep W (.inr (by simp only [sumO]; omega)) (by omega) (by decide)
  refine WP.block_append (WP.mono (xorB_ok (s := t) (pd := sumO) (qd := 0) (cd := sumO) L.wal
    (L.alW (by omega)) L.wal (by decide) (by decide) (by decide) hs0 ha7 hs0 (by decide) (by decide) (by decide)
    (in_left (in_off hw (by decide) (by decide))) (in_left (in_off hw (by decide) (by decide)))
    (by rw [e0]; exact in_left (in_off hw (by omega) (by decide)))
    (by rw [e8]; exact in_left (in_off hw (by omega) (by decide))) (in_off hw (by decide) (by decide))
    (in_off hw (by decide) (by decide)) (Offset.sep W (by decide) (by decide) (by decide)) sq₁) fun t₁ B₁ => ?_)
  rw [e0] at B₁
  refine wp_addi (imm := 16) (by decide) fun t₂ u₂ => wp_subi (imm := 1) (by decide) fun t₃ u₃ =>
    WP.block_nil ?_
  refine ⟨⟨by rw [u₃.mem, u₂.mem]; exact B₁.frame, by rw [u₃.mem, u₂.mem]; exact B₁.val, fun r hr => ?_,
    by rw [u₃.sp, u₂.sp, B₁.sp], by rw [u₃.rd, u₂.rd, B₁.rd], by rw [u₃.wr, u₂.wr, B₁.wr]⟩, ?_, ?_⟩
  · simp only [sumRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2.2, u₂.other _ hr.2.2.1, B₁.gpr r (by simp [hr.1, hr.2.1])]
  · rw [u₃.other _ (by decide), u₂.gpr, B₁.gpr _ (by decide), ha7, Offset.add_add,
      show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega]
  · rw [u₃.gpr, u₂.other _ (by decide), B₁.gpr _ (by decide), hs5, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

theorem hashSum_ok {K W : Addr} (L : Lay K W) {t : State} (hs0 : t.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (ha7 : t.gpr .a7 = W + BitVec.ofNat 64 384)
    (hs5 : t.gpr .s5 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ∉ sumRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  unfold hashSum
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧
      u.gpr .a7 = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .s5 = BitVec.ofNat 64 (c - i) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ∉ sumRegs → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr) ?_
    (c - 0) _ ⟨0, rfl, hc0, ha7, hs5, Frame.refl _ _, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k u ⟨i, rfl, hi, a7, s5, fr, sum, gu, sp, rd, wr⟩
  refine WP.mono (sumStep_ok L (by rw [gu _ (by decide), hs0]) (by rw [wr]; exact hw) hi hc a7 s5)
    fun u' ⟨B, a7', s5'⟩ => ?_
  have hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega)) (by omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  have sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) =
      sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  have gu' : ∀ r, r ∉ sumRegs → u'.gpr r = t.gpr r := fun r hr => by rw [B.gpr r hr, gu r hr]
  have ev := eval_nonzero s5' (by omega)
  by_cases he : i + 1 = c
  · left
    exact ⟨ev.trans (by simp; omega), fr', he ▸ sum', gu', by rw [B.sp, sp], by rw [B.rd, rd],
      by rw [B.wr, wr]⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (i + 1), by omega, i + 1, rfl, by omega, a7', s5', fr',
      sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

theorem shr3 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The blocks left `k` (at `W + hlO`) to `t1`, and `k / 8` to `t2`. -/
theorem chunkLd_ok {K W : Addr} (L : Lay K W) {t : State} (hs0 : t.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {k : Nat} (hk : k < 2 ^ 63) (hl : t.mem.readW (W + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 k) :
    WP isa (.block [.load .d .t1 .s0 hlO, .shift .srl .d .t2 .t1 3]) t fun t₂ =>
      t₂.gpr .t1 = BitVec.ofNat 64 k ∧ t₂.gpr .t2 = BitVec.ofNat 64 (k / 8) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → t₂.gpr r = t.gpr r) ∧ Keeps t t₂ :=
  wp_ld (a := W + BitVec.ofNat 64 hlO) (by decide) (by rw [hs0]) (L.alW (by decide))
    (in_left (in_off hw (by decide) (by decide))) fun t₁ u₁ => wp_srl (by decide) fun t₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, hl], by rw [u₂.gpr, u₁.gpr, hl, shr3 (by omega)],
      fun r a b => by rw [u₂.other _ b, u₁.other _ a],
      ⟨by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩⟩

/-- The number of blocks of a chunk: `s5 ← min(8, k)`, `k` the blocks left (at `W + hlO`). -/
theorem chunkHead_ok {K W : Addr} (L : Lay K W) {t : State} (hs0 : t.gpr .s0 = W)
    (hw : Covers [⟨W, 2560⟩] t.wr) {k : Nat}
    (hk : k < 2 ^ 63) (hl : t.mem.readW (W + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 k) :
    WP isa (.seq (.block [.load .d .t1 .s0 hlO, .shift .srl .d .t2 .t1 3])
      (.ite (.zero .t2) (.block [Impl.AesGcm.RISCV64.mov .s5 .t1]) (.block [.li .s5 8]))) t fun t' =>
      t'.gpr .s5 = BitVec.ofNat 64 (min 8 k) ∧ (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .s5 → t'.gpr r = t.gpr r) ∧
      Keeps t t' := by
  refine WP.seq (WP.mono (chunkLd_ok L hs0 hw hk hl) fun t₂ ⟨r1₂, r2₂, g₂, k₂⟩ => ?_)
  by_cases h8 : k < 8
  · refine WP.ite true (by rw [eval_zero r2₂ (by omega)]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    refine wp_mv fun t₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, r1₂, Nat.min_eq_right (by omega)],
      fun r a b c => by rw [u₃.other _ c, g₂ r a b], k₂.trans ⟨u₃.mem, u₃.rd, u₃.wr, u₃.sp⟩⟩
  · refine WP.ite false (by rw [eval_zero r2₂ (by omega)]; simp; omega) (fun h => by cases h) (fun _ => ?_)
    refine wp_li (imm := 8) (by decide) fun t₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, Nat.min_eq_left (by omega)],
      fun r a b c => by rw [u₃.other _ c, g₂ r a b], k₂.trans ⟨u₃.mem, u₃.rd, u₃.wr, u₃.sp⟩⟩

/-- The `c` blocks of the buffer, their number at `W + cnO`. -/
theorem bufArgs_ok {K W : Addr} (L : Lay K W) {s : State} (hs0 : s.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {c : Nat} (hcn : s.mem.readW (W + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c) :
    ArgsOk [.addi .a2 .s0 (bufO : Int), .load .d .a3 .s0 cnO] s (W + BitVec.ofNat 64 384) c := by
  have hal : (s.gpr .s0 + BitVec.ofNat 64 cnO).toNat % 8 = 0 := by rw [hs0]; exact L.alW (by decide)
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .s0 + BitVec.ofNat 64 cnO) 8 := by
    rw [hs0]; exact in_left (in_off hw (by decide) (by decide))
  refine ⟨(s.write .a2 (s.gpr .s0 + BitVec.ofNat 64 bufO)).write .a3
      (s.mem.readW (s.gpr .s0 + BitVec.ofNat 64 cnO) 64), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hs0]; rfl,
    by rw [gpr_write_self, hs0, hcn], fun r h2 h3 => by rw [gpr_write_of_ne _ _ h3, gpr_write_of_ne _ _ h2],
    ⟨rfl, rfl, rfl, rfl⟩⟩
  rw [runBlock_cons, exec_addi_nat (by decide), runStep_some, runBlock_cons,
    exec_load_d (by decide) (by rwa [gpr_write_of_ne _ _ (by decide)])
      (by rwa [gpr_write_of_ne _ _ (by decide), rd_write, wr_write]),
    runStep_some, runBlock_nil, gpr_write_of_ne _ _ (by decide), mem_write]

/-- The frame of the counts at `W + cnO` and `W + hlO`. -/
theorem frame_counts (m : Mem) (W : Addr) (v w : BitVec 64) :
    Frame [⟨W + BitVec.ofNat 64 296, 16⟩] m ((m.writeW (W + BitVec.ofNat 64 296) v).writeW (W + BitVec.ofNat 64 304) w) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_pre _ (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains W (e := 296) (k := 16) (d := 304) (n := 8) (by decide) (by decide)
      (by decide))

/-- After the number `c` of blocks of a chunk in `s5`: the counts stored, the
buffer's start in `a7`, and the fill loop before its first block. -/
theorem chunkMid_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .s2) (V .s0) D n R ciph l A a s₀) {t t₁ : State}
    {j c : Nat} (H : HInv V sp ciph l A a s₀ t j) (hc : c ≤ a.length / 16 - j)
    (g₁ : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .s5 → t₁.gpr r = t.gpr r) (k₁ : Keeps t t₁)
    (h5 : t₁.gpr .s5 = BitVec.ofNat 64 c) :
    WP isa (.block [.store .d .s5 .s0 cnO, .load .d .t1 .s0 hlO, .sub .t1 .t1 .s5, .store .d .t1 .s0 hlO,
      .addi .a7 .s0 (bufO : Int)]) t₁ fun t₂ => FillInv V sp ciph l A a s₀ j c t₂ 0 := by
  have L := C.lay
  have hs := C.short
  have h0 : t₁.gpr .s0 = V .s0 := by rw [g₁ _ (by decide) (by decide) (by decide), H.env.s0]
  have hw : Covers [⟨V .s0, 2560⟩] t₁.wr := by rw [k₁.wr]; exact H.env.perm.w
  have hl₁ : t₁.mem.readW (V .s0 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [k₁.mem, H.hl]
  refine wp_sd (a := V .s0 + BitVec.ofNat 64 cnO) (by decide) (by rw [h0]) (L.alW (by decide))
    (in_off hw (by decide) (by decide)) fun t₂ u₂ => ?_
  refine wp_ld (a := V .s0 + BitVec.ofNat 64 hlO) (by decide) (by rw [u₂.gpr, h0]) (L.alW (by decide))
    (by rw [u₂.rd, u₂.wr]; exact in_left (in_off hw (by decide) (by decide))) fun t₃ u₃ => wp_sub fun t₄ u₄ => ?_
  have sep : Mem.Sep (V .s0 + BitVec.ofNat 64 hlO) (64 / 8) (V .s0 + BitVec.ofNat 64 cnO) (64 / 8) :=
    Offset.sep _ (by decide) (by decide) (by decide)
  have r1₄ : t₄.gpr .t1 = BitVec.ofNat 64 (a.length / 16 - j - c) := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.mem, u₂.gpr, h5, Mem.readW_writeW_sep sep (by decide), hl₁,
      Offset.ofNat_sub_ofNat hc]
  refine wp_sd (a := V .s0 + BitVec.ofNat 64 hlO) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h0]) (L.alW (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact in_off hw (by decide) (by decide)) fun t₅ u₅ => ?_
  refine wp_addi (imm := bufO) (by decide) fun t₆ u₆ => WP.block_nil ?_
  have m₆ : t₆.mem = (t.mem.writeW (V .s0 + BitVec.ofNat 64 296) (BitVec.ofNat 64 c)).writeW
      (V .s0 + BitVec.ofNat 64 304) (BitVec.ofNat 64 (a.length / 16 - j - c)) := by
    rw [u₆.mem, u₅.mem, r1₄, u₄.mem, u₃.mem, u₂.mem, h5, k₁.mem]; rfl
  have f₆ : Frame [⟨V .s0 + BitVec.ofNat 64 296, 16⟩] t.mem t₆.mem := by rw [m₆]; exact frame_counts _ _ _ _
  have kb : ∀ {d : Nat}, (d + 16 ≤ 296 ∨ 312 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₆.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem t.mem (V .s0 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => blockAtMem_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h₂ (by decide)
  have g₆ : ∀ r, r ∉ [.t1, .t2, .a7, .s5] → t₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.1, u₅.gpr, u₄.other _ hr.1, u₃.other _ hr.1, u₂.gpr, g₁ r hr.1 hr.2.1 hr.2.2.2]
  have sep' : Mem.Sep (V .s0 + BitVec.ofNat 64 cnO) (64 / 8) (V .s0 + BitVec.ofNat 64 304) (64 / 8) :=
    Offset.sep _ (by decide) (by decide) (by decide)
  refine
    { env := H.env.others g₆ (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, k₁.sp])
        (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, k₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, k₁.wr])
      frame := H.frame.trans (f₆.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact in_hashR (e := 296) (n := 16) (by simp) (by decide) (by decide))
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, k₁.rd, H.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, k₁.wr, H.wr]
      s4 := by rw [g₆ _ (by decide), H.s4]; rfl
      s6 := by rw [g₆ _ (by decide), H.s6]
      a7 := by rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h0]; rfl
      s5 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h5]; rfl
      cn := by rw [m₆, Mem.readW_writeW_sep sep' (by decide)]; exact Mem.readW_writeW_self64 _ _ _
      hl := by rw [m₆, show V .s0 + BitVec.ofNat 64 hlO = V .s0 + BitVec.ofNat 64 304 from rfl,
        Mem.readW_writeW_self64, Nat.sub_sub]
      oh := by rw [kb (by simp only [ohO]; omega) (by decide), H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [kb (by simp only [sumO]; omega) (by decide), H.sum]
      l0 := by rw [kb (by simp only [l0O]; omega) (by decide), H.l0] }

/-- A doubleword of `W` below the buffer, after the call on the buffer's `c ≤ 8` blocks. -/
theorem bufCall_readW {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {K W : Addr} (L : Lay K W)
    {t t' : State} {K' : Addr} {R c : Nat}
    (P : BPost f t K' (W + BitVec.ofNat 64 384) (W + BitVec.ofNat 64 512) R c t')
    (hc : c ≤ 8) {d : Nat} (hd : d + 8 ≤ 384) :
    t'.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  P.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inl (by omega)) (by omega) (by omega)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)) (by decide)

/-- The buffer's start to `a7` and its `c` blocks (at `W + cnO`) to `s5`. -/
theorem sumArgs_ok {K W : Addr} (L : Lay K W) {t : State} (hs0 : t.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {c : Nat} (hcn : t.mem.readW (W + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c) :
    WP isa (.block [.addi .a7 .s0 (bufO : Int), .load .d .s5 .s0 cnO]) t fun t₅ =>
      t₅.gpr .a7 = W + BitVec.ofNat 64 384 ∧ t₅.gpr .s5 = BitVec.ofNat 64 c ∧
      (∀ r, r ≠ .a7 → r ≠ .s5 → t₅.gpr r = t.gpr r) ∧ Keeps t t₅ :=
  wp_addi (imm := bufO) (by decide) fun t₄ u₄ => wp_ld (a := W + BitVec.ofNat 64 cnO)
    (by decide) (by rw [u₄.other _ (by decide), hs0]) (L.alW (by decide))
    (by rw [u₄.rd, u₄.wr]; exact in_left (in_off hw (by decide) (by decide))) fun t₅ u₅ => WP.block_nil
    ⟨by rw [u₅.other _ (by decide), u₄.gpr, hs0]; rfl, by rw [u₅.gpr, u₄.mem, hcn],
      fun r a b => by rw [u₅.other _ b, u₄.other _ a],
      ⟨by rw [u₅.mem, u₄.mem], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr], by rw [u₅.sp, u₄.sp]⟩⟩

/-- A chunk from the fill loop on, with its `c` blocks at `W + cnO`. -/
theorem chunkRest_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .s2) (V .s0) D n R ciph l A a s₀)
    (hs3 : V .s3 = BitVec.ofNat 64 R) {t : State} {j c : Nat} (F₀ : FillInv V sp ciph l A a s₀ j c t 0)
    (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16) :
    WP isa (.seq (.loop hashFill (.nonzero .s5))
      (.seq (.block (callArgs ++ ([.addi .a2 .s0 (bufO : Int), .load .d .a3 .s0 cnO] : List Instr)))
      (.seq encCall
      (.seq (.block [.addi .a7 .s0 (bufO : Int), .load .d .s5 .s0 cnO])
      (.seq hashSum (.block [.load .d .t1 .s0 hlO])))))) t
      fun t' => HInv V sp ciph l A a s₀ t' (j + c) := by
  have L := C.lay
  have hs := C.short
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) L
    Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames C.rounds hs3 F.env
    (fun s₁ g₁ k₁ => bufArgs_ok L (by rw [g₁ _ (by decide) (by decide) (by decide), F.env.s0])
      (by rw [k₁.wr]; exact F.env.perm.w) (by rw [k₁.mem, F.cn]))
    (dstW L F.env.perm (d := 384) (n := c) (by omega))) fun t₃ P₃ => ?_))
  have E₃ := P₃.env F.env
  have F₃ : Frame (hashR (V .s0)) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by omega)
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by decide)
  have k₃ : ∀ {d : Nat}, d + 16 ≤ 384 →
      blockAtMem t₃.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have kw₃ : ∀ {d : Nat}, d + 8 ≤ 384 →
      t₃.mem.readW (V .s0 + BitVec.ofNat 64 d) 64 = t₂.mem.readW (V .s0 + BitVec.ofNat 64 d) 64 := fun hd =>
    bufCall_readW L P₃ hc hd
  have hg : ∀ k < c, blockAtMem t₃.mem (V .s0 + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (hashR_mut F.frame)) _
  have h0₃ := E₃.s0
  have hw₃ : Covers [⟨V .s0, 2560⟩] t₃.wr := E₃.perm.w
  have cn₃ : t₃.mem.readW (V .s0 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c := by
    rw [kw₃ (by decide), F.cn]
  refine WP.seq (WP.mono (sumArgs_ok L h0₃ hw₃ cn₃) ?_)
  rintro t₅ ⟨a7₅, s5₅, g₅, k₅⟩
  have hg₅ : ∀ k < c, blockAtMem t₅.mem (V .s0 + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by rw [k₅.mem, hg k hk]
  refine WP.seq (WP.mono (hashSum_ok L (by rw [g₅ _ (by decide) (by decide), h0₃]) (by rw [k₅.wr]; exact hw₃)
    hc0 hc a7₅ s5₅ hg₅) fun t₆ ⟨fr₆, sum₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  have h0₆ : t₆.gpr .s0 = V .s0 := by rw [g₆ _ (by decide), g₅ _ (by decide) (by decide), h0₃]
  have kb₆ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₆.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem t₃.mem (V .s0 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => by
      rw [blockAtMem_frame fr₆ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂
          (by decide), k₅.mem]
  have hl₆ : t₆.mem.readW (V .s0 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - (j + c)) := by
    rw [fr₆.readW (r := ⟨V .s0 + BitVec.ofNat 64 hlO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), k₅.mem, kw₃ (by decide), F.hl]
  refine wp_ld (a := V .s0 + BitVec.ofNat 64 hlO) (by decide) (by rw [h0₆]) (L.alW (by decide))
    (by rw [rd₆, wr₆, k₅.rd, k₅.wr]; exact in_left (in_off hw₃ (by decide) (by decide))) fun t₇ u₇ =>
    WP.block_nil ?_
  have g₇ : ∀ r, r ∉ sumRegs → t₇.gpr r = t₃.gpr r := fun r hr => by
    simp only [sumRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.1, g₆ r (by simp [sumRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), g₅ r hr.2.2.1 hr.2.2.2]
  refine
    { env := E₃.others g₇ (by rw [u₇.sp, sp₆, k₅.sp]) (by rw [u₇.rd, rd₆, k₅.rd]) (by rw [u₇.wr, wr₆, k₅.wr])
      frame := F.frame.trans (F₃.trans ((by rw [k₅.mem]; exact Frame.refl _ _ : Frame [] t₃.mem t₅.mem).mono
        (by simp) |>.trans ((fr₆.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact in_hashR (e := 48) (n := 16) (by simp) (by decide) (by decide)).trans
          ((by rw [u₇.mem]; exact Frame.refl _ _ : Frame [] t₆.mem t₇.mem).mono (by simp)))))
      rd := by rw [u₇.rd, rd₆, k₅.rd, P₃.rd, F.rd]
      wr := by rw [u₇.wr, wr₆, k₅.wr, P₃.wr, F.wr]
      le := by omega
      sum := by rw [u₇.mem, sum₆, k₅.mem, k₃ (by decide), F.sum, hsum_add]
      oh := by rw [u₇.mem, kb₆ (by simp only [ohO]; omega) (by decide), k₃ (by decide), F.oh]
      s4 := by rw [g₇ _ (by decide), P₃.saved _ (by decide), F.s4]
      s6 := by rw [g₇ _ (by decide), P₃.saved _ (by decide), F.s6]
      t1 := by rw [u₇.gpr, hl₆]
      hl := by rw [u₇.mem, hl₆]
      l0 := by rw [u₇.mem, kb₆ (by simp only [l0O]; omega) (by decide), k₃ (by decide), F.l0] }

theorem hashChunk_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .s2) (V .s0) D n R ciph l A a s₀)
    (hs3 : V .s3 = BitVec.ofNat 64 R) {t : State} {j : Nat} (H : HInv V sp ciph l A a s₀ t j)
    (hj : j < a.length / 16) :
    WP isa hashChunk t fun t' => HInv V sp ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) := by
  have hs := C.short
  unfold hashChunk
  refine WP.assoc (WP.seq (WP.mono (chunkHead_ok (k := a.length / 16 - j) C.lay H.env.s0 H.env.perm.w
    (by omega) H.hl) fun t₁ ⟨h5, g₁, k₁⟩ => ?_))
  refine WP.seq (WP.mono (chunkMid_ok C H (by omega) g₁ k₁ h5) fun t₂ F₀ => ?_)
  exact chunkRest_ok C hs3 F₀ (by omega) (by omega) (by omega)

end VG.Proof.AesOcb.RISCV64
