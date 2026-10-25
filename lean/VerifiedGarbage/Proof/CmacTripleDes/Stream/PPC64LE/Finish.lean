module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Calls
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Copy
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common
public import VerifiedGarbage.Proof.Cmac.Mem
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Streaming TDEA-CMAC on PPC64LE: `finish`

`finish_wp`: `finish` writes to `out` the cipher, under the schedule in the
state, of the chaining value XORed with the last block (`lastBlock`) of the
bytes held back, which `held count` gives the number of: `K1` XORed with
them if they are a complete block, else `K2` XORed with them padded. The
padded block is built in the working space (`padOff`): zeroed, the bytes
held back copied onto it (`copyLoop_wp`), and `0x80` after them
(`padded_bytes8`). `finish_spec` is then `tdesFinishPost`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)
open VG.Proof.CmacTripleDes.Stream (held)

/-- `finish`'s precondition, with the working space of 640 bytes at `r6`. -/
structure FinishPre (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .r3, 416⟩, ⟨s.gpr .r5, 8⟩, ⟨s.gpr .r6, 640⟩]
  stateOut : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r5, 8⟩
  stateScr : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r6, 640⟩
  outScr : Region.Disjoint ⟨s.gpr .r5, 8⟩ ⟨s.gpr .r6, 640⟩
  stateFit : (s.gpr .r3).toNat + 416 ≤ 2 ^ 64
  outFit : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  scrFit : (s.gpr .r6).toNat + 640 ≤ 2 ^ 64

/-- The last block `finish` enciphers: the chaining value XORed with the
last block of the bytes held back. -/
abbrev finBlock (m : Mem) (S : Addr) (h : Nat) : List Byte :=
  Spec.Cmac.xor (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 400) 8)
    (Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 384) 8)
      (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 408) h))

theorem xor3 (a b c : BitVec 64) : a ^^^ b ^^^ c = c ^^^ (b ^^^ a) := by
  rw [BitVec.xor_comm (a ^^^ b), BitVec.xor_comm a]

theorem le8_xor3 (a b c : BitVec 64) : le8 (a ^^^ b ^^^ c) = Spec.Cmac.xor (le8 c) (Spec.Cmac.xor (le8 b) (le8 a)) := by
  rw [xor3, Proof.Cmac.le8_xor, Proof.Cmac.le8_xor]

/-- After the branch: the block to encipher in the buffer, the memory but
the working space unchanged, and the registers but the temporaries. -/
structure BufReady (t u : State) (S B : Addr) (h : Nat) : Prop where
  buf : Spec.Aes.bytesAt u.mem (B + BitVec.ofNat 64 512) 8 = finBlock t.mem S h
  frame : Frame [⟨B, 528⟩] t.mem u.mem
  regs : ∀ r, r ≠ .r0 → r ≠ .r7 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → u.gpr r = t.gpr r
  rd : u.rd = t.rd
  wr : u.wr = t.wr

theorem complete_wp {t : State} {S B : Addr} (h3 : t.gpr .r3 = S) (h5 : t.gpr .r5 = B)
    (hS : (⟨S, 416⟩ : Region) ∈ t.wr) (hW : (⟨B, 640⟩ : Region) ∈ t.wr) :
    WP isa (.block complete) t fun u => BufReady t u S B 8 := by
  have inS : ∀ off, off + 8 ≤ 416 → InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, List.mem_append_right _ hS, VG.Offset.contains_base _ h (by omega_arith)⟩
  simp only [complete]
  refine wp_ld (a := S + BitVec.ofNat 64 408) (by decide) (by decide) (by rw [h3]) (inS 408 (by decide))
    fun s₁ u₁ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 384) (by decide) (by decide) (by rw [u₁.other _ (by decide), h3])
    (by rw [u₁.rd, u₁.wr]; exact inS 384 (by decide)) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 400) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h3])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact inS 400 (by decide)) fun s₄ u₄ => wp_xor fun s₅ u₅ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h5]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₆ u₆ => wp_nil ?_
  have m₅ : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have w : s₅.gpr .r7 = t.mem.readW (S + BitVec.ofNat 64 408) 64 ^^^ t.mem.readW (S + BitVec.ofNat 64 384) 64 ^^^
      t.mem.readW (S + BitVec.ofNat 64 400) 64 := by
    have a3 : s₃.gpr .r7 = t.mem.readW (S + BitVec.ofNat 64 408) 64 ^^^ t.mem.readW (S + BitVec.ofNat 64 384) 64 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
    have b4 : s₄.gpr .r9 = t.mem.readW (S + BitVec.ofNat 64 400) 64 := by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
    rw [u₅.gpr, u₄.other _ (by decide), a3, b4]
  refine ⟨?_, ?_, fun r h0 h7 h9 _ _ _ => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · rw [u₆.mem, m₅, w, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, le8_xor3, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, finBlock, Spec.Cmac.lastBlock,
      ite_eq_left (by simp [Spec.Aes.bytesAt] : (Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) 8).length = 8)]
  · rw [u₆.mem, m₅]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 528 by decide)
      (by decide))
  · rw [u₆.gpr, u₅.other r h7, u₄.other r h9, u₃.other r h7, u₂.other r h9, u₁.other r h7]

theorem sub_add_ofNat (C : Addr) {k : Nat} (hk : k < 2 ^ 64) : (C + BitVec.ofNat 64 k - C).toNat = k :=
  Mem.sub_ofNat_toNat C hk

theorem add_ofNat_inj (C : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : C + BitVec.ofNat 64 i = C + BitVec.ofNat 64 j) : i = j := by
  have := congrArg (fun a => (a - C).toNat) h
  simp only [sub_add_ofNat C hi, sub_add_ofNat C hj] at this
  exact this

/-- The padded block: the bytes copied onto zeros, and `0x80` after them, as
`padded_bytes8` has it. -/
theorem pad_bytes {m₀ mc : Mem} {S C : Addr} {h : Nat} (hh : h < 8)
    (hcopied : ∀ i < h, mc (C + BitVec.ofNat 64 i) = (m₀.writeW C (0 : BitVec 64)) (S + BitVec.ofNat 64 (408 + i)))
    (hrest : ∀ x, (∀ i < h, x ≠ C + BitVec.ofNat 64 i) → mc x = (m₀.writeW C (0 : BitVec 64)) x)
    (hsep : ∀ i < h, (m₀.writeW C (0 : BitVec 64)) (S + BitVec.ofNat 64 (408 + i)) = m₀ (S + BitVec.ofNat 64 (408 + i))) :
    Spec.Aes.bytesAt (mc.writeW (C + BitVec.ofNat 64 h) ((BitVec.ofNat 64 0x80).setWidth 8)) C 8 =
      Spec.Aes.bytesAt m₀ (S + BitVec.ofNat 64 408) h ++ [0x80] ++
        Spec.Cmac.zeros (8 - (Spec.Aes.bytesAt m₀ (S + BitVec.ofNat 64 408) h).length - 1) := by
  have hlen : (Spec.Aes.bytesAt m₀ (S + BitVec.ofNat 64 408) h).length = h := by simp [Spec.Aes.bytesAt]
  rw [← padded_bytes8 (m₀.writeW C (0 : BitVec 64)) C _ (by rw [hlen]; exact hh) (by
      rw [← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_zero]), hlen]
  refine List.map_congr_left fun k hk => ?_
  have hk := List.mem_range.mp hk
  rw [VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
    show ((BitVec.ofNat 64 0x80).setWidth 8 : Byte) = 0x80 from rfl]
  split
  · rfl
  · rename_i hne
    simp only [VG.WriteBytes.writeBytes, sub_add_ofNat C (show k < 2 ^ 64 by omega_arith), hlen]
    by_cases hkh : k < h
    · rw [ite_eq_left hkh, hcopied k hkh, hsep k hkh, Proof.Cmac.getD_bytesAt _ _ hkh, VG.Offset.add_add]
    · rw [ite_eq_right hkh, hrest _ fun i hi e => hkh (by
        have := add_ofNat_inj C (show k < 2 ^ 64 by omega_arith) (show i < 2 ^ 64 by omega_arith) e; omega_arith)]

theorem padded_wp {t : State} {S B : Addr} {h : Nat} (hh : h < 8) (h3 : t.gpr .r3 = S) (h5 : t.gpr .r5 = B)
    (h8 : t.gpr .r8 = BitVec.ofNat 64 h)
    (hS : (⟨S, 416⟩ : Region) ∈ t.wr) (hW : (⟨B, 640⟩ : Region) ∈ t.wr) (hd : Region.Disjoint ⟨S, 416⟩ ⟨B, 640⟩) :
    WP isa padded t fun u => BufReady t u S B h := by
  have inS : ∀ off, off + 8 ≤ 416 → InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, List.mem_append_right _ hS, VG.Offset.contains_base _ h (by omega_arith)⟩
  -- The state's bytes and the working space's are apart.
  have sep1 : ∀ i j, i < 416 → j < 640 → S + BitVec.ofNat 64 i ≠ B + BitVec.ofNat 64 j := fun i j hi hj e =>
    hd _ (VG.Offset.contains_base _ (show i + 1 ≤ 416 by omega_arith) (by omega_arith))
      (by rw [e]; exact VG.Offset.contains_base _ (show j + 1 ≤ 640 by omega_arith) (by omega_arith))
  unfold padded
  refine WP.seq ?_
  simp only [padStart, mr]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 padOff) (by decide) (by decide) (by rw [u₁.other _ (by decide), h5])
    (by rw [u₁.wr]; exact scr_in hW (by decide)) fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  have m₅ : s₅.mem = t.mem.writeW (B + BitVec.ofNat 64 520) (0 : BitVec 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl
  have g₅ : ∀ r, r ≠ .r0 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s₅.gpr r = t.gpr r := fun r h0 h10 h11 h12 => by
    rw [u₅.other r h12, u₄.other r h11, u₃.other r h10, u₂.gpr, u₁.other r h0]
  have wr₅ : s₅.wr = t.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₅ : s₅.rd = t.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine WP.seq (copyLoop_wp (src := S + BitVec.ofNat 64 408) (dst := B + BitVec.ofNat 64 520) (n := h)
    (by omega_arith) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h3])
    (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h5, padOff])
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h8])
    (fun i hi => by
      rw [rd₅, wr₅, VG.Offset.add_add]
      exact ⟨_, List.mem_append_right _ hS, VG.Offset.contains_base _ (show 408 + i + 1 ≤ 416 by omega_arith) (by omega_arith)⟩)
    (fun i hi => by
      rw [wr₅, VG.Offset.add_add]
      exact ⟨_, hW, VG.Offset.contains_base _ (show 520 + i + 1 ≤ 640 by omega_arith) (by omega_arith)⟩)
    (fun i hi i' hi' => by rw [VG.Offset.add_add, VG.Offset.add_add]; exact sep1 _ _ (by omega_arith) (by omega_arith))
    fun c hc => ?_)
  have c3 : c.gpr .r3 = S := by rw [hc.regs _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide)
    (by decide) (by decide) (by decide), h3]
  have c5 : c.gpr .r5 = B := by rw [hc.regs _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide)
    (by decide) (by decide) (by decide), h5]
  have cwr : c.wr = t.wr := by rw [hc.wr, wr₅]
  have crd : c.rd = t.rd := by rw [hc.rd, rd₅]
  -- The memory but the working space is unchanged.
  have fc : Frame [⟨B, 528⟩] t.mem c.mem := by
    intro x hx
    rw [hc.rest x fun i hi e => hx _ List.mem_cons_self (by
        rw [e, VG.Offset.add_add]; exact VG.Offset.contains_base _ (show 520 + i + 1 ≤ 528 by omega_arith) (by omega_arith)), m₅]
    exact ((Frame.refl [(⟨B, 528⟩ : Region)] t.mem).writeW List.mem_cons_self (0 : BitVec 64)
      (VG.Offset.contains_base _ (show 520 + 64 / 8 ≤ 528 by decide) (by decide))) x hx
  simp only [padDone]
  refine wp_li (by decide) fun c₁ u₁ => ?_
  refine wp_stb (a := B + BitVec.ofNat 64 520 + BitVec.ofNat 64 h) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), hc.r11]; exact BitVec.add_zero _)
    (by rw [u₁.wr, cwr, VG.Offset.add_add]
        exact ⟨_, hW, VG.Offset.contains_base _ (show 520 + h + 1 ≤ 640 by omega_arith) (by omega_arith)⟩) fun c₂ u₂ => ?_
  have m₂ : c₂.mem = c.mem.writeW (B + BitVec.ofNat 64 520 + BitVec.ofNat 64 h) ((BitVec.ofNat 64 0x80).setWidth 8) := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
  have f₂ : Frame [⟨B, 528⟩] t.mem c₂.mem := by
    rw [m₂, VG.Offset.add_add]
    exact fc.writeW List.mem_cons_self _ (VG.Offset.contains_base _ (show 520 + h + 8 / 8 ≤ 528 by omega_arith) (by omega_arith))
  have rdS : ∀ off, off + 8 ≤ 416 → c₂.mem.readW (S + BitVec.ofNat 64 off) 64 = t.mem.readW (S + BitVec.ofNat 64 off) 64 :=
    fun off h => f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_right (Region.sub_prefix (by decide))).sub_left (VG.Offset.sub_base _ h)) (by decide)
  have hrd₂ : ∀ off, off + 8 ≤ 416 → InRegions (c₂.rd ++ c₂.wr) (S + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, crd, cwr]; exact inS off h
  refine wp_ld (a := B + BitVec.ofNat 64 padOff) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), c5])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, crd, cwr]; exact scr_rd hW (by decide)) fun c₃ u₃ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 392) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c3])
    (by rw [u₃.rd, u₃.wr]; exact hrd₂ 392 (by decide)) fun c₄ u₄ => wp_xor fun c₅ u₅ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 400) (by decide) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c3])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact hrd₂ 400 (by decide)) fun c₆ u₆ => wp_xor fun c₇ u₇ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c5]; rfl)
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, cwr]; exact scr_in hW (by decide)) fun c₈ u₈ => wp_nil ?_
  have m₇ : c₇.mem = c₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have a5 : c₅.gpr .r7 = c₂.mem.readW (B + BitVec.ofNat 64 padOff) 64 ^^^ c₂.mem.readW (S + BitVec.ofNat 64 392) 64 := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, u₃.mem]
  have w : c₇.gpr .r7 = c₂.mem.readW (B + BitVec.ofNat 64 padOff) 64 ^^^ c₂.mem.readW (S + BitVec.ofNat 64 392) 64 ^^^
      c₂.mem.readW (S + BitVec.ofNat 64 400) 64 := by
    rw [u₇.gpr, u₆.other _ (by decide), a5, u₆.gpr, u₅.mem, u₄.mem, u₃.mem]
  have pad : Spec.Aes.bytesAt c₂.mem (B + BitVec.ofNat 64 padOff) 8 =
      Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) h ++ [0x80] ++
        Spec.Cmac.zeros (8 - (Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) h).length - 1) := by
    rw [m₂]
    refine pad_bytes hh (fun i hi => ?_) (fun x hx => ?_) (fun i hi => ?_)
    · rw [hc.copied i hi, m₅, VG.Offset.add_add]
    · rw [hc.rest x hx, m₅]
    · exact ((Frame.refl [(⟨B + BitVec.ofNat 64 520, 8⟩ : Region)] t.mem).writeW List.mem_cons_self (0 : BitVec 64)
        (Region.contains_self _ _)) _ fun r hr hcon => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hd _ (VG.Offset.contains_base _ (show 408 + i + 1 ≤ 416 by omega_arith) (by omega_arith))
            ((VG.Offset.sub_base B (show 520 + 8 ≤ 640 by decide)) _ hcon)
  have hlen : (Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) h).length ≠ 8 := by
    simp [Spec.Aes.bytesAt]; omega_arith
  refine ⟨?_, ?_, fun r h0 h7 h9 h10 h11 h12 => ?_, ?_, ?_⟩
  · rw [u₈.mem, m₇, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, w, rdS 392 (by decide), rdS 400 (by decide),
      le8_xor3, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, pad, finBlock,
      Spec.Cmac.lastBlock, ite_eq_right hlen]
  · rw [u₈.mem, m₇]
    exact f₂.writeW List.mem_cons_self _ (VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 528 by decide) (by decide))
  · rw [u₈.gpr, u₇.other r h7, u₆.other r h9, u₅.other r h7, u₄.other r h9, u₃.other r h7, u₂.gpr,
      u₁.other r h9, hc.regs r h0 h10 h11 h12, g₅ r h0 h10 h11 h12]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, crd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, cwr]

/-- `finBlock` reads only the state. -/
theorem finBlock_frame {m m' : Mem} {S B : Addr} {h : Nat} (hh : h ≤ 8) (hf : Frame [⟨B, 640⟩] m m')
    (hd : Region.Disjoint ⟨S, 416⟩ ⟨B, 640⟩) : finBlock m' S h = finBlock m S h := by
  have e : ∀ off n, off + n ≤ 416 → Spec.Aes.bytesAt m' (S + BitVec.ofNat 64 off) n =
      Spec.Aes.bytesAt m (S + BitVec.ofNat 64 off) n := fun off n hn =>
    List.map_congr_left fun i hi => hf.bytes (R := ⟨S + BitVec.ofNat 64 off, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_left (VG.Offset.sub_base _ hn))
      (by show n ≤ 2 ^ 64; omega_arith) (List.mem_range.mp hi)
  rw [finBlock, finBlock, e 400 8 (by decide), e 384 8 (by decide), e 392 8 (by decide), e 408 h (by omega_arith)]

theorem finishSave_wp {s : State} (hp : FinishPre s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r31 = s.gpr .r5 → t.gpr .r5 = s.gpr .r6 →
      (∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r31 → t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.mem = (s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 lrOff) s.lr).writeW (s.gpr .r6 + BitVec.ofNat 64 r31Off)
        (s.gpr .r31) → WP isa (.block is) t Q) :
    WP isa (.block (finishSave ++ is)) s Q := by
  have hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  simp only [finishSave, mr, List.cons_append, List.nil_append]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]; exact scr_in hW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₃ u₃ => ?_
  refine wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => ?_
  refine k s₅ ?_ ?_ (fun r h0 h5 h31 => ?_) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) ?_
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.other r h5, u₄.other r h31, u₃.gpr, u₂.gpr, u₁.other r h0]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₂.gpr, u₁.gpr, u₁.mem, u₁.other _ (by decide)]

theorem ofNat_sub8_eq_zero {h : Nat} (hh : h ≤ 8) :
    (BitVec.ofNat 64 h - BitVec.ofNat 64 8 == 0) = decide (h = 8) := by
  by_cases e : h = 8
  · subst e; rfl
  · rw [decide_eq_false e]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    simp at this
    omega_arith

theorem finish_wp (s : State) (hp : FinishPre s) :
    WP isa finish s fun f => (∀ r ∈ preserved, f.gpr r = s.gpr r) ∧ f.lr = s.lr ∧
      Spec.Aes.bytesAt f.mem (s.gpr .r5) 8 = Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
        (finBlock s.mem (s.gpr .r3) (held (s.gpr .r4).toNat)) := by
  have hS : (⟨s.gpr .r3, 416⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hO : (⟨s.gpr .r5, 8⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hfitB := hp.scrFit
  have hh := Proof.CmacTripleDes.Stream.held_le (s.gpr .r4).toNat
  have cB : ∀ off, off + 8 ≤ 640 → (⟨s.gpr .r6, 640⟩ : Region).Contains (s.gpr .r6 + BitVec.ofNat 64 off) (64 / 8) :=
    fun off h => VG.Offset.contains_base _ h (by omega_arith)
  unfold finish
  refine WP.seq ?_
  rw [← List.append_nil finishSave]
  refine finishSave_wp hp fun t t31 t5 tg trd twr tm => wp_nil ?_
  have F0 : Frame [⟨s.gpr .r6, 640⟩] s.mem t.mem := by
    rw [tm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cB lrOff (by decide))).writeW List.mem_cons_self _
      (cB r31Off (by decide))
  refine WP.seq (heldCode_wp (s.gpr .r4).isLt (by rw [tg _ (by decide) (by decide) (by decide),
    BitVec.ofNat_toNat, BitVec.setWidth_eq]) fun t₁ h8 g₁ m₁ rd₁ wr₁ => ?_)
  refine WP.seq (wp_subi (by decide) (by decide) fun t₂ u₂ => wp_nil (Q := fun t₂ =>
      WP isa (.seq (.ite (.zero .d .r9) (.block complete) padded) (.seq (.block [.addi .r4 .r5 bufOff])
        (.seq encCall (.block finishOut)))) t₂ _) ?_)
  have r3₂ : t₂.gpr .r3 = s.gpr .r3 := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide),
    tg _ (by decide) (by decide) (by decide)]
  have r5₂ : t₂.gpr .r5 = s.gpr .r6 := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), t5]
  have r8₂ : t₂.gpr .r8 = BitVec.ofNat 64 (held (s.gpr .r4).toNat) := by rw [u₂.other _ (by decide), h8]
  have wr₂ : t₂.wr = s.wr := by rw [u₂.wr, wr₁, twr]
  have rd₂ : t₂.rd = s.rd := by rw [u₂.rd, rd₁, trd]
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, m₁]
  -- The branch, to the block in the buffer.
  have hb : WP isa (.ite (.zero .d .r9) (.block complete) padded) t₂
      (fun u => BufReady t₂ u (s.gpr .r3) (s.gpr .r6) (held (s.gpr .r4).toNat)) := by
    have ev : isa.eval (.zero .d .r9) t₂ = some (decide (held (s.gpr .r4).toNat = 8)) := by
      rw [eval_zero, u₂.gpr, h8, ofNat_sub8_eq_zero hh]
    by_cases e8 : held (s.gpr .r4).toNat = 8
    · refine WP.ite true (by rw [ev, decide_eq_true e8]) (fun _ => ?_) (fun h => by cases h)
      rw [e8]
      exact complete_wp r3₂ r5₂ (by rw [wr₂]; exact hS) (by rw [wr₂]; exact hW)
    · refine WP.ite false (by rw [ev, decide_eq_false e8]) (fun h => by cases h) fun _ => ?_
      exact padded_wp (by omega_arith) r3₂ r5₂ r8₂ (by rw [wr₂]; exact hS) (by rw [wr₂]; exact hW) hp.stateScr
  refine WP.seq (WP.mono hb fun u hu => ?_)
  have wru : u.wr = s.wr := by rw [hu.wr, wr₂]
  have rdu : u.rd = s.rd := by rw [hu.rd, rd₂]
  have ug : ∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
      u.gpr r = t.gpr r := fun r h0 h4 h7 h8 h9 h10 h11 h12 => by
    rw [hu.regs r h0 h7 h9 h10 h11 h12, u₂.other r h9, g₁ r h8 h9]
  refine WP.seq (wp_addi (n := .r5) (by decide) (by decide) fun u₁ v₁ => wp_nil ?_)
  have u3 : u₁.gpr .r3 = s.gpr .r3 := by
    rw [v₁.other _ (by decide), ug _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), tg _ (by decide) (by decide) (by decide)]
  have u5 : u₁.gpr .r5 = s.gpr .r6 := by
    rw [v₁.other _ (by decide), ug _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), t5]
  refine WP.seq (encCall_wp u3 (by rw [v₁.gpr, ← u5, v₁.other _ (by decide)]; rfl) u5
    ⟨_, List.mem_append_right _ (by rw [v₁.wr, wru]; exact hS), VG.Offset.contains_base _ (show 0 + 384 ≤ 416 by decide)
      (by decide) |> fun h => by simpa using h⟩ (by rw [v₁.wr, wru]; exact hW) (Nat.le_refl _)
    (hp.stateScr.sub_left (Region.sub_prefix (by decide))) fun v rdv wrv cv v3 v4 v5 fv outv => ?_)
  have wrv' : v.wr = s.wr := by rw [wrv, v₁.wr, wru]
  have rdv' : v.rd = s.rd := by rw [rdv, v₁.rd, rdu]
  have v31 : v.gpr .r31 = s.gpr .r5 := by
    rw [cv _ (by decide), v₁.other _ (by decide), ug _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), t31]
  simp only [finishOut]
  refine wp_ld (a := s.gpr .r6 + BitVec.ofNat 64 bufOff) (by decide) (by decide) (by rw [v5])
    (by rw [rdv', wrv']; exact scr_rd hW (by decide)) fun w₁ x₁ => ?_
  refine wp_std (a := s.gpr .r5) (by decide) (by decide)
    (by rw [x₁.other _ (by decide), v31]; exact BitVec.add_zero _)
    (by rw [x₁.wr, wrv']; exact ⟨_, hO, Region.contains_self _ _⟩) fun w₂ x₂ => ?_
  have hR : ∀ off, off + 8 ≤ 640 → InRegions (w₂.rd ++ w₂.wr) (s.gpr .r6 + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [x₂.rd, x₂.wr, x₁.rd, x₁.wr, rdv', wrv']; exact scr_rd hW h
  refine wp_ld (a := s.gpr .r6 + BitVec.ofNat 64 lrOff) (by decide) (by decide)
    (by rw [x₂.gpr, x₁.other _ (by decide), v5]) (hR lrOff (by decide)) fun w₃ x₃ => ?_
  refine wp_ld (a := s.gpr .r6 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [x₃.other _ (by decide), x₂.gpr, x₁.other _ (by decide), v5])
    (by rw [x₃.rd, x₃.wr]; exact hR r31Off (by decide)) fun w₄ x₄ => wp_mtlr (wp_nil ?_)
  -- The memory.
  have mw₂ : w₂.mem = v.mem.writeW (s.gpr .r5) (v.mem.readW (s.gpr .r6 + BitVec.ofNat 64 bufOff) 64) := by
    rw [x₂.mem, x₁.gpr, x₁.mem]
  have Fu : Frame [⟨s.gpr .r6, 640⟩] s.mem u.mem := F0.trans (by
    rw [← m₂]; exact hu.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  -- The saved slots, through the branch, the call and the output.
  have slot : ∀ off, 528 ≤ off → off + 8 ≤ 640 → w₂.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 =
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 := fun off h1 h2 => by
    rw [mw₂, readW_sep64 ((hp.outScr.sub_right (VG.Offset.sub_base _ h2)).symm),
      fv.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide), v₁.mem,
      hu.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide), m₂]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases e31 : r = .r31
    · subst e31
      show w₄.gpr .r31 = _
      rw [x₄.gpr, x₃.mem, slot r31Off (by decide) (by decide), tm, Mem.readW_writeW_self64]
    obtain ⟨h0, h3', h4', h5', h6', h7', h8', h9', h10', h11', h12'⟩ := preserved_ne r hr
    show w₄.gpr r = _
    rw [x₄.other r e31, x₃.other r h0, x₂.gpr, x₁.other r h7', cv r hr, v₁.other r h4',
      ug r h0 h4' h7' h8' h9' h10' h11' h12', tg r h0 h5' e31]
  · show w₄.gpr .r0 = _
    rw [x₄.other _ (by decide), x₃.gpr, slot lrOff (by decide) (by decide), tm,
      readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · show Spec.Aes.bytesAt w₄.mem (s.gpr .r5) 8 = _
    rw [x₄.mem, x₃.mem, mw₂, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW, bufOff,
      VG.Proof.TripleDes.bytesAt_eq, outv, v₁.mem, Proof.TripleDes.scheduleAt_eq_of_frame _ Fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.stateScr.sub_left (Region.sub_prefix (by decide))),
      ← VG.Proof.TripleDes.ofFn_bytesAt, hu.buf, m₂, finBlock_frame hh F0 hp.stateScr]
    rfl

/-- The block `finish` enciphers, for a state that represents `msg`: its
cipher is the MAC. -/
theorem finish_spec {m : Mem} {S : Addr} {key msg : List Byte} (hr : Spec.Cmac.tdesRepr m S key msg) :
    Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m S) (finBlock m S (held msg.length)) =
      Spec.Cmac.tdesCmac key 8 msg := by
  obtain ⟨hm, hne, hc, hcat⟩ := Proof.CmacTripleDes.Stream.repr_finish hr
  obtain ⟨-, hs, hk, -, -⟩ := hr
  have hks : Spec.Aes.bytesAt m (S + BitVec.ofNat 64 384) 8 = (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).1 ∧
      Spec.Aes.bytesAt m (S + BitVec.ofNat 64 392) 8 = (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).2 := by
    have hl1 : (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).1.length = 8 := by
      rw [Spec.Cmac.tdes, Proof.CmacTripleDes.subkeys_tdes]; exact Proof.Cmac.length_le8 _
    have e := hk
    rw [show (S + 384 : Addr) = S + BitVec.ofNat 64 384 from rfl, Proof.Cmac.bytesAt_split, VG.Offset.add_add,
      show (384 + 8 : Nat) = 392 from rfl] at e
    exact List.append_inj e (by simp [Spec.Aes.bytesAt, hl1])
  have hl := Proof.CmacTripleDes.Stream.held_le msg.length
  rw [Proof.CmacTripleDes.Stream.tdesCmac_eq]
  conv => rhs; rw [← hcat]
  rw [Proof.CmacTripleDes.macFull_split8 _ hm (by simp [Spec.Aes.bytesAt]; omega_arith) (by
      rcases hne with h | h
      · exact .inl h
      · exact .inr (by simp [Spec.Aes.bytesAt]; omega_arith)),
    ← hc, ← hks.1, ← hks.2, hs]
  rfl

end VG.Proof.CmacTripleDes.Stream.PPC64LE
