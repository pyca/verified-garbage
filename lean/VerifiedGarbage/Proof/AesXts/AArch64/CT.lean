module

import VerifiedGarbage.Proof.AesCbc.AArch64.CT
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesCbc.AArch64.CT
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.AesXts.AArch64.Steps
public import VerifiedGarbage.Proof.AesXts.Batch
public import VerifiedGarbage.Proof.AesOcb.AArch64.Callee
public import VerifiedGarbage.Impl.AesXts.AArch64
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesXts.AArch64.Steps
meta import VerifiedGarbage.Proof.AesXts.Batch
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Callee
meta import VerifiedGarbage.Impl.AesXts.AArch64
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Body
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `AesXts.AArch64.Body`, which only this module used -/

section

/-!
# XTS-AES on AArch64: all the blocks in one call

`crypt_wp`: from AES-CBC's loop invariant after no blocks
(`Proof/AesCbc/AArch64/Loop.lean`), `batch` reaches it after all of them
(`batch_wp`), for `xtsMode enc`, for any implementation of the block
functions (`BlocksImpl`). The tweak is saved (`saveT_wp`); a pass XORs each
block's tweak into it, multiplying the tweak by `α` after each (`pass_wp`, by
`pstep_wp` for one block, whose invariant `PInv` says what `xored` the blocks
are); the tweak is restored and the block function called on all the blocks
(`callArgs_wp`, `call_wp`, from AES-OCB's `BCall`); and a second pass XORs
the tweaks in again (`AesXts.crypt_eq`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64
open VG.Impl.AesCbc.AArch64 (mov save setup restore xorInto copy cOff advance)
open VG.Proof.AesCbc (xorMem_frame xorMem_bytes copyMem_frame copyMem_bytes Mode ciphOf length_blocksAt
  getElem_blocksAt)
open VG.Proof.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesXts (xored xored_zero xored_getElem xored_step xored_all crypt_eq blocksAt_frame blocksAt_of_out)
open VG.Proof.Cmac (bytesAt_frame)

/-- The saved copy of the tweak. -/
abbrev Sv (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 2048

/-- A pass over the blocks `ys`, after `i` of them, with `x14` and `x15`
kept. -/
structure PInv (s₀ : State) (ys : List (List Byte)) (y14 y15 : BitVec 64) (i : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = blk s₀ i
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - i)
  x24 : s.gpr .x24 = S s₀
  x14 : s.gpr .x14 = y14
  x15 : s.gpr .x15 = y15
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
    r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, gR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = xored (iv0 s₀) ys i
  iv : bytesAt s.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) i
  sv : bytesAt s.mem (Sv s₀) 16 = iv0 s₀

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

theorem length_xored (t : List Byte) (ys : List (List Byte)) (i : Nat) (hi : i ≤ ys.length) :
    (xored t ys i).length = ys.length := by
  simp [xored, AesXts.length_tweaks]; omega

/-- The registers of the invariant, after code that keeps the preserved
registers but `x30` (and changes `x22` and `x23` at most). -/
theorem PInv.keep {s₀ : State} {ys : List (List Byte)} {y14 y15 : BitVec 64} {i : Nat} {s s' : State}
    (h : PInv s₀ ys y14 y15 i s)
    (g : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) :
    s'.gpr .x19 = W s₀ ∧ s'.gpr .x20 = s₀.gpr .x1 ∧ s'.gpr .x21 = Iv s₀ ∧ s'.gpr .x24 = S s₀ ∧
      ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
        r ≠ .x30 → s'.gpr r = s₀.gpr r :=
  ⟨by rw [g .x19 (by simp [preserved]) (by decide) (by decide) (by decide), h.x19],
   by rw [g .x20 (by simp [preserved]) (by decide) (by decide) (by decide), h.x20],
   by rw [g .x21 (by simp [preserved]) (by decide) (by decide) (by decide), h.x21],
   by rw [g .x24 (by simp [preserved]) (by decide) (by decide) (by decide), h.x24],
   fun r hr h19 h20 h21 h22 h23 h24 h30 => by rw [g r hr h30 h22 h23, h.other r hr h19 h20 h21 h22 h23 h24 h30]⟩

theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) :
    r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧
      r ≠ .x4 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.dataBlk {j : Nat} (hj : j < N s₀) {r : Region} (hr : (dataR s₀).Disjoint r) :
    (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
  hr.sub_left (UPre.data_sub hj)

/-- One block of a pass. -/
theorem pstep_wp {ys : List (List Byte)} {y14 y15 : BitVec 64} {i : Nat} (hi : i < N s₀) {s : State}
    (h : PInv s₀ ys y14 y15 i s) :
    WP isa (.block passBody) s (PInv s₀ ys y14 y15 (i + 1)) := by
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ i) (Q := Iv s₀) h.x22 h.x21
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hi)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hi))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hi)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hi))
  obtain hR₁ : s₁.rd ++ s₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₁, wr₁, hR]
  obtain hW₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, hW]
  obtain ⟨s₂, run₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ :=
    mulA_ok s₁ (Q := Iv s₀) (by rw [g₁ _ (by decide) (by decide), h.x21])
      (by rw [hR₁]; exact in_rw (by simp) cIv0) (by rw [hR₁]; exact in_rw (by simp) cIv8)
      (by rw [hW₁]; exact in_rw (by simp) cIv0) (by rw [hW₁]; exact in_rw (by simp) cIv8)
  obtain ⟨s₃, run₃, x22₃, x23₃, keep₃, sp₃, mem₃, rd₃, wr₃⟩ := advance_regs (s := s₂) hi
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), h.x22])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), h.x23])
  rw [passBody, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, WP.of_runBlock ⟨s₃, run₃, ?_⟩⟩
  have g (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12) (h22 : r ≠ .x22)
      (h23 : r ≠ .x23) : s₃.gpr r = s.gpr r := by
    rw [keep₃ r h22 h23, g₂ r h9 h10 h11 h12, g₁ r h9 h10]
  obtain f₁ : Frame [⟨blk s₀ i, 16⟩] s.mem s₁.mem := by rw [mem₁]; exact xorMem_frame _ _ _
  obtain f₂ : Frame [ivR s₀] s₁.mem s₂.mem := by rw [mem₂]; exact alphaMem_frame _ _
  obtain fStep : Frame [⟨blk s₀ i, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₃.mem := by
    rw [mem₃]
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  obtain hy : i < ys.length := by rw [h.len]; exact hi
  obtain blkI : bytesAt s.mem (blk s₀ i) 16 = ys[i] := by
    have := congrArg (·[i]?) h.data
    rw [xored_getElem _ hy, List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hi),
      getElem_blocksAt _ _ hi, List.getElem?_eq_getElem hy] at this
    exact Option.some.inj this
  obtain newBlk : bytesAt s₃.mem (blk s₀ i) 16 = Spec.Cbc.xor ys[i] (Spec.Xts.next (iv0 s₀) i) := by
    rw [mem₃, mem₂, bytesAt_frame (alphaMem_frame _ _) (one (hp.blk_iv hi)) (by decide), mem₁,
      xorMem_bytes _ (hp.blk_iv hi), blkI, h.iv]
  obtain newIv : bytesAt s₃.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (i + 1) := by
    rw [mem₃, mem₂, alphaMem_bytes, mem₁,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_iv hi).symm) (by decide), h.iv]
    rfl
  obtain newSv : bytesAt s₃.mem (Sv s₀) 16 = iv0 s₀ := by
    rw [mem₃, mem₂, bytesAt_frame (alphaMem_frame _ _) (one hp.iv_sv.symm) (by decide), mem₁,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_sv hi).symm) (by decide), h.sv]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.keep fun r hr _ h22 h23 =>
    g r (preserved_ne' hr).1 (preserved_ne' hr).2.1 (preserved_ne' hr).2.2.1 (preserved_ne' hr).2.2.2.1 h22 h23
  refine ⟨x19', x20', x21', x22₃, x23₃, x24', ?_, ?_, other', ?_, ?_, ?_, h.frame.trans (stepFrame hi fStep), h.len,
    ?_, newIv, newSv⟩
  · rw [g .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x14]
  · rw [g .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x15]
  · rw [sp₃, sp₂, sp₁, h.sp]
  · rw [rd₃, rd₂, rd₁, h.rd]
  · rw [wr₃, wr₂, wr₁, h.wr]
  · rw [hp.blocksAt_step hi fStep, h.data, newBlk, xored_step _ hy]

/-- A whole pass. -/
theorem pass_wp {ys : List (List Byte)} {y14 y15 : BitVec 64} (hN : 0 < N s₀) {s : State}
    (h : PInv s₀ ys y14 y15 0 s) : WP isa pass s (PInv s₀ ys y14 y15 (N s₀)) := by
  refine WP.loop (M := isa) (body := .block passBody) (c := .nonzero .x .x23) (Q := PInv s₀ ys y14 y15 (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ PInv s₀ ys y14 y15 j t) ?_ (N s₀ - 0) s
    ⟨0, rfl, hN, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (pstep_wp hp hk h) fun s' h' => ?_
  obtain hb : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ev := eval_x23 (x := N s₀ - (k + 1)) (by omega_using [hb]) h'.x23
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz], h'⟩

omit hp in
theorem movs_ok (s : State) :
    ∃ s', runBlock isa [mov .x14 .x22, mov .x15 .x23] s = some s' ∧
      s'.gpr .x14 = s.gpr .x22 ∧ s'.gpr .x15 = s.gpr .x23 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl,
    rfl⟩

/-- The tweak saved, and the data pointer and number of blocks kept. -/
theorem saveT_wp {M : Mode} (hM : ∀ R w t, M.chain R w t [] = t) (hO : ∀ R w t, M.out R w t [] = [])
    {s : State} (h : LInv M s₀ 0 s) :
    WP isa (.block saveT) s (PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0) := by
  obtain hR := h.regs hp
  obtain hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .x24) (src := .x21) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.x24]; rfl) (by rw [h.x24, Offset.add_add]; rfl) (by simp [h.x21])
      (by simp [h.x21]) (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, run₂, x14₂, x15₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ := movs_ok s₁
  rw [saveT, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .x9) (h2 : r ≠ .x14) (h3 : r ≠ .x15) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h2 h3, g₁ r h1]
  obtain fC : Frame [⟨Sv s₀, 16⟩] s.mem s₂.mem := by rw [mem₂, mem₁]; exact copyMem_frame _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h19 h20 h21 h22 h23 h24 h30 => ?_, ?_, ?_, ?_, ?_,
    by simp [Spec.Cbc.blocksAt], ?_, ?_, ?_⟩
  · rw [g .x19 (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide), h.x20]
  · rw [g .x21 (by decide) (by decide) (by decide), h.x21]
  · rw [g .x22 (by decide) (by decide) (by decide), h.x22]
  · rw [g .x23 (by decide) (by decide) (by decide), h.x23]
  · rw [g .x24 (by decide) (by decide) (by decide), h.x24]
  · rw [x14₂, g₁ _ (by decide), h.x22]
  · rw [x15₂, g₁ _ (by decide), h.x23]; rfl
  · rw [g r (preserved_ne' hr).1 (preserved_ne' hr).2.2.2.2.1 (preserved_ne' hr).2.2.2.2.2.1,
      h.other r hr h19 h20 h21 h22 h23 h24 h30]
  · rw [sp₂, sp₁, h.sp]
  · rw [rd₂, rd₁, h.rd]
  · rw [wr₂, wr₁, h.wr]
  · exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩)
  · rw [blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (UPre.dataBlk hj hp.data_scr).sub_right (UPre.scr_sub (by decide))), h.data, xored_zero]
    simp [outK, hO]
  · rw [bytesAt_frame fC (one hp.iv_sv) (by decide), h.iv]; simp [chainK, hM]; rfl
  · rw [mem₂, mem₁, copyMem_bytes _ hp.iv_sv.symm, h.iv]; simp [chainK, hM]

omit hp in
theorem movsBack_ok (s : State) :
    ∃ s', runBlock isa [mov .x22 .x14, mov .x23 .x15] s = some s' ∧
      s'.gpr .x22 = s.gpr .x14 ∧ s'.gpr .x23 = s.gpr .x15 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl,
    rfl⟩

omit hp in
theorem args_ok (s : State) :
    ∃ s', runBlock isa [mov .x0 .x19, mov .x1 .x20, mov .x2 .x22, mov .x3 .x23, mov .x4 .x24] s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x22 ∧
      s'.gpr .x3 = s.gpr .x23 ∧ s'.gpr .x4 = s.gpr .x24 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_write, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl, rfl⟩

/-- The arguments of the block function on all the blocks. -/
theorem UPre.bcall {s : State} (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1)
    (x2 : s.gpr .x2 = Dp s₀) (x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀)) (x4 : s.gpr .x4 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Proof.AesOcb.AArch64.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  rounds := hp.rounds
  wrap := hp.data_wrap
  kd := hp.sch_data
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.data_scr.sub_right (Region.sub_prefix (by decide))
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The data pointer and number of blocks back, the tweak restored, and the
arguments of the block function. -/
theorem callArgs_wp {ys : List (List Byte)} {s : State}
    (h : PInv s₀ ys (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) (N s₀) s) :
    WP isa (.block callArgs) s fun s' =>
      Proof.AesOcb.AArch64.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) ys (N s₀)) (s'.gpr .x14) (s'.gpr .x15) 0 s' := by
  obtain ⟨s₁, run₁, x22₁, x23₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ := movsBack_ok s
  obtain hR₁ : s₁.rd ++ s₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₁, wr₁, h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hW₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, h.wr, hp.wr]
  obtain x21₁ : s₁.gpr .x21 = Iv s₀ := by rw [g₁ _ (by decide) (by decide), h.x21]
  obtain x24₁ : s₁.gpr .x24 = S s₀ := by rw [g₁ _ (by decide) (by decide), h.x24]
  obtain ⟨s₂, run₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ :=
    copy_ok s₁ (dst := .x21) (src := .x24) (d := 0) (e := cOff) (P := Iv s₀) (Q := Sv s₀)
      (by simp [x21₁]) (by simp [x21₁]) (by rw [x24₁]; rfl) (by rw [x24₁, Offset.add_add]; rfl)
      (by rw [hR₁]; exact in_rw (by simp) cSv0) (by rw [hR₁]; exact in_rw (by simp) cSv8)
      (by rw [hW₁]; exact in_rw (by simp) cIv0) (by rw [hW₁]; exact in_rw (by simp) cIv8) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₃, run₃, x0₃, x1₃, x2₃, x3₃, x4₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := args_ok s₂
  rw [callArgs, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, WP.of_runBlock ⟨s₃, run₃, ?_⟩⟩
  have g (r : Reg) (h0 : r ≠ .x0) (h1 : r ≠ .x1) (h2 : r ≠ .x2) (h3 : r ≠ .x3) (h4 : r ≠ .x4)
      (h9 : r ≠ .x9) (h22 : r ≠ .x22) (h23 : r ≠ .x23) : s₃.gpr r = s.gpr r := by
    rw [g₃ r h0 h1 h2 h3 h4, g₂ r h9, g₁ r h22 h23]
  obtain x22₃ : s₃.gpr .x22 = blk s₀ 0 := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), x22₁, h.x14]
  obtain x23₃ : s₃.gpr .x23 = BitVec.ofNat 64 (N s₀) := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), x23₁, h.x15]
  obtain fC : Frame [ivR s₀] s.mem s₃.mem := by rw [mem₃, mem₂, mem₁]; exact copyMem_frame _ _ _
  obtain hrd : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁, h.rd]
  obtain hwr : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, h.wr]
  have hlen : ys.length = N s₀ := h.len
  refine ⟨UPre.bcall hp
    (by rw [x0₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), h.x19])
    (by rw [x1₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), h.x20])
    (by rw [x2₃, g₂ _ (by decide), x22₁, h.x14]; simp [blk])
    (by rw [x3₃, g₂ _ (by decide), x23₁, h.x15])
    (by rw [x4₃, g₂ _ (by decide), x24₁]) hrd hwr, ?_⟩
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.keep fun r hr _ h22 h23 =>
    g r (preserved_ne' hr).2.2.2.2.2.2.1 (preserved_ne' hr).2.2.2.2.2.2.2.1 (preserved_ne' hr).2.2.2.2.2.2.2.2.1
      (preserved_ne' hr).2.2.2.2.2.2.2.2.2.1 (preserved_ne' hr).2.2.2.2.2.2.2.2.2.2 (preserved_ne' hr).1 h22 h23
  refine ⟨x19', x20', x21', x22₃, by rw [x23₃]; rfl, x24', rfl, rfl, other', by rw [sp₃, sp₂, sp₁, h.sp],
    hrd, hwr, ?_, by rw [length_xored _ _ _ (by omega_using [hlen]), hlen], ?_, ?_, ?_⟩
  · exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  · rw [blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact UPre.dataBlk hj hp.iv_data.symm), h.data, xored_zero]
  · rw [mem₃, mem₂, copyMem_bytes _ hp.iv_sv, mem₁, h.sv]; rfl
  · rw [bytesAt_frame fC (one hp.iv_sv.symm) (by decide), h.sv]

/-- The call of the block function on all the blocks. -/
theorem call_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {ys : List (List Byte)} {y14 y15 : BitVec 64} {s : State}
    (hc : Proof.AesOcb.AArch64.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀)) (h : PInv s₀ ys y14 y15 0 s) :
    WP isa (.call b.name b.code) s fun s' =>
      PInv s₀ (ys.map (ciphOf enc (R s₀) (wK s₀))) (s'.gpr .x14) (s'.gpr .x15) 0 s' := by
  refine WP.mono (Proof.AesOcb.AArch64.blk_call ok nf hc) fun s' c => ?_
  obtain fCall : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] s.mem s'.mem :=
    c.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  obtain dIv : ∀ r ∈ [(⟨Dp s₀, 16 * N s₀⟩ : Region), ⟨S s₀, 2048⟩], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.iv_data
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  obtain dSv : ∀ r ∈ [(⟨Dp s₀, 16 * N s₀⟩ : Region), ⟨S s₀, 2048⟩], (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.data_scr.sub_right (UPre.scr_sub (by decide))).symm
    · exact hp.sv_scr
  obtain sched : bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp (UPre.big_of h.frame)
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.keep fun r hr h30 _ _ => c.saved r hr h30
  refine ⟨x19', x20', x21', by rw [c.saved .x22 (by simp [preserved]) (by decide), h.x22],
    by rw [c.saved .x23 (by simp [preserved]) (by decide), h.x23], x24', rfl, rfl, other',
    by rw [c.sp, h.sp], by rw [c.rd, h.rd], by rw [c.wr, h.wr], h.frame.trans (UPre.frameG fCall), by simp [h.len], ?_, ?_, ?_⟩
  · rw [blocksAt_of_out c.out (fun p => hf _ _ _ p), h.data, xored_zero, xored_zero, sched]
  · rw [bytesAt_frame c.frame dIv (by decide), h.iv]
  · rw [bytesAt_frame c.frame dSv (by decide), h.sv]

omit hp in
/-- After the second pass: XTS of all the blocks (`AesXts.crypt_eq`). -/
theorem final_of (enc : Bool) {y14 y15 : BitVec 64} {s : State}
    (h : PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) y14 y15 (N s₀) s) :
    LInv (AesXts.xtsMode enc) s₀ (N s₀) s := by
  obtain hl : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  obtain ce := crypt_eq (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)
  rw [hl] at ce
  exact { x19 := h.x19, x20 := h.x20, x21 := h.x21, x22 := h.x22, x23 := h.x23, x24 := h.x24,
          other := h.other, sp := h.sp, rd := h.rd, wr := h.wr, frame := h.frame
          data := by
            rw [h.data, xored_all _ h.len, xored_all _ hl, ce, outK, AesXts.xtsMode_out,
              List.take_of_length_le (by omega_using [hl]), List.drop_of_length_le (by omega_using [hl]), List.append_nil]
          iv := by
            rw [h.iv, chainK, AesXts.xtsMode_chain, List.take_of_length_le (by omega_using [hl]), hl] }

/-- All the blocks. -/
theorem batch_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hN : 0 < N s₀) {s : State} (h : LInv (AesXts.xtsMode enc) s₀ 0 s) :
    WP isa (batch b) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) :=
  WP.seq (WP.mono (saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h) fun _ h₁ =>
    WP.seq (WP.mono (pass_wp hp hN h₁) fun _ h₂ =>
      WP.seq (WP.mono (callArgs_wp hp h₂) fun _ ⟨c₃, h₃⟩ =>
        WP.seq (WP.mono (call_wp hp enc ok nf hf c₃ h₃) fun _ h₄ =>
          WP.mono (pass_wp hp hN h₄) fun _ h₅ => final_of enc h₅))))

end

/-- The whole function. -/
theorem crypt_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {s₀ : State} (h0 : (modeAArch64 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt b) s₀ fun s' => GprAbi s₀ s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s₀ s' :=
  ends_wp h0 fun hp hN _ h => batch_wp hp enc ok nf hf hN h

end VG.Proof.AesXts.AArch64

end

end

/-!
# XTS-AES on AArch64: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/AArch64/CT.lean`): the taint
analysis covers the code around the call, from the registers the correctness
proof pins to the public arguments (`PInv`), and the call of the block
function on all the blocks is constant time by its own proof (`blk_rel`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.Impl.AesXts.AArch64
open VG.Impl.AesCbc.AArch64 (save setup restore)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs (as do the stack pointers), with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp) (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (P := P) _ (fun s₁ s₂ h => agree_of (hsp s₁ s₂ h) (ha s₁ s₂ h)) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem saveT_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block saveT) h).isSome = true := ⟨_, by taint_decide⟩

theorem pass_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24]) pass h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem callArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x14, .x15, .x21, .x24])
    (.block callArgs) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (modeAArch64 (AesXts.xtsMode enc)).pub s₀ s₀')
include hq

theorem PInv.agree {ys ys' : List (List Byte)} {x10 x11 x10' x11' : BitVec 64} {i : Nat} {s₁ s₂ : State}
    (h₁ : PInv s₀ ys x10 x11 i s₁) (h₂ : PInv s₀' ys' x10' x11' i s₂) :
    ∀ r ∈ [Reg.x21, .x22, .x23, .x24], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.x21, h₂.x21, pub_Iv hq]
  · rw [h₁.x22, h₂.x22, pub_blk hq]
  · rw [h₁.x23, h₂.x23, pub_N hq]
  · rw [h₁.x24, h₂.x24, pub_S hq]

/-- All the blocks, in two runs. -/
theorem batch_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) :
    RelCT isa (fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) (batch b)
      fun a b => LInv (AesXts.xtsMode enc) s₀ (N s₀) a ∧ LInv (AesXts.xtsMode enc) s₀' (N s₀') b := by
  have hN' : 0 < N s₀' := by rw [← pub_N hq]; exact hN
  -- The tweak saved.
  have a := taint_rel _ saveT_taint (P := fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b)
    (fun _ _ h => by rw [h.1.sp, h.2.sp, pub_sp hq])
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.x21, h.2.x21, pub_Iv hq]
      · rw [h.1.x22, h.2.x22, pub_blk hq]
      · rw [h.1.x23, h.2.x23, pub_N hq]
      · rw [h.1.x24, h.2.x24, pub_S hq])
    (F₁ := PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0)
    (F₂ := PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) 0)
    fun _ _ h => ⟨saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.1,
      saveT_wp hp' (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.2⟩
  -- The first pass.
  have p₁ := taint_rel _ pass_taint (P := fun a b => PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0 a ∧
      PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) 0 b) (fun _ _ h => by rw [h.1.sp, h.2.sp, pub_sp hq])
    (fun _ _ h => PInv.agree hq h.1 h.2)
    (F₁ := PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) (N s₀))
    (F₂ := PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) (N s₀'))
    fun _ _ h => ⟨pass_wp hp hN h.1, pass_wp hp' hN' h.2⟩
  -- The arguments of the call.
  have c := taint_rel _ callArgs_taint (P := fun a b =>
      PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) (N s₀) a ∧
      PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) (N s₀') b)
    (fun _ _ h => by rw [h.1.sp, h.2.sp, pub_sp hq])
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19, pub_W hq]
      · rw [h.1.x20, h.2.x20, pub_x1 hq]
      · rw [h.1.x14, h.2.x14, pub_blk hq]
      · rw [h.1.x15, h.2.x15, pub_N hq]
      · rw [h.1.x21, h.2.x21, pub_Iv hq]
      · rw [h.1.x24, h.2.x24, pub_S hq])
    (F₁ := fun (s' : State) => Proof.AesOcb.AArch64.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) (s'.gpr .x14) (s'.gpr .x15) 0 s')
    (F₂ := fun (s' : State) => Proof.AesOcb.AArch64.BCall s' (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
      PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) (s'.gpr .x14) (s'.gpr .x15) 0 s')
    fun _ _ h => ⟨callArgs_wp hp h.1, callArgs_wp hp' h.2⟩
  -- The call.
  have k := (Proof.AesOcb.AArch64.blk_rel ok ct (name := b.name) (P := fun a b =>
      (Proof.AesOcb.AArch64.BCall a (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
        PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) (a.gpr .x14) (a.gpr .x15) 0 a) ∧
      (Proof.AesOcb.AArch64.BCall b (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
        PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) (b.gpr .x14) (b.gpr .x15) 0 b)) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.1, by
        rw [pub_W hq, pub_Dp hq, pub_S hq, pub_R hq, pub_N hq]; exact h.2.1,
        by rw [h.1.2.sp, h.2.2.sp, pub_sp hq]⟩).wp
    (F₁ := fun (s' : State) => PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀)))
      (s'.gpr .x14) (s'.gpr .x15) 0 s')
    (F₂ := fun (s' : State) => PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀')))
      (s'.gpr .x14) (s'.gpr .x15) 0 s')
    fun _ _ h => ⟨call_wp hp enc ok nf hf h.1.1 h.1.2, call_wp hp' enc ok nf hf h.2.1 h.2.2⟩
  -- The second pass.
  have p₂ := taint_rel _ pass_taint (P := fun a b =>
      PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) (a.gpr .x14) (a.gpr .x15) 0 a ∧
      PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀'))) (b.gpr .x14)
        (b.gpr .x15) 0 b) (fun _ _ h => by rw [h.1.sp, h.2.sp, pub_sp hq])
    (fun _ _ h => PInv.agree hq h.1 h.2)
    (F₁ := LInv (AesXts.xtsMode enc) s₀ (N s₀)) (F₂ := LInv (AesXts.xtsMode enc) s₀' (N s₀'))
    fun _ _ h => ⟨WP.mono (pass_wp hp hN h.1) fun _ h => final_of enc h,
      WP.mono (pass_wp hp' hN' h.2) fun _ h => final_of enc h⟩
  exact a.seq (p₁.seq (c.seq ((k.mono (fun _ _ h => h) fun _ _ h => h.2).seq p₂)))

end

theorem crypt_ct (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre (modeAArch64 (AesXts.xtsMode enc)).pub (crypt b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' hN => batch_rel hq ok ct nf hf hp hp' hN)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.AArch64
