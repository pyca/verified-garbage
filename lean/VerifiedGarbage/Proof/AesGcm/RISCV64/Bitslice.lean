module

public import VerifiedGarbage.Impl.AesGcm.RISCV64.Bitslice
public import VerifiedGarbage.Spec.Gcm.Bitsliced
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.RISCV64.Common
import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Gcm.RISCV64.PrepLaw
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Bitslice
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.StackScratch.RISCV64

/-!
# AES-GCM's bitsliced key on RISC-V

Untrusted: everything here is checked by Lean. `bitslice_wp`: the body of
`vg_aes_gcm_bitslice` (`Impl/AesGcm/RISCV64/Bitslice.lean`) writes the
buffer of `Spec/Gcm/Bitsliced.lean` (`SlicedRepr`), from the proofs of the
code it shares with `vg_aes_ctr32` (`keyLoop_ok`, which leaves round key `j`
of a 14-round schedule bitsliced at byte `1024 + 64 j` of the working space)
and `vg_ghash` (`prep`'s, which it takes as `PrepLaw`, so as not to import
its algebra), and of `copyLoopW` (`copyLoopW_ok`). Then constant time (only
the pointers reach addresses and branches), the shared contract with the
working space in a frame of its own (`bitslice_framed`), and that frame,
which holds the bitsliced round keys, cleared on return with the
caller-saved registers (`bitsliceReg`, `RISCV64.Scrub.withScrubSel`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64.Bitslice

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.RISCV64.Straight VG.Impl.Aes.RISCV64 VG.Proof.Aes
  VG.Proof.Aes.RISCV64
open VG.Impl.AesGcm.RISCV64.Bitslice
open VG.Spec.Gcm (SlicedRepr SlicedKeyAt ctxH blockAt)

/-! ## The contract the proof is written against -/

/-- `vg_aes_gcm_bitslice(ctx = a0, bk = a1, scratch = a2)`. -/
def bitsliceRISCV64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .a0, 256⟩
    let bk : Region := ⟨s.gpr .a1, 1248⟩
    let scr : Region := ⟨s.gpr .a2, 2048⟩
    s.rd = [ctx] ∧ s.wr = [bk, scr] ∧ ctx.Disjoint bk ∧ ctx.Disjoint scr ∧ bk.Disjoint scr ∧
      (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 1248 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 2048 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat % 8 = 0
  post s s' :=
    SlicedRepr s'.mem (s.gpr .a1) (Spec.Aes.bytesAt s.mem (s.gpr .a0) 240) (ctxH s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

/-! ## The round keys -/

theorem slicedKeyAt_of_keyRel {m : Mem} {p : Addr} {rk : List Byte}
    (h : KeyRel (fun k => m.readW (p + BitVec.ofNat 64 (8 * k)) 64) rk) : SlicedKeyAt m p rk := by
  intro t ht b hb i hi
  rw [← h b hb i hi, getLsbD_bsByte _ _ ht]
  rfl

/-! ## The body -/

theorem read_congr2 {m m' : Mem} {a b : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)) :
    m.read a n = m'.read b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega_using [])
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega_using [hi])
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

theorem bitslice_wp [Proof.Gcm.RISCV64.PrepLaw] {s₀ : State} (h : bitsliceRISCV64.pre s₀) :
    WP isa bitslice s₀ fun s' => (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ bitsliceRISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dCB, dCS, dBS, fC, fB, fS, alB⟩ := h
  let C := s₀.gpr .a0
  let BK := s₀.gpr .a1
  let X := s₀.gpr .a2
  let b := X + BitVec.ofNat 64 (pad X)
  unfold bitslice
  refine WP.seq ?_
  -- The working space, rounded.
  simp only [entry, List.append_assoc, List.singleton_append]
  refine wp_mv fun s₁ u₁ => ?_
  rw [List.append_eq, WP.block_append_iff]
  refine roundSb_wp fun s₂ b₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_
  obtain hb₂ : s₂.gpr sb = b := by rw [b₂, show sb = .a5 from rfl, u₁.gpr]
  obtain o₂' : ∀ r, r ≠ sb → s₂.gpr r = s₀.gpr r := fun r hr => by rw [o₂ r hr, u₁.other r hr]
  obtain hwS : (⟨X, 2048⟩ : Region) ∈ s₂.wr := by rw [wr₂, u₁.wr, hwr]; simp [X]
  obtain hscr₂ : Scr s₂ X 2048 := ⟨hwS, hb₂⟩
  -- Our caller's registers saved.
  rw [WP.block_append_iff, saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₂.al savedOffs_ho (fun p hp => ⟨_, hscr₂.wr,
    hscr₂.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩) (WP.block_nil ?_)
  generalize hS : ({ s₂ with mem := Spill.saveMem s₂.mem (s₂.gpr sb) s₂.gpr savedOffs } : State) = s₃
  obtain g₃ : s₃.gpr = s₂.gpr := by rw [← hS]
  obtain mm₃ : s₃.mem = Spill.saveMem s₂.mem (s₂.gpr sb) s₂.gpr savedOffs := by rw [← hS]
  obtain rd₃ : s₃.rd = s₂.rd := by rw [← hS]
  obtain wr₃ : s₃.wr = s₂.wr := by rw [← hS]
  obtain sp₃ : s₃.sp = s₂.sp := by rw [← hS]
  obtain sv₃ : Spill.Saved b s₂.gpr savedOffs s₃.mem := by
    rw [mm₃, ← hb₂]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  obtain f₃ : Frame [⟨b + BitVec.ofNat 64 320, 96⟩] s₂.mem s₃.mem := by
    rw [mm₃, ← hb₂]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  obtain hscr₃ : Scr s₃ X 2048 := ⟨by rw [wr₃]; exact hscr₂.wr, by rw [g₃]; exact hscr₂.base⟩
  obtain hb₃ : s₃.gpr sb = b := by rw [g₃]; exact hb₂
  -- The masks.
  rw [WP.block_append_iff]
  refine WP.mono (maskInit_ok hscr₃) fun s₄ ⟨mk₄, fm₄, g₄, rd₄, wr₄, sp₄⟩ => ?_
  rw [hb₃] at mk₄ fm₄
  -- `ctx` and `bk` kept, and the key loop set up for 14 rounds.
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_li (imm := 14) (by decide) fun s₇ u₇ => ?_
  obtain k₇ : ∀ r, r ≠ .a1 → r ≠ .a3 → r ≠ .a4 → r ≠ t0 → r ≠ t1 → r ≠ sb → s₇.gpr r = s₀.gpr r :=
    fun r h1 h3 h4 h0 h1' hsb => by
      rw [u₇.other r h1, u₆.other r h4, u₅.other r h3, g₄ r h0 h1', g₃, o₂' r hsb]
  obtain a3₇ : s₇.gpr .a3 = C := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide), g₃,
      o₂' _ (by decide)]
  obtain a4₇ : s₇.gpr .a4 = BK := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide) (by decide), g₃,
      o₂' _ (by decide)]
  obtain hb₇ : s₇.gpr sb = b := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide) (by decide), hb₃]
  obtain m₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, rd₄, rd₃, rd₂, u₁.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, wr₄, wr₃, wr₂, u₁.wr]
  obtain sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, sp₄, sp₃, sp₂, u₁.sp]
  refine keySetup_wp (s := s₇) (R := 14) u₇.gpr (by decide)
    fun s₈ a0₈ a2₈ a1₈ o₈ m₈ rd₈ wr₈ sp₈ => ?_
  obtain hb₈ : s₈.gpr sb = b := by rw [o₈ sb (by decide) (by decide) (by decide) (by decide), hb₇]
  obtain hscr₈ : Scr s₈ X 2048 := ⟨by rw [wr₈, wr₇, hwr]; simp [X], hb₈⟩
  -- The memory so far changed only in the working space.
  obtain f₀₈ : Frame [⟨X, 2048⟩] s₀.mem s₈.mem := by
    rw [m₈, m₇]
    obtain e₂ : s₂.mem = s₀.mem := by rw [m₂, u₁.mem]
    rw [← e₂]
    refine (f₃.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩).trans (fm₄.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega_using [])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact scr_part X (by omega_using [])
      · exact scr_part X (by omega_using [])
  let w := Spec.Aes.bytesAt s₀.mem C 240
  obtain hk : KSetup s₈ X b C 14 w :=
    { scr := hscr₈
      base := hb₈
      masks := by rw [m₈, m₇]; exact mk₄
      sch := ⟨256, by decide, List.mem_append_left _ (by rw [rd₈, rd₇, hrd]; simp [C])⟩
      sep := dCS.sub_left (Region.sub_prefix (by decide))
      rounds := by decide
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (show i < 240 by omega_arith), Option.map_some, Option.getD_some]
        refine (f₀₈.bytes (R := ⟨C, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_left (Region.sub_prefix (by decide)) }
  obtain hi₈ : KInv s₈ b C 14 w 14 s₈ :=
    { hj := Nat.le_refl _
      a1 := a1₈
      a0 := by
        rw [a0₈, k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      a2 := by rw [a2₈, hb₇]; simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₈) fun s₉ d₉ => ?_)
  obtain hb₉ : s₉.gpr sb = b := by rw [d₉.keep sb (by decide), hb₈]
  obtain a3₉ : s₉.gpr .a3 = C := by
    rw [d₉.keep _ (by decide), o₈ _ (by decide) (by decide) (by decide) (by decide), a3₇]
  obtain a4₉ : s₉.gpr .a4 = BK := by
    rw [d₉.keep _ (by decide), o₈ _ (by decide) (by decide) (by decide) (by decide), a4₇]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [d₉.rd, rd₈, rd₇]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [d₉.wr, wr₈, wr₇]
  obtain hal : b.toNat % 8 = 0 := by rw [← hb₂]; exact hscr₂.al
  -- The 120 doublewords of bitsliced blocks, to `bk`.
  refine WP.seq ?_
  simp only [copyArgs]
  refine wp_addi (imm := 1024) (by decide) fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ =>
    wp_li (imm := 120) (by decide) fun s₁₂ u₁₂ => WP.block_nil ?_
  obtain a0₁₂ : s₁₂.gpr .a0 = b + BitVec.ofNat 64 1024 := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, show Reg.a5 = sb from rfl, hb₉]
  obtain a1₁₂ : s₁₂.gpr .a1 = BK := by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), a4₉]
  obtain rd₁₂ : s₁₂.rd = s₀.rd := by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉]
  obtain wr₁₂ : s₁₂.wr = s₀.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]
  obtain m₁₂ : s₁₂.mem = s₉.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem]
  obtain hX : (⟨X, 2048⟩ : Region) ∈ s₁₂.wr := by rw [wr₁₂, hwr]; simp [X]
  obtain hBK : (⟨BK, 1248⟩ : Region) ∈ s₁₂.wr := by rw [wr₁₂, hwr]; simp [BK]
  obtain cb : ∀ i < 120, (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (8 * i)) 8 :=
    fun i hi => by
      rw [Offset.add_add, ← hb₈]
      exact hscr₈.contains (by omega_using [hi]) (by decide)
  refine WP.seq (WP.mono (copyLoopW_ok (tmp := .t0) (src := .a0) (dst := .a1) (cnt := .a2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) s₁₂ (N := 120) (by decide) (by decide)
    u₁₂.gpr (by rw [a0₁₂]; exact Spill.al8 hal (by decide)) (by rw [a1₁₂]; exact alB)
    (fun i hi => ⟨_, List.mem_append_right _ hX, by rw [a0₁₂]; exact cb i hi⟩)
    (fun i hi => ⟨_, hBK, by rw [a1₁₂]; exact Offset.contains_base BK (by omega_using [hi]) (by omega_using [hi])⟩)
    (by
      rw [a0₁₂, a1₁₂]
      refine dBS.sep (n := 8 * 120) (k := 8 * 120) ?_ ?_
      · simpa using Offset.contains_base BK (d := 0) (n := 8 * 120) (k := 1248) (by decide) (by decide)
      · rw [← hb₈]; exact hscr₈.contains (d := 1024) (n := 8 * 120) (by decide) (by decide)))
    fun s₁₃ ⟨cp₁₃, fc₁₃, kc₁₃⟩ => ?_)
  -- `prep`, from the hash subkey at `ctx + 240`, to `bk + 960`.
  rw [WP.block_append_iff]
  simp only [ghArgs]
  refine wp_addi (imm := 240) (by decide) fun s₁₄ u₁₄ => wp_addi (imm := 960) (by decide)
    fun s₁₅ u₁₅ => WP.block_nil ?_
  obtain kc : ∀ r, r ∉ [Reg.t0, .a0, .a1, .a2] → s₁₃.gpr r = s₁₂.gpr r := kc₁₃.1
  obtain e12 : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₁₂.gpr r = s₉.gpr r := fun r h0 h1 h2 => by
    rw [u₁₂.other r h2, u₁₁.other r h1, u₁₀.other r h0]
  obtain hp₁₅ : s₁₅.gpr Impl.Gcm.RISCV64.HP = C + BitVec.ofNat 64 240 := by
    rw [show Impl.Gcm.RISCV64.HP = .a0 from rfl, u₁₅.other _ (by decide), u₁₄.gpr, kc _ (by decide),
      e12 _ (by decide) (by decide) (by decide), a3₉]
  obtain fp₁₅ : s₁₅.gpr Impl.Gcm.RISCV64.FP = BK + BitVec.ofNat 64 960 := by
    rw [show Impl.Gcm.RISCV64.FP = .s9 from rfl, u₁₅.gpr, u₁₄.other _ (by decide), kc _ (by decide),
      e12 _ (by decide) (by decide) (by decide), a4₉]
  obtain rd₁₅ : s₁₅.rd = s₀.rd := by rw [u₁₅.rd, u₁₄.rd, kc₁₃.2.1, rd₁₂]
  obtain wr₁₅ : s₁₅.wr = s₀.wr := by rw [u₁₅.wr, u₁₄.wr, kc₁₃.2.2, wr₁₂]
  obtain m₁₅ : s₁₅.mem = s₁₃.mem := by rw [u₁₅.mem, u₁₄.mem]
  obtain hBK' : (⟨BK, 1248⟩ : Region) ∈ s₁₅.wr := by rw [wr₁₅, hwr]; simp [BK]
  obtain hH : InRegions (s₁₅.rd ++ s₁₅.wr) (s₁₅.gpr Impl.Gcm.RISCV64.HP) 16 := by
    refine ⟨⟨C, 256⟩, List.mem_append_left _ (by rw [rd₁₅, hrd]; simp [C]), ?_⟩
    rw [hp₁₅]; exact Offset.contains_base C (by decide) (by decide)
  obtain hW : ∀ k < 36, (s₁₅.gpr Impl.Gcm.RISCV64.FP + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 ∧
      InRegions s₁₅.wr (s₁₅.gpr Impl.Gcm.RISCV64.FP + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨?_, ⟨_, hBK', ?_⟩⟩
    · rw [fp₁₅, Offset.add_add]; exact Spill.al8 alB (by omega_using [])
    · rw [fp₁₅, Offset.add_add]
      exact Offset.contains_base BK (by omega_using [hk]) (by omega_using [hk])
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Gcm.RISCV64.PrepLaw.ok s₁₅ hH hW) fun s₁₆ ⟨T₁₆, k₁₆, _, wr₁₆', _, F₁₆⟩ => ?_
  obtain e15 : ∀ r, r ∉ [Reg.t0, .a0, .a1, .a2, .s9] → s₁₅.gpr r = s₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₅.other r hr.2.2.2.2, u₁₄.other r hr.2.1, kc r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]),
      e12 r hr.2.1 hr.2.2.1 hr.2.2.2.1]
  obtain hb₁₆ : s₁₆.gpr sb = b := by rw [k₁₆ _ (by decide), e15 _ (by decide), hb₉]
  obtain wr₁₆ : s₁₆.wr = s₀.wr := by rw [wr₁₆', wr₁₅]
  -- What the code wrote: the working space, then `bk`.
  obtain dSl : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
      Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
    · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
  obtain dK : ∀ r ∈ kRegions b, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
    · exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain dXB : ∀ {d n}, d + n + 7 ≤ 2048 → ∀ {e k}, e + k ≤ 1248 →
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ ⟨BK + BitVec.ofNat 64 e, k⟩ := fun {_ _} h1 {_ _} h2 =>
    (dBS.symm.sub_left (scr_part X h1)).sub_right (Offset.sub_base BK h2)
  obtain dC : ∀ r ∈ [(⟨s₁₂.gpr .a1, 8 * 120⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [a1₁₂]; simpa using dXB (d := 320) (n := 96) (by decide) (e := 0) (k := 8 * 120) (by decide)
  obtain dP : ∀ r ∈ [(⟨s₁₅.gpr Impl.Gcm.RISCV64.FP, 288⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [fp₁₅]; exact dXB (by decide) (by decide)
  obtain sv : Spill.Saved b s₂.gpr savedOffs s₁₆.mem := by
    obtain s4 := sv₃.frame_in savedOffs_range fm₄ dSl
    rw [← m₇, ← m₈] at s4
    obtain s9 := s4.frame_in savedOffs_range d₉.frame dK
    rw [← m₁₂] at s9
    obtain s13 := s9.frame_in savedOffs_range fc₁₃ dC
    rw [← m₁₅] at s13
    exact s13.frame_in savedOffs_range F₁₆ dP
  -- Our caller's registers back.
  obtain hX₁₆ : (⟨X, 2048⟩ : Region) ∈ s₁₆.wr := by rw [wr₁₆, hwr]; simp [X]
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) hal hb₁₆ savedOffs_ho savedOffs_restorable (fun p hp => ⟨_,
    List.mem_append_right _ hX₁₆, by
      rw [← hb₈]; exact hscr₈.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩)
    sv) fun s₁₇ rs₁₇ => ?_
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    obtain h1 : r ≠ sb := by revert hr; revert r; decide
    rw [rs₁₇.gpr_of (.inl hr'), o₂' r h1]
  · rw [rs₁₇.other _ not_saved_ra, k₁₆ _ (by decide), e15 _ (by decide), d₉.keep _ (by decide),
      o₈ _ (by decide) (by decide) (by decide) (by decide),
      k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  -- The buffer.
  show SlicedRepr s₁₇.mem BK w (ctxH s₀.mem C)
  rw [rs₁₇.mem]
  -- `bk`'s first 960 bytes are the working space's at byte 1024 after the key loop.
  obtain cpy : ∀ x, x + 8 ≤ 960 →
      s₁₆.mem.readW (BK + BitVec.ofNat 64 x) 64 = s₉.mem.readW (b + BitVec.ofNat 64 (1024 + x)) 64 := by
    intro x hx
    rw [F₁₆.readW (r := ⟨BK + BitVec.ofNat 64 x, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [fp₁₅]; exact Offset.disjoint BK (.inl (by omega_using [hx])) (by omega_using [hx]) (by decide))
      (by decide), m₁₅, ← m₁₂]
    simp only [Mem.readW]
    rw [read_congr2 fun i hi => ?_]
    rw [Offset.add_add, Offset.add_add, ← a1₁₂, cp₁₃ (x + i) (by omega_using [hx, hi]), a0₁₂, Offset.add_add,
      show 1024 + (x + i) = 1024 + x + i by omega_using []]
  refine ⟨fun j hj => slicedKeyAt_of_keyRel (keyRel_congr (d₉.keys j (by omega_using [hj])) fun k hk => ?_),
    fun i hi j hj => ?_⟩
  · rw [Offset.add_add, cpy (64 * j + 8 * k) (by omega_using [hj, hk])]
    simp only [wordAddr, keyAddr, Offset.add_add]
    congr 3
    omega_using [hj]
  · -- The hash subkey, as on entry, in `prep`'s two words.
    obtain f₀₁₅ : Frame [⟨X, 2048⟩, ⟨BK, 1248⟩] s₀.mem s₁₅.mem := by
      rw [m₁₅]
      obtain fA : Frame [⟨X, 2048⟩, ⟨BK, 1248⟩] s₀.mem s₈.mem := f₀₈.mono (by simp)
      obtain fB : Frame [⟨X, 2048⟩, ⟨BK, 1248⟩] s₈.mem s₉.mem := by
        refine d₉.frame.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact scr_base X (by omega_using [])
        · exact scr_part X (by omega_using [])
      obtain fC : Frame [⟨X, 2048⟩, ⟨BK, 1248⟩] s₉.mem s₁₃.mem := by
        rw [← m₁₂]
        refine fc₁₃.sub fun r hr => ⟨⟨BK, 1248⟩, by simp, ?_⟩
        simp only [List.mem_singleton] at hr; subst hr
        rw [a1₁₂]; exact Region.sub_prefix (by decide)
      exact (fA.trans fB).trans fC
    obtain hH : Spec.Gcm.blockAt s₁₅.mem (C + BitVec.ofNat 64 240) = ctxH s₀.mem C := by
      rw [show ctxH s₀.mem C = blockAt s₀.mem (C + BitVec.ofNat 64 240) from rfl]
      refine Proof.Gcm.blockAt_congr fun i hi => ?_
      rw [Offset.add_add]
      refine f₀₁₅.bytes (R := ⟨C, 256⟩) (fun r hr => ?_) (by simp only; omega_using []) (by simp only; omega_using [hi])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dCS
      · exact dCB
    obtain t := T₁₆ i hi j hj
    rw [fp₁₅, Offset.add_add, hp₁₅, hH] at t
    exact t

theorem bitslice_correct [Proof.Gcm.RISCV64.PrepLaw] (s : State) (hs : bitsliceRISCV64.pre s) :
    ∃ t s', Exec isa bitslice s t s' ∧ abiPreserved s s' ∧ bitsliceRISCV64.post s s' := by
  obtain ⟨t, s', he, h1, h2, h3⟩ := bitslice_wp hs
  exact ⟨t, s', he, ⟨h1, (Exec.regions he (by decide)).2.2.1, h2⟩, h3⟩

/-! ## Constant time: only the pointers reach addresses and branches -/

theorem bitslice_ct : ConstantTime isa bitsliceRISCV64.pre bitsliceRISCV64.pub bitslice := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  rintro s₁ s₂ - - ⟨h0, h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

/-! ## The contract -/

/-- `vg_aes_gcm_bitslice` with `scratch: *mut [u64; 256]`. -/
def bitsliceScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("bk", .array true .u64 156), ("scratch", .array true .u64 256)]

/-- `bitsliceContract`, whatever `scratch` is. -/
def bitsliceScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  bitsliceScratchSig.contract A (pre := fun _ctx _bk _scratch _ => True)
    (post := fun ctx bk _scratch => Spec.Gcm.bitslicePost A.ptrBits ctx bk) (stack := stack)

/-- A state satisfying the precondition. -/
def bitsliceSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x2000, 1248⟩, ⟨0x4000, 2048⟩]

theorem bitslice_verified [Proof.Gcm.RISCV64.PrepLaw] :
    Verified RISCV64.target bitslice (bitsliceScratchContract RISCV64.abi) :=
  Verified.of_correct bitslice_correct bitslice_ct (by
    sig_implies [bitsliceScratchContract, bitsliceScratchSig, Spec.Gcm.bitslicePost, bitsliceRISCV64,
      RISCV64.abi, RISCV64.argRegs, and_true] [bitsliceSat] using bitsliceSat)

/-! ## In a frame of its own -/

/-- `SlicedRepr` reads the memory only within the buffer's 1248 bytes. -/
theorem slicedRepr_congr {m₁ m₂ : Mem} {bk : Addr} {w : List Byte} {h : Spec.Gcm.Block}
    (hm : ∀ i < 1248, m₂ (bk + BitVec.ofNat 64 i) = m₁ (bk + BitVec.ofNat 64 i))
    (H : SlicedRepr m₁ bk w h) : SlicedRepr m₂ bk w h := by
  obtain rd : ∀ x, x + 8 ≤ 1248 →
      m₂.readW (bk + BitVec.ofNat 64 x) 64 = m₁.readW (bk + BitVec.ofNat 64 x) 64 := fun x hx =>
    Mem.readW_congr fun i hi => by rw [Offset.add_add]; exact hm _ (by omega_using [hx, hi])
  refine ⟨fun j hj t ht b hb i hi => ?_, fun i hi j hj => ?_⟩
  · rw [Offset.add_add, rd _ (by omega_using [hj, ht]), ← Offset.add_add]
    exact H.1 j hj t ht b hb i hi
  · rw [rd _ (by omega_using [hi, hj])]
    exact H.2 i hi j hj

/-- `bitslicePost` reads the memory on return only within the buffers. -/
theorem bitslicePost_out {pb : Nat} : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.Gcm.bitsliceSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.bitsliceSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.bitsliceSig.words pb) (Spec.Gcm.bitslicePost pb) vs m m₁ r →
      Curry.apply (Spec.Gcm.bitsliceSig.words pb) (Spec.Gcm.bitslicePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.bitsliceSig, Spec.Gcm.bitsliceParam, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr] (Spec.Gcm.bitslicePost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr] (Spec.Gcm.bitslicePost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.bitslicePost, ArgWord.ofRaw] at h ⊢
  exact slicedRepr_congr (fun i hi => Proof.AesGcm.agree_of hb.2 i hi) h

theorem bitslicePostOut_local {pb : Nat} : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.Gcm.bitsliceSig.words pb).length →
    Curry.apply (Spec.Gcm.bitsliceSig.words pb) (fun _ _ _ => True) vs m →
    (∀ b ∈ Sig.bufs Spec.Gcm.bitsliceSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.bitsliceSig.words pb) (Spec.Gcm.bitslicePost pb) vs m m₁ r →
      Curry.apply (Spec.Gcm.bitsliceSig.words pb) (Spec.Gcm.bitslicePost pb) vs m m₂ r :=
  fun vs m m₁ m₂ r hlen _ => bitslicePost_out vs m m₁ m₂ r hlen

/-- A state satisfying `vg_aes_gcm_bitslice`'s precondition, without the
working space. -/
def bitsliceFrameSat : State := { bitsliceSat with wr := [⟨0x2000, 1248⟩] }

theorem bitsliceFrameSat_pre : ∃ s, (Spec.Gcm.bitsliceContract RISCV64.abi 2048).pre s := by
  implies_sat [Spec.Gcm.bitsliceContract, Spec.Gcm.bitsliceSig, Spec.Gcm.bitsliceParam, Spec.Gcm.bitslicePost,
    RISCV64.abi, RISCV64.argRegs] [bitsliceFrameSat, bitsliceSat] using bitsliceFrameSat

theorem bitslice_framed [Proof.Gcm.RISCV64.PrepLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2048 .a2 bitslice)
      (Spec.Gcm.bitsliceContract RISCV64.abi 2048) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.bitsliceSig) (nm := "scratch") (e := .u64) (n := 256)
    (pre := fun _ _ _ => True) (post := Spec.Gcm.bitslicePost RISCV64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 2048) bitslice_verified (by decide) (by decide)
    bitslicePostOut_local bitsliceFrameSat_pre

/-! ## Without secret residue -/

open VG.RISCV64.Scrub in
theorem bitsliceOut :
    PostOut (Spec.Gcm.bitsliceContract RISCV64.abi 2048) (Spec.Gcm.bitsliceSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain bitslicePost_out

open VG.RISCV64.Scrub in
/-- `vg_aes_gcm_bitslice`, followed by the clearing of the caller-saved registers and of
its working space, which holds the bitsliced round keys. -/
def bitsliceReg [Proof.Gcm.RISCV64.PrepLaw] : Registration Spec.Gcm.bitsliceApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratch 2048 .a2 Impl.AesGcm.RISCV64.Bitslice.bitslice, verified := bitslice_framed } [(2048, [(0, 256)])]
    bitsliceOut
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb bitsliceOut (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratch 2048 .a2 bitslice) 2048 0 rfl rfl rfl
      (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.AesGcm.RISCV64.Bitslice
