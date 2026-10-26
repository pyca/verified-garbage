module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesCbc.Mem
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa
import Mathlib.Data.List.Induction

/-!
# AES-CBC on PPC64LE: the code between the calls, and the loop

The straight-line pieces of the bodies (`xorInto`, `copy`, `callArgs`,
`advance`), each run in continuation-passing style, with their memories as
explicit writes (`xorMem`, `copyMem`, `Proof/AesCbc/Mem.lean`).

The invariant after `k` blocks (`LInv`), for any mode on whole blocks, as on
x86-64 (`Proof/AesCbc/X86_64/Loop.lean`): `r14`–`r19` hold the arguments
(`r17` the next block, `r18` the blocks left), the other nonvolatile
registers are our caller's, only the chaining value, the data and the first
2064 bytes of the scratch buffer have changed since the registers and the
return address were saved, the first `k` blocks are the mode's
(`Mode.out`) of the first `k` blocks on entry and the rest are unchanged,
and the chaining value is the mode's after them (`Mode.chain`).

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
blocks (`BodyOk`), `whole body` meets the contract.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

/-! ## Straight-line pieces -/

theorem ofNat_zero_add (P : Addr) : P + BitVec.ofNat 64 0 = P := by simp

/-- The block at `dst` XORed with the block at `src`, in place. -/
theorem xorInto_wp {dst src : Reg} {s : State} {P Q : Addr} {rest : List Instr} {Φ : State → Prop}
    (hd : dst ≠ .r0) (hs : src ≠ .r0) (hd9 : dst ≠ .r9) (hd10 : dst ≠ .r10) (hs9 : src ≠ .r9)
    (hs10 : src ≠ .r10) (hp : s.gpr dst = P) (hq : s.gpr src = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = xorMem s.mem P Q →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (xorInto dst src ++ rest)) s Φ := by
  simp only [xorInto, List.cons_append, List.nil_append]
  refine wp_ld hd ⟨by decide, by decide⟩ (by rw [hp, ofNat_zero_add]) rp fun s₁ u₁ => ?_
  refine wp_ld hs ⟨by decide, by decide⟩ (by rw [u₁.other _ hs9, hq, ofNat_zero_add])
    (by rw [u₁.rd, u₁.wr]; exact rq) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_std hd ⟨by decide, by decide⟩
    (by rw [u₃.other _ hd9, u₂.other _ hd10, u₁.other _ hd9, hp, ofNat_zero_add])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wp) fun s₄ u₄ => ?_
  have g₄ (r : Reg) (h9 : r ≠ .r9) (h10 : r ≠ .r10) : s₄.gpr r = s.gpr r := by
    rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  refine wp_ld hd ⟨by decide, by decide⟩ (by rw [g₄ _ hd9 hd10, hp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rp8) fun s₅ u₅ => ?_
  refine wp_ld hs ⟨by decide, by decide⟩ (by rw [u₅.other _ hs9, g₄ _ hs9 hs10, hq])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rq8)
    fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_std hd ⟨by decide, by decide⟩
    (by rw [u₇.other _ hd9, u₆.other _ hd10, u₅.other _ hd9, g₄ _ hd9 hd10, hp])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact wp8) fun s₈ u₈ => ?_
  refine k s₈ (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₈.gpr, u₇.other _ h9, u₆.other _ h10, u₅.other _ h9, g₄ _ h9 h10]
  · rw [u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.other _ (by decide), u₆.mem, u₅.gpr, u₅.mem, u₄.mem,
      u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide), u₂.mem, u₁.gpr, u₁.mem]
    rfl
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- The block at `src + e` copied to `dst + d`, given as `P` and `Q`. -/
theorem copy_wp {dst src : Reg} {d e : Nat} {s : State} {P Q : Addr} {rest : List Instr}
    {Φ : State → Prop} (hd : dst ≠ .r0) (hs : src ≠ .r0) (hd9 : dst ≠ .r9) (hs9 : src ≠ .r9)
    (hdo : d + 8 < 2 ^ 15 ∧ d % 8 = 0) (heo : e + 8 < 2 ^ 15 ∧ e % 8 = 0)
    (hp : s.gpr dst + BitVec.ofNat 64 d = P) (hp8 : s.gpr dst + BitVec.ofNat 64 (d + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr src + BitVec.ofNat 64 e = Q) (hq8 : s.gpr src + BitVec.ofNat 64 (e + 8) = Q + BitVec.ofNat 64 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) → s'.mem = copyMem s.mem P Q →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (copy dst d src e ++ rest)) s Φ := by
  simp only [copy, List.cons_append, List.nil_append]
  refine wp_ld hs ⟨by omega_arith, by omega_arith⟩ hq rq fun s₁ u₁ => ?_
  refine wp_std hd ⟨by omega_arith, by omega_arith⟩ (by rw [u₁.other _ hd9, hp])
    (by rw [u₁.wr]; exact wp) fun s₂ u₂ => ?_
  refine wp_ld hs ⟨by omega_arith, by omega_arith⟩ (by rw [u₂.gpr, u₁.other _ hs9, hq8])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rq8) fun s₃ u₃ => ?_
  refine wp_std hd ⟨by omega_arith, by omega_arith⟩ (by rw [u₃.other _ hd9, u₂.gpr, u₁.other _ hd9, hp8])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wp8) fun s₄ u₄ => ?_
  refine k s₄ (fun r h9 => ?_) ?_ ?_ ?_
  · rw [u₄.gpr, u₃.other _ h9, u₂.gpr, u₁.other _ h9]
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
    rfl
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- The registers `callArgs` writes. -/
abbrev argRegs5 : List Reg := [.r3, .r4, .r5, .r6, .r7]

/-- The arguments of the block function. -/
theorem callArgs_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r3 = s.gpr .r14 → s'.gpr .r4 = s.gpr .r15 → s'.gpr .r5 = s.gpr .r17 →
      s'.gpr .r6 = BitVec.ofNat 64 1 → s'.gpr .r7 = s.gpr .r19 →
      (∀ r, r ∉ argRegs5 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block callArgs) s Φ := by
  unfold callArgs mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  refine k s₅ ?_ ?_ ?_ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · simp only [argRegs5, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h3, h4, h5, h6, h7⟩ := hr
    rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- On to the next block. -/
theorem advance_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r17 = s.gpr .r17 + BitVec.ofNat 64 16 → s'.gpr .r18 = s.gpr .r18 - BitVec.ofNat 64 1 →
      (∀ r, r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → Φ s') :
    WP isa (.block advance) s Φ := by
  unfold advance
  refine wp_addi (by decide) (by decide) fun s₁ u₁ => wp_subi (by decide) (by decide) fun s₂ u₂ => wp_nil ?_
  refine k s₂ ?_ ?_ (fun r h₁ h₂ => ?_) ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr, u₁.other _ (by decide)]
  · rw [u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

/-! ## The arguments and the invariant -/

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .r3
abbrev R : Nat := (s₀.gpr .r4).toNat
abbrev Iv : Addr := s₀.gpr .r5
abbrev Dp : Addr := s₀.gpr .r6
abbrev N : Nat := (s₀.gpr .r7).toNat
abbrev S : Addr := s₀.gpr .r8

abbrev schR : Region := ⟨W s₀, 240⟩
abbrev ivR : Region := ⟨Iv s₀, 16⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 2176⟩

/-- The blocks on entry. -/
abbrev blks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)

/-- The chaining value on entry. -/
abbrev iv0 : List Byte := bytesAt s₀.mem (Iv s₀) 16

/-- The address of block `k`. -/
abbrev blk (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 (16 * k)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {M : Mode} {s₀ : State} (h : (modePPC64LE M).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- What the prologue saves, the return address first (in `r0`). -/
abbrev saveL : List (Reg × Nat) := (.r0, lrOff) :: saved

/-- The values saved: `r0` holds the return address. -/
abbrev saveG (s₀ : State) : Reg → BitVec 64 := (s₀.write .r0 s₀.lr).gpr

/-- The memory after saving the registers. -/
abbrev savedMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (S s₀) (saveG s₀) saveL

/-- The registers holding our variables. -/
abbrev vars : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19]

/-- The key schedule as the mode uses it. -/
abbrev wK (s₀ : State) : List Byte := bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1))

/-- The first `k` blocks after the mode. -/
abbrev outK (M : Mode) (s₀ : State) (k : Nat) : List (List Byte) :=
  M.out (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The chaining value after the first `k` blocks. -/
abbrev chainK (M : Mode) (s₀ : State) (k : Nat) : List Byte :=
  M.chain (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The loop invariant, after `k` blocks. -/
structure LInv (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = chainK M s₀ k

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem UPre.blk_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨blk s₀ j, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

end

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2120) :
    (⟨b + BitVec.ofNat 64 2064, 56⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega_arith)).symm]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem saved_bound : ∀ p ∈ saveL, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2120 := by decide

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨S s + BitVec.ofNat 64 2064, 56⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame (lo := 2064) (n := 56) saved_bound (by decide) _ _ _

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

/-- The blocks after a step that changed only block `k`, the chaining
value and the first 2064 bytes of the scratch buffer. -/
theorem UPre.blocksAt_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] m m') :
    Spec.Cbc.blocksAt m' (Dp s₀) (N s₀) =
      (Spec.Cbc.blocksAt m (Dp s₀) (N s₀)).set k (bytesAt m' (blk s₀ k) 16) := by
  refine blocksAt_set fun j hj hjk => bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.blk_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))

omit hp in
/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega_arith
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ k by omega_arith), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at this
  show bytesAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 = _
  rw [← getElem_blocksAt _ _ hk]
  exact Option.some.inj this

end

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; exact hk)]
  rfl

theorem r4_ofNat (s₀ : State) : s₀.gpr .r4 = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [R]

theorem r7_ofNat (s₀ : State) : s₀.gpr .r7 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

/-- What `advance` leaves after block `k`: the registers of block `k + 1`. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State} {Φ : State → Prop}
    (h17 : s.gpr .r17 = blk s₀ k) (h18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k))
    (h : ∀ s', s'.gpr .r17 = blk s₀ (k + 1) → s'.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + 1)) →
      (∀ r, r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → Φ s') :
    WP isa (.block advance) s Φ := by
  have hN := (s₀.gpr .r7).isLt
  refine advance_wp fun s' r17' r18' keep mem' rd' wr' => h s' ?_ ?_ keep mem' rd' wr'
  · rw [r17', h17, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_arith)]
  · rw [r18', h18, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`. -/
def BodyOk (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa body s (LInv M s₀ (k + 1))

theorem loop_ok {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    WP isa (.loop body (.nonzero .d .r18)) s (LInv M s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d .r18) (Q := LInv M s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv M s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat' s' .r18 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.r18
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

/-! ## Saving and restoring the registers -/

theorem save_eq : save = .mflr .r0 :: Spill.saveCode .r8 saveL := rfl

theorem restore_eq : restore = Spill.restoreCode .r19 saveL ++ ([.mtlr .r0] : List Instr) := rfl

theorem preserved_ne_r0 : ∀ r ∈ preserved, r ≠ .r0 := by decide

theorem prologue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv M s₀ 0) := by
  have hN := (s₀.gpr .r7).isLt
  rw [save_eq, List.cons_append]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := saveL) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := saved_bound p hp'
    show InRegions s₀.wr (S s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith))
  unfold setup mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] →
      ∀ r' ∈ [⟨S s₀ + BitVec.ofNat 64 2064, 56⟩], r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : Spec.Cbc.blocksAt (savedMem s₀) (Dp s₀) (N s₀) = blks s₀ := by
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => bytesAt_frame f₀ (fun r hr => ?_) (by decide)
    have := List.mem_range.mp hj
    exact (disj _ (by simp) r hr).sub_left (UPre.data_sub this)
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; rfl
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by
    simp [State.write, hr]
  exact {
    r14 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .r3 (by decide)
    r15 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .r4 (by decide)
    r16 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r5 (by decide)
    r17 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r6 (by decide)]; simp
    r18 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r7 (by decide), r7_ofNat]; rfl
    r19 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r8 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h14, h15, h16, h17, h18, h19⟩ := hv
      rw [u₆.other _ h19, u₅.other _ h18, u₄.other _ h17, u₃.other _ h16, u₂.other _ h15, u₁.other _ h14]
      exact g₀ _ (preserved_ne_r0 r hr)
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    data := by rw [m₆, dataS, outK, List.take_zero, M.out_nil, List.drop_zero, List.nil_append]
    iv := by rw [m₆, ivS, chainK, List.take_zero, M.chain_nil] }

/-- No blocks, or `mid` on all of them. -/
theorem ends_mid_wp {M : Mode} {mid : Prog isa} {s₀ : State} {s₁ : State}
    (hm : 0 < N s₀ → WP isa mid s₁ (LInv M s₀ (N s₀))) (h : LInv M s₀ 0 s₁) :
    WP isa (.ite (.zero .d .r18) (.block []) mid) s₁ (LInv M s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  have ev := eval_zero_ofNat s₁ .r18 (k := N s₀ - 0) (by omega_arith) h.r18
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact hm (by omega_arith)

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ p ∈ saveL, ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  intro p hp' r hr
  have hb := saved_bound p hp'
  have hsub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := UPre.scr_sub (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left hsub
  · exact hp.data_scr.symm.sub_left hsub
  · exact Offset.disjoint_base _ (by omega_arith) (by have := hp.scr_wrap; omega_arith)

/-- The postcondition of the whole function, but for the stack pointer. -/
def Done (M : Mode) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ (modePPC64LE M).post s₀ s'

theorem epilogue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv M s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (Done M s₀) := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved (S s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame (slots_disj hp)
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  rw [restore_eq]
  refine Spill.restore_ok (b := .r19) (l := saveL) (by decide) h₂.r19 (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => ?_
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by have := hp.scr_wrap; omega_arith))
  refine WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_, ?_⟩)
  · show s₃.gpr r = _
    have h0 : saveG s₀ r = s₀.gpr r := ite_eq_right_iff.mpr fun h => absurd h (preserved_ne_r0 r hr)
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h₂.keep r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, lrOff) (by decide)]; rfl
  · show Spec.Cbc.blocksAt s₃.mem (Dp s₀) (N s₀) = _
    rw [r₃.mem, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [r₃.mem, h₂.iv]; simp only [chainK, hall]

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, when `mid` takes the invariant from no
blocks to all of them (as `body`'s loop does, `whole_wp`). -/
theorem ends_wp {M : Mode} {mid : Prog isa} {s₀ : State} (h0 : (modePPC64LE M).pre s₀)
    (hm : UPre s₀ → 0 < N s₀ → ∀ {s₁ : State}, LInv M s₀ 0 s₁ → WP isa mid s₁ (LInv M s₀ (N s₀))) :
    WP isa (.seq (.block (save ++ setup)) (.seq (.ite (.zero .d .r18) (.block []) mid) (.block restore)))
      s₀ (Done M s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (ends_mid_wp (fun hn => hm hp hn h₁) h₁) fun _ h₂ => epilogue_wp hp h₂))

theorem whole_wp {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State}
    (h0 : (modePPC64LE M).pre s₀) : WP isa (whole body) s₀ (Done M s₀) :=
  ends_wp h0 fun hp hn _ h => loop_ok hb hp hn h

end VG.Proof.AesCbc.PPC64LE
