module

import VerifiedGarbage.Proof.Argon2.IterationsIndices
public import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Argon2.IterationsIndices
meta import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1
meta import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Argon2.FillStep
public import VerifiedGarbage.Proof.Argon2.X86.Derive.FillLoops
public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.SegmentIndices
meta import VerifiedGarbage.Proof.Argon2.FillStep
meta import VerifiedGarbage.Proof.Argon2.X86.Derive.FillLoops
meta import VerifiedGarbage.Proof.Argon2.Slices
meta import VerifiedGarbage.Proof.Argon2.SegmentIndices
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCache
meta import VerifiedGarbage.Proof.Argon2.FillPositions
meta import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCache
public import VerifiedGarbage.Proof.Argon2.X86.Derive.FillDep
meta import VerifiedGarbage.Proof.Argon2.X86.Derive.FillDep
public import VerifiedGarbage.Proof.Argon2.FinalReduction
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Lit
public import VerifiedGarbage.Proof.Argon2.Contract
meta import VerifiedGarbage.Proof.Argon2.FinalReduction
meta import VerifiedGarbage.Proof.Argon2.Serialization
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Argon2.Permutation
meta import VerifiedGarbage.Proof.Argon2.Reference
meta import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
meta import VerifiedGarbage.Proof.Blake2.Scratch
meta import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
meta import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.StackScratch
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Blake2.X86.CompressB.Lit
meta import VerifiedGarbage.Proof.Argon2.Contract

/-! ### `Argon2.X86.Derive.ReduceCT`, which only this module used -/

section

/-! ### `Argon2.X86.Derive.Correct`, which only this module used -/

section

@[expose] public section

section

/-!
# Argon2 on x86 (32-bit): the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (laneOff laneLenOff argOff divisorOff segLenOff strideOff)

theorem reduction_snoc (p : Spec.Argon2.Params) (M : Array Block) (l : Nat) (acc : Block) :
    Proof.Argon2.reduction p M 0 (l + 1) acc =
      xorBlock (Proof.Argon2.reduction p M 0 l acc) (M[Proof.Argon2.lastIndex p l]?.getD zeroBlock) := by
  unfold Proof.Argon2.reduction
  rw [foldl_range'_snoc, Nat.zero_add]

/-- The state of the reduction after `l` lanes. -/
structure RI (s₀ : State) (M : Array Block) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  lane : lw s₀ s laneOff = BitVec.ofNat 32 l
  first : blockAt s.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 l zeroBlock
  rest : ∀ k < (prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (memB s₀) k) = M[k]?.getD zeroBlock

theorem cell0 (s₀ : State) : matrixCell (memB s₀) 0 = memB s₀ := by simp [matrixCell]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.seq (.block Impl.Argon2.X86.Derive.reduceLane) Impl.Argon2.X86.Derive.reduceXor)
      s fun t => RI s₀ M (l + 1) t ∧ t.cf = some (decide (l + 1 < lanesN s₀)) := by
  obtain L8 := laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (prm s₀).laneLen - 1) (by omega_using [L8])
  obtain last : Proof.Argon2.lastIndex (prm s₀) l = l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega_using [L8]
  obtain ne0 : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) ≠ 0 := by omega_using [L8]
  unfold Impl.Argon2.X86.Derive.reduceLane Impl.Argon2.X86.Derive.reduceXor
  simp only [List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  obtain i₁ := h.inv.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => ?_
  obtain i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega_using [L8])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, Wp.ofNat_pred (by omega_using [L8])]) fun s₄ a₄ _ k₄ => WP.block_nil ?_
  obtain i₄ := i₃.keep k₄
  refine WP.seq (wp_mov fun s₅ u₅ => ?_)
  obtain i₅ := i₄.upd u₅ (by decide) (by decide)
  refine wp_ldarg hp i₅ (i := 13) (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain i₆ := i₅.upd u₆ (by decide) (by decide)
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  have hm := hp.mem_fits
  obtain b22 := blocks22 hp
  obtain b1 := blocks_pos hp
  generalize hc : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) = c at cl a₄ ne0 last
  obtain hc' : c * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [cl]
  obtain sx : s₆.gpr .esi = memP s₀ + BitVec.ofNat 32 (c * 1024) := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]
  obtain dx : s₆.gpr .edi = memP s₀ + BitVec.ofNat 32 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.seq ((writeBlock_ok hp i₆ (cur := 0) b1 true sx
    (by rw [add_nat (by omega_using [hc', hm])]; omega_using [hc', hm])
    ⟨memR s₀, by simp, c * 1024, cell_addr hp cl, hc'⟩
    (by rw [cell_addr hp cl]; exact cell_other hp cl b1 ne0) dx).mono
    fun t₇ ⟨i₇, f₇, w₇⟩ => ?_)
  obtain lt₇ : ∀ d, d + 4 ≤ 144 → lw s₀ t₇ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₆ d]
    exact f₇.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine (advance_ok hp i₇ (d := laneOff) (n := l) (by decide) (by rw [lt₇ _ (by decide)]; exact h.lane)
    (by omega_using [hl, hlt]) (B := lanesN s₀) (by omega_using [hlt]) fun v iv _ => ?_).mono fun t ⟨it, mt, ct, _⟩ => ⟨?_, ct⟩
  · rw [show Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg) = .mem ⟨.ebp, argOff 7⟩ from rfl,
      Wp.readSrc_mem iv.ebp (iv.arg_in hp (by decide)), iv.arg hp (by decide)]
    simp
  obtain ⟨lt, _, ct⟩ := loc_store hp (d := laneOff) (by decide) mt
  obtain new : blockAt t₇.mem (matrixCell (memB s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (memB s₀) c)) (blockAt s.mem (matrixCell (memB s₀) 0)) := by
    rw [cell_blk hp _ b1, cell_blk hp _ b1, cell_blk hp _ cl,
      blk_of_words (f := fun i => mw s₀ s.mem (c * 1024 + 4 * i) ^^^ mw s₀ s.mem (0 * 1024 + 4 * i)) fun i hi => by
        rw [← mw, w₇ i hi, ite_eq_left hi]; simp only [wnew, ite_true]; rw [m₆, addr_shift],
      blk_of_words (m := s.mem) (B := memP s₀) (o := c * 1024) (f := fun i => mw s₀ s.mem (c * 1024 + 4 * i))
        fun _ _ => rfl,
      blk_of_words (m := s.mem) (B := memP s₀) (o := 0 * 1024) (f := fun i => mw s₀ s.mem (0 * 1024 + 4 * i))
        fun _ _ => rfl, xor_words]
  refine ⟨it, Prm.of_lw h.pr fun d hd => ?_, ?_, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega_using [hd4]) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lt₇ d hd4]
  · show t.mem.readW _ 32 = _
    rw [mt, Mem.readW_writeW_self32]
  · rw [ct _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [ct _ hk, blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa (.seq Impl.Argon2.X86.Derive.reduceClear (.block (Impl.Argon2.X86.Derive.setLocal laneOff 0))) s
      (RI s₀ M 0) := by
  obtain b1 := blocks_pos hp
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  have hmf := hp.mem_fits
  unfold Impl.Argon2.X86.Derive.reduceClear Impl.Argon2.X86.Derive.setLocal
  refine WP.seq (WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => WP.block_nil ?_))
  obtain i₁ := h.upd u₁ (by decide) (by decide)
  refine (zeroWords_ok i₁ (r := .edi) (by decide) (by decide) (by decide) (by decide) (X := memP s₀) (n := 256)
    (R := memR s₀) (by simp) (mem_mem hp) (off := 0) (BitVec.add_zero _).symm
    (show 0 + 4 * 256 ≤ blocksN s₀ * 1024 by omega_using [b1]) (show blocksN s₀ * 1024 < 2 ^ 64 by omega_using [hmf])
    (Nat.le_trans (Nat.add_le_add_left (show 4 * 256 ≤ blocksN s₀ * 1024 by omega_using [b1]) _) hmf)
    (by decide) u₁.gpr).mono fun s₃ ⟨i₃, _, f₃', z₃⟩ => ?_
  obtain f₃ : Frame [⟨matrixCell (memB s₀) 0, 1024⟩] s₁.mem s₃.mem := by rw [cell0]; exact f₃'
  refine wp_movi fun s₄ u₄ => ?_
  obtain i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_stloc hp i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ _ _ m₅ => WP.block_nil ?_
  obtain ⟨l₅, _, c₅⟩ := loc_store hp (d := laneOff) (by decide) m₅
  have m₂ : s₁.mem = s.mem := u₁.mem
  obtain lt₃ : ∀ d, d + 4 ≤ 144 → lw s₀ s₃ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₂ d]
    exact f₃.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine ⟨i₅, Prm.of_lw pr fun d hd => ?_, by rw [v₅, u₄.gpr]; rfl, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [l₅ d (by omega_using [hd4]) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lw_mem u₄.mem, lt₃ d hd4]
  · rw [c₅ _ (by rw [← hb]; exact b1), u₄.mem, cell0, blockAt_zero fun i hi => z₃ i (by omega_using [hi])]
    rfl
  · rw [c₅ _ hk, u₄.mem, blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa Impl.Argon2.X86.Derive.reduce s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      blockAt t.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 (lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.X86.Derive.reduce
  refine WP.seq ((reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ RI s₀ M l t) ?_ (lanesN s₀) s₅
    ⟨0, by omega_using [], hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 < lanesN s₀
  · exact .inr ⟨by rw [show isa.eval .b u = u.cf from rfl, cu]; simp [e], _, by omega_using [hl], l + 1, rfl, e, hu⟩
  · refine .inl ⟨by rw [show isa.eval .b u = u.cf from rfl, cu]; simp [e], hu.inv, hu.pr, ?_⟩
    rw [hu.first, show l + 1 = lanesN s₀ by omega_using [hl, e]]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.X86.Derive.finalOutput s fun t => Inv s₀ t ∧
      bytesAt t.mem ((outP s₀).setWidth 64) (outL s₀) =
        Spec.Argon2.hPrime (outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (memB s₀) 0))) := by
  obtain b1 := blocks_pos hp
  have hm := hp.mem_fits
  have ho := hp.out_fits
  have tg := hp.tag_ge
  unfold Impl.Argon2.X86.Derive.finalOutput
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  obtain i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_movi fun s₂ u₂ => ?_
  obtain i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide) (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  obtain i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain i₅ := i₄.upd u₅ (by decide) (by decide)
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain si : s₅.gpr .esi = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  obtain ax : (s₅.gpr .eax).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  obtain di : s₅.gpr .edi = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  obtain cx : (s₅.gpr .ecx).toNat = outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  refine hcall_ok hp i₅ (r := .esi) (by decide) u₅.gpr
    ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_using [b1]⟩
    (by rw [si, ax]; omega_using [b1, hm]) ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_using []⟩
    (by rw [di, cx]; exact ho) (by rw [cx]; omega_using [tg]) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, cell0, Proof.Argon2.serialize_blockAt]

end
end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frames, keeps the ABI's registers too.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Spec.Blake2 (bytesAt)

theorem body_nosp : NoSp Impl.Argon2.X86.Derive.body := NoSp.of_all (by lit_decide)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.X86.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧
    bytesAt t.mem ((outP s₀).setWidth 64) (outL s₀) =
      Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  unfold Impl.Argon2.X86.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
  refine parameters_ok hp fun s₁ i₁ p₁ => WP.block_nil ?_
  refine WP.seq ((code_ok hp i₁ p₁).mono fun s₂ ⟨i₂, p₂, b₂⟩ => ?_)
  refine WP.seq ((memoryInit_ok hp i₂ p₂ b₂).mono fun s₃ ⟨i₃, p₃, m₃⟩ => ?_)
  refine WP.seq ((passes_ok hp (st := Spec.Argon2.initMemory (prm s₀)
    (Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))) ⟨i₃, p₃, m₃⟩).mono
    fun s₄ f₄ => ?_)
  rw [show itersN s₀ = (prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₄
  refine WP.seq ((reduce_ok hp f₄.inv f₄.pr f₄.mem).mono fun s₅ ⟨i₅, _, b₅⟩ => ?_)
  refine (finalOutput_ok hp i₅).mono fun t ⟨it, ot⟩ => ⟨it.done hp, ?_⟩
  rw [ot, b₅, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct : WP isa Impl.Argon2.X86.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveX86.post s₀ t :=
  frames_ok (by have := hp.esp_lo; omega_using [this]) body_nosp (body_ok hp) fun t u q f => by
    show bytesAt u.mem _ _ = _
    rw [Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := outR s₀) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ((hp.stk_all _ (by simp)).sub_left
        (below_sub (by decide) (by have := hp.esp_lo; omega_using [this]))).symm)
      (by show outL s₀ ≤ 2 ^ 64; have := hp.out_fits; omega_using [this]) hi]
    exact q

end

end VG.Proof.Argon2.X86.Derive

end

end

/-!
# Argon2 on x86 (32-bit): the final block and the tag, in two runs

`reduce_rel`: XORing every lane's last block into the first leaks the same
trace in two runs (the lane's last block's address, which the taint analysis
forgets, is related by correctness); `finalOutput_rel`: so does the call of
H′ that writes the tag.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_addi wp_subi)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.X86.Derive (argOff laneOff laneLenOff)

theorem RI.of_keep {s₀ s t : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (k : Divide.Keep s t) :
    RI s₀ M l t :=
  ⟨h.inv.keep k, h.pr.of_mem k.mem, by rw [lw_mem k.mem]; exact h.lane, by rw [k.mem]; exact h.first,
    fun j hj j0 => by rw [k.mem]; exact h.rest j hj j0⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first part of a lane's reduction: `eax :=` the address of its last block. -/
theorem redPart1_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (([.mov .eax (Impl.Argon2.X86.Derive.fr laneOff),
      .mov .ecx (Impl.Argon2.X86.Derive.fr laneLenOff), .alu .sub .ecx (.imm 1)] : List Instr) ++
      Impl.Argon2.X86.Derive.blockAddr)) s fun t => RI s₀ M l t ∧
      t.gpr .eax = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + ((prm s₀).laneLen - 1)) * 1024) := by
  have L8 := laneLen_ge hp
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  rw [← List.append_nil Impl.Argon2.X86.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega_using [L8])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, Wp.ofNat_pred (by omega_using [L8])]) fun s₄ a₄ _ k₄ =>
      WP.block_nil ⟨h.of_keep (((Divide.Keep.of_upd u₁ (by simp)).trans ((Divide.Keep.of_upd u₂ (by simp)).trans
        (Divide.Keep.of_upd u₃ (by simp)))).trans k₄), a₄⟩

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : Inv s₀ s) :
    WP isa (.block [.mov .esi (Impl.Argon2.X86.Derive.fr (argOff 13)), .mov .eax (.imm 1024),
      .mov .edi (Impl.Argon2.X86.Derive.fr (argOff 16)), .mov .ecx (Impl.Argon2.X86.Derive.fr (argOff 17)),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .esi = memP s₀ ∧ t.gpr .eax = 1024 ∧ t.gpr .edi = outP s₀ ∧ t.gpr .ecx = arg s₀ 17 := by
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_movi fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ⟨i₄.upd u₅ (by decide) (by decide),
    u₅.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ Represents s₁.mem (memB s₀₁) (prm s₀₁).blocks M₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ Represents s₂.mem (memB s₀₂) (prm s₀₂).blocks M₂))
      Impl.Argon2.X86.Derive.reduce fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.X86.Derive.reduce
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_using [], hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂)
      (.seq (.block Impl.Argon2.X86.Derive.reduceLane) Impl.Argon2.X86.Derive.reduceXor) fun _ _ => True := by
    refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
      (fun s h => redPart1_ok T.hp₁ h (by rw [hN]; exact hl))
      (fun s h => redPart1_ok T.hp₂ h (by rw [hN₂]; exact hl)) ?_
    exact T.leafI [.eax] (fun s₁ s₂ h => ⟨h.1.1.inv, h.2.1.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := HPrime.rel_wp body
    (fun s h => reduceLane_ok T.hp₁ h (by rw [hN]; exact hl))
    (fun s h => reduceLane_ok T.hp₂ h (by rw [hN₂]; exact hl)) s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega_using [hn, hl], l + 1, rfl, e, k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) Impl.Argon2.X86.Derive.finalOutput fun _ _ => True := by
  have pre : ∀ {s₀ : State}, DPre s₀ → ∀ {t : State}, Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .esi = memP s₀ ∧ t.gpr .eax = 1024 ∧ t.gpr .edi = outP s₀ ∧ t.gpr .ecx = arg s₀ 17 →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, (t.gpr .esi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .eax).toNat ≤ R.len) ∧ (t.gpr .esi).toNat + (t.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, (t.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .ecx).toNat ≤ R.len) ∧ (t.gpr .edi).toNat + (t.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .ecx).toNat := fun {s₀} hp {t} ⟨i, d, si, ax, di, cx⟩ => by
    have b1 := blocks_pos hp
    have hm := hp.mem_fits
    have ho := hp.out_fits
    have tg := hp.tag_ge
    refine ⟨i, d, ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_using [b1]⟩,
      by rw [si, ax]; show _ + 1024 ≤ 2 ^ 32; omega_using [b1, hm],
      ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_using []⟩,
      by rw [di, cx]; exact ho, by rw [cx]; show 1 ≤ outL s₀; omega_using [tg]⟩
  unfold Impl.Argon2.X86.Derive.finalOutput
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => foBlk_ok T.hp₁ h) (fun s h => foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel (r := .esi) (by decide) fun s₁ s₂ k₁ k₂ =>
    ⟨pre T.hp₁ k₁, pre T.hp₂ k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.X86.Derive

end

end

/-! ### `Argon2.X86.Derive.InitialCT`, which only this module used -/

section

/-!
# Argon2 on x86 (32-bit): H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s macros' relations
(`HPrime.init_rel`, `update_rel`, `finalize_rel`, `absorbFixed_rel`), from
the same arguments: `scratch`, the inputs' places and lengths, and the byte
count, which only the inputs' lengths fix.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.X86.HPrime (Ctx InitIn UpdateIn FinalizeIn FixedIn)
open VG.Impl.Argon2.X86.Derive (countLoOff countHiOff argOff)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `scratch`'s context in the second run, in the first run's terms. -/
theorem ctx₂ {s : State} (h : Inv s₀₂ s) (hb : s.gpr .ebx = scrP s₀₂) : Ctx (scrP s₀₁) (E s₀₁) s := by
  rw [T.pb.scrP_eq, T.pb.E]; exact ctx T.hp₂ h hb

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.X86.Derive.start fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  unfold Impl.Argon2.X86.Derive.start
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => stA_ok T.hp₁ h.1 h.2) (fun s h => stA_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW ((HPrime.init_rel (B := scrP s₀₁) (E := E s₀₁) (n := 64) (by decide) (by decide)).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, h.1.2.2.2⟩, ⟨T.ctx₂ h.2.1 h.2.2.2.1, h.2.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => stInit_ok T.hp₁ h) (fun s h => stInit_ok T.hp₂ h) ?_
  refine RelCT.seqW (T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t ∧ t.gpr .ebx = scrP s₀₁ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀₁).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀₁).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₁))
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t ∧ t.gpr .ebx = scrP s₀₂ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀₂).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀₂).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₂))
    (fun s h => (header_ok T.hp₁ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩)
    (fun s h => (header_ok T.hp₂ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩) ?_
  refine RelCT.seqW ((HPrime.absorbFixed_rel (B := scrP s₀₁) (E := E s₀₁) (offset := 768) (size := 24)
      (by omega_arith) (by decide) (by decide) (stk_scr T.hp₁ (by decide) (by decide)) ⟨_, by taint_decide⟩).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, scr_cov T.hp₁ h.1.1 (by decide)⟩,
        ⟨T.ctx₂ h.2.1 h.2.2.2.1, by rw [T.pb.scrP_eq]; exact scr_cov T.hp₂ h.2.1 (by decide)⟩⟩) fun _ _ h => h)
    (fun s h => stFix_ok T.hp₁ h) (fun s h => stFix_ok T.hp₂ h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR₁ : (⟨(arg s₀₁ ptr).setWidth 64, (arg s₀₁ len).toNat⟩ : Region) ∈ [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁])
    (hR₂ : (⟨(arg s₀₂ ptr).setWidth 64, (arg s₀₂ len).toNat⟩ : Region) ∈ [pwR s₀₂, saltR s₀₂, secR s₀₂, adR s₀₂])
    (hfit₁ : (arg s₀₁ ptr).toNat + (arg s₀₁ len).toNat ≤ 2 ^ 32)
    (hfit₂ : (arg s₀₂ ptr).toNat + (arg s₀₂ len).toNat ≤ 2 ^ 32) {data₁ data₂ : List Byte}
    (hd : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (heq : data₁.length = data₂.length)
    (hcA : ∃ hc, (VG.Taint.check taint (τB [] [.ebx]) (.block [.mov .eax (Impl.Argon2.X86.Derive.fr (argOff len)),
      .store ⟨.ebx, 792⟩ .eax, .mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff), .mov .esi (.reg .ebx), .alu .add .esi (.imm 792),
      .mov .edi (.imm 4)]) hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check taint (τB [] []) (.block (Impl.Argon2.X86.Derive.addCount (.imm 4) ++
      ([.mov .esi (Impl.Argon2.X86.Derive.fr (argOff ptr)), .mov .edi (Impl.Argon2.X86.Derive.fr (argOff len))] :
        List Instr)))
      hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check taint (τB [] [])
      (.block (Impl.Argon2.X86.Derive.addCount (Impl.Argon2.X86.Derive.fr (argOff len)))) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) (Impl.Argon2.X86.Derive.absorb ptr len)
      fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  have ep := T.pb.arg_eq hptr
  have el := T.pb.arg_eq hlen
  have e792 : (scrP s₀₁ + 792).setWidth 64 = (scrP s₀₁).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega_arith)
  have cov792 : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      Covers [⟨(scrP s₀ + 792).setWidth 64, 4⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h => by
    have := hp.scr_fits
    have e : (scrP s₀ + 792).setWidth 64 = (scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
      HPrime.setWidth_add (d := 792) (by omega_arith)
    rw [e]; exact Covers.right (scr_cov hp h (by decide))
  have covIn : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      Covers [⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h hR => by
    have hR' : (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈
        [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
    rw [h.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩
  have hS : (⟨(arg s₀₁ ptr).setWidth 64, (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, memR s₀₁, scrR s₀₁, outR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  have hR' : (⟨(arg s₀₁ ptr).setWidth 64, (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, argR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.X86.Derive.absorb
  refine RelCT.seqW (T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.ebx, h.2.ebx, T.pb.scrP_eq]⟩) hcA)
    (fun s h => absA_ok T.hp₁ hlen h.hc) (fun s h => absA_ok T.hp₂ hlen h.hc) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (E := E s₀₁) (D := scrP s₀₁ + 792) (L := 4)
      (lo := BitVec.ofNat 32 data₁.length) (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))
      (by have : (scrP s₀₁ + 792).toNat = (scrP s₀₁).toNat + 792 := add_nat (k := 792) (by omega_arith)
          omega_arith)
      (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by rw [e792]; exact stk_scr T.hp₁ (by decide) (by decide))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁, _⟩, ⟨g₂, e₂, d₂, c₂, x₂, _⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.ebx, e₁, d₁, c₁, x₁, cov792 T.hp₁ g₁.inv⟩,
         ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [e₂, T.pb.scrP_eq], d₂, by rw [c₂, heq], by rw [x₂, heq],
           by rw [T.pb.scrP_eq]; exact cov792 T.hp₂ g₂.inv⟩⟩) fun _ _ h => h)
    (fun s h => absU1_ok T.hp₁ h.1 rfl (by omega_arith) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun s h => absU1_ok T.hp₂ h.1 rfl (by omega_arith) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcB)
    (fun s h => absB_ok T.hp₁ hptr hlen h) (fun s h => absB_ok T.hp₂ hptr hlen h) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (E := E s₀₁) (D := arg s₀₁ ptr)
      (L := (arg s₀₁ len).toNat) (lo := BitVec.ofNat 32 (data₁.length + 4))
      (hi := BitVec.ofNat 32 ((data₁.length + 4) / 2 ^ 32))
      hfit₁ ((T.hp₁.ro_w _ hR' (scrR s₀₁) (by simp)).sub_right (Region.sub_prefix (by decide)))
      ((T.hp₁.stk_all _ hS).sub_left fun a ha => call_stk T.hp₁ a (below60_call T.hp₁ a ha))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁⟩, ⟨g₂, e₂, d₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.ebx, e₁, d₁, c₁, x₁, covIn T.hp₁ g₁.inv hR₁⟩,
         ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [e₂, ep], by rw [d₂, el], by rw [c₂, heq], by rw [x₂, heq],
           by rw [ep, el]; exact covIn T.hp₂ g₂.inv hR₂⟩⟩) fun _ _ h => h)
    (fun s h => absU2_ok T.hp₁ hR₁ hfit₁ h.1 (by simp [Proof.Argon2.le32_length]) (by omega_arith)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun s h => absU2_ok T.hp₂ hR₂ hfit₂ h.1 (by simp [Proof.Argon2.le32_length]) (by omega_arith)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose absorbed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) Impl.Argon2.X86.Derive.finish fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.finish
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fiA_ok T.hp₁ h) (fun s h => fiA_ok T.hp₂ h) ?_
  refine RelCT.seqW ((HPrime.finalize_rel (B := scrP s₀₁) (E := E s₀₁) (lo := BitVec.ofNat 32 data₁.length)
      (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))).mono
      (fun s₁ s₂ ⟨⟨g₁, c₁, x₁⟩, ⟨g₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.ebx, c₁, x₁⟩, ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [c₂, heq], by rw [x₂, heq]⟩⟩)
      fun _ _ h => h)
    (fun s h => fiFin_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fiFin_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  exact T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- H₀'s code leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.X86.Derive.code fun _ _ => True := by
  have l1 := (arg s₀₁ 2).isLt
  have l2 := (arg s₀₁ 4).isLt
  have l3 := (arg s₀₁ 10).isLt
  have hpp := T.pb
  have a2 : (arg s₀₂ 2).toNat = (arg s₀₁ 2).toNat := by rw [hpp.arg_eq (by decide)]
  have a4 : (arg s₀₂ 4).toNat = (arg s₀₁ 4).toNat := by rw [hpp.arg_eq (by decide)]
  have a10 : (arg s₀₂ 10).toNat = (arg s₀₁ 10).toNat := by rw [hpp.arg_eq (by decide)]
  have a12 : (arg s₀₂ 12).toNat = (arg s₀₁ 12).toNat := by rw [hpp.arg_eq (by decide)]
  unfold Impl.Argon2.X86.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => start_ok T.hp₁ h.1 h.2) (fun s h => start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.pw_fits T.hp₂.pw_fits (by rw [Proof.Argon2.initialHeader_length]; omega_arith)
      (by rw [Proof.Argon2.initialHeader_length, Proof.Argon2.initialHeader_length])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₁.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₂.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.salt_fits T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₁.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.sec_fits T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₁.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.ad_fits T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4,
        a10])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₁.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; have := (arg s₀₂ 10).isLt; omega_arith) h) ?_
  exact T.finish_rel (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length,
    bytesAt_length, a2, a4, a10, a12])

end Two

end VG.Proof.Argon2.X86.Derive

end

end

/-! ### `Argon2.X86.Derive.FillCT3`, which only this module used -/

section

/-! ### `Argon2.X86.Derive.FillCT2`, which only this module used -/

section

/-!
# Argon2 on x86 (32-bit): a block of the filling loops, in two runs

`fillBlock_rel`: one block's trace depends only on its position and on the
reference block's index, which the leakage permits (`Spec.Argon2.references`):
the reference is computed from the random word in the locals (`reference_rel`),
G is called on the previous and the reference blocks (`fillCompress_rel`), and
its output is written to the current block (`fillWrite_rel`), whose address the
runs agree on.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_add wp_addi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off refLaneOff tmpOff curOff)

/-- The slots of the words `ws0` and `ex`. -/
abbrev slx (ex : List Nat) : List (Nat × Nat × Nat) := sl0 ++ ex.map fun d => (0, d, 4)

theorem slotsOkX {ex : List Nat} (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144) (rs : List Reg) :
    VG.X86.Taint.SlotsOk (τB (slx ex) rs) := by
  refine VG.X86.Taint.slotsOk_of_list rfl fun x hx => ?_
  simp only [slx, List.append_assoc, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨d, hd, rfl⟩ | hx
  · exact (slotsOk0 rs).of_mem rfl (List.mem_append_left _ hx) (by
      simp only [sl0, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide)
  · have := hex d hd; simp [τB]; omega_using [this]
  · exact (slotsOk0 rs).of_mem rfl (List.mem_append_right _ hx) (by
      simp only [List.mem_singleton] at hx; subst hx; decide)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- As `leafF`, with the words `ex` of the locals public too. -/
theorem leafX {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (ex : List Nat)
    (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ d ∈ ex, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∃ hc, (VG.Taint.check taint (τB (slx ex) rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (τB (slx ex) rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr, he⟩ := hag s₁ s₂ h
  refine agreeB T.hp₁ T.hp₂ T.pb w₁.inv w₂.inv _ rs hr (slotsOkX hex rs)
    (slots_of_words (ws := ws0 ++ ex) (fun d hd => ?_) fun x hx => ?_)
  · rcases List.mem_append.mp hd with hd | hd
    · exact T.words w₁ w₂ d hd
    · exact he d hd
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h0, hj⟩ := (show ∀ x ∈ sl0, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws0 by decide) x hx
      exact ⟨h0, fun j hj' => List.mem_append_left _ (hj j hj')⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      refine ⟨rfl, fun j hj => List.mem_append_right _ ?_⟩
      have := (hex d hd).1
      rw [show 4 * ((d + j) / 4) = d by simp only at hj; omega_using [hj, this]]
      exact hd

/-! ## The reference -/

/-- `refLane` leaks the same trace in two runs at the same position. -/
theorem refLane_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32}
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.X86.Derive.refLane fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.refLane
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => refLaneBlk_ok T.hp₁ h hpass hs) (fun s h => refLaneBlk_ok T.hp₂ h hpass hs) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.1, h₂.2.1])
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.fs.w, h.2.1.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (RelCT.nil fun _ _ _ => trivial)

/-- `reference` leaks the same trace in two runs at the same position. -/
theorem reference_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32}
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.X86.Derive.reference fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.reference
  refine RelCT.seqW (T.refLane_rel hpass hs)
    (fun s h => (refLane_ok T.hp₁ h hpass hs).mono fun t ht => ht.1)
    (fun s h => (refLane_ok T.hp₂ h hpass hs).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (refStart_ok T.hp₁ h hpass hs).mono fun t ht => ht.1)
    (fun s h => (refStart_ok T.hp₂ h hpass hs).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (countBase_ok T.hp₁ h hpass hs).mono fun t ht => h.of_keep ht.1)
    (fun s h => (countBase_ok T.hp₂ h hpass hs).mono fun t ht => h.of_keep ht.1) ?_
  exact T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## G and the new block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before `fillCompress`'s call of G. -/
theorem fcBlk_ok {s : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    {P R : Nat} (ha : s.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024))
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa (.block [.mov .esi (Impl.Argon2.X86.Derive.fr tmpOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm 4096)]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 ∧ t.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) ∧
      t.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
  refine wp_ldloc hp h.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_ldarg hp (h.inv.upd u₂ (by decide)
    (by decide)) (i := 15) (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => WP.block_nil
    ⟨(((h.inv.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)).upd u₄ (by decide)
      (by decide)).upd u₅ (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ha]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, htmp]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `fillCompress` leaks the same trace in two runs at the same position and
with the same reference block. -/
theorem fillCompress_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hl : lane < lanesN s₀₁)
    (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) {R : Nat} (hR : R < blocksN s₀₁) :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧
        lw s₀₁ s₁ tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024)) ∧
      (FS s₀₂ pass slice lane index ctr st₂ s₂ ∧ lw s₀₂ s₂ tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024)))
      Impl.Argon2.X86.Derive.fillCompress fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hR₂ : R < blocksN s₀₂ := T.pb.blocksN_eq ▸ hR
  have L8 := laneLen_ge T.hp₁
  obtain ⟨cl, _⟩ := cell_fits T.hp₁ hl (col := (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
    (prm s₀₁).laneLen) (Nat.mod_lt _ (by omega_using [L8]))
  have L8₂ := laneLen_ge T.hp₂
  obtain ⟨cl₂, _⟩ := cell_fits T.hp₂ hl₂ (col := (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
    (prm s₀₂).laneLen) (Nat.mod_lt _ (by omega_using [L8₂]))
  unfold Impl.Argon2.X86.Derive.fillCompress
  refine RelCT.seq (HPrime.rel_wp ((T.prevPointer_rel hs hi).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩)
      fun _ _ h => h)
    (G₁ := fun t => W s₀₁ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₁ + BitVec.ofNat 32
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024) ∧ lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024))
    (G₂ := fun t => W s₀₂ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₂ + BitVec.ofNat 32
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024) ∧ lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024))
    (fun s h => (prevPointer_ok T.hp₁ h.1.inv h.1.pr h.1.pos hl hs hi).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_keep k, a, by rw [lw_mem k.mem]; exact h.2⟩)
    (fun s h => (prevPointer_ok T.hp₂ h.1.inv h.1.pr h.1.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_keep k, a, by rw [lw_mem k.mem]; exact h.2⟩)) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fcBlk_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fcBlk_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine T.ccall_rel (o := 4096) (by decide) (by decide) fun s₁ s₂ ⟨i₁, d₁, c₁, a₁, e₁⟩ ⟨i₂, d₂, c₂, a₂, e₂⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inl ⟨_, cl, rfl⟩, by rw [e₁]; exact .inl ⟨R, hR, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inl ⟨_, cl₂, rfl⟩, by rw [e₂]; exact .inl ⟨R, hR₂, rfl⟩⟩,
     by rw [a₁, a₂, pe, T.pb.memP_eq], by rw [e₁, e₂, T.pb.memP_eq]⟩

/-- `fillWrite` leaks the same trace in two runs at the same position. -/
theorem fillWrite_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂) ∧
      lw s₀₁ s₁ curOff = lw s₀₂ s₂ curOff) Impl.Argon2.X86.Derive.fillWrite fun _ _ => True :=
  T.leafX [] [curOff] (by decide) (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.1.2.w⟩, by simp, by
    simp only [List.mem_singleton, forall_eq]; exact h.2⟩) ⟨_, by taint_decide⟩

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `fillBlock` leaks the same trace in two runs at the same position whose
reference blocks agree. -/
theorem fillBlock_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.fillBlock fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hb₁ : blocksN s₀₁ = (prm s₀₁).blocks := T.hp₁.blocks
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀₁) T.hp₁.lanes_pos T.hp₁.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) hl
  simp only at refLt
  generalize hR : (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).1 * (prm s₀₁).laneLen +
    (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).2 = R at refLt
  have hR₂ : (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).1 * (prm s₀₂).laneLen +
    (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).2 = R := by
    rw [← href, ← pe]; exact hR
  generalize hC : lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index) = C
  have hC₂ : lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index) = C := by rw [← pe]; exact hC
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine RelCT.seqW (T.randomSource_rel hpass hl hs hi)
    (fun s h => randomSource_ok T.hp₁ h hpass hl hs hi) (fun s h => randomSource_ok T.hp₂ h hpass hl₂ hs hi₂) ?_
  refine RelCT.seq (HPrime.rel_wp (G₁ := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G₂ := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₂) pass slice index ctr) st₂ t ∧
      lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    (RelCT.of_eq fun s₁ s₂ ⟨g₁, g₂⟩ => (T.reference_rel hpass hs (J1 := lw s₀₁ s₁ j1Off) (J2 := lw s₀₁ s₁ j2Off)
      (J1' := lw s₀₂ s₂ j1Off) (J2' := lw s₀₂ s₂ j2Off)).mono (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        rw [← pe] at g₂
        exact ⟨⟨g₁.1, rfl, rfl⟩, ⟨g₂.1, rfl, rfl⟩⟩) fun _ _ h => h)
    (fun s g => (reference_ok T.hp₁ ⟨g.1, rfl, rfl⟩ hpass hl hs hi active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR], by rw [cur, hC]⟩)
    (fun s g => (reference_ok T.hp₂ ⟨g.1, rfl, rfl⟩ hpass hl₂ hs hi₂ active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR₂], by rw [cur, hC₂]⟩)) ?_
  rw [show ctrNext (prm s₀₂) pass slice index ctr = ctrNext (prm s₀₁) pass slice index ctr by rw [pe]]
  refine RelCT.seq (HPrime.rel_wp (G₁ := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G₂ := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₂ t ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    ((T.fillCompress_rel hl hs hi (by rw [hb₁]; exact refLt)).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) fun _ _ h => h)
    (fun s g => (fillCompress_ok T.hp₁ g.1 hl hs hi (by rw [hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)
    (fun s g => (fillCompress_ok T.hp₂ g.1 hl₂ hs hi₂ (by rw [← T.pb.blocksN_eq, hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)) ?_
  exact T.fillWrite_rel.mono (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, by rw [h.1.2, h.2.2, T.pb.memP_eq]⟩) fun _ _ h => h

end Two

end VG.Proof.Argon2.X86.Derive

end

end

/-!
# Argon2 on x86 (32-bit): the filling loops, in two runs

The loops run in lockstep in two runs with the same public data: their
positions and counters agree, and so do the indices of the data-dependent
references still to be made (the rest of `Spec.Argon2.references`), from
which each block's reference agrees (`ref_same`). `passes_rel`: the filling
loops leak the same trace in two runs whose references agree.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- A block's reference, in two runs whose references from it on agree. -/
theorem ref_same (p : Spec.Argon2.Params) (pass lane slice i count : Nat) (X₁ X₂ : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (h : (Proof.Argon2.segment p pass lane slice i (count + 1) X₁).indices =
      (Proof.Argon2.segment p pass lane slice i (count + 1) X₂).indices) :
    Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₁.memory) =
      Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₂.memory) := by
  cases hind : Spec.Argon2.independent p pass slice
  · exact Proof.Argon2.segment_first_reference p pass lane slice i count X₁ X₂ active h hind
  · unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

/-- The words of the locals a lane's state fixes. -/
abbrev wsL : List Nat := [72, 76, 80, 92, 96, 100, 132]

theorem slotsOkL : VG.X86.Taint.SlotsOk (τB [(0, 72, 12), (0, 92, 12), (0, 132, 4)]) := by
  refine VG.X86.Taint.slotsOk_of_list rfl fun x hx => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem wordsL {st₁ st₂ : FillState} {pass slice lane : Nat} {s₁ s₂ : State}
    (h₁ : LS s₀₁ st₁ pass slice lane s₁) (h₂ : LS s₀₂ st₂ pass slice lane s₂) :
    ∀ d ∈ wsL, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [wsL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pass.trans h₂.pass.symm
  · exact h₁.lane.trans h₂.lane.symm
  · exact h₁.slice.trans h₂.slice.symm
  · exact (h₁.fb.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans
      h₂.fb.pr.laneLen.symm
  · exact (h₁.fb.pr.stride.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans h₂.fb.pr.stride.symm
  · exact (h₁.fb.pr.segLen.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans h₂.fb.pr.segLen.symm
  · exact (h₁.fb.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans
      h₂.fb.pr.divisor.symm

/-- `segmentStart` leaks the same trace in two runs at the same lane. -/
theorem segmentStart_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.X86.Derive.segmentStart fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.segmentStart
  refine RelCT.seq (T.leaf wsL [(0, 72, 12), (0, 92, 12), (0, 132, 4)] [] slotsOkL (by decide)
      (fun s₁ s₂ h₁ h₂ => ⟨h₁.fb.inv, h₂.fb.inv, T.wordsL h₁ h₂, by simp⟩) ⟨_, by taint_decide⟩
      (fun s h => segStartBlk_ok T.hp₁ h hpass hs) (fun s h => segStartBlk_ok T.hp₂ h hpass hs)) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.2, h₂.2.2])
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1.fb.inv, h.2.1.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1.fb.inv, h.2.1.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)

/-- A block of a segment and the index advanced, in two runs at the same
position whose reference blocks agree. -/
theorem segBody_rel {pass slice lane i c : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : i < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice i X₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice i X₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane i c X₁ s₁ ∧ FS s₀₂ pass slice lane i c X₂ s₂)
      (.seq Impl.Argon2.X86.Derive.fillBlock
        (.block (Impl.Argon2.X86.Derive.advance indexOff (Impl.Argon2.X86.Derive.fr segLenOff))))
      fun v₁ v₂ => (FS s₀₁ pass slice lane (i + 1) (ctrNext (prm s₀₁) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i X₁) v₁ ∧
          v₁.cf = some (decide (i + 1 < (prm s₀₁).segmentLen))) ∧
        (FS s₀₂ pass slice lane (i + 1) (ctrNext (prm s₀₂) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₂) pass slice lane i X₂) v₂ ∧
          v₂.cf = some (decide (i + 1 < (prm s₀₂).segmentLen))) := by
  have pe := T.pb.prm_eq
  have hi₂ : i < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  refine HPrime.rel_wp (RelCT.seqW (T.fillBlock_rel hpass hl hs hi active href)
    (fun s h => fillBlock_ok T.hp₁ h hpass hl hs hi active)
    (fun s h => fillBlock_ok T.hp₂ h hpass hl₂ hs hi₂ active)
    (T.leafF [] (fun s₁ s₂ h => by
      have h₂ := h.2
      rw [← pe] at h₂
      exact ⟨⟨_, _, _, _, _, h.1.w, h₂.w⟩, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => segStep_ok T.hp₁ h hpass hl hs hi active) (fun s h => segStep_ok T.hp₂ h hpass hl₂ hs hi₂ active)

/-- `segment` leaks the same trace in two runs at the same lane whose
references in it agree. -/
theorem segment_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : lane < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.X86.Derive.segment fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have s2 := T.hp₁.segLen_two
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega_arith
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, Proof.Argon2.segment_start _ _ _ _ _ s2] at hind
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2 hind
  generalize hL : (prm s₀₁).segmentLen = L at hind s2
  have hL₂ : (prm s₀₂).segmentLen = L := by rw [← pe, hL]
  unfold Impl.Argon2.X86.Derive.segment
  refine RelCT.seq (HPrime.rel_wp (T.segmentStart_rel hpass hs)
    (fun s h => segmentStart_ok T.hp₁ h hpass hs) (fun s h => segmentStart_ok T.hp₂ h hpass hs)) ?_
  rw [hSd]
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => segCmp_ok T.hp₁ h hS) (fun s h => segCmp_ok T.hp₂ h hS) ?_
  refine RelCT.ite (fun s₁ s₂ h => by
      show s₁.cf = s₂.cf
      rw [h.1.2, h.2.2, hL, hL₂]) ?_ ((RelCT.nil fun _ _ _ => trivial))
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ i, n = L - i ∧ S ≤ i ∧ i < L ∧ ∃ c,
      FS s₀₁ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁) s₁ ∧
      FS s₀₂ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂) s₂ ∧
      (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁)).indices =
        (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂)).indices) ?step (L - S)).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, e⟩ => ?init) fun _ _ h => h
  case init =>
    have hb : S < L := by
      rw [show isa.eval .b s₁ = s₁.cf from rfl, c₁, hL] at e
      simpa using e
    exact ⟨S, rfl, Nat.le_refl _, hb, 0, by rw [Nat.sub_self]; exact h₁, by rw [Nat.sub_self]; exact h₂,
      by rw [Nat.sub_self]; exact hind⟩
  case step =>
    intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hn, hSi, hi, c, h₁, h₂, hidx⟩ e₁ e₂
    have active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i := by
      by_cases a : pass = 0
      · by_cases b : slice = 0
        · have := hS2 a b; omega_arith
        · exact .inr (.inl b)
      · exact .inl a
    rw [show L - i = (L - (i + 1)) + 1 by omega_arith] at hidx
    have href := ref_same (prm s₀₁) pass lane slice i (L - (i + 1)) _ _ active hidx
    rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at hidx
    obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.segBody_rel (c := c) hpass hl hs (by rw [hL]; exact hi) active
      (by rw [← pe]; exact href) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
    rw [← pe] at g₂ c₂
    have eq₁ : ∀ X, Proof.Argon2.segment (prm s₀₁) pass lane slice S (i + 1 - S) X =
        Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) X) :=
      fun X => by rw [show i + 1 - S = (i - S) + 1 by omega_arith, segment_snoc, show S + (i - S) = i by omega_arith]
    rw [← eq₁] at g₁ g₂ hidx
    rw [← eq₁] at hidx
    rw [hL] at c₁ c₂
    refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
    have e : i + 1 < L := by
      rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
      simpa using hc
    exact ⟨L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, e, _, g₁, g₂, hidx⟩

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A lane's segment and the lane advanced, in two runs. -/
theorem laneBody_rel {pass slice l : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : l < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ X₁ pass slice l s₁ ∧ LS s₀₂ X₂ pass slice l s₂)
      (.seq Impl.Argon2.X86.Derive.segment
        (.block (Impl.Argon2.X86.Derive.advance laneOff (Impl.Argon2.X86.Derive.fr (argOff 7)))))
      fun v₁ v₂ => (LS s₀₁ (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁) pass slice
          (l + 1) v₁ ∧ v₁.cf = some (decide (l + 1 < lanesN s₀₁))) ∧
        (LS s₀₂ (Proof.Argon2.segment (prm s₀₂) pass l slice 0 (prm s₀₂).segmentLen X₂) pass slice (l + 1) v₂ ∧
          v₂.cf = some (decide (l + 1 < lanesN s₀₂))) := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  exact HPrime.rel_wp (RelCT.seqW (T.segment_rel hpass hs hl hind)
    (fun s h => segment_ok T.hp₁ h hpass hs hl) (fun s h => segment_ok T.hp₂ h hpass hs hl₂)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => laneStep_ok T.hp₁ h hpass hs hl) (fun s h => laneStep_ok T.hp₂ h hpass hs hl₂)

/-- `lanesLoop` leaks the same trace in two runs at the same slice whose
references in it agree. -/
theorem lanes_rel {pass slice : Nat} {Y₁ Y₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ Y₁ pass slice s₁ ∧ SS s₀₂ Y₂ pass slice s₂)
      Impl.Argon2.X86.Derive.lanesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.lanesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_ok T.hp₁ h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₁ Y₁ pass slice 0 t))
    (fun s h => (setLocal_ok T.hp₂ h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₂ Y₂ pass slice 0 t)) ?_
  generalize hN : lanesN s₀₁ = N at hind hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁) pass slice l s₁ ∧
      LS s₀₂ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂) pass slice l s₂ ∧
      (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁)).indices =
        (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_arith, hl1, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - l = (N - (l + 1)) + 1 by omega_arith] at hidx
  have hseg := Proof.Argon2.lanes_first_segment (prm s₀₁) pass slice l (N - (l + 1)) _ _ s2 hidx
  rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.laneBody_rel hpass hs (by rw [hN]; exact hl) hseg
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l X) = Proof.Argon2.lanes (prm s₀₁) pass slice 0 (l + 1) X :=
    fun X => by unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega_arith, l + 1, rfl, e, g₁, g₂, hidx⟩

/-- A slice's lanes and the slice advanced, in two runs. -/
theorem sliceBody_rel {pass j : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hj : j < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ X₁ pass j s₁ ∧ SS s₀₂ X₂ pass j s₂)
      (.seq Impl.Argon2.X86.Derive.lanesLoop (.block (Impl.Argon2.X86.Derive.advance sliceOff (.imm 4))))
      fun v₁ v₂ => (SS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁) pass (j + 1) v₁ ∧
          v₁.cf = some (decide (j + 1 < 4))) ∧
        (SS s₀₂ (Proof.Argon2.lanes (prm s₀₂) pass j 0 (lanesN s₀₂) X₂) pass (j + 1) v₂ ∧
          v₂.cf = some (decide (j + 1 < 4))) :=
  HPrime.rel_wp (RelCT.seqW (T.lanes_rel hpass hj hind)
    (fun s h => lanes_ok T.hp₁ h hpass hj) (fun s h => lanes_ok T.hp₂ h hpass hj)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => sliceStep_ok T.hp₁ h hpass hj) (fun s h => sliceStep_ok T.hp₂ h hpass hj)

/-- `slicesLoop` leaks the same trace in two runs at the same pass whose
references in it agree. -/
theorem slices_rel {pass : Nat} {Z₁ Z₂ : FillState} (hpass : pass < 2 ^ 32)
    (hind : (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₁).indices =
      (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₂).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ Z₁ pass s₁ ∧ PS s₀₂ Z₂ pass s₂)
      Impl.Argon2.X86.Derive.slicesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.slicesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_ok T.hp₁ h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₁ Z₁ pass 0 t))
    (fun s h => (setLocal_ok T.hp₂ h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₂ Z₂ pass 0 t)) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ j, n = 4 - j ∧ j < 4 ∧
      SS s₀₁ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁) pass j s₁ ∧
      SS s₀₂ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂) pass j s₂ ∧
      (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁)).indices =
        (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂)).indices)
    ?step 4).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, rfl, by decide, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, hn, hj, h₁, h₂, hidx⟩ e₁ e₂
  rw [show 4 - j = (3 - j) + 1 by omega_arith] at hidx
  have hl := Proof.Argon2.slices_first_lane_fold (prm s₀₁) pass j (3 - j) _ _ s2 hidx
  rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.sliceBody_rel hpass hj hl s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe, ← le] at g₂
  have eq : ∀ X, Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) (Proof.Argon2.slices (prm s₀₁) pass 0 j X) =
      Proof.Argon2.slices (prm s₀₁) pass 0 (j + 1) X :=
    fun X => by unfold Proof.Argon2.slices; rw [foldl_range'_snoc, Nat.zero_add]; rfl
  rw [eq] at g₁ g₂
  rw [show 3 - j = 4 - (j + 1) by omega_arith] at hidx
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : j + 1 < 4 := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  refine ⟨4 - (j + 1), by omega_arith, j + 1, rfl, e, g₁, g₂, ?_⟩
  rw [← eq, ← eq]
  exact hidx

/-- A pass and the pass advanced, in two runs. -/
theorem passBody_rel {k : Nat} {X₁ X₂ : FillState} (hk : k < itersN s₀₁)
    (hind : (Spec.Argon2.fillPass (prm s₀₁) X₁ k).indices = (Spec.Argon2.fillPass (prm s₀₁) X₂ k).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ X₁ k s₁ ∧ PS s₀₂ X₂ k s₂)
      (.seq Impl.Argon2.X86.Derive.slicesLoop
        (.block (Impl.Argon2.X86.Derive.advance passOff (Impl.Argon2.X86.Derive.fr (argOff 5)))))
      fun v₁ v₂ => (PS s₀₁ (Spec.Argon2.fillPass (prm s₀₁) X₁ k) (k + 1) v₁ ∧
          v₁.cf = some (decide (k + 1 < itersN s₀₁))) ∧
        (PS s₀₂ (Spec.Argon2.fillPass (prm s₀₂) X₂ k) (k + 1) v₂ ∧ v₂.cf = some (decide (k + 1 < itersN s₀₂))) := by
  have hk₂ : k < itersN s₀₂ := T.pb.itersN_eq ▸ hk
  have hpl : itersN s₀₁ < 2 ^ 32 := (arg s₀₁ 5).isLt
  rw [← Proof.Argon2.slices_pass, ← Proof.Argon2.slices_pass] at hind
  exact HPrime.rel_wp (RelCT.seqW (T.slices_rel (by omega_arith) hind)
    (fun s h => slices_ok T.hp₁ h (by omega_arith)) (fun s h => slices_ok T.hp₂ h (by omega_arith))
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => passStep_ok T.hp₁ h hk) (fun s h => passStep_ok T.hp₂ h hk₂)

/-- `passesLoop` leaks the same trace in two runs whose references agree. -/
theorem passes_rel {W₁ W₂ : FillState}
    (hind : (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₁).indices =
      (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₂).indices) :
    RelCT isa (fun s₁ s₂ => FB s₀₁ W₁ s₁ ∧ FB s₀₂ W₂ s₂) Impl.Argon2.X86.Derive.passesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have ie := T.pb.itersN_eq
  have hp1 := T.hp₁.passes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.passesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_ok T.hp₁ h (d := passOff) (by decide) (by decide) 0).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : PS s₀₁ W₁ 0 t))
    (fun s h => (setLocal_ok T.hp₂ h (d := passOff) (by decide) (by decide) 0).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : PS s₀₂ W₂ 0 t)) ?_
  generalize hN : itersN s₀₁ = N at hind hp1
  have hN₂ : itersN s₀₂ = N := by rw [← ie, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ k, n = N - k ∧ k < N ∧
      PS s₀₁ (Proof.Argon2.iterations (prm s₀₁) 0 k W₁) k s₁ ∧
      PS s₀₂ (Proof.Argon2.iterations (prm s₀₁) 0 k W₂) k s₂ ∧
      (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₁)).indices =
        (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_arith, by omega_arith, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hk, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - k = (N - (k + 1)) + 1 by omega_arith] at hidx
  have hpass := Proof.Argon2.iterations_first_pass (prm s₀₁) k (N - (k + 1)) _ _ s2 hidx
  rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.passBody_rel (by rw [hN]; exact hk) hpass s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Spec.Argon2.fillPass (prm s₀₁) (Proof.Argon2.iterations (prm s₀₁) 0 k X) k =
      Proof.Argon2.iterations (prm s₀₁) 0 (k + 1) X :=
    fun X => by unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : k + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (k + 1), by omega_arith, k + 1, rfl, e, g₁, g₂, hidx⟩

end Two

end VG.Proof.Argon2.X86.Derive

end

end

@[expose] public section

section

section

/-!
# Argon2 on x86 (32-bit): memory initialization, in two runs

`memoryInit_rel`: clearing the matrix and the calls of H′ for the first two
blocks of every lane leak the same trace in two runs with the same public
data: the calls' arguments are H₀'s place in the locals and the blocks'
addresses, which only the lane fixes.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_addi)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (argOff columnOff laneWordOff)

/-- The state before block `c` of lane `l`. -/
def IB (s₀ : State) (h0 : List Byte) (l c : Nat) (s : State) : Prop :=
  Inv s₀ s ∧ Prm s₀ s ∧ bytesAt s.mem ((E s₀).setWidth 64) 64 = h0 ∧ s.gpr .esi = BitVec.ofNat 32 l ∧
    s.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem initBlock_w {h0 : List Byte} {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2) {s : State}
    (h : IB s₀ h0 l c s) : WP isa (Impl.Argon2.X86.Derive.initBlock c) s (IB s₀ h0 l c) :=
  (initBlock_ok hp h.1 h.2.1 h.2.2.1 hl hc h.2.2.2.1 h.2.2.2.2).mono fun _ ⟨i, p, b, e, d, _, _⟩ =>
    ⟨i, p, b, e.trans h.2.2.2.1, d.trans h.2.2.2.2⟩

omit hp in
theorem nextBlock_w {h0 : List Byte} {l : Nat} {s : State} (h : IB s₀ h0 l 0 s) :
    WP isa (.block [.alu .add .edi (.imm 1024)]) s (IB s₀ h0 l 1) :=
  wp_addi fun t u => WP.block_nil ⟨h.1.upd u (by decide) (by decide), h.2.1.of_mem u.mem,
    by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1, by
      rw [u.gpr, h.2.2.2.2, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, show (l * (prm s₀).laneLen + 0) * 1024 + 1024 = (l * (prm s₀).laneLen + 1) * 1024 by
          rw [Nat.add_mul, Nat.add_mul]]⟩

/-- The instructions before `initBlock`'s call of H′. -/
theorem ibBlk_ok {s : State} (h : Inv s₀ s) (c : Nat) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 c)), .store (at_ .ebp columnOff) .eax,
      .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72), .mov .ecx (.imm 1024),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi := by
  refine wp_movi fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ _ _ g₂ _ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ _ _ g₃ _ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil
    ⟨((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide),
      u₆.gpr, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr],
      by rw [u₆.other _ (by decide), u₅.gpr],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃, g₂,
        u₁.other _ (by decide)]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `initBlock c` leaks the same trace in two runs at the same lane. -/
theorem initBlock_rel {h₁ h₂ : List Byte} {l c : Nat} (hl : l < lanesN s₀₁) (hc : c < 2)
    (hchk : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [.mov .eax (.imm (BitVec.ofNat 32 c)),
      .store (at_ .ebp columnOff) .eax, .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72),
      .mov .ecx (.imm 1024), .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => IB s₀₁ h₁ l c s₁ ∧ IB s₀₂ h₂ l c s₂) (Impl.Argon2.X86.Derive.initBlock c)
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have cellF : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ →
      (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 ∧ l * (prm s₀).laneLen + c < blocksN s₀ :=
    fun {s₀} hp hl => by
      have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_using [this]
      have : l * (prm s₀).laneLen + c < blocksN s₀ := by
        rw [hp.blocks_eq]
        have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_using [hl])
        rw [Nat.succ_mul] at this
        omega_using [hc, L2, this]
      exact ⟨by omega_using [this], this⟩
  have pre : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ → ∀ {s t : State}, IB s₀ h₁ l c s ∨ IB s₀ h₂ l c s →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧ t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, (t.gpr .ebp).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .eax).toNat ≤ R.len) ∧ (t.gpr .ebp).toNat + (t.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, (t.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .ecx).toNat ≤ R.len) ∧ (t.gpr .edi).toNat + (t.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .ecx).toNat := fun {s₀} hp hl {s t} hs ⟨i, d, a, c', e⟩ => by
    have hE := E_hi hp
    have hm := hp.mem_fits
    obtain ⟨hc', hk⟩ := cellF hp hl
    have ed : t.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024) := by
      rw [e]; rcases hs with hs | hs <;> exact hs.2.2.2.2
    have an : (memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)).toNat =
        (memP s₀).toNat + (l * (prm s₀).laneLen + c) * 1024 := add_nat (by omega_using [hm, hc'])
    refine ⟨i, d, ⟨locR s₀, by simp, 0, by rw [i.ebp]; simp, by rw [a]; show 0 + 72 ≤ 144; decide⟩,
      by rw [i.ebp, a]; show (E s₀).toNat + 72 ≤ 2 ^ 32; omega_using [hE],
      ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [ed, cell_addr hp hk]; rfl,
        by rw [c']; exact hc'⟩, by rw [ed, c', an]; show _ + 1024 ≤ 2 ^ 32; omega_using [hm, hc'],
      by rw [c']; decide⟩
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) hchk)
    (G₁ := fun t => ∃ s, IB s₀₁ h₁ l c s ∧ Inv s₀₁ t ∧ t.gpr .edx = scrP s₀₁ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (G₂ := fun t => ∃ s, IB s₀₂ h₂ l c s ∧ Inv s₀₂ t ∧ t.gpr .edx = scrP s₀₂ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (fun s h => (ibBlk_ok T.hp₁ h.1 c).mono fun t ht => ⟨s, h, ht⟩)
    (fun s h => (ibBlk_ok T.hp₂ h.1 c).mono fun t ht => ⟨s, h, ht⟩) ?_
  refine T.hcall_rel (r := .ebp) (by decide) fun s₁ s₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ =>
    ⟨pre T.hp₁ hl (.inl g₁) k₁, pre T.hp₂ (T.pb.lanesN_eq ▸ hl) (.inr g₂) k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.1.ebp, k₂.1.ebp, T.pb.E]
  · rw [k₁.2.2.1, k₂.2.2.1]
  · rw [k₁.2.2.2.2, k₂.2.2.2.2, g₁.2.2.2.2, g₂.2.2.2.2, pe, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]

/-- `initLane` leaks the same trace in two runs at the same lane. -/
theorem initLane_rel {h₁ h₂ : List Byte} {l : Nat} (hl : l < lanesN s₀₁) :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) Impl.Argon2.X86.Derive.initLane fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have ib : ∀ {s₀ s : State} {h0 : List Byte}, LI s₀ h0 l s → IB s₀ h0 l 0 s := fun h =>
    ⟨h.inv, h.pr, h.b0, h.esi, by rw [Nat.add_zero]; exact h.edi⟩
  unfold Impl.Argon2.X86.Derive.initLane
  refine (RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_).mono (fun _ _ h => ⟨ib h.1, ib h.2⟩) fun _ _ h => h
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => nextBlock_w h) (fun s h => nextBlock_w h) ?_
  refine RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `memoryInit` leaks the same trace in two runs. -/
theorem memoryInit_rel {h₁ h₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ bytesAt s₁.mem ((E s₀₁).setWidth 64) 64 = h₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ bytesAt s₂.mem ((E s₀₂).setWidth 64) 64 = h₂))
      Impl.Argon2.X86.Derive.memoryInit fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => laneStart_ok T.hp₁ h) (fun s h => laneStart_ok T.hp₂ h) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_using [], hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := HPrime.rel_wp (T.initLane_rel (by rw [hN]; exact hl))
    (fun s h => lane_ok T.hp₁ (by rw [hN]; exact hl) h) (fun s h => lane_ok T.hp₂ (by rw [hN₂]; exact hl) h)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega_using [hn, hl], l + 1, rfl, e, k₁, k₂⟩

end Two

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveX86.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = entry s₀₁) (F₂ := fun s => s = entry s₀₂)
    (RelCT.taint (A := taint) (τr [.esp]) (fun s₁ s₂ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2, entry_esp, entry_esp, T.pb.E]) (by taint_decide))
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.X86.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega_using [L8]) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)
    (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.X86.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t)
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  exact T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end Two

/-- A frame around code related from the pushed states. -/
theorem frame_chain {P : State → State → Prop} {f : State → State} {rs : List Reg} {r : Reg} {k : Nat}
    {body : Prog isa} {Q : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → (f s₁).gpr .esp = (f s₂).gpr .esp)
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs (f s₁) ∧ b = pushed rs (f s₂)) body Q) :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = f s₁ ∧ b = f s₂) (.frame (.push rs) body (.pop r k))
      fun _ _ => True :=
  RelCT.frame (fun a b ⟨s₁, s₂, hp, ha, hb⟩ => by subst ha hb; exact hsp s₁ s₂ hp)
    (h.mono (fun a b ⟨x, y, ⟨s₁, s₂, hp, hx, hy⟩, ha, hb⟩ => ⟨s₁, s₂, hp, by rw [ha, hx], by rw [hb, hy]⟩)
      fun _ _ h => h)

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveX86.pre s₁ ∧ deriveX86.pre s₂ ∧ deriveX86.pub s₁ s₂)
      Impl.Argon2.X86.Derive.derive fun _ _ => True := by
  have esp : ∀ s₁ s₂ : State, s₁.gpr .esp = s₂.gpr .esp → ∀ rs : List Reg,
      (pushed rs s₁).gpr .esp = (pushed rs s₂).gpr .esp := fun s₁ s₂ h rs => by
    rw [pushed_esp, pushed_esp, h]
  refine (frame_chain (f := id) (fun s₁ s₂ h => h.2.2.1.1) (frame_chain (f := fun s => pushed [.ebp] s)
    (fun s₁ s₂ h => esp _ _ h.2.2.1.1 _) (frame_chain (f := fun s => pushed [.edi] (pushed [.ebp] s))
    (fun s₁ s₂ h => esp _ _ (esp _ _ h.2.2.1.1 _) _)
    (frame_chain (f := fun s => pushed [.esi] (pushed [.edi] (pushed [.ebp] s)))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _)
    (frame_chain (Q := fun _ _ => True) (f := fun s => pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s))))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _) _) ?_))))).mono
    (fun s₁ s₂ h => ⟨s₁, s₂, h, rfl, rfl⟩) fun _ _ h => h
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, ha, hb⟩ e₁ e₂
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 a b t₁ t₂ a' b' ⟨ha, hb⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveX86.pre deriveX86.pub Impl.Argon2.X86.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is verified

`derive_verified`: the derivation against `deriveX86` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, which also lets the code write
its arguments, by narrowing (`deriveWide`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86

/-! ## A state satisfying the precondition -/

/-- The arguments: Argon2d, empty inputs, one pass over 8 KiB in one lane, a
4-byte tag. -/
def satArgs : List Nat := [0, 0, 0, 0, 0, 1, 8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satArgs` at `0x40004`. -/
def satMem (a : Addr) : Byte :=
  if 0x40004 ≤ a.toNat ∧ a.toNat < 0x4004C then
    ((BitVec.ofNat 32 (satArgs[(a.toNat - 0x40004) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40004) % 4))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .esp => 0x40000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40004, 72⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
  have e : argAddr satState 0 = 0x40004 := by decide
  have esp : satState.gpr .esp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, retR, stkR, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, E0, kindV, itersN, mcostN, lanesN, threadsN, prm,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, esp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
       rcases hw with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveX86 :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `deriveX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def deriveWide : Contract X86.isa :=
  { deriveX86 with
    pre := fun s =>
      let pw : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
      let salt : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let sec : Region := ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩
      let ad : Region := ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩
      let mem : Region := ⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨(arg s 15).setWidth 64, 16384⟩
      let out : Region := ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩
      let args : Region := ⟨argAddr s 0, 72⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩
      s.rd = [pw, salt, sec, ad] ∧ s.wr = [mem, scr, out, args] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      ret.Disjoint mem ∧ ret.Disjoint scr ∧ ret.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 32 ∧ 244 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 72 ≤ 2 ^ 32 ∧ (arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg s 8).toNat ∧ (arg s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat).blocks }

/-- A state satisfying `deriveWide.pre`. -/
def satWide : State where
  gpr := satState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩, ⟨0x40004, 72⟩]

theorem deriveWide_pre {s : State} (h : deriveWide.pre s) :
    DPre (s.withRegions [⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩]
      [⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩]) := by
  obtain ⟨_, _, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃, r₁, r₂, r₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, kd, vd, t₁, t₂, bl⟩ := h
  have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 244).setWidth 64, 244⟩ : Region) =
      ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ := by rw [Taint.sub_setWidth lo]; rfl
  refine
    { rd := rfl
      wr := rfl
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      ret_w := ?_
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      esp_lo := lo
      esp_hi := (by show (s.gpr .esp).toNat + 76 ≤ 2 ^ 32; omega_using [hi])
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · show ∀ r ∈ [(⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ : Region), ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
        ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩],
      ∀ w ∈ [(⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩ : Region), ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], r.Disjoint w
    intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ w ∈ [(⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩ : Region), ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint w
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ r ∈ [(⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ : Region), ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
        ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩,
        ⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], (below (s.gpr .esp) 244).Disjoint r
    rw [show below (s.gpr .esp) 244 = ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ from e]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem deriveWide_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveWide :=
  Verified.narrowTo derive_verified
    (fun s => [⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩])
    (fun s => [⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
      ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩])
    (fun _ h => deriveWide_pre h)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩)
    (fun _ _ _ h => by
      simp only [deriveX86, deriveWide, VG.X86.arg_withRegions, State.withRegions_mem] at h ⊢
      exact h)
    (fun _ _ _ _ h => by
      simp only [deriveX86, VG.X86.arg_withRegions, State.withRegions_gpr]
      exact h)
    ⟨satWide, by
      have a : ∀ i < 18, arg satWide i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
      have e : argAddr satWide 0 = 0x40004 := by decide
      simp only [deriveWide, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem derive_implies : deriveWide.Implies (Spec.Argon2.deriveContract X86.abi 244) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveWide, deriveX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [satWide, satState, satMem, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using satWide

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified X86.target Impl.Argon2.X86.Derive.derive (Spec.Argon2.deriveContract X86.abi 244) :=
  deriveWide_verified.of_implies derive_implies

end VG.Proof.Argon2.X86.Derive
