module

public import VerifiedGarbage.Proof.Modes.Arm.Seq
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# The modes one block at a time on ARMv7: one block

`body_ok`: one run of `Core.body c M`, on block `k`, takes the invariant
from `k` blocks to `k + 1`, and sets Z when no blocks are left. The data
block `k`, the chaining block and the spare block are `Blks` in memory
(`BlkMem`) throughout: the operations before the call (`opsCode_wp`), the
call of the core on the mode's block (`call_wp`), the operations after it,
and the step to the next block. Block `k` is then `stepOf`'s data block,
and the others are unchanged.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_subs op2_imm op2_reg ofNat_beq_zero)

/-- A mode whose operations are each on two different blocks (and, a byte
at a time, do not treat the data byte as a block), and which calls the
cipher on a whole block at an encodable offset. -/
structure ModeOk (c : Core) (M : Mode) : Prop where
  pre : M.pre.all (opOk c.bs M.byte) = true
  post : M.post.all (opOk c.bs M.byte) = true
  tgt : M.byte = true → M.tgt ≠ .d
  tgt_enc : encodable (BitVec.ofNat 32 (c.base M.tgt).2) = true

theorem ds_of (c : Core) {M : Mode} (h : M.byte = false) : c.ds M = c.bs := by simp [Core.ds, h]

/-- The call's block is a whole block. -/
theorem ModeOk.tgt_sz {c : Core} {M : Mode} (hM : ModeOk c M) : sz c (c.ds M) M.tgt = c.bs := by
  cases ht : M.tgt
  · cases hb : M.byte
    · simp [sz, ds_of c hb]
    · exact absurd ht (hM.tgt hb)
  · rfl
  · rfl

/-! ## Blocks in memory -/

theorem length_blocksOf (L : Nat) (m : Mem) (p : Addr) (n : Nat) : (blocksOf L m p n).length = n := by
  simp [blocksOf, VG.Proof.Modes.blocksOf]

theorem getElem_blocksOf (L : Nat) (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (blocksOf L m p n)[k]'(by rw [length_blocksOf]; exact hk) = bytesAt m (p + BitVec.ofNat 64 (L * k)) L := by
  simp [blocksOf, VG.Proof.Modes.blocksOf]

/-- The blocks after one of them changed. -/
theorem blocksOf_set {L : Nat} {m m' : Mem} {p : Addr} {n k : Nat}
    (h : ∀ j < n, j ≠ k →
      bytesAt m' (p + BitVec.ofNat 64 (L * j)) L = bytesAt m (p + BitVec.ofNat 64 (L * j)) L) :
    blocksOf L m' p n = (blocksOf L m p n).set k (bytesAt m' (p + BitVec.ofNat 64 (L * k)) L) := by
  apply List.ext_getElem (by simp [length_blocksOf])
  intro j h₁ h₂
  rw [length_blocksOf] at h₁
  rw [List.getElem_set, getElem_blocksOf _ _ _ h₁]
  by_cases hj : k = j
  · subst hj; simp
  · simp only [hj, ↓reduceIte]; rw [getElem_blocksOf _ _ _ h₁, h j h₁ (Ne.symm hj)]

/-- The first `k` blocks transformed and the rest not, with block `k`
replaced. -/
theorem set_prefix {α : Type} (ys xs : List α) (x : α) {k : Nat} (hy : ys.length = k) (hk : k < xs.length) :
    (ys ++ xs.drop k).set k x = (ys ++ [x]) ++ xs.drop (k + 1) := by
  subst hy
  rw [List.set_append_right _ _ (by omega_arith), Nat.sub_self, List.append_assoc]
  congr 1
  rw [List.drop_eq_getElem_cons hk, List.set_cons_zero]
  rfl

/-! ## Block `k` -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
theorem idx_lt' {L k n : Nat} (hk : k < n) : L * k + L ≤ n * L := by
  rw [Nat.mul_comm n]; exact VG.Proof.Modes.idx_lt hk

/-- The address of block `k`, in 32 bits. -/
abbrev Dk (s₀ : State) (c : Core) (M : Mode) (k : Nat) : BitVec 32 := Dp c s₀ + BitVec.ofNat 32 (c.ds M * k)

theorem UPre.dk_toNat {k : Nat} (hk : k < N c s₀) : (Dk s₀ c M k).toNat = (Dp c s₀).toNat + c.ds M * k := by
  have := hp.fD
  have := idx_lt' (L := c.ds M) hk
  have := S.ds_pos M
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.ds M * k) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem UPre.dk_addr {k : Nat} (hk : k < N c s₀) :
    State.addr (Dk s₀ c M k) = State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * k) := by
  have := hp.fD
  have := idx_lt' (L := c.ds M) hk
  exact addr_add (by have := S.ds_pos M; omega_arith)

theorem UPre.blk_sub_data {k : Nat} (hk : k < N c s₀) :
    Region.Sub ⟨State.addr (Dk s₀ c M k), c.ds M⟩ (dataR c s₀ M) := by
  rw [hp.dk_addr hk]
  exact VG.Offset.sub_base _ (by have := idx_lt' (L := c.ds M) hk; omega_arith)

theorem UPre.lay {k : Nat} (hk : k < N c s₀) : Lay c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s₀.wr := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  refine ⟨S.bw_pos, S.bw_le, S.ds_pos M, S.ds_le M, ?_, by omega_arith, ?_, ?_, ?_⟩
  · rw [hp.dk_toNat hk]
    have := hp.fD; have := idx_lt' (L := c.ds M) hk; omega_arith
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨dataR c s₀ M, hp.data_in, c.ds M * k, hp.dk_addr hk, ?_⟩
      have := idx_lt' (L := c.ds M) hk; show _ ≤ N c s₀ * c.ds M; omega_arith
  · exact cov_off (R := scrR c s₀) hp.scr_in (by show oOff + 2 * c.bs ≤ c.scratchBytes; omega_arith)
  · exact (hp.data_scr.sub_left (hp.blk_sub_data hk)).sub_right UPre.blk2_sub

/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {k : Nat} {s : State} (h : LInv c S M s₀ k s) (hk : k < N c s₀) :
    bytesAt s.mem (State.addr (Dk s₀ c M k)) (c.ds M) = (xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk) := by
  have hl : (rK S s₀ M k).1.length = k := by
    rw [runSeq_length, List.length_take, length_blocksOf]; omega_arith
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀)).length by
      rw [length_blocksOf]; exact hk),
    List.getElem?_append_right (show (rK S s₀ M k).1.length ≤ k by omega_arith), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (xs c s₀ M).length by rw [length_blocksOf]; exact hk)] at this
  rw [hp.dk_addr hk, ← getElem_blocksOf _ _ _ hk]
  exact Option.some.inj this

/-- The blocks of the step, in memory. -/
theorem LInv.blkMem {k : Nat} {s : State} (h : LInv c S M s₀ k s) (hk : k < N c s₀) :
    BlkMem c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s.mem
      ((rK S s₀ M k).2.set .d ((xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk))) := by
  intro x
  cases x
  · exact h.block hp hk
  · exact h.o
  · exact h.t

end

/-! ## The callee's working space -/

/-- The address of the callee's working space, at the end of the scratch
buffer. -/
abbrev Cs (c : Core) (s₀ : State) : BitVec 32 := Sc c s₀ + BitVec.ofNat 32 c.csOff

/-- The callee's working space. -/
abbrev csR (c : Core) (s₀ : State) : Region := ⟨State.addr (Cs c s₀), c.stackScratch⟩

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

theorem UPre.cs_toNat (hs : c.stackScratch ≠ 0) : (Cs c s₀).toNat = (Sc c s₀).toNat + c.csOff := by
  have := hp.fS; unfold Core.scratchBytes at this
  have := S.bw_le
  have e : c.csOff = oOff + 2 * c.bs := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.csOff) (by rw [e]; unfold oOff at *; omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem UPre.cs_addr (hs : c.stackScratch ≠ 0) :
    State.addr (Cs c s₀) = State.addr (Sc c s₀) + BitVec.ofNat 64 c.csOff := by
  have := hp.fS; unfold Core.scratchBytes at this
  exact addr_add (by omega_arith)

theorem UPre.cs_fit (hs : c.stackScratch ≠ 0) : (Cs c s₀).toNat + c.stackScratch ≤ 2 ^ 32 := by
  have := hp.fS; unfold Core.scratchBytes at this; rw [hp.cs_toNat hs]; omega_arith

omit hp in
theorem csR_empty (hs : c.stackScratch = 0) (a : Addr) : ¬ (csR c s₀).Contains a 1 := by
  simp only [Region.Contains, hs]; omega_arith

theorem UPre.cs_sub_scr : Region.Sub (csR c s₀) (scrR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a h => absurd h (csR_empty hs a)
  show Region.Sub ⟨State.addr (Cs c s₀), _⟩ _
  rw [hp.cs_addr hs]; exact VG.Offset.sub_base _ (by unfold Core.scratchBytes; omega_arith)

theorem UPre.cs_sub_blk : Region.Sub (csR c s₀) (blkR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a h => absurd h (csR_empty hs a)
  show Region.Sub ⟨State.addr (Cs c s₀), _⟩ _
  rw [hp.cs_addr hs]; exact VG.Offset.sub _ (by unfold Core.csOff; omega_arith) (by unfold Core.csOff; omega_arith)

/-- The blocks of a step are apart from the callee's working space. -/
theorem UPre.blk_cs {k : Nat} (hk : k < N c s₀) (x : Blk) :
    Region.Disjoint ⟨addrOf c (Dk s₀ c M k) (Sc c s₀) x, sz c (c.ds M) x⟩ (csR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a _ h => csR_empty hs a h
  have hS := hp.fS; unfold Core.scratchBytes at hS
  have hcs : c.csOff = oOff + 2 * c.bs := rfl
  cases x
  · exact (hp.data_scr.sub_left (hp.blk_sub_data hk)).sub_right hp.cs_sub_scr
  · show Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 oOff, c.bs⟩ ⟨State.addr (Cs c s₀), _⟩
    rw [hp.cs_addr hs]; exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · show Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ ⟨State.addr (Cs c s₀), _⟩
    rw [hp.cs_addr hs]; exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

end

theorem scrArg_wp {c : Core} (S : CoreSpec c) {s : State} {Sb : BitVec 32} {Q : State → Prop}
    (h8 : s.gpr .r8 = Sb)
    (hQ : ∀ s', (∀ x, x ≠ .r12 → s'.gpr x = s.gpr x) →
      (c.stackScratch ≠ 0 → s'.gpr .r12 = Sb + BitVec.ofNat 32 c.csOff) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.mem = s.mem → Q s') :
    WP isa (.block c.scrArg) s Q := by
  unfold Core.scrArg
  split
  · exact WP.block_nil (hQ s (fun _ _ => rfl) (fun h => absurd ‹_› h) rfl rfl rfl rfl)
  · exact wp_add (op2_imm (S.cs_enc ‹_›)) fun s' u => WP.block_nil
      (hQ s' u.other (fun _ => by rw [u.gpr, h8]) u.rd u.wr u.sp u.mem)

/-- The constant argument to `r3`, if the core takes one. -/
theorem arg3_wp {c : Core} (S : CoreSpec c) {s : State} {Q : State → Prop}
    (hQ : ∀ s', (∀ x, x ≠ .r3 → s'.gpr x = s.gpr x) → (c.arg3 = none → s'.gpr .r3 = s.gpr .r3) →
      (∀ k, c.arg3 = some k → s'.gpr .r3 = BitVec.ofNat 32 k) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.mem = s.mem → Q s') :
    WP isa (.block c.arg3Code) s Q := by
  unfold Core.arg3Code
  split
  · rename_i k hk
    exact wp_mov (op2_imm (S.arg3_enc k hk)) fun s' u => WP.block_nil
      (hQ s' u.other (fun h => by rw [hk] at h; cases h)
        (fun k' h => by rw [hk] at h; cases h; exact u.gpr) u.rd u.wr u.sp u.mem)
  · rename_i hk
    exact WP.block_nil (hQ s (fun _ _ => rfl) (fun _ => rfl) (fun k h => by rw [hk] at h; cases h) rfl rfl rfl rfl)

/-! ## The call's block -/

/-- The address of block `x` in 32 bits, with the data block at `D` and the
scratch buffer at `Sb`. -/
def bt (c : Core) (D Sb : BitVec 32) : Blk → BitVec 32
  | .d => D + BitVec.ofNat 32 (c.base .d).2
  | .o => Sb + BitVec.ofNat 32 (c.base .o).2
  | .t => Sb + BitVec.ofNat 32 (c.base .t).2

theorem bt_eq {c : Core} {D Sb : BitVec 32} {s : State} (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = Sb) (x : Blk) :
    s.gpr (c.base x).1 + BitVec.ofNat 32 (c.base x).2 = bt c D Sb x := by
  cases x <;> simp [Core.base, bt, h6, h8]

theorem Lay.bt_addr {c : Core} {ds : Nat} {D Sb : BitVec 32} {wr : List Region} (h : Lay c ds D Sb wr) (x : Blk) :
    State.addr (bt c D Sb x) = addrOf c D Sb x := by
  have := h.fD; have := h.fS; have := h.bw
  have hb : c.bs = 4 * c.bw := rfl
  cases x
  · simp [bt, Core.base, addrOf]
  · simp only [bt, Core.base, addrOf]; exact addr_add (by omega_arith)
  · simp only [bt, Core.base, addrOf]; exact addr_add (by omega_arith)

theorem Lay.bt_fit {c : Core} {ds : Nat} {D Sb : BitVec 32} {wr : List Region} (h : Lay c ds D Sb wr) (x : Blk) :
    (bt c D Sb x).toNat + sz c ds x ≤ 2 ^ 32 := by
  have := h.fD; have := h.fS
  have e : ∀ (a : BitVec 32) (d : Nat), a.toNat + d < 2 ^ 32 → (a + BitVec.ofNat 32 d).toNat = a.toNat + d :=
    fun a d hd => by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
      Nat.mod_eq_of_lt hd]
  have := h.bw
  have hb : c.bs = 4 * c.bw := rfl
  cases x
  · simp only [bt, Core.base]; rw [e _ _ (by omega_arith)]; simp only [sz]; omega_arith
  · simp only [bt, Core.base]; rw [e _ _ (by omega_arith)]; simp only [sz]; omega_arith
  · simp only [bt, Core.base]; rw [e _ _ (by omega_arith)]; simp only [sz]; omega_arith

/-! ## One block -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

/-- The memory since entry, for the cipher's schedule. -/
theorem UPre.frame_entry {m₁ m₂ : Mem} {k : Nat} (hk : k < N c s₀)
    (h₁ : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) m₁)
    (h₂ : Frame (blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀)) m₁ m₂) :
    Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem m₂ := by
  have f₀ : Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem (savedMem c s₀) :=
    (UPre.savedMem_frame (c := c) (s₀ := s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR c s₀, .tail _ (.head _), UPre.slots_sub⟩
  refine f₀.trans ((h₁.sub fun r hr => ?_).trans (h₂.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, fun _ h => h⟩
    · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk_sub⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), fun _ h => h⟩
  · simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, .head _, hp.blk_sub_data hk⟩
    · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk2_sub⟩

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (b : Blks) (s s₂ : State) : Prop where
  regs : ∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r9 → x ≠ .r10 → x ≠ .r12 → s₂.gpr x = s.gpr x
  r0 : s₂.gpr .r0 = Kp s₀
  r1 : c.rounds = true → s₂.gpr .r1 = Rp s₀
  rD : s₂.gpr c.dReg = bt c (Dk s₀ c M k) (Sc c s₀) M.tgt
  rN : s₂.gpr c.nReg = 1
  a3 : ∀ k, c.arg3 = some k → s₂.gpr .r3 = BitVec.ofNat 32 k
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  frame : Frame (blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀)) s.mem s₂.mem
  blks : BlkMem c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s₂.mem b
  r12 : c.stackScratch ≠ 0 → s₂.gpr .r12 = Cs c s₀

theorem pre_wp (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {s : State} (h : LInv c S M s₀ k s) :
    WP isa (.block (c.opsCode M.pre ++ c.callArgs M.tgt)) s
      (PreA (c := c) (M := M) s₀ k (runOps M.pre ((rK S s₀ M k).2.set .d
        ((xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk)))) s) := by
  have hb := h.blkMem hp hk
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (ds_of c) (h.wr ▸ hp.lay hk) h.r6 h.r8 hb hM.pre) fun s₁ h₁ => ?_
  have h4 : s₁.gpr .r4 = Kp s₀ := by rw [h₁.regs _ (by decide) (by decide), h.r4]
  have hbt : s₁.gpr (c.base M.tgt).1 + BitVec.ofNat 32 (c.base M.tgt).2 = bt c (Dk s₀ c M k) (Sc c s₀) M.tgt :=
    bt_eq (by rw [h₁.regs _ (by decide) (by decide), h.r6]) (by rw [h₁.regs _ (by decide) (by decide), h.r8]) _
  have enc := hM.tgt_enc
  have hne : (c.base M.tgt).1 ≠ .r0 ∧ (c.base M.tgt).1 ≠ .r1 := by cases M.tgt <;> simp [Core.base]
  simp only [Core.callArgs, mov]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  have h11 : c.rounds = true → s₂.gpr .r11 = Rp s₀ := fun hr => by
    rw [u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), h.r11 hr]
  have bt₂ : s₂.gpr (c.base M.tgt).1 + BitVec.ofNat 32 (c.base M.tgt).2 = bt c (Dk s₀ c M k) (Sc c s₀) M.tgt := by
    rw [u₂.other _ hne.1, hbt]
  cases hr : c.rounds
  · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
    have hN : c.nReg = .r2 := by unfold Core.nReg; rw [hr]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, hD, hN]
    refine wp_add (op2_imm enc) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
      WP.block_append_iff.2 (arg3_wp S fun s₄' g₄ _ a₄ rd₄ wr₄ sp₄ m₄ => scrArg_wp S
      (by rw [g₄ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        h₁.regs _ (by decide) (by decide), h.r8]) fun s₅ g₅ c₅ rd₅ wr₅ sp₅ m₅ =>
      ⟨fun x a b d e f g i => ?_, ?_, fun h => absurd h (by simp [hr]), ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_,
        ?_, c₅⟩)
    · rw [g₅ _ i, g₄ _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a, h₁.regs _ f g]
    · rw [g₅ _ (by decide), g₄ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h4]
    · rw [hD, g₅ _ (by decide), g₄ _ (by decide), u₄.other _ (by decide), u₃.gpr, bt₂]
    · rw [hN, g₅ _ (by decide), g₄ _ (by decide), u₄.gpr]
    · rw [g₅ _ (by decide), a₄ k hk]
    · rw [rd₅, rd₄, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
    · rw [wr₅, wr₄, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
    · rw [sp₅, sp₄, u₄.sp, u₃.sp, u₂.sp, h₁.sp]
    · rw [m₅, m₄, u₄.mem, u₃.mem, u₂.mem]; exact h₁.frame
    · rw [m₅, m₄, u₄.mem, u₃.mem, u₂.mem]; exact h₁.blks
  · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
    have hN : c.nReg = .r3 := by unfold Core.nReg; rw [hr]; rfl
    have hn3 : c.arg3 = none := by
      cases h3 : c.arg3
      · rfl
      · have := S.arg3_rounds (by rw [h3]; rfl); rw [hr] at this; cases this
    simp only [↓reduceIte, List.cons_append, List.nil_append, hD, hN]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_add (op2_imm enc) fun s₄ u₄ => wp_mov (op2_imm (by decide))
      fun s₅ u₅ => WP.block_append_iff.2 (arg3_wp S fun s₅' g₅' n₅ _ rd₅' wr₅' sp₅' m₅' => scrArg_wp S
      (by rw [g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), h.r8]) fun s₆ g₆ c₆ rd₆ wr₆ sp₆ m₆ =>
      ⟨fun x a b d e f g i => ?_, ?_, fun _ => ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, c₆⟩)
    · rw [g₆ _ i, g₅' _ e, u₅.other _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a, h₁.regs _ f g]
    · rw [g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, h4]
    · rw [g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, h11 hr]
    · rw [hD, g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ hne.2, bt₂]
    · rw [hN, g₆ _ (by decide), n₅ hn3, u₅.gpr]
    · rw [hn3] at hk; cases hk
    · rw [rd₆, rd₅', u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
    · rw [wr₆, wr₅', u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
    · rw [sp₆, sp₅', u₅.sp, u₄.sp, u₃.sp, u₂.sp, h₁.sp]
    · rw [m₆, m₅', u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact h₁.frame
    · rw [m₆, m₅', u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact h₁.blks


/-- A region apart from the data and the scratch buffer is apart from the
blocks of a step. -/
theorem UPre.disj_blks {k : Nat} (hk : k < N c s₀) {R : Region} (hd : R.Disjoint (dataR c s₀ M))
    (hs : R.Disjoint (scrR c s₀)) (x : Blk) :
    R.Disjoint ⟨addrOf c (Dk s₀ c M k) (Sc c s₀) x, sz c (c.ds M) x⟩ := by
  obtain ⟨r, hr, hsub⟩ := Lay.sub (c := c) (ds := c.ds M) (Dp := Dk s₀ c M k) (S := Sc c s₀) x
  refine Region.Disjoint.sub_right ?_ hsub
  simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hd.sub_right (hp.blk_sub_data hk)
  · exact hs.sub_right UPre.blk2_sub

/-- The call's arguments make its precondition. -/
theorem PreA.callPre (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {b : Blks} {s s₂ : State}
    (h : LInv c S M s₀ k s) (a : PreA (c := c) (M := M) s₀ k b s s₂) (hsy : s₂.syms = s₀.syms) :
    CallPre c S s₂ (Kp s₀) (Rp s₀) (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt) (Cs c s₀) := by
  have hL := hp.lay hk
  have sp : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  have ts := hM.tgt_sz
  have et : tabRegs S.consts s₂ = tabRegs S.consts s₀ := by simp only [tabRegs, hsy]
  have tw := hp.tabs.2.1
  refine ⟨a.r0, a.r1, hp.rok, a.rD, a.rN, a.a3, by rw [sp]; exact hp.stk, hp.fK, ts ▸ hL.bt_fit _, ?_, ?_, ?_, ?_, ?_,
    a.r12, hp.cs_fit, hp.key_scr.sub_right hp.cs_sub_scr, ?_, by rw [sp]; exact hp.b_scr.sub_right hp.cs_sub_scr,
    fun hs => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.bt_addr, ← ts]; exact hp.disj_blks hk hp.key_data hp.key_scr _
  · rw [sp]; exact hp.b_key
  · rw [sp, hL.bt_addr, ← ts]; exact hp.disj_blks hk hp.b_data hp.b_scr _
  · rw [a.rd, a.wr, h.rd, h.wr]; exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.key_in
  · rw [a.wr, h.wr, hL.bt_addr, ← ts]; exact hL.writable _
  · rw [hL.bt_addr, ← ts]; exact hp.blk_cs hk _
  · rw [a.wr, h.wr]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := hp.fS; unfold Core.scratchBytes at this
      exact ⟨_, hp.scr_in, c.csOff, hp.cs_addr hs, by show c.csOff + c.stackScratch ≤ c.scratchBytes; rfl⟩
  · rw [et, a.rd, h.rd]; exact fun t ht => (tw t ht).1
  · have e2 : (fun n => State.addr (s₂.syms n)) = fun n => State.addr (s₀.syms n) := by rw [hsy]
    rw [e2]
    refine held_frame (hp.frame_entry hk h.frame a.frame) (fun t ht r hr => ?_) (fun t ht => ?_) hp.tabs.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (tw t ht).2.2.1 _ hp.data_in
      · exact (tw t ht).2.2.1 _ hp.scr_in
      · exact (tw t ht).2.2.2
    · have := (tw t ht).2.1; omega_arith
  · rw [et]; exact fun t ht => (tw t ht).2.1
  · rw [et]; intro t ht
    rw [hL.bt_addr, ← ts]
    exact hp.disj_blks hk ((tw t ht).2.2.1 _ hp.data_in) ((tw t ht).2.2.1 _ hp.scr_in) _
  · rw [et]; exact fun t ht => ((tw t ht).2.2.1 _ hp.scr_in).sub_right hp.cs_sub_scr
  · rw [et, sp]; exact fun t ht => (tw t ht).2.2.2
  · rw [et]; exact hp.tabs.2.2

/-- The blocks after the call. -/
theorem call_blks (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {b : Blks} {s s₂ s₃ : State}
    (h : LInv c S M s₀ k s) (a : PreA (c := c) (M := M) s₀ k b s s₂)
    (cp : CallPost c S s₂ (Kp s₀) (Rp s₀) (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt) (Cs c s₀) s₃) :
    BlkMem c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s₃.mem (b.set M.tgt (ciph S s₀ (b.get M.tgt))) := by
  have hL := hp.lay hk
  have sp : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith
  intro x
  by_cases hx : x = M.tgt
  · subst hx
    rw [Blks.get_set_self, hM.tgt_sz, ← hL.bt_addr, cp.out, hL.bt_addr, ← hM.tgt_sz, a.blks M.tgt,
      hp.ciph_eq (hp.frame_entry hk h.frame a.frame)]
  · rw [Blks.get_set_of_ne _ _ hx, ← a.blks x]
    refine VG.Proof.Modes.bytesAt_frame cp.frame (fun r hr => ?_) (by have := hL.sz_le x; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hL.bt_addr, ← hM.tgt_sz]; exact hL.disjoint hx
    · exact hp.blk_cs hk x
    · rw [sp]; exact (hp.disj_blks hk hp.b_data hp.b_scr x).symm

end

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
theorem take_succ_xs {k : Nat} (hk : k < N c s₀) :
    (xs c s₀ M).take (k + 1) = (xs c s₀ M).take k ++ [(xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_blocksOf]; exact hk)]
  rfl

/-- The regions a step may change, within those the invariant allows. -/
theorem UPre.step_sub {k : Nat} (hk : k < N c s₀) :
    ∀ r ∈ blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀), ∃ r' ∈ [dataR c s₀ M, blkR c s₀, belowR S s₀], Region.Sub r r' := by
  intro r hr
  simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, .head _, hp.blk_sub_data hk⟩
  · exact ⟨_, .tail _ (.head _), Region.sub_prefix (by omega_arith)⟩

theorem body_ok (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {s : State} (h : LInv c S M s₀ k s)
    (hsy : s.syms = s₀.syms) :
    WP isa (c.body M) s fun s' => LInv c S M s₀ (k + 1) s' ∧ s'.z = decide (N c s₀ - (k + 1) = 0) := by
  have hL := hp.lay hk
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith
  refine WP.seq (VG.Arm.WP.mono_syms (pre_wp hp hM hk h) fun s₂ a sy₂ => ?_)
  refine WP.seq (WP.mono (call_wp S (a.callPre hp hM hk h (sy₂.trans hsy))) fun s₃ cp => ?_)
  have hb₂ := call_blks hp hM hk h a cp
  have g₃ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h9 h10
      (by rintro rfl; simp [preserved] at hr)]
  have r6 : s₃.gpr .r6 = Dk s₀ c M k := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r6]
  have r8 : s₃.gpr .r8 = Sc c s₀ := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r8]
  have wr₃ : s₃.wr = s₀.wr := by rw [cp.wr, a.wr, h.wr]
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (ds_of c) (wr₃ ▸ hL) r6 r8 hb₂ hM.post) fun s₄ h₄ => ?_
  -- The memory the step changed: block `k`, the chaining and spare blocks, the stack.
  have sp₂ : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  have fstep : Frame (blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀) ++ [csR c s₀, belowR S s₀]) s.mem s₄.mem := by
    refine ((a.frame.mono fun r hr => List.mem_append_left _ hr).trans (cp.frame.sub fun r hr => ?_)).trans
      (h₄.frame.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hL.bt_addr]
      obtain ⟨r', hr', hs'⟩ := Lay.sub (c := c) (ds := c.ds M) (Dp := Dk s₀ c M k) (S := Sc c s₀) M.tgt
      exact ⟨r', List.mem_append_left _ hr', hM.tgt_sz ▸ hs'⟩
    · exact ⟨csR c s₀, by simp, fun _ h => h⟩
    · exact ⟨belowR S s₀, by simp, by rw [sp₂]; exact fun _ h => h⟩
  have r6' : s₄.gpr .r6 = Dk s₀ c M k := by rw [h₄.regs _ (by decide) (by decide), r6]
  have r7 : s₄.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k) := by
    rw [h₄.regs _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide), h.r7]
  simp only [Core.advance]
  refine wp_add (op2_imm (S.ds_enc M)) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, fun hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [u₆.other _ (by decide), u₅.gpr, r6', Dk, VG.Offset.add_add, Nat.mul_succ]
  · rw [u₆.gpr, u₅.other _ (by decide), r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide), r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r11 hr]
  · rw [u₆.sp, u₅.sp, h₄.sp, cp.sp, a.sp, h.sp]
  · rw [u₆.rd, u₅.rd, h₄.rd, cp.rd, a.rd, h.rd]
  · rw [u₆.wr, u₅.wr, h₄.wr, wr₃]
  · rw [u₆.mem, u₅.mem]
    exact h.frame.trans (fstep.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hp.step_sub hk r hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, hp.cs_sub_blk⟩
        · exact ⟨_, by simp, fun _ h => h⟩)
  · rw [u₆.mem, u₅.mem]
    have hl : (rK S s₀ M k).1.length = k := by rw [runSeq_length, List.length_take, length_blocksOf]; omega_arith
    rw [blocksOf_set (k := k) fun j hj hjk => ?_, h.data, set_prefix _ _ _ hl (by rw [length_blocksOf]; exact hk)]
    simp only [rK]
    rw [take_succ_xs hk, runSeq_snoc]
    · congr 2
      rw [← hp.dk_addr hk]
      exact congrArg (fun z => [z]) (h₄.blks .d)
    · refine VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) (by have := S.ds_le M; omega_arith)
      have hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
        VG.Offset.sub_base _ (by have := idx_lt' (L := c.ds M) hj; omega_arith)
      simp only [blkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hp.dk_addr hk]
        have := hp.fD; have := idx_lt' (L := c.ds M) hj; have := idx_lt' (L := c.ds M) hk
        rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
        · exact VG.Offset.disjoint _ (.inl (by have := VG.Proof.Modes.idx_lt (L := c.ds M) hlt; omega_arith))
            (by omega_arith) (by omega_arith)
        · exact VG.Offset.disjoint _ (.inr (by have := VG.Proof.Modes.idx_lt (L := c.ds M) hlt; omega_arith))
            (by omega_arith) (by omega_arith)
      · exact (hp.data_scr.sub_left hsub).sub_right UPre.blk2_sub
      · exact (hp.data_scr.sub_left hsub).sub_right hp.cs_sub_scr
      · exact hp.b_data.symm.sub_left hsub
  · simp only [rK]; rw [u₆.mem, u₅.mem, take_succ_xs hk, runSeq_snoc]; exact h₄.blks .o
  · simp only [rK]; rw [u₆.mem, u₅.mem, take_succ_xs hk, runSeq_snoc]; exact h₄.blks .t
  · rw [z₆, u₅.other _ (by decide), r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_arith)]
    exact ofNat_beq_zero (by have := N_lt c s₀; omega_arith)

end

end VG.Proof.Modes.Arm
