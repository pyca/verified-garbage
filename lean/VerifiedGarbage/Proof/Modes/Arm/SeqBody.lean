import VerifiedGarbage.Proof.Modes.Arm.Seq

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

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_subs op2_imm op2_reg ofNat_beq_zero)

/-- A mode whose operations are each on two different blocks, and which
calls the cipher on the data block or the chaining block. -/
structure ModeOk (M : Mode) : Prop where
  pre : M.pre.all opOk = true
  post : M.post.all opOk = true
  tgt : M.tgt ≠ .t

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
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, List.append_assoc]
  congr 1
  rw [List.drop_eq_getElem_cons hk, List.set_cons_zero]
  rfl

theorem BlkMem.len {c : Core} {Dp S : BitVec 32} {m : Mem} {b : Blks} (h : BlkMem c Dp S m b) :
    ∀ x, (b.get x).length = c.bs := fun x => by rw [← h x]; simp [bytesAt]

/-! ## Block `k` -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
theorem idx_lt' {L k n : Nat} (hk : k < n) : L * k + L ≤ n * L := by
  rw [Nat.mul_comm n]; exact VG.Proof.Modes.idx_lt hk

/-- The address of block `k`, in 32 bits. -/
abbrev Dk (s₀ : State) (c : Core) (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 (c.bs * k)

theorem UPre.dk_toNat {k : Nat} (hk : k < N s₀) : (Dk s₀ c k).toNat = (Dp s₀).toNat + c.bs * k := by
  have := hp.fD
  have := idx_lt' (L := c.bs) hk
  have := S.bs_pos
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.bs * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.dk_addr {k : Nat} (hk : k < N s₀) :
    State.addr (Dk s₀ c k) = State.addr (Dp s₀) + BitVec.ofNat 64 (c.bs * k) := by
  have := hp.fD
  have := idx_lt' (L := c.bs) hk
  exact addr_add (by have := S.bs_pos; omega)

theorem UPre.blk_sub_data {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨State.addr (Dk s₀ c k), c.bs⟩ (dataR c s₀) := by
  rw [hp.dk_addr hk]
  exact VG.Offset.sub_base _ (by have := idx_lt' (L := c.bs) hk; omega)

theorem UPre.lay {k : Nat} (hk : k < N s₀) : Lay c (Dk s₀ c k) (Sc s₀) s₀.wr := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs := rfl
  refine ⟨S.bw_pos, S.bw_le, ?_, by omega, ?_, ?_, ?_⟩
  · rw [hp.dk_toNat hk]
    have := hp.fD; have := idx_lt' (L := c.bs) hk; omega
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨dataR c s₀, hp.data_in, c.bs * k, hp.dk_addr hk, ?_⟩
      have := idx_lt' (L := c.bs) hk; show _ ≤ N s₀ * c.bs; omega
  · exact cov_off (R := scrR c s₀) hp.scr_in (by show oOff + 2 * c.bs ≤ c.scratchBytes; omega)
  · exact (hp.data_scr.sub_left (hp.blk_sub_data hk)).sub_right UPre.blk_sub

/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {k : Nat} {s : State} (h : LInv c S M s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (State.addr (Dk s₀ c k)) c.bs = (xs c s₀)[k]'(by rw [length_blocksOf]; exact hk) := by
  have hl : (rK S s₀ M k).1.length = k := by
    rw [runSeq_length, List.length_take, length_blocksOf]; omega
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (blocksOf c.bs s.mem (State.addr (Dp s₀)) (N s₀)).length by
      rw [length_blocksOf]; exact hk),
    List.getElem?_append_right (show (rK S s₀ M k).1.length ≤ k by omega), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (xs c s₀).length by rw [length_blocksOf]; exact hk)] at this
  rw [hp.dk_addr hk, ← getElem_blocksOf _ _ _ hk]
  exact Option.some.inj this

/-- The blocks of the step, in memory. -/
theorem LInv.blkMem {k : Nat} {s : State} (h : LInv c S M s₀ k s) (hk : k < N s₀) :
    BlkMem c (Dk s₀ c k) (Sc s₀) s.mem
      ((rK S s₀ M k).2.set .d ((xs c s₀)[k]'(by rw [length_blocksOf]; exact hk))) := by
  intro x
  cases x
  · exact h.block hp hk
  · exact h.o
  · exact h.t

end

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

theorem Lay.bt_addr {c : Core} {D Sb : BitVec 32} {wr : List Region} (h : Lay c D Sb wr) (x : Blk) :
    State.addr (bt c D Sb x) = addrOf c D Sb x := by
  have := h.fD; have := h.fS; have := h.bw
  have hb : c.bs = 4 * c.bw := rfl
  cases x
  · simp [bt, Core.base, addrOf]
  · simp only [bt, Core.base, addrOf]; exact addr_add (by omega)
  · simp only [bt, Core.base, addrOf]; exact addr_add (by omega)

theorem Lay.bt_fit {c : Core} {D Sb : BitVec 32} {wr : List Region} (h : Lay c D Sb wr) (x : Blk) :
    (bt c D Sb x).toNat + c.bs ≤ 2 ^ 32 := by
  have := h.fD; have := h.fS
  have e : ∀ (a : BitVec 32) (d : Nat), a.toNat + d < 2 ^ 32 → (a + BitVec.ofNat 32 d).toNat = a.toNat + d :=
    fun a d hd => by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
      Nat.mod_eq_of_lt hd]
  have := h.bw
  have hb : c.bs = 4 * c.bw := rfl
  cases x
  · simp only [bt, Core.base]; rw [e _ _ (by omega)]; omega
  · simp only [bt, Core.base]; rw [e _ _ (by omega)]; omega
  · simp only [bt, Core.base]; rw [e _ _ (by omega)]; omega

/-! ## One block -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

/-- The memory since entry, for the cipher's schedule. -/
theorem UPre.frame_entry {m₁ m₂ : Mem} {k : Nat} (hk : k < N s₀)
    (h₁ : Frame [dataR c s₀, blkR c s₀, belowR S s₀] (savedMem s₀) m₁)
    (h₂ : Frame (blkRegions c (Dk s₀ c k) (Sc s₀)) m₁ m₂) :
    Frame [dataR c s₀, scrR c s₀, belowR S s₀] s₀.mem m₂ := by
  have f₀ : Frame [dataR c s₀, scrR c s₀, belowR S s₀] s₀.mem (savedMem s₀) :=
    (UPre.savedMem_frame (s₀ := s₀)).sub fun r hr => by
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
    · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk_sub⟩

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (b : Blks) (s s₂ : State) : Prop where
  regs : ∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → x ≠ .r9 → x ≠ .r10 → s₂.gpr x = s.gpr x
  r0 : s₂.gpr .r0 = Kp s₀
  r1 : s₂.gpr .r1 = bt c (Dk s₀ c k) (Sc s₀) M.tgt
  r2 : s₂.gpr .r2 = 1
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  frame : Frame (blkRegions c (Dk s₀ c k) (Sc s₀)) s.mem s₂.mem
  blks : BlkMem c (Dk s₀ c k) (Sc s₀) s₂.mem b

theorem pre_wp (hM : ModeOk M) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv c S M s₀ k s) :
    WP isa (.block (c.opsCode M.pre ++ c.callArgs M.tgt)) s
      (PreA (c := c) (M := M) s₀ k (runOps M.pre ((rK S s₀ M k).2.set .d
        ((xs c s₀)[k]'(by rw [length_blocksOf]; exact hk)))) s) := by
  have hb := h.blkMem hp hk
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (h.wr ▸ hp.lay hk) h.r6 h.r8 hb hM.pre hb.len) fun s₁ h₁ => ?_
  have h4 : s₁.gpr .r4 = Kp s₀ := by rw [h₁.regs _ (by decide) (by decide), h.r4]
  have hbt : s₁.gpr (c.base M.tgt).1 + BitVec.ofNat 32 (c.base M.tgt).2 = bt c (Dk s₀ c k) (Sc s₀) M.tgt :=
    bt_eq (by rw [h₁.regs _ (by decide) (by decide), h.r6]) (by rw [h₁.regs _ (by decide) (by decide), h.r8]) _
  have enc : encodable (BitVec.ofNat 32 (c.base M.tgt).2) = true := by
    have := hM.tgt; cases hx : M.tgt
    · simp [Core.base]; decide
    · simp [Core.base, oOff]; decide
    · exact absurd hx this
  simp only [Core.callArgs, mov]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_add (op2_imm enc) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨fun x a b d e f => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ d, u₃.other _ b, u₂.other _ a, h₁.regs _ e f]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h4]
  · rw [u₄.other _ (by decide), u₃.gpr, ← hbt]
    have hne : (c.base M.tgt).1 ≠ .r0 := by cases M.tgt <;> simp [Core.base]
    rw [u₂.other _ hne]
  · rw [u₄.gpr]
  · rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, h₁.sp]
  · rw [u₄.mem, u₃.mem, u₂.mem]; exact h₁.frame
  · rw [u₄.mem, u₃.mem, u₂.mem]; exact h₁.blks


/-- A region apart from the data and the scratch buffer is apart from the
blocks of a step. -/
theorem UPre.disj_blks {k : Nat} (hk : k < N s₀) {R : Region} (hd : R.Disjoint (dataR c s₀))
    (hs : R.Disjoint (scrR c s₀)) (x : Blk) :
    R.Disjoint ⟨addrOf c (Dk s₀ c k) (Sc s₀) x, c.bs⟩ := by
  obtain ⟨r, hr, hsub⟩ := Lay.sub (c := c) (Dp := Dk s₀ c k) (S := Sc s₀) x
  refine Region.Disjoint.sub_right ?_ hsub
  simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hd.sub_right (hp.blk_sub_data hk)
  · exact hs.sub_right UPre.blk_sub

/-- The call's arguments make its precondition. -/
theorem PreA.callPre {k : Nat} (hk : k < N s₀) {b : Blks} {s s₂ : State}
    (h : LInv c S M s₀ k s) (a : PreA (c := c) (M := M) s₀ k b s s₂) :
    CallPre c S s₂ (Kp s₀) (bt c (Dk s₀ c k) (Sc s₀) M.tgt) := by
  have hL := hp.lay hk
  have sp : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  refine ⟨a.r0, a.r1, a.r2, by rw [sp]; exact hp.stk, hp.fK, hL.bt_fit _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.bt_addr]; exact hp.disj_blks hk hp.key_data hp.key_scr _
  · rw [sp]; exact hp.b_key
  · rw [sp, hL.bt_addr]; exact hp.disj_blks hk hp.b_data hp.b_scr _
  · rw [a.rd, a.wr, h.rd, h.wr]; exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.key_in
  · rw [a.wr, h.wr, hL.bt_addr]; exact hL.writable _

/-- The blocks after the call. -/
theorem call_blks {k : Nat} (hk : k < N s₀) {b : Blks} {s s₂ s₃ : State}
    (h : LInv c S M s₀ k s) (a : PreA (c := c) (M := M) s₀ k b s s₂)
    (cp : CallPost c S s₂ (Kp s₀) (bt c (Dk s₀ c k) (Sc s₀) M.tgt) s₃) :
    BlkMem c (Dk s₀ c k) (Sc s₀) s₃.mem (b.set M.tgt (ciph S s₀ (b.get M.tgt))) := by
  have hL := hp.lay hk
  have sp : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes at this; omega
  intro x
  by_cases hx : x = M.tgt
  · subst hx
    rw [Blks.get_set_self, ← hL.bt_addr, cp.out, hL.bt_addr, a.blks M.tgt,
      hp.ciph_eq (hp.frame_entry hk h.frame a.frame)]
  · rw [Blks.get_set_of_ne _ _ hx, ← a.blks x]
    refine VG.Proof.Modes.bytesAt_frame cp.frame (fun r hr => ?_) hfit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hL.bt_addr]; exact hL.disjoint hx
    · rw [sp]; exact (hp.disj_blks hk hp.b_data hp.b_scr x).symm

end

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
theorem take_succ_xs {k : Nat} (hk : k < N s₀) :
    (xs c s₀).take (k + 1) = (xs c s₀).take k ++ [(xs c s₀)[k]'(by rw [length_blocksOf]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_blocksOf]; exact hk)]
  rfl

/-- The regions a step may change, within those the invariant allows. -/
theorem UPre.step_sub {k : Nat} (hk : k < N s₀) :
    ∀ r ∈ blkRegions c (Dk s₀ c k) (Sc s₀), ∃ r' ∈ [dataR c s₀, blkR c s₀, belowR S s₀], Region.Sub r r' := by
  intro r hr
  simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, .head _, hp.blk_sub_data hk⟩
  · exact ⟨_, .tail _ (.head _), fun _ h => h⟩

theorem body_ok (hM : ModeOk M) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv c S M s₀ k s) :
    WP isa (c.body M) s fun s' => LInv c S M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hL := hp.lay hk
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes at this; omega
  refine WP.seq (WP.mono (pre_wp hp hM hk h) fun s₂ a => ?_)
  refine WP.seq (WP.mono (call_wp S (a.callPre hp hk h)) fun s₃ cp => ?_)
  have hb₂ := call_blks hp hk h a cp
  have g₃ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) h9 h10]
  have r6 : s₃.gpr .r6 = Dk s₀ c k := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r6]
  have r8 : s₃.gpr .r8 = Sc s₀ := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r8]
  have wr₃ : s₃.wr = s₀.wr := by rw [cp.wr, a.wr, h.wr]
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (wr₃ ▸ hL) r6 r8 hb₂ hM.post hb₂.len) fun s₄ h₄ => ?_
  -- The memory the step changed: block `k`, the chaining and spare blocks, the stack.
  have sp₂ : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  have fstep : Frame (blkRegions c (Dk s₀ c k) (Sc s₀) ++ [belowR S s₀]) s.mem s₄.mem := by
    refine ((a.frame.mono fun r hr => List.mem_append_left _ hr).trans (cp.frame.sub fun r hr => ?_)).trans
      (h₄.frame.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hL.bt_addr]
      obtain ⟨r', hr', hs'⟩ := Lay.sub (c := c) (Dp := Dk s₀ c k) (S := Sc s₀) M.tgt
      exact ⟨r', List.mem_append_left _ hr', hs'⟩
    · exact ⟨belowR S s₀, by simp, by rw [sp₂]; exact fun _ h => h⟩
  have r6' : s₄.gpr .r6 = Dk s₀ c k := by rw [h₄.regs _ (by decide) (by decide), r6]
  have r7 : s₄.gpr .r7 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [h₄.regs _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide), h.r7]
  simp only [Core.advance]
  refine wp_add (op2_imm S.bs_enc) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [u₆.other _ (by decide), u₅.gpr, r6', Dk, VG.Offset.add_add, Nat.mul_succ]
  · rw [u₆.gpr, u₅.other _ (by decide), r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide), r8]
  · rw [u₆.sp, u₅.sp, h₄.sp, cp.sp, a.sp, h.sp]
  · rw [u₆.rd, u₅.rd, h₄.rd, cp.rd, a.rd, h.rd]
  · rw [u₆.wr, u₅.wr, h₄.wr, wr₃]
  · rw [u₆.mem, u₅.mem]
    exact h.frame.trans (fstep.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hp.step_sub hk r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  · rw [u₆.mem, u₅.mem]
    have hl : (rK S s₀ M k).1.length = k := by rw [runSeq_length, List.length_take, length_blocksOf]; omega
    rw [blocksOf_set (k := k) fun j hj hjk => ?_, h.data, set_prefix _ _ _ hl (by rw [length_blocksOf]; exact hk)]
    simp only [rK]
    rw [take_succ_xs hk, runSeq_snoc]
    · congr 2
      rw [← hp.dk_addr hk]
      exact congrArg (fun z => [z]) (h₄.blks .d)
    · refine VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) hfit
      have hsub : Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (c.bs * j), c.bs⟩ (dataR c s₀) :=
        VG.Offset.sub_base _ (by have := idx_lt' (L := c.bs) hj; omega)
      simp only [blkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hp.dk_addr hk]
        have := hp.fD; have := idx_lt' (L := c.bs) hj; have := idx_lt' (L := c.bs) hk
        rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
        · exact VG.Offset.disjoint _ (.inl (by have := VG.Proof.Modes.idx_lt (L := c.bs) hlt; omega))
            (by omega) (by omega)
        · exact VG.Offset.disjoint _ (.inr (by have := VG.Proof.Modes.idx_lt (L := c.bs) hlt; omega))
            (by omega) (by omega)
      · exact (hp.data_scr.sub_left hsub).sub_right UPre.blk_sub
      · exact hp.b_data.symm.sub_left hsub
  · simp only [rK]; rw [u₆.mem, u₅.mem, take_succ_xs hk, runSeq_snoc]; exact h₄.blks .o
  · simp only [rK]; rw [u₆.mem, u₅.mem, take_succ_xs hk, runSeq_snoc]; exact h₄.blks .t
  · rw [z₆, u₅.other _ (by decide), r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega)]
    exact ofNat_beq_zero (by have := (s₀.gpr .r3).isLt; simp only [N]; omega)

end

end VG.Proof.Modes.Arm
