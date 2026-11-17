module

public import VerifiedGarbage.Proof.AesCbc.Arm.GroupOps
public import VerifiedGarbage.Proof.AesCbc.Arm.CT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES's modes on ARMv7, a group of blocks at a time: correctness

`wholeG_wp`: `wholeG frame gm lgs body` (`Impl/AesCbc/Arm/Groups.lean`) meets
the contract of `whole body` (`modeArm`, `Loop.lean`), with the same stack,
if `body` takes the loop invariant from `k` blocks to `k + 1` (`BodyOk`) and
each level's groups compute the mode's steps (`LevelOk`).

* The groups keep `whole`'s invariant but for where memory has changed: also
  in the groups' buffer, bytes `[wOff, wOff + 80)` of the scratch buffer,
  which `whole`'s bodies leave alone (`WInv`).
* A group of `G` blocks (`gBody_ok`): the operations before the call
  (`opsCode_wp`), the call of the block function on the `G` blocks of the
  buffer or of the data (`blk_call`), which enciphers each (`gciph`), and
  the operations after it leave the data and the chaining value as the
  mode's `out` and `chain` after `G` more blocks are (`GSim`).
* After the groups, the invariant of `whole`'s loop holds of an entry state
  whose memory has the buffer's bytes as the groups left them (`anch`,
  `WInv.toL`): the precondition holds of it too, and the postcondition from
  it is the postcondition (`UPre.anch`, `post_anch`), so the loop over the
  blocks left and the epilogue are `whole`'s (`loop_ok`, `epilogue_wp`).
-/

-- separate module: correctness costs more than its imports, so a change to the constant-time proof (`GroupsCT.lean`) does not check it again.

@[expose] public section

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (save setup restore saved mov)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem savedMem_frame add0)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp cmp0 eval_eq eval_ne
  sub_ofNat ofNat_shr)
open VG.Spec.Aes (bytesAt)

/-! ## What a group computes -/

/-- The chaining value after two pieces. -/
theorem next_append (iv : List Byte) (xs ys : List (List Byte)) :
    Spec.Cbc.next iv (xs ++ ys) = Spec.Cbc.next (Spec.Cbc.next iv xs) ys := by
  cases ys with
  | nil => simp [Spec.Cbc.next]
  | cons y ys => simp [Spec.Cbc.next, List.getLastD_eq_getLast?, List.getLast?_append]


/-- Whether the call enciphers a block: one of the buffer, or of the data. -/
def gtgt (onW : Bool) : GBlk → Bool
  | .d _ => !onW
  | .w _ => onW
  | .iv => false

/-- What the call does to the blocks. -/
def gciph (onW : Bool) (ciph : Spec.Cbc.Cipher) (b : GBlks) : GBlks :=
  fun x => if gtgt onW x then ciph (b x) else b x

/-- What a group does to the blocks. -/
def gstep (gm : GMode) (G : Nat) (ciph : Spec.Cbc.Cipher) (b : GBlks) : GBlks :=
  grunOps (gm.post G) (gciph gm.onW ciph (grunOps (gm.pre G) b))

/-- A group of `G` blocks computes the mode `M` on them, with the cipher
`C R w`: from the chaining value after the blocks `xs` and the next `G`
blocks `ys`, it leaves the mode's output on `ys` and the chaining value
after them. -/
def GSim (M : Mode) (C : Nat → List Byte → Spec.Cbc.Cipher) (gm : GMode) (G : Nat) : Prop :=
  ∀ (R : Nat) (w iv : List Byte) (xs ys : List (List Byte)) (b : GBlks), ys.length = G →
    b .iv = M.chain R w iv xs → (∀ j, j < G → ys[j]? = some (b (.d j))) →
    M.out R w iv (xs ++ ys) = M.out R w iv xs ++ (List.range G).map (fun j => gstep gm G (C R w) b (.d j)) ∧
      M.chain R w iv (xs ++ ys) = gstep gm G (C R w) b .iv

/-- What the groups of `2 ^ lg` blocks need: the shift and the immediates
encodable, at most five blocks, the operations on blocks of the group, the
group computing the mode, and the block function `F` computing the cipher
on bytes. -/
structure LevelOk (M : Mode) (F : BlkFn) (C : Nat → List Byte → Spec.Cbc.Cipher) (gm : GMode) (lg : Nat) :
    Prop where
  sh : 1 ≤ lg ∧ lg ≤ 31
  g5 : 2 ^ lg ≤ 5
  encG : encodable (BitVec.ofNat 32 (2 ^ lg)) = true
  encA : encodable (BitVec.ofNat 32 (16 * 2 ^ lg)) = true
  pre : (gm.pre (2 ^ lg)).all (gopOk (2 ^ lg)) = true
  post : (gm.post (2 ^ lg)).all (gopOk (2 ^ lg)) = true
  sim : GSim M C gm (2 ^ lg)
  hf : ∀ R w m p, (F.f R w (Spec.Aes.stateAt m p)).toList = C R w (bytesAt m p 16)

/-! ## The invariant, with the buffer -/

/-- The groups' buffer. -/
abbrev wR (s₀ : State) : Region := ⟨State.addr (S s₀) + BitVec.ofNat 64 wOff, 80⟩

/-- Where memory may have changed since the registers were saved: `whole`'s
regions, and the groups' buffer. -/
abbrev gFrame (s₀ : State) : List Region :=
  [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀, wR s₀]

/-- `whole`'s loop invariant after `k` blocks (`LInv`), but that memory may
also have changed in the groups' buffer. -/
structure WInv (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : Regs s₀ k s
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r11 : s.gpr .r11 = s₀.gpr .r11
  frame : Frame (gFrame s₀) (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 = chainK M s₀ k

theorem LInv.toW {M : Mode} {s₀ : State} {k : Nat} {s : State} (h : LInv M s₀ k s) : WInv M s₀ k s :=
  ⟨h.regs, h.r8, h.r11, h.frame.sub fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp, fun _ h => h⟩, h.data, h.iv⟩

theorem wR_sub (s₀ : State) : Region.Sub (wR s₀) (scrR s₀) := Offset.sub_base _ (by decide)

theorem wR_slots (s₀ : State) : (wR s₀).Disjoint ⟨State.addr (S s₀), 2096⟩ :=
  Offset.disjoint_base _ (Nat.le_refl _) (by decide)

/-! ## The entry state, with the buffer as the groups left it -/

/-- The state `s₀` with the bytes of the groups' buffer those of `m`. -/
def anch (s₀ : State) (m : Mem) : State :=
  { s₀ with mem := fun a => if (wR s₀).Contains a 1 then m a else s₀.mem a }

theorem anch_frame (s₀ : State) (m : Mem) : Frame [wR s₀] s₀.mem (anch s₀ m).mem := fun x hx => by
  have : ¬ (wR s₀).Contains x 1 := hx _ (List.mem_singleton_self _)
  simp only [anch, this, ↓reduceIte]

theorem anch_in (s₀ : State) (m : Mem) {a : Addr} (h : (wR s₀).Contains a 1) : (anch s₀ m).mem a = m a := by
  simp only [anch, h, ↓reduceIte]

theorem anch_out (s₀ : State) (m : Mem) {a : Addr} (h : ¬ (wR s₀).Contains a 1) : (anch s₀ m).mem a = s₀.mem a := by
  simp only [anch, h, ↓reduceIte]

theorem anch_gpr (s₀ : State) (m : Mem) : (anch s₀ m).gpr = s₀.gpr := rfl
theorem anch_sp (s₀ : State) (m : Mem) : (anch s₀ m).sp = s₀.sp := rfl
theorem anch_rd (s₀ : State) (m : Mem) : (anch s₀ m).rd = s₀.rd := rfl
theorem anch_wr (s₀ : State) (m : Mem) : (anch s₀ m).wr = s₀.wr := rfl

/-- Saving the registers changes a byte as it does in a memory with the same byte. -/
theorem saveMem_agree (B : Addr) (g : Reg → BitVec 32) (x : Addr) :
    ∀ (l : List (Reg × Nat)) (m m' : Mem), m' x = m x → Spill.saveMem m' B g l x = Spill.saveMem m B g l x
  | [], _, _, h => h
  | p :: l, m, m', h => by
    simp only [Spill.saveMem]
    refine saveMem_agree B g x l _ _ ?_
    simp only [Mem.writeW, Mem.write, h]

section
variable {s₀ : State} (hp : UPre s₀) (m : Mem)
include hp

theorem anch_arg {i : Nat} (hi : i < 2) : stackArg (anch s₀ m) i = stackArg s₀ i := by
  have hs : (⟨stackArgAddr s₀ i, 4⟩ : Region).Disjoint (wR s₀) := by
    refine ((hp.scr_args.symm.sub_right (wR_sub s₀))).sub_left ?_
    rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
    · exact UPre.arg_sub
    · rw [hp.arg1]; exact Offset.sub_base _ (by decide)
  exact (anch_frame s₀ m).readW (r := ⟨stackArgAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hs) (by decide)

theorem anch_N : N (anch s₀ m) = N s₀ := congrArg BitVec.toNat (anch_arg hp m (by decide))

theorem anch_S : S (anch s₀ m) = S s₀ := anch_arg hp m (by decide)

set_option linter.unusedSimpArgs false in
/-- The precondition holds of the state with the buffer changed. -/
theorem UPre.anch : UPre (anch s₀ m) := by
  have e0 := anch_arg hp m (i := 0) (by decide)
  have e1 := anch_arg hp m (i := 1) (by decide)
  have k {P Q : Prop} (h : P) (e : Q = P) : Q := e ▸ h
  refine ⟨k hp.rd ?_, k hp.wr ?_, k hp.sch_iv ?_, k hp.sch_data ?_, k hp.sch_scr ?_, k hp.iv_data ?_,
    k hp.iv_scr ?_, k hp.data_scr ?_, k hp.iv_args ?_, k hp.data_args ?_, k hp.scr_args ?_, k hp.b_sch ?_,
    k hp.b_iv ?_, k hp.b_data ?_, k hp.b_scr ?_, k hp.sch_fit ?_, k hp.iv_fit ?_, k hp.data_fit ?_,
    k hp.scr_fit ?_, k hp.sp8 ?_, k hp.sp_fit ?_, k hp.rounds ?_⟩ <;>
    simp only [schR, argsR, ivR, dataR, scrR, belowR, W, R, Iv, Dp, N, S, stackArgAddr, anch_gpr, anch_sp,
      anch_rd, anch_wr, e0, e1]

theorem anch_wK : wK (anch s₀ m) = wK s₀ := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  show bytesAt (anch s₀ m).mem (State.addr (W s₀)) (16 * (R s₀ + 1)) = bytesAt s₀.mem _ _
  exact Proof.Cmac.bytesAt_frame (anch_frame s₀ m) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.sch_scr.sub_right (wR_sub s₀)).sub_left (Region.sub_prefix hR)) (by omega_using [hR])

theorem anch_iv0 : iv0 (anch s₀ m) = iv0 s₀ :=
  Proof.Cmac.bytesAt_frame (anch_frame s₀ m) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_scr.sub_right (wR_sub s₀)) (by decide)

theorem anch_blks : blks (anch s₀ m) = blks s₀ := by
  show Spec.Cbc.blocksAt (anch s₀ m).mem (State.addr (Dp s₀)) (N (anch s₀ m)) = _
  rw [anch_N hp]
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame (anch_frame s₀ m) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.data_scr.sub_left (UPre.data_sub (List.mem_range.mp hj))).sub_right (wR_sub s₀)

theorem anch_outK (M : Mode) (k : Nat) : outK M (anch s₀ m) k = outK M s₀ k := by
  show M.out (R s₀) (wK (anch s₀ m)) (iv0 (anch s₀ m)) ((blks (anch s₀ m)).take k) = _
  rw [anch_wK hp, anch_iv0 hp, anch_blks hp]

theorem anch_chainK (M : Mode) (k : Nat) : chainK M (anch s₀ m) k = chainK M s₀ k := by
  show M.chain (R s₀) (wK (anch s₀ m)) (iv0 (anch s₀ m)) ((blks (anch s₀ m)).take k) = _
  rw [anch_wK hp, anch_iv0 hp, anch_blks hp]

/-- The postcondition from the state with the buffer changed is the
postcondition. -/
theorem post_anch {M : Mode} {s' : State} (h : (modeArm M).post (anch s₀ m) s') : (modeArm M).post s₀ s' := by
  have hall : ∀ t : State, (blks t).take (N t) = blks t := fun t =>
    List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have h' : Spec.Cbc.blocksAt s'.mem (State.addr (Dp s₀)) (N (anch s₀ m)) = outK M (anch s₀ m) (N (anch s₀ m)) ∧
      bytesAt s'.mem (State.addr (Iv s₀)) 16 = chainK M (anch s₀ m) (N (anch s₀ m)) := by
    simp only [outK, chainK, hall]; exact h
  rw [anch_outK hp, anch_chainK hp, anch_N hp] at h'
  show Spec.Cbc.blocksAt s'.mem (State.addr (Dp s₀)) (N s₀) = M.out (R s₀) (wK s₀) (iv0 s₀) (blks s₀) ∧
    bytesAt s'.mem (State.addr (Iv s₀)) 16 = M.chain (R s₀) (wK s₀) (iv0 s₀) (blks s₀)
  simpa only [outK, chainK, hall] using h'

end

/-- `whole`'s invariant, of the entry state with the buffer as it is now. -/
theorem WInv.toL {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : WInv M s₀ k s) :
    LInv M (anch s₀ s.mem) k s := by
  have eN := anch_N hp s.mem
  have eS := anch_S hp s.mem
  refine ⟨h.regs.r4, h.regs.r5, h.regs.r6, h.regs.r7, by rw [eN]; exact h.r8, by rw [eS]; exact h.regs.r10,
    h.r11, h.regs.sp, h.regs.rd, h.regs.wr, ?_, ?_, ?_⟩
  · intro x hx
    have e : [ivR (anch s₀ s.mem), dataR (anch s₀ s.mem), ⟨State.addr (S (anch s₀ s.mem)), 2064⟩,
        belowR (anch s₀ s.mem)] = [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] := by
      show [ivR s₀, ⟨State.addr (Dp s₀), 16 * N (anch s₀ s.mem)⟩, ⟨State.addr (S (anch s₀ s.mem)), 2064⟩,
        belowR s₀] = _
      rw [eN, eS]
    have hx' : ∀ r ∈ [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀], ¬ r.Contains x 1 := by
      rw [← e]; exact hx
    show s.mem x = Spill.saveMem (anch s₀ s.mem).mem (State.addr (S (anch s₀ s.mem))) s₀.gpr saved x
    rw [eS]
    by_cases hw : (wR s₀).Contains x 1
    · have f := Spill.saveMem_frame (anch s₀ s.mem).mem (State.addr (S s₀)) s₀.gpr (L := 2096) (by decide) saved
        (by decide)
      rw [f x (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact wR_slots s₀ x hw), anch_in _ _ hw]
    · rw [saveMem_agree _ _ _ saved s₀.mem _ (anch_out _ _ hw)]
      refine h.frame x fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hx' _ (by simp)
      · exact hx' _ (by simp)
      · exact hx' _ (by simp)
      · exact hx' _ (by simp)
      · exact hw
  · rw [eN, anch_outK hp, anch_blks hp]; exact h.data
  · rw [anch_chainK hp]; exact h.iv

/-! ## Blocks in memory -/

theorem getElem?_blocksAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Cbc.blocksAt m p n)[i]? = some (bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16) := by
  rw [List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hi), getElem_blocksAt _ _ hi]

/-- The blocks after the `G` from block `k` changed. -/
theorem blocksAt_splice {m m' : Mem} {p : Addr} {n k G : Nat} (hk : k + G ≤ n)
    (ys : List (List Byte)) (hy : ys.length = G)
    (hin : ∀ j < G, ys[j]? = some (bytesAt m' (p + BitVec.ofNat 64 (16 * (k + j))) 16))
    (hout : ∀ i < n, i < k ∨ k + G ≤ i →
      bytesAt m' (p + BitVec.ofNat 64 (16 * i)) 16 = bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16) :
    Spec.Cbc.blocksAt m' p n =
      (Spec.Cbc.blocksAt m p n).take k ++ ys ++ (Spec.Cbc.blocksAt m p n).drop (k + G) := by
  have lt : ((Spec.Cbc.blocksAt m p n).take k).length = k := by
    rw [List.length_take, length_blocksAt]; omega_using [hk]
  apply List.ext_getElem?
  intro i
  by_cases h1 : i < k
  · rw [List.append_assoc, List.getElem?_append_left (by rw [lt]; exact h1), List.getElem?_take, ite_eq_left h1,
      getElem?_blocksAt _ _ (by omega_using [h1, hk]), getElem?_blocksAt _ _ (by omega_using [h1, hk]),
      hout i (by omega_using [h1, hk]) (.inl h1)]
  · by_cases h2 : i < k + G
    · rw [List.getElem?_append_left (by rw [List.length_append, lt, hy]; exact h2),
        List.getElem?_append_right (by rw [lt]; omega_using [h1]), lt, hin _ (by omega_using [h1, h2]),
        getElem?_blocksAt _ _ (by omega_using [h2, hk]), show k + (i - k) = i by omega_using [h1]]
    · rw [List.getElem?_append_right (by rw [List.length_append, lt, hy]; omega_using [h2]), List.length_append,
        lt, hy, List.getElem?_drop, show k + G + (i - (k + G)) = i by omega_using [h2]]
      by_cases h3 : i < n
      · rw [getElem?_blocksAt _ _ h3, getElem?_blocksAt _ _ h3, hout i h3 (.inr (by omega_using [h2]))]
      · rw [List.getElem?_eq_none (by rw [length_blocksAt]; omega_using [h3]),
          List.getElem?_eq_none (by rw [length_blocksAt]; omega_using [h3])]

/-- Block `j` at `D` after a function of states on `n` blocks replaced them. -/
theorem bytesAt_of_statesAtN {m m' : Mem} {D : Addr} {g : Spec.Aes.State → Spec.Aes.State} {n : Nat}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {j : Nat} (hj : j < n) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * j)) 16 =
      (g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)))).toList := by
  have := congrArg (·[j]?) h
  simp only [Spec.Aes.statesAt, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at this
  rw [bytesAt_toList, this]

section
variable {M : Mode} {s₀ : State}

/-- Block `i`, not yet enciphered, from the invariant. -/
theorem WInv.blockAt {k : Nat} {s : State} (h : WInv M s₀ k s) {i : Nat} (hki : k ≤ i) (hi : i < N s₀) :
    (blks s₀)[i]? = some (bytesAt s.mem (blk s₀ i) 16) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out, List.length_take, length_blocksAt]; omega_using [hki, hi]
  have := congrArg (·[i]?) h.data
  simp only [getElem?_blocksAt _ _ hi,
    List.getElem?_append_right (show (outK M s₀ k).length ≤ i by omega_using [hl, hki]), hl,
    List.getElem?_drop, show k + (i - k) = i by omega_using [hki]] at this
  rw [show (blks s₀)[i]? = _ from getElem?_blocksAt _ _ hi]
  exact this.symm

/-- Memory since entry, in the regions the function writes. -/
theorem WInv.big {k : Nat} {s : State} (h : WInv M s₀ k s) : Frame (Big s₀) s₀.mem s.mem :=
  ((savedMem_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩).trans (h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, wR_sub s₀⟩)

/-- The invariant after a step that keeps the registers and memory. -/
theorem WInv.of_regs {k : Nat} {s s' : State} (h : WInv M s₀ k s)
    (g : ∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) (sp : s'.sp = s.sp) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (mem : s'.mem = s.mem) : WInv M s₀ k s' :=
  ⟨h.regs.of g sp rd wr, by rw [g _ (by decide) (by decide), h.r8], by rw [g _ (by decide) (by decide), h.r11],
    by rw [mem]; exact h.frame, by rw [mem]; exact h.data, by rw [mem]; exact h.iv⟩

end

/-! ## The call of a group -/

/-- The blocks of the call, as the register holds them: the buffer's, or
the data's. -/
def gB (s₀ : State) (k : Nat) (onW : Bool) : BitVec 32 :=
  if onW then S s₀ + BitVec.ofNat 32 wOff else D32 s₀ k

/-- Their address. -/
def gBA (s₀ : State) (k : Nat) (onW : Bool) : Addr :=
  if onW then State.addr (S s₀) + BitVec.ofNat 64 wOff else blk s₀ k

/-- Where a group of `G` blocks after `k` may change memory. -/
abbrev gStep (s₀ : State) (k G : Nat) : List Region :=
  [⟨blk s₀ k, 16 * G⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀, wR s₀]

theorem sub_trans {a b c : Region} (h : Region.Sub a b) (h' : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h' x (h x hx)

theorem seg_sub {s₀ : State} {k G : Nat} (hk : k + G ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * G⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem gStep_sub {s₀ : State} {k G : Nat} (hk : k + G ≤ N s₀) :
    ∀ r ∈ gStep s₀ k G, ∃ r' ∈ gFrame s₀, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨dataR s₀, by simp, seg_sub hk⟩
  · exact ⟨ivR s₀, by simp, fun _ h => h⟩
  · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, fun _ h => h⟩
  · exact ⟨belowR s₀, by simp, fun _ h => h⟩
  · exact ⟨wR s₀, by simp, fun _ h => h⟩

section
variable {s₀ : State} (hp : UPre s₀) {k G : Nat} (hG : 0 < G) (hG5 : G ≤ 5) (hk : k + G ≤ N s₀)
include hp hG hG5 hk

theorem UPre.gB_addr (onW : Bool) : State.addr (gB s₀ k onW) = gBA s₀ k onW := by
  have _ := hG5
  cases onW
  · exact hp.dataA (by omega_using [hG, hk])
  · exact hp.scrA (by decide)

theorem UPre.gB_fit (onW : Bool) : (gB s₀ k onW).toNat + 16 * G ≤ 2 ^ 32 := by
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  cases onW
  · show (D32 s₀ k).toNat + 16 * G ≤ 2 ^ 32
    rw [hp.dataN (by omega_using [hG, hk])]; omega_using [hk, hdf]
  · show (S s₀ + BitVec.ofNat 32 wOff).toNat + 16 * G ≤ 2 ^ 32
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wOff) (by decide),
      Nat.mod_eq_of_lt (by unfold wOff; omega_using [hsc])]
    unfold wOff; omega_using [hsc, hG5]

/-- The blocks of the call lie in the group's data, or in the buffer. -/
theorem UPre.gBA_sub (onW : Bool) :
    Region.Sub ⟨gBA s₀ k onW, 16 * G⟩ (if onW then wR s₀ else ⟨blk s₀ k, 16 * G⟩) := by
  have _ := hp; have _ := hG; have _ := hk
  cases onW
  · exact fun _ h => h
  · exact Region.sub_prefix (by omega_using [hG5])

/-- The regions the operations of the group change, among those of a step. -/
theorem UPre.gRegions_step :
    ∀ r ∈ gRegions G (D32 s₀ k) (S s₀) (Iv s₀), ∃ r' ∈ gStep s₀ k G, Region.Sub r r' := fun r hr => by
  have _ := hG5
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨blk s₀ k, 16 * G⟩, by simp, by rw [hp.dataA (by omega_using [hG, hk])]; exact fun _ h => h⟩
  · exact ⟨wR s₀, by simp, fun _ h => h⟩
  · exact ⟨ivR s₀, by simp, fun _ h => h⟩

/-- The regions the call changes, among those of a step. -/
theorem UPre.call_step (onW : Bool) :
    ∀ r ∈ [⟨gBA s₀ k onW, 16 * G⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀],
      ∃ r' ∈ gStep s₀ k G, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := hp.gBA_sub hG hG5 hk onW
    cases onW
    · exact ⟨⟨blk s₀ k, 16 * G⟩, by simp, this⟩
    · exact ⟨wR s₀, by simp, this⟩
  · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨belowR s₀, by simp, fun _ h => h⟩

/-- A block of the data outside the group is apart from what a step changes. -/
theorem UPre.out_step {i : Nat} (hi : i < N s₀) (ho : i < k ∨ k + G ≤ i) :
    ∀ r ∈ gStep s₀ k G, (⟨blk s₀ i, 16⟩ : Region).Disjoint r := fun r hr => by
  have _ := hG; have _ := hG5
  have hdf := hp.data_fit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [hi, hdf]) (by omega_using [hk, hdf])
  · exact hp.blk_iv hi
  · exact (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (Region.sub_prefix (by decide))
  · exact hp.b_data.symm.sub_left (UPre.data_sub hi)
  · exact (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (wR_sub s₀)

/-- The arguments of the call on the group. -/
theorem UPre.grpCall (onW : Bool) {s : State} (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1)
    (r2 : s.gpr .r2 = gB s₀ k onW) (r3 : s.gpr .r3 = BitVec.ofNat 32 G) (r12 : s.gpr .r12 = S s₀)
    (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (gB s₀ k onW) (S s₀) (R s₀) G := by
  obtain hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  have hsc := hp.scr_fit
  obtain hA := hp.gB_addr hG hG5 hk onW
  obtain hsub := hp.gBA_sub hG hG5 hk onW
  -- The blocks of the call, within the data or the buffer.
  obtain ⟨A, hA', sA, bA, dA, cA⟩ : ∃ A : Region, Region.Sub ⟨gBA s₀ k onW, 16 * G⟩ A ∧
      (schR s₀).Disjoint A ∧ (belowR s₀).Disjoint A ∧ A.Disjoint ⟨State.addr (S s₀), 2048⟩ ∧
      Covers [⟨gBA s₀ k onW, 16 * G⟩] s₀.wr := by
    cases onW
    · refine ⟨dataR s₀, sub_trans hsub (seg_sub hk), hp.sch_data, hp.b_data,
        hp.data_scr.sub_right (Region.sub_prefix (by decide)), ?_⟩
      rw [hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨dataR s₀, by simp, 16 * k, rfl, by show 16 * k + 16 * G ≤ 16 * N s₀; omega_using [hk]⟩
    · refine ⟨wR s₀, hsub, hp.sch_scr.sub_right (wR_sub s₀), hp.b_scr.sub_right (wR_sub s₀),
        Offset.disjoint_base _ (by decide) (by decide), ?_⟩
      rw [hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, wOff, rfl, by show wOff + 16 * G ≤ 2176; unfold wOff; omega_using [hG5]⟩
  refine ⟨r0, by rw [r1]; simp [R], r2, r3, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    hp.gB_fit hG hG5 hk onW, by omega_using [hsc], by rw [hA]; exact sA.sub_right hA',
    hp.sch_scr.sub_right (Region.sub_prefix (by decide)), by rw [hA]; exact dA.sub_left hA',
    by rw [hb]; exact hp.b_sch, by rw [hb, hA]; exact bA.sub_right hA',
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hA]
    refine Covers.pair cA ?_
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The address of a block the call enciphers. -/
theorem UPre.gaddr_tgt {onW : Bool} {x : GBlk} (ht : gtgt onW x = true) (hx : x.ok G = true) :
    ∃ j, j < G ∧ gaddr (D32 s₀ k) (S s₀) (Iv s₀) x = State.addr (gB s₀ k onW) + BitVec.ofNat 64 (16 * j) := by
  have hA := hp.gB_addr hG hG5 hk onW
  cases x with
  | d j =>
    obtain rfl : onW = false := by simpa [gtgt] using ht
    exact ⟨j, by simpa [GBlk.ok] using hx, rfl⟩
  | w j =>
    obtain rfl : onW = true := by simpa [gtgt] using ht
    refine ⟨j, by simpa [GBlk.ok] using hx, ?_⟩
    rw [hA]
    show State.addr (S s₀) + BitVec.ofNat 64 (wOff + 16 * j) = State.addr (S s₀) + BitVec.ofNat 64 wOff + _
    rw [Offset.add_add]
  | iv => simp [gtgt] at ht

/-- A block the call does not encipher is apart from what it changes. -/
theorem UPre.gcall_other {onW : Bool} {x : GBlk} (ht : gtgt onW x = false) (hx : x.ok G = true) :
    ∀ r ∈ [⟨gBA s₀ k onW, 16 * G⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀],
      (⟨gaddr (D32 s₀ k) (S s₀) (Iv s₀) x, 16⟩ : Region).Disjoint r := by
  obtain hk' : k < N s₀ := by omega_using [hG, hk]
  have hsub := hp.gBA_sub hG hG5 hk onW
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  cases x with
  | d j =>
    obtain rfl : onW = true := by simpa [gtgt] using ht
    obtain hj : j < G := by simpa [GBlk.ok] using hx
    rw [hp.gaddr_d hk']
    obtain dS : (⟨blk s₀ (k + j), 16⟩ : Region).Disjoint (scrR s₀) :=
      hp.data_scr.sub_left (UPre.data_sub (by omega_using [hj, hk]))
    rcases hr with rfl | rfl | rfl
    · exact dS.sub_right (sub_trans hsub (wR_sub s₀))
    · exact dS.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_data.symm.sub_left (UPre.data_sub (by omega_using [hj, hk]))
  | w j =>
    obtain rfl : onW = false := by simpa [gtgt] using ht
    obtain hj : j < G := by simpa [GBlk.ok] using hx
    obtain wS : Region.Sub ⟨wblk s₀ j, 16⟩ (scrR s₀) := hp.wblk_sub (by omega_using [hj, hG5])
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.symm.sub_left wS).sub_right (sub_trans hsub (seg_sub hk))
    · exact Offset.disjoint_base _ (d := wOff + 16 * j) (by unfold wOff; omega_using [])
        (by unfold wOff; omega_using [hj, hG5])
    · exact hp.b_scr.symm.sub_left wS
  | iv =>
    show Region.Disjoint ⟨State.addr (Iv s₀) + BitVec.ofNat 64 0, 16⟩ r
    rw [add0]
    rcases hr with rfl | rfl | rfl
    · cases onW
      · exact hp.iv_data.sub_right (sub_trans hsub (seg_sub hk))
      · exact hp.iv_scr.sub_right (sub_trans hsub (wR_sub s₀))
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm

/-- The blocks after the call: those of the call enciphered, the others as
they were. -/
theorem UPre.gcall_blks {F : BlkFn} {C : Nat → List Byte → Spec.Cbc.Cipher}
    (hf : ∀ R w m p, (F.f R w (Spec.Aes.stateAt m p)).toList = C R w (bytesAt m p 16)) {onW : Bool}
    {s₂ s₃ : State} (c : BlkPost F s₂ (W s₀) (gB s₀ k onW) (S s₀) (R s₀) G s₃) {b : GBlks}
    (hb : GBlkMem G (D32 s₀ k) (S s₀) (Iv s₀) s₂.mem b) (hsp : s₂.sp = s₀.sp)
    (hw : bytesAt s₂.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) = wK s₀) :
    GBlkMem G (D32 s₀ k) (S s₀) (Iv s₀) s₃.mem (gciph onW (C (R s₀) (wK s₀)) b) := by
  intro x hx
  unfold gciph
  by_cases ht : gtgt onW x = true
  · obtain ⟨j, hj, e⟩ := hp.gaddr_tgt hG hG5 hk ht hx
    rw [ite_eq_left ht, e, bytesAt_of_statesAtN c.out hj, hf, hw, ← e, hb x hx]
  · obtain ht : gtgt onW x = false := by simpa using ht
    obtain fr := c.frame
    rw [show below s₂.sp = belowR s₀ by rw [hsp]; rfl, hp.gB_addr hG hG5 hk onW] at fr
    rw [ite_eq_right (by simp [ht]), Proof.Cmac.bytesAt_frame fr (hp.gcall_other hG hG5 hk ht hx) (by decide), hb x hx]

end

/-! ## The arguments of the call -/

/-- What the arguments of the call leave. -/
structure GPreA (s₀ : State) (k : Nat) (onW : Bool) (G : Nat) (s s₂ : State) : Prop where
  pre : BlkCall s₂ (W s₀) (gB s₀ k onW) (S s₀) (R s₀) G
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₂.gpr r = s.gpr r
  sp : s₂.sp = s.sp
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr

theorem gArgs_wp {s₀ : State} (hp : UPre s₀) {k G : Nat} (hG : 0 < G) (hG5 : G ≤ 5) (hk : k + G ≤ N s₀)
    (henc : encodable (BitVec.ofNat 32 G) = true) {s : State} (h : Regs s₀ k s) (onW : Bool) :
    WP isa (.block (gArgs onW G)) s (GPreA s₀ k onW G s) := by
  have fin : ∀ {s₁ s₂ s₃ s₄ s₅ : State}, Upd s s₁ .r0 (s.gpr .r4) → Upd s₁ s₂ .r1 (s₁.gpr .r5) →
      Upd s₂ s₃ .r2 (gB s₀ k onW) → Upd s₃ s₄ .r3 (BitVec.ofNat 32 G) → Upd s₄ s₅ .r12 (s₄.gpr .r10) →
      GPreA s₀ k onW G s s₅ := by
    intro s₁ s₂ s₃ s₄ s₅ u₁ u₂ u₃ u₄ u₅
    obtain sp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
    obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    refine ⟨hp.grpCall hG hG5 hk onW ?_ ?_ ?_ ?_ ?_ (by rw [sp₅, h.sp]) (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]),
      fun r h0 h1 h2 h3 h12 => by rw [u₅.other _ h12, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0],
      sp₅, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        h.r4]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
        h.r5]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        h.r10]
  cases onW
  · show WP isa (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r7),
      .mov .r3 (.imm (BitVec.ofNat 32 G)), .mov .r12 (.reg .r10)]) s _
    refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
      wp_mov (op2_imm henc) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
    refine fin u₁ u₂ ?_ u₄ u₅
    rw [show gB s₀ k false = s₂.gpr .r7 by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r7]; rfl]
    exact u₃
  · show WP isa (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5),
      .dp .add .r2 .r10 (.imm (BitVec.ofNat 32 wOff)), .mov .r3 (.imm (BitVec.ofNat 32 G)),
      .mov .r12 (.reg .r10)]) s _
    refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
      wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm henc) fun s₄ u₄ =>
      wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
    refine fin u₁ u₂ ?_ u₄ u₅
    rw [show gB s₀ k true = s₂.gpr .r10 + BitVec.ofNat 32 wOff by
      rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r10]; rfl]
    exact u₃

/-! ## One group -/

/-- One group of `2 ^ lg` blocks takes the invariant from `k` blocks to
`k + 2 ^ lg`, and sets Z if no group is left. -/
theorem gBody_ok {M : Mode} {F : BlkFn} {C : Nat → List Byte → Spec.Cbc.Cipher} {gm : GMode} {lg : Nat}
    (hl : LevelOk M F C gm lg) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 2 ^ lg ≤ N s₀) {s : State}
    (h : WInv M s₀ k s) :
    WP isa (gBody (blkFrame F) gm lg) s fun s' =>
      WInv M s₀ (k + 2 ^ lg) s' ∧ s'.z = decide ((N s₀ - (k + 2 ^ lg)) / 2 ^ lg = 0) := by
  obtain hG : 0 < 2 ^ lg := Nat.two_pow_pos lg
  have hG5 := hl.g5
  obtain hk' : k < N s₀ := by omega_using [hG, hk]
  have hNlt : N s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt
  obtain lay : GLay (2 ^ lg) (D32 s₀ k) (S s₀) (Iv s₀) s.wr := by rw [h.regs.wr]; exact hp.glay hG hG5 hk
  obtain ⟨b₀, eb₀⟩ : ∃ b₀ : GBlks, b₀ = fun x => bytesAt s.mem (gaddr (D32 s₀ k) (S s₀) (Iv s₀) x) 16 := ⟨_, rfl⟩
  obtain hb₀ : GBlkMem (2 ^ lg) (D32 s₀ k) (S s₀) (Iv s₀) s.mem b₀ := fun x _ => by rw [eb₀]
  unfold gBody
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp lay h.regs.r7 h.regs.r10 h.regs.r6 hb₀ hl.pre) fun s₁ i₁ => ?_
  obtain rg₁ := h.regs.of i₁.regs i₁.sp i₁.rd i₁.wr
  refine WP.mono (gArgs_wp hp hG hG5 hk hl.encG rg₁ gm.onW) fun s₂ a => ?_
  refine WP.seq (WP.mono (blk_call F a.pre) fun s₃ c => ?_)
  -- The registers the call keeps.
  have sv : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s.gpr r := fun r hr hlr => by
    have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [c.saved r hr hlr, a.keep r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h12, i₁.regs r h12 hlr]
  obtain rg₃ : Regs s₀ k s₃ :=
    ⟨by rw [sv _ (by simp [preserved]) (by decide), h.regs.r4], by rw [sv _ (by simp [preserved]) (by decide), h.regs.r5],
      by rw [sv _ (by simp [preserved]) (by decide), h.regs.r6], by rw [sv _ (by simp [preserved]) (by decide), h.regs.r7],
      by rw [sv _ (by simp [preserved]) (by decide), h.regs.r10], by rw [c.sp, a.sp, rg₁.sp],
      by rw [c.rd, a.rd, rg₁.rd], by rw [c.wr, a.wr, rg₁.wr]⟩
  -- Memory up to the call, and the blocks after it.
  obtain f₁ : Frame (gStep s₀ k (2 ^ lg)) s.mem s₁.mem := i₁.frame.sub (hp.gRegions_step hG hG5 hk)
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := h.big.trans (f₁.sub fun r hr => by
    obtain ⟨r', hr', hs⟩ := gStep_sub hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, hs⟩
    · exact ⟨dataR s₀, by simp, hs⟩
    · exact ⟨scrR s₀, by simp, sub_trans hs (Region.sub_prefix (by decide))⟩
    · exact ⟨belowR s₀, by simp, hs⟩
    · exact ⟨scrR s₀, by simp, sub_trans hs (wR_sub s₀)⟩)
  obtain hw : bytesAt s₂.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) = wK s₀ := by
    rw [a.mem]; exact hp.sched_bytes big₁
  obtain hb₃ := hp.gcall_blks hG hG5 hk hl.hf c (b := grunOps (gm.pre (2 ^ lg)) b₀) (by rw [a.mem]; exact i₁.blks)
    (by rw [a.sp, rg₁.sp]) hw
  obtain f₃ : Frame (gStep s₀ k (2 ^ lg)) s₁.mem s₃.mem := by
    obtain fr := c.frame
    rw [show below s₂.sp = belowR s₀ by rw [a.sp, rg₁.sp]; rfl, hp.gB_addr hG hG5 hk gm.onW, a.mem] at fr
    exact fr.sub (hp.call_step hG hG5 hk gm.onW)
  obtain lay₃ : GLay (2 ^ lg) (D32 s₀ k) (S s₀) (Iv s₀) s₃.wr := by rw [rg₃.wr]; exact hp.glay hG hG5 hk
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp lay₃ rg₃.r7 rg₃.r10 rg₃.r6 hb₃ hl.post) fun s₄ i₄ => ?_
  obtain rg₄ := rg₃.of i₄.regs i₄.sp i₄.rd i₄.wr
  obtain f₄ : Frame (gStep s₀ k (2 ^ lg)) s.mem s₄.mem :=
    (f₁.trans f₃).trans (i₄.frame.sub (hp.gRegions_step hG hG5 hk))
  obtain r8₄ : s₄.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [i₄.regs _ (by decide) (by decide), sv _ (by simp [preserved]) (by decide), h.r8]
  obtain r11₄ : s₄.gpr .r11 = s₀.gpr .r11 := by
    rw [i₄.regs _ (by decide) (by decide), sv _ (by simp [preserved]) (by decide), h.r11]
  -- What the group computed.
  obtain hys : (((blks s₀).drop k).take (2 ^ lg)).length = 2 ^ lg := by
    rw [List.length_take, List.length_drop, length_blocksAt]; omega_using [hk]
  obtain ⟨hout, hiv⟩ := hl.sim (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k) (((blks s₀).drop k).take (2 ^ lg)) b₀
    hys (by rw [← hb₀ .iv rfl]; show bytesAt s.mem (State.addr (Iv s₀) + BitVec.ofNat 64 0) 16 = _; rw [add0]; exact h.iv)
    (fun j hj => by
      rw [List.getElem?_take, ite_eq_left hj, List.getElem?_drop,
        h.blockAt (Nat.le_add_right k j) (by omega_using [hj, hk]), ← hb₀ (.d j) (by simpa [GBlk.ok] using hj),
        hp.gaddr_d hk'])
  rw [← List.take_add] at hout hiv
  obtain hl' : (outK M s₀ k).length = k := by
    rw [outK, M.length_out, List.length_take, length_blocksAt]; omega_using [hk']
  obtain hdrop : (outK M s₀ k ++ (blks s₀).drop k).drop (k + 2 ^ lg) = (blks s₀).drop (k + 2 ^ lg) := by
    rw [← List.drop_drop, List.drop_left' hl', List.drop_drop]
  -- On to the next group.
  show WP isa (.block [.dp .add .r7 .r7 (.imm (BitVec.ofNat 32 (16 * 2 ^ lg))),
    .dp .sub .r8 .r8 (.imm (BitVec.ofNat 32 (2 ^ lg))), .mov .r12 (.shifted .r8 .lsr lg),
    .cmp .r12 (.imm 0)]) s₄ _
  refine wp_add (op2_imm hl.encA) fun s₅ u₅ => wp_sub (op2_imm hl.encG) fun s₆ u₆ =>
    wp_mov (op2_lsr hl.sh) fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → s₈.gpr r = s₄.gpr r := fun r h7 h8 h12 => by
    rw [f₈.gpr, u₇.other _ h12, u₆.other _ h8, u₅.other _ h7]
  obtain m₈ : s₈.mem = s₄.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem]
  obtain r8₈ : s₈.gpr .r8 = BitVec.ofNat 32 (N s₀ - (k + 2 ^ lg)) := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), r8₄, sub_ofNat (by omega_using [hk]),
      Nat.sub_sub]
  refine ⟨⟨⟨by rw [g _ (by decide) (by decide) (by decide), rg₄.r4],
      by rw [g _ (by decide) (by decide) (by decide), rg₄.r5],
      by rw [g _ (by decide) (by decide) (by decide), rg₄.r6], ?_,
      by rw [g _ (by decide) (by decide) (by decide), rg₄.r10], by rw [f₈.sp, u₇.sp, u₆.sp, u₅.sp, rg₄.sp],
      by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, rg₄.rd], by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, rg₄.wr]⟩, r8₈,
      by rw [g _ (by decide) (by decide) (by decide), r11₄], ?_, ?_, ?_⟩, ?_⟩
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, rg₄.r7,
      Offset.add_add_eq _ (c := 16 * (k + 2 ^ lg)) (by omega_using [])]
  · rw [m₈]; exact h.frame.trans (f₄.sub (gStep_sub hk))
  · show _ = M.out (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take (k + 2 ^ lg)) ++ _
    rw [m₈, hout]
    rw [blocksAt_splice (m := s.mem) hk ((List.range (2 ^ lg)).map fun j =>
        gstep gm (2 ^ lg) (C (R s₀) (wK s₀)) b₀ (.d j)) (by simp) (fun j hj => ?_) (fun i hi ho => ?_), h.data,
      List.take_left' hl', hdrop]
    · rw [List.getElem?_map, List.getElem?_range hj, Option.map_some]
      show some _ = some (bytesAt s₄.mem (blk s₀ (k + j)) 16)
      rw [← hp.gaddr_d hk' (S s₀) (Iv s₀), i₄.blks (.d j) (by simpa [GBlk.ok] using hj)]
      rfl
    · exact Proof.Cmac.bytesAt_frame f₄ (hp.out_step hG hG5 hk hi ho) (by decide)
  · show _ = M.chain (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take (k + 2 ^ lg))
    rw [m₈, hiv, ← add0 (State.addr (Iv s₀))]
    exact i₄.blks .iv rfl
  · rw [z₈, u₇.gpr, show s₆.gpr .r8 = s₈.gpr .r8 by rw [f₈.gpr, u₇.other _ (by decide)], r8₈,
      ofNat_shr (by omega_using [hNlt])]
    exact cmp0 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNlt]))

/-! ## The levels -/

section
variable {M : Mode} {F : BlkFn} {C : Nat → List Byte → Spec.Cbc.Cipher} {gm : GMode} {s₀ : State}

/-- Whether a group of `2 ^ lg` blocks is left. -/
theorem ghead_wp {lg : Nat} (hlg : 1 ≤ lg ∧ lg ≤ 31) {k : Nat} {s : State} (h : WInv M s₀ k s) :
    WP isa (.block (groupsLeft lg)) s fun s' => WInv M s₀ k s' ∧ s'.z = decide ((N s₀ - k) / 2 ^ lg = 0) := by
  have hNlt : N s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt
  refine wp_mov (op2_lsr hlg) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ⟨?_, ?_⟩
  · exact h.of_regs (fun r h12 _ => by rw [f₂.gpr, u₁.other _ h12]) (by rw [f₂.sp, u₁.sp]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr]) (by rw [f₂.mem, u₁.mem])
  · rw [z₂, u₁.gpr, h.r8, ofNat_shr (by omega_using [hNlt])]
    exact cmp0 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNlt]))

/-- The groups of `2 ^ lg` blocks. -/
theorem gLevel_ok {lg : Nat} (hl : LevelOk M F C gm lg) (hp : UPre s₀) {k : Nat} (hk : k ≤ N s₀) {s : State}
    (h : WInv M s₀ k s) :
    WP isa (gLevel (blkFrame F) gm lg) s fun s' => ∃ k', k' ≤ N s₀ ∧ WInv M s₀ k' s' := by
  obtain hG : 0 < 2 ^ lg := Nat.two_pow_pos lg
  unfold gLevel
  refine WP.seq (WP.mono (ghead_wp hl.sh h) fun s₁ ⟨h₁, z₁⟩ => ?_)
  have ev : isa.eval .eq s₁ = some (decide ((N s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, z₁]
  by_cases hz : (N s₀ - k) / 2 ^ lg = 0
  · exact WP.ite true (by rw [ev]; simp [hz]) (fun _ => WP.block_nil ⟨k, hk, h₁⟩) (fun h => by cases h)
  · refine WP.ite false (by rw [ev]; simp [hz]) (fun h => by cases h) fun _ => ?_
    obtain hkG : k + 2 ^ lg ≤ N s₀ := by
      rw [Nat.div_eq_zero_iff_lt hG] at hz; omega_using [hz, hk]
    refine WP.loop (M := isa) (body := gBody (blkFrame F) gm lg) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j + 2 ^ lg ≤ N s₀ ∧ WInv M s₀ j t) ?_
      (N s₀ - k) s₁ ⟨k, rfl, hkG, h₁⟩
    rintro n t ⟨j, rfl, hj, ht⟩
    refine WP.mono (gBody_ok hl hp hj ht) fun t' ⟨h', hz'⟩ => ?_
    have ev' : isa.eval .ne t' = some !decide ((N s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0) := by
      show VG.Arm.eval .ne t' = _; rw [eval_ne, hz']
    by_cases hz'' : (N s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0
    · left
      exact ⟨by rw [ev']; simp [hz''], j + 2 ^ lg, hj, h'⟩
    · right
      refine ⟨by rw [ev']; simp [hz''], N s₀ - (j + 2 ^ lg), by omega_using [hj, hG], j + 2 ^ lg, rfl, ?_, h'⟩
      rw [Nat.div_eq_zero_iff_lt hG] at hz''; omega_using [hz'', hj]

/-- The groups of every level. -/
theorem gLevels_ok {lgs : List Nat} (hl : ∀ lg ∈ lgs, LevelOk M F C gm lg) (hp : UPre s₀) {k : Nat}
    (hk : k ≤ N s₀) {s : State} (h : WInv M s₀ k s) :
    WP isa (gLevels (blkFrame F) gm lgs) s fun s' => ∃ k', k' ≤ N s₀ ∧ WInv M s₀ k' s' := by
  induction lgs generalizing k s with
  | nil => exact WP.block_nil ⟨k, hk, h⟩
  | cons lg lgs ih =>
    show WP isa (.seq (gLevel (blkFrame F) gm lg) (gLevels (blkFrame F) gm lgs)) s _
    refine WP.seq (WP.mono (gLevel_ok (hl lg List.mem_cons_self) hp hk h) fun s₁ ⟨k₁, hk₁, h₁⟩ => ?_)
    exact ih (fun lg' h' => hl lg' (List.mem_cons_of_mem _ h')) hk₁ h₁

/-! ## The blocks left, and the whole function -/

/-- Whether a block is left. -/
theorem gtest_wp {k : Nat} {s : State} (h : WInv M s₀ k s) :
    WP isa (.block [.cmp .r8 (.imm 0)]) s fun s' => WInv M s₀ k s' ∧ s'.z = decide (N s₀ - k = 0) := by
  have hNlt : N s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt
  refine wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ⟨?_, ?_⟩
  · exact h.of_regs (fun r _ _ => by rw [f₁.gpr]) f₁.sp f₁.rd f₁.wr f₁.mem
  · rw [z₁, h.r8]; exact cmp0 (by omega_using [hNlt])

/-- The blocks the groups left, one at a time, and the epilogue. -/
theorem gtail_wp {body : Prog isa} (hb : BodyOk M body) (hp : UPre s₀) {k : Nat} (hk : k ≤ N s₀) {s : State}
    (h : WInv M s₀ k s) :
    WP isa (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))) s
      fun s' => abiPreserved s₀ s' ∧ (modeArm M).post s₀ s' := by
  refine WP.seq (WP.mono (gtest_wp h) fun s₁ ⟨h₁, z₁⟩ => ?_)
  obtain hpa := hp.anch s₁.mem
  obtain hL := h₁.toL hp
  obtain eN := anch_N hp s₁.mem
  have ev : isa.eval .eq s₁ = some (decide (N s₀ - k = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, z₁]
  have fin : ∀ s₂, LInv M (anch s₀ s₁.mem) (N (anch s₀ s₁.mem)) s₂ →
      WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ (modeArm M).post s₀ s' := fun s₂ h₂ =>
    WP.mono (epilogue_wp hpa h₂) fun s' ⟨ha, hq⟩ => ⟨ha, post_anch hp s₁.mem hq⟩
  by_cases hz : N s₀ - k = 0
  · refine WP.seq (WP.ite true (by rw [ev]; simp [hz]) (fun _ => WP.block_nil ?_) (fun h => by cases h))
    refine fin s₁ ?_
    rw [eN, show N s₀ = k by omega_using [hz, hk]]; exact hL
  · refine WP.seq (WP.ite false (by rw [ev]; simp [hz]) (fun h => by cases h) fun _ => ?_)
    exact WP.mono (loop_ok hb hpa (by rw [eN]; omega_using [hz]) hL) fin

/-- The whole function, in groups: `whole`'s contract. -/
theorem wholeG_wp {lgs : List Nat} {body : Prog isa} (hl : ∀ lg ∈ lgs, LevelOk M F C gm lg) (hb : BodyOk M body)
    (h0 : (modeArm M).pre s₀) :
    WP isa (wholeG (blkFrame F) gm lgs body) s₀ fun s' => abiPreserved s₀ s' ∧ (modeArm M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, _⟩ =>
    WP.seq (WP.mono (gLevels_ok hl hp (Nat.zero_le _) h₁.toW) fun s₂ ⟨k, hk, h₂⟩ => gtail_wp hb hp hk h₂))

/-- The levels of a mode whose groups of 4 and of 2 blocks compute it. -/
theorem levels_of (hpre : ∀ lg ∈ groupLevels, (gm.pre (2 ^ lg)).all (gopOk (2 ^ lg)) = true)
    (hpost : ∀ lg ∈ groupLevels, (gm.post (2 ^ lg)).all (gopOk (2 ^ lg)) = true)
    (hsim : ∀ lg ∈ groupLevels, GSim M C gm (2 ^ lg))
    (hf : ∀ R w m p, (F.f R w (Spec.Aes.stateAt m p)).toList = C R w (bytesAt m p 16)) :
    ∀ lg ∈ groupLevels, LevelOk M F C gm lg := by
  intro lg h
  have h' := h
  simp only [groupLevels, List.mem_cons, List.not_mem_nil, or_false] at h'
  refine ⟨?_, ?_, ?_, ?_, hpre lg h, hpost lg h, hsim lg h, hf⟩ <;> rcases h' with rfl | rfl <;> decide

end

end VG.Proof.AesCbc.Arm
