module

public import VerifiedGarbage.Impl.Modes.Arm.Wide
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Modes.Arm.Ctr
import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.Modes.Arm.WideOps
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Modes.Arm.WideOps
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.Ctr
meta import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Modes.Arm.Wide`, which only this module used -/

section

/-!
# The modes a group of blocks at a time on ARMv7: the groups and the whole function

`seqW_wp`: `Core.seqW c M wm lgs wb` meets `seqArm c S M`, the contract of
`Core.seq c M` (`SeqBody.lean`), for a core `c` that takes no working space,
where `S` is the core's `S₀ : CoreSpec c` with `wb` more bytes of stack
(`CoreSpec.deeper`, `Deep`): the buffer of the groups is on the stack, so
what a group writes there is within the stack below the stack pointer that
`seqArm` lets the function change, and the invariant of `Core.seq`'s loop
(`LInv`) holds of the groups too, in the frame that holds the buffer
(`WInv`). The blocks left after the groups are `Core.seq`'s loop's, with
its own proof (`loop_ok`), and so are the prologue and the epilogue.

`wbody_ok`: one group of `G = 2 ^ lg` blocks takes the invariant from `k`
blocks to `k + G`. The group's data blocks, the buffer's blocks and the
chaining and spare blocks are `WBlks` in memory (`WBlkMem`) throughout: the
operations before the call (`wopsCode_wp`), the call of the core on `G`
blocks (`callN_wp`), and the operations after it leave them as `wstep` says,
which is what `G` steps of the mode one block at a time leave (`WideSim`:
each wide mode's own lemma, by evaluating both for its `G`).
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf over)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_sub wp_cmp op2_imm op2_reg op2_lsr cmp0 ofNat_shr eval_eq
  eval_ne)

/-! ## A core with more stack -/

/-- The callee's precondition with less stack reserved. -/
theorem EcbPre.shallow {c : Core} {keyLen stack W : Nat} {rok : BitVec 32 → Prop} {s : State}
    (h : EcbPre c keyLen (stack + W) rok s) : EcbPre c keyLen stack rok s where
  stk := Nat.le_trans (Nat.le_add_right _ _) h.stk
  rd := h.rd
  wr := h.wr
  kd := h.kd
  bk := h.bk.sub_left (VG.Offset.sub_below _ (Nat.le_add_right _ _) (by omega_arith))
  bd := h.bd.sub_left (VG.Offset.sub_below _ (Nat.le_add_right _ _) (by omega_arith))
  fK := h.fK
  fD := h.fD
  rr := h.rr
  a3 := h.a3

/-- What the modes need of a core that takes no working space, with `W`
more bytes of stack below the stack pointer than its code uses. -/
def CoreSpec.deeper {c : Core} (S : CoreSpec c) (W : Nat) (h0 : c.stackScratch = 0) : CoreSpec c :=
  { S with
    stack := S.stack + W
    depth := Nat.le_trans S.depth (Nat.le_add_right _ _)
    pre_of := fun hs s h => S.pre_of hs s h.shallow
    post_of := fun hs s s' h hp => S.post_of hs s s' h.shallow hp
    pre_ofS := fun hs => absurd h0 hs
    post_ofS := fun hs => absurd h0 hs
    depthS := fun hs => absurd h0 hs }

/-- `S` is `S₀` with `W` more bytes of stack. -/
structure Deep {c : Core} (S₀ S : CoreSpec c) (W : Nat) : Prop where
  stack : S.stack = S₀.stack + W
  keyLen : S.keyLen = S₀.keyLen
  rok : S.rok = S₀.rok
  ciphAt : S.ciphAt = S₀.ciphAt

theorem CoreSpec.deeper_deep {c : Core} (S : CoreSpec c) (W : Nat) (h0 : c.stackScratch = 0) :
    Deep S (S.deeper W h0) W := ⟨rfl, rfl, rfl, rfl⟩

/-! ## A call on a group of blocks -/

/-- What a call of the core on the `G` blocks at `B` needs, from the
caller's state `s`: as `CallPre`, for a core that takes no working space. -/
structure CallPreN (c : Core) (S : CoreSpec c) (s : State) (K R B : BitVec 32) (G : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : c.rounds = true → s.gpr .r1 = R
  rok : c.rounds = true → S.rok R
  rd : s.gpr c.dReg = B
  rn : s.gpr c.nReg = BitVec.ofNat 32 G
  hG : G < 2 ^ 32
  a3 : ∀ k, c.arg3 = some k → s.gpr .r3 = BitVec.ofNat 32 k
  stk : S.stack ≤ s.sp.toNat
  fK : K.toNat + S.keyLen ≤ 2 ^ 32
  fB : B.toNat + c.bs * G ≤ 2 ^ 32
  kb : Region.Disjoint ⟨State.addr K, S.keyLen⟩ ⟨State.addr B, c.bs * G⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr K, S.keyLen⟩
  bb : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr B, c.bs * G⟩
  rK : Covers [⟨State.addr K, S.keyLen⟩] (s.rd ++ s.wr)
  wB : Covers [⟨State.addr B, c.bs * G⟩] s.wr

/-- What the call leaves: as `CallPost`, with the `G` blocks their images
under the cipher. -/
structure CallPostN (c : Core) (S : CoreSpec c) (s : State) (K R B : BitVec 32) (G : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr B, c.bs * G⟩, ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩] s.mem s'.mem
  out : blocksOf c.bs s'.mem (State.addr B) G =
    (blocksOf c.bs s.mem (State.addr B) G).map (S.ciphAt s.mem (State.addr K) R)

section
variable {c : Core} {S : CoreSpec c} {s : State} {K R B : BitVec 32} {G : Nat}

theorem CallPreN.toNat_G (h : CallPreN c S s K R B G) : (BitVec.ofNat 32 G).toNat = G := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.hG]

/-- The callee's precondition, on the state it is entered in. -/
theorem CallPreN.ecbPre (h : CallPreN c S s K R B G) :
    EcbPre c S.keyLen S.stack S.rok
      (s.callEntry.withRegions [⟨State.addr K, S.keyLen⟩] [⟨State.addr B, c.bs * G⟩]) := by
  have hd := c.dReg_ne
  have hn := c.nReg_ne
  refine ⟨by simpa using h.stk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hr => ?_, fun k hk => ?_⟩ <;>
    try simp only [entry_gpr _ _ _ (show Reg.r0 ≠ .r12 by decide) (by decide), entry_gpr _ _ _ hd.1 hd.2.1,
      entry_gpr _ _ _ hn.1 hn.2.1, h.r0, h.rd, h.rn, h.toNat_G, Nat.mul_comm G c.bs, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp]
  · exact h.kb
  · exact h.bk
  · exact h.bb
  · exact h.fK
  · exact h.fB
  · rw [entry_gpr _ _ _ (by decide) (by decide), h.r1 hr]; exact h.rok hr
  · rw [entry_gpr _ _ _ (by decide) (by decide), h.a3 k hk]

/-- The call of a core without a working space, on `G` blocks. -/
theorem callN_wp (S : CoreSpec c) (h : CallPreN c S s K R B G) (hs : c.stackScratch = 0) :
    WP isa (.call c.name c.code) s (CallPostN c S s K R B G) := by
  refine WP.callF S.correct (S.pre_of hs _ h.ecbPre) (Covers.append_left h.rK (Covers.right h.wB))
    h.wB (Nat.le_trans S.depth h.stk) fun s' hrd hwr hsp hf hsv hpost => ⟨hrd, hwr, hsp, hsv, ?_, ?_⟩
  · refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩, by simp, ?_⟩
      have := belowA_sub (sp := s.sp) (b := S.stack) S.depth h.stk
      rwa [belowA, belowA, addr_sub' h.stk] at this
  · have e := S.post_of hs _ _ h.ecbPre hpost
    have hd := c.dReg_ne
    have hn := c.nReg_ne
    simp only [entry_gpr _ _ _ (show Reg.r0 ≠ .r12 by decide) (by decide), entry_gpr _ _ _ hd.1 hd.2.1,
      entry_gpr _ _ _ hn.1 hn.2.1, entry_gpr _ _ _ (show Reg.r1 ≠ .r12 by decide) (by decide),
      h.r0, h.rd, h.rn, h.toNat_G, State.withRegions_mem, State.callEntry_mem] at e
    rw [e]
    cases hr : c.rounds
    · rw [S.ciphAt_R hr _ _ _ R]
    · rw [h.r1 hr]

end

/-! ## Steps of a mode, and blocks in memory -/

theorem runSeq_append (M : Mode) (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs ys : List (List Byte)), runSeq M ciph b (xs ++ ys) =
      ((runSeq M ciph b xs).1 ++ (runSeq M ciph (runSeq M ciph b xs).2 ys).1,
        (runSeq M ciph (runSeq M ciph b xs).2 ys).2)
  | _, [], _ => rfl
  | b, x :: xs, ys => by
    simp only [List.cons_append, runSeq, runSeq_append M ciph _ xs ys]

/-- The steps on blocks do not read the data block they start from. -/
theorem runSeq_d (M : Mode) (ciph : Spec.Cbc.Cipher) (b : Blks) :
    ∀ ys : List (List Byte), ys ≠ [] → runSeq M ciph b ys = runSeq M ciph ⟨[], b.o, b.t⟩ ys
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem getElem?_blocksOf (L : Nat) (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (blocksOf L m p n)[i]? = some (bytesAt m (p + BitVec.ofNat 64 (L * i)) L) := by
  rw [List.getElem?_eq_getElem (by rw [length_blocksOf]; exact hi), getElem_blocksOf _ _ _ hi]

/-- The blocks after the `G` from block `k` changed. -/
theorem blocksOf_splice {L : Nat} {m m' : Mem} {p : Addr} {n k G : Nat} (hk : k + G ≤ n)
    (ys : List (List Byte)) (hy : ys.length = G)
    (hin : ∀ j < G, ys[j]? = some (bytesAt m' (p + BitVec.ofNat 64 (L * (k + j))) L))
    (hout : ∀ i < n, i < k ∨ k + G ≤ i →
      bytesAt m' (p + BitVec.ofNat 64 (L * i)) L = bytesAt m (p + BitVec.ofNat 64 (L * i)) L) :
    blocksOf L m' p n = (blocksOf L m p n).take k ++ ys ++ (blocksOf L m p n).drop (k + G) := by
  have lt : ((blocksOf L m p n).take k).length = k := by
    rw [List.length_take, length_blocksOf]; omega_using [hk]
  apply List.ext_getElem?
  intro i
  by_cases h1 : i < k
  · rw [List.append_assoc, List.getElem?_append_left (by rw [lt]; exact h1), List.getElem?_take, ite_eq_left h1,
      getElem?_blocksOf _ _ _ (by omega_using [h1, hk]), getElem?_blocksOf _ _ _ (by omega_using [h1, hk]),
      hout i (by omega_using [h1, hk]) (.inl h1)]
  · by_cases h2 : i < k + G
    · rw [List.getElem?_append_left (by rw [List.length_append, lt, hy]; exact h2),
        List.getElem?_append_right (by rw [lt]; omega_using [h1]), lt, hin _ (by omega_using [h1, h2]),
        getElem?_blocksOf _ _ _ (by omega_using [h2, hk]), show k + (i - k) = i by omega_using [h1]]
    · rw [List.getElem?_append_right (by rw [List.length_append, lt, hy]; omega_using [h2]), List.length_append,
        lt, hy, List.getElem?_drop, show k + G + (i - (k + G)) = i by omega_using [h2]]
      by_cases h3 : i < n
      · rw [getElem?_blocksOf _ _ _ h3, getElem?_blocksOf _ _ _ h3, hout i h3 (.inr (by omega_using [h2]))]
      · rw [List.getElem?_eq_none (by rw [length_blocksOf]; omega_using [h3]),
          List.getElem?_eq_none (by rw [length_blocksOf]; omega_using [h3])]

theorem grp_le {L k G n : Nat} (h : k + G ≤ n) : L * k + L * G ≤ n * L := by
  rw [← Nat.mul_add, Nat.mul_comm]; exact Nat.mul_le_mul_right _ h

/-! ## What a group computes -/

/-- The cipher on the `G` blocks of the buffer (`onW`) or of the data. -/
def wciph (onW : Bool) (G : Nat) (ciph : Spec.Cbc.Cipher) (b : WBlks) : WBlks
  | .w j => if onW && decide (j < G) then ciph (b (.w j)) else b (.w j)
  | .d j => if !onW && decide (j < G) then ciph (b (.d j)) else b (.d j)
  | x => b x

/-- A group's work: the operations before the call, the cipher on its
blocks, and the operations after it. -/
def wstep (wm : WMode) (G : Nat) (ciph : Spec.Cbc.Cipher) (b : WBlks) : WBlks :=
  wrunOps (wm.post G) (wciph wm.onW G ciph (wrunOps (wm.pre G) b))

/-- A group of `G` blocks of `wm` leaves the data blocks, the chaining block
and the spare block as `G` steps of `M` do. -/
structure WideSim (M : Mode) (wm : WMode) (G : Nat) : Prop where
  sim : ∀ (ciph : Spec.Cbc.Cipher) (b : WBlks),
    (List.range G).map (fun j => wstep wm G ciph b (.d j)) =
        (runSeq M ciph ⟨[], b .o, b .t⟩ ((List.range G).map fun j => b (.d j))).1 ∧
      wstep wm G ciph b .o = (runSeq M ciph ⟨[], b .o, b .t⟩ ((List.range G).map fun j => b (.d j))).2.o ∧
      wstep wm G ciph b .t = (runSeq M ciph ⟨[], b .o, b .t⟩ ((List.range G).map fun j => b (.d j))).2.t

/-- What the groups of `G` blocks of `wm` need, for the mode `M` on the
core `c`: operations on different blocks of the group (and 16-byte blocks
where a counter is stepped), which compute `G` steps of `M`. -/
structure WideOk (c : Core) (M : Mode) (wm : WMode) (G : Nat) : Prop where
  pos : 0 < G
  byte : M.byte = false
  pre : (wm.pre G).all (wopOk c.bs G) = true
  post : (wm.post G).all (wopOk c.bs G) = true
  sim : WideSim M wm G

/-- What the level of groups of `2 ^ lg` blocks needs: `WideOk`, a shift
and immediates that can be encoded, and room in the buffer of `wb` bytes. -/
structure LevelOk (c : Core) (M : Mode) (wm : WMode) (wb lg : Nat) : Prop where
  ok : WideOk c M wm (2 ^ lg)
  sh : 1 ≤ lg ∧ lg ≤ 31
  fit : c.bs * 2 ^ lg ≤ wb
  encG : encodable (BitVec.ofNat 32 (2 ^ lg)) = true
  encB : encodable (BitVec.ofNat 32 (c.bs * 2 ^ lg)) = true

/-- The blocks of a group, as memory has them. -/
def wmem (c : Core) (D S W : BitVec 32) (m : Mem) : WBlks := fun x => bytesAt m (waddr c D S W x) c.bs

theorem wmem_blk (c : Core) (G : Nat) (D S W : BitVec 32) (m : Mem) : WBlkMem c G D S W m (wmem c D S W m) :=
  fun _ _ => rfl

/-! ## The invariant, in the buffer's frame -/

/-- The buffer's address: the stack pointer in its frame. -/
abbrev Wp (wb : Nat) (s₀ : State) : BitVec 32 := s₀.sp - BitVec.ofNat 32 wb
/-- The buffer. -/
abbrev wR (wb : Nat) (s₀ : State) : Region := ⟨State.addr (Wp wb s₀), wb⟩

/-- The invariant after `k` blocks, in the buffer's frame: `LInv` of the
state as the frame's end leaves it, with the stack pointer at the buffer,
which is writable. -/
structure WInv (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  inv : LInv c S M s₀ k (freed wb s)
  sp : s.sp = Wp wb s₀
  wr : s.wr = wR wb s₀ :: s₀.wr

theorem freed_allocated (wb : Nat) (s : State) : freed wb (allocated wb s) = s := by
  cases s
  simp only [freed, allocated, BitVec.sub_add_cancel, List.tail_cons]

/-- The invariant on entry to the buffer's frame. -/
theorem LInv.toW {wb : Nat} {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} {k : Nat} {s : State}
    (h : LInv c S M s₀ k s) : WInv wb c S M s₀ k (allocated wb s) :=
  ⟨by rw [freed_allocated]; exact h, by show s.sp - _ = _; rw [h.sp],
    by show _ :: s.wr = _; rw [h.sp, h.wr]⟩

theorem LInv.congr {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} {k : Nat} {s s' : State}
    (h : LInv c S M s₀ k s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : LInv c S M s₀ k s' :=
  ⟨by rw [hg]; exact h.r4, by rw [hg]; exact h.r5, by rw [hg]; exact h.r6, by rw [hg]; exact h.r7,
    by rw [hg]; exact h.r8, fun hr => by rw [hg]; exact h.r11 hr, by rw [hsp]; exact h.sp, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr, by rw [hm]; exact h.frame, by rw [hm]; exact h.data, by rw [hm]; exact h.o,
    by rw [hm]; exact h.t⟩

section
variable {c : Core} {S₀ S : CoreSpec c} {M : Mode} {s₀ : State} {wb : Nat}

/-- Block `i`, not yet enciphered, from the invariant. -/
theorem LInv.blockAt {k : Nat} {s : State} (h : LInv c S M s₀ k s) {i : Nat} (hki : k ≤ i) (hi : i < N c s₀) :
    (xs c s₀ M)[i]? =
      some (bytesAt s.mem (State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * i)) (c.ds M)) := by
  have hl : (rK S s₀ M k).1.length = k := by
    rw [runSeq_length, List.length_take, length_blocksOf]; omega_using [hki, hi]
  have := congrArg (·[i]?) h.data
  simp only [getElem?_blocksOf _ _ _ hi,
    List.getElem?_append_right (show (rK S s₀ M k).1.length ≤ i by omega_using [hl, hki]), hl,
    List.getElem?_drop, show k + (i - k) = i by omega_using [hki]] at this
  rw [show (xs c s₀ M)[i]? = _ from getElem?_blocksOf _ _ _ hi]
  exact this.symm

/-- The invariant, from its parts on the state in the frame. -/
theorem WInv.mk' {k : Nat} {s : State} (r4 : s.gpr .r4 = Kp s₀) (r5 : s.gpr .r5 = Ivp c s₀)
    (r6 : s.gpr .r6 = Dp c s₀ + BitVec.ofNat 32 (c.ds M * k)) (r7 : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k))
    (r8 : s.gpr .r8 = Sc c s₀) (r11 : c.rounds = true → s.gpr .r11 = Rp s₀) (sp : s.sp = Wp wb s₀)
    (rd : s.rd = s₀.rd) (wr : s.wr = wR wb s₀ :: s₀.wr)
    (frame : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) s.mem)
    (data : blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀) = (rK S s₀ M k).1 ++ (xs c s₀ M).drop k)
    (o : bytesAt s.mem (oA c s₀) c.bs = (rK S s₀ M k).2.o)
    (t : bytesAt s.mem (tA c s₀) c.bs = (rK S s₀ M k).2.t) : WInv wb c S M s₀ k s :=
  ⟨⟨r4, r5, r6, r7, r8, r11, by show s.sp + _ = _; rw [sp]; exact BitVec.sub_add_cancel _ _, rd,
    by show s.wr.tail = _; rw [wr]; rfl, frame, data, o, t⟩, sp, wr⟩

theorem UPre.wb_le (hp : UPre c S M s₀) (hd : Deep S₀ S wb) : wb ≤ s₀.sp.toNat := by
  have := hp.stk; rw [hd.stack] at this; omega_using [this]

theorem UPre.wp_toNat (hp : UPre c S M s₀) (hd : Deep S₀ S wb) : (Wp wb s₀).toNat = s₀.sp.toNat - wb :=
  sub_toNat' (hp.wb_le hd)

theorem UPre.wp_addr (hp : UPre c S M s₀) (hd : Deep S₀ S wb) :
    State.addr (Wp wb s₀) = State.addr s₀.sp - BitVec.ofNat 64 wb := addr_sub' (hp.wb_le hd)

/-- The buffer, within the stack the contract reserves. -/
theorem UPre.buf_sub (hp : UPre c S M s₀) (hd : Deep S₀ S wb) {n : Nat} (hn : n ≤ wb) :
    Region.Sub ⟨State.addr (Wp wb s₀), n⟩ (belowR S s₀) := by
  rw [hp.wp_addr hd]
  exact VG.Offset.sub_below _ (by rw [hd.stack]; omega_arith) (by rw [hd.stack]; omega_using [hn])

/-- The callee's stack below the buffer, within the stack the contract reserves. -/
theorem UPre.callee_sub (hp : UPre c S M s₀) (hd : Deep S₀ S wb) :
    Region.Sub ⟨State.addr (Wp wb s₀) - BitVec.ofNat 64 S₀.stack, S₀.stack⟩ (belowR S s₀) := by
  rw [hp.wp_addr hd, BitVec.sub_sub, ← BitVec.ofNat_add, show wb + S₀.stack = S.stack by rw [hd.stack, Nat.add_comm]]
  exact Region.sub_prefix (by rw [hd.stack]; omega_arith)

/-- The group's data, within the data. -/
theorem UPre.grp_sub_data (hp : UPre c S M s₀) (hb : M.byte = false) {k G : Nat} (hG : 0 < G)
    (hk : k + G ≤ N c s₀) : Region.Sub ⟨State.addr (Dk s₀ c M k), c.bs * G⟩ (dataR c s₀ M) := by
  rw [hp.dk_addr (by omega_using [hG, hk])]
  exact VG.Offset.sub_base _ (by rw [ds_of c hb]; exact grp_le hk)

/-- A block of the data outside the group, apart from the group's. -/
theorem UPre.blk_grp (hp : UPre c S M s₀) (hb : M.byte = false) {k G i : Nat} (hG : 0 < G) (hk : k + G ≤ N c s₀)
    (hi : i < N c s₀) (ho : i < k ∨ k + G ≤ i) :
    Region.Disjoint ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * i), c.ds M⟩
      ⟨State.addr (Dk s₀ c M k), c.bs * G⟩ := by
  have hD := hp.fD
  have hi' := idx_lt' (L := c.ds M) hi
  have hg := grp_le (L := c.ds M) hk
  rw [hp.dk_addr (by omega_using [hG, hk]), ← ds_of c hb]
  rcases ho with ho | ho
  · exact VG.Offset.disjoint _ (.inl (VG.Proof.Modes.idx_lt ho)) (by omega_using [hi', hD]) (by omega_using [hg, hD])
  · have : c.ds M * k + c.ds M * G ≤ c.ds M * i := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ ho
    exact VG.Offset.disjoint _ (.inr this) (by omega_using [hi', hD]) (by omega_using [hg, hD])

/-- The layout of a group's blocks. -/
theorem UPre.wlay (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hb : M.byte = false) {k G : Nat} (hG : 0 < G)
    (hk : k + G ≤ N c s₀) (hGW : c.bs * G ≤ wb) (hW : wb ≤ 4096) :
    WLay c G (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) (wR wb s₀ :: s₀.wr) := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hds := ds_of c hb
  have hk' : k < N c s₀ := by omega_using [hG, hk]
  have hgl := grp_le (L := c.bs) hk
  have hD := hp.fD
  rw [hds] at hD
  have hdk := hp.dk_toNat hk'
  rw [hds] at hdk
  have hwb := hp.wb_le hd
  have hwp := hp.wp_toNat hd
  have hsp := s₀.sp.isLt
  have dsub := hp.grp_sub_data hb hG hk
  have ssub : Region.Sub ⟨State.addr (Sc c s₀), oOff + 2 * c.bs⟩ (scrR c s₀) :=
    Region.sub_prefix (by omega_using [hsc])
  have bsub := hp.buf_sub hd hGW
  refine ⟨S.bw_pos, fun a => ?_, fun a => ?_, ?_, ?_, ?_, fun a a' ha => ?_⟩
  · cases a
    · exact Nat.le_trans hGW hW
    · exact S.bw_le
    · exact Nat.le_trans hGW hW
  · cases a
    · show (Dk s₀ c M k).toNat + c.bs * G ≤ 2 ^ 32
      omega_using [hdk, hD, hgl]
    · show (Sc c s₀).toNat + (oOff + 2 * c.bs) ≤ 2 ^ 32
      omega_using [hS, hsc]
    · show (Wp wb s₀).toNat + c.bs * G ≤ 2 ^ 32
      omega_using [hwp, hwb, hGW, hsp]
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR c s₀ M, List.mem_cons_of_mem _ hp.data_in, c.ds M * k, hp.dk_addr hk', by
        show c.ds M * k + c.bs * G ≤ N c s₀ * c.ds M
        rw [hds]; exact hgl⟩
  · exact cov_off (R := scrR c s₀) (List.mem_cons_of_mem _ hp.scr_in)
      (by show oOff + 2 * c.bs ≤ c.scratchBytes; omega_using [hsc])
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wR wb s₀, List.mem_cons_self, 0, (add0 _).symm, by show 0 + c.bs * G ≤ wb; omega_using [hGW]⟩
  · cases a <;> cases a' <;> first | exact absurd rfl ha | skip
    · exact (hp.data_scr.sub_left dsub).sub_right ssub
    · exact (hp.b_data.symm.sub_left dsub).sub_right bsub
    · exact (hp.data_scr.symm.sub_left ssub).sub_right dsub
    · exact (hp.b_scr.symm.sub_left ssub).sub_right bsub
    · exact (hp.b_data.sub_left bsub).sub_right dsub
    · exact (hp.b_scr.sub_left bsub).sub_right ssub

/-- The arrays of a group, apart from the callee's stack. -/
theorem UPre.arr_callee (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hb : M.byte = false) {k G : Nat} (hG : 0 < G)
    (hk : k + G ≤ N c s₀) (hGW : c.bs * G ≤ wb) (a : WArr) :
    Region.Disjoint ⟨State.addr (a.ptr (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀)), a.len c G⟩
      ⟨State.addr (Wp wb s₀) - BitVec.ofNat 64 S₀.stack, S₀.stack⟩ := by
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hwb := hp.wb_le hd
  have hst := hp.stk
  rw [hd.stack] at hst
  have hsp := s₀.sp.isLt
  cases a
  · exact (hp.b_data.symm.sub_left (hp.grp_sub_data hb hG hk)).sub_right (hp.callee_sub hd)
  · exact (hp.b_scr.symm.sub_left (Region.sub_prefix (by
      show oOff + 2 * c.bs ≤ c.scratchBytes
      omega_using [hsc]))).sub_right (hp.callee_sub hd)
  · exact VG.Offset.base_disjoint_below _ (by
      show S₀.stack + c.bs * G ≤ 2 ^ 64
      omega_using [hst, hGW, hsp])

/-- The regions a group may change, within those the invariant allows. -/
theorem UPre.wstep_sub (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hb : M.byte = false) {k G : Nat} (hG : 0 < G)
    (hk : k + G ≤ N c s₀) (hGW : c.bs * G ≤ wb) :
    ∀ r ∈ wblkRegions c G (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) ++
        [(⟨State.addr (Wp wb s₀) - BitVec.ofNat 64 S₀.stack, S₀.stack⟩ : Region)],
      ∃ r' ∈ [dataR c s₀ M, blkR c s₀, belowR S s₀], Region.Sub r r' := by
  intro r hr
  simp only [wblkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, .head _, hp.grp_sub_data hb hG hk⟩
  · exact ⟨_, .tail _ (.head _), Region.sub_prefix (by omega_arith)⟩
  · exact ⟨_, .tail _ (.tail _ (.head _)), hp.buf_sub hd hGW⟩
  · exact ⟨_, .tail _ (.tail _ (.head _)), hp.callee_sub hd⟩

/-- The memory since entry, for the cipher's schedule. -/
theorem wframe_entry {rs : List Region} {m₁ m₂ : Mem}
    (hs : ∀ r ∈ rs, ∃ r' ∈ [dataR c s₀ M, blkR c s₀, belowR S s₀], Region.Sub r r')
    (h₁ : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) m₁) (h₂ : Frame rs m₁ m₂) :
    Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem m₂ := by
  obtain f₀ : Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem (savedMem c s₀) :=
    (UPre.savedMem_frame (c := c) (s₀ := s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR c s₀, .tail _ (.head _), UPre.slots_sub⟩
  refine f₀.trans (((h₁.trans (h₂.sub hs)).sub fun r hr => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, .head _, fun _ h => h⟩
  · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk_sub⟩
  · exact ⟨_, .tail _ (.tail _ (.head _)), fun _ h => h⟩

/-- The invariant in a state that differs in registers the invariant does
not name, and in memory within the buffer. -/
theorem WInv.congr (hp : UPre c S M s₀) (hd : Deep S₀ S wb) {k : Nat} {s s' : State}
    (h : WInv wb c S M s₀ k s) (hg : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r11], s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : Frame [wR wb s₀] s.mem s'.mem) :
    WInv wb c S M s₀ k s' := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have bsub := hp.buf_sub hd (Nat.le_refl wb)
  have hdis : ∀ {R : Region}, R.Disjoint (belowR S s₀) → ∀ r ∈ [wR wb s₀], R.Disjoint r := fun hR r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right bsub
  refine WInv.mk' (by rw [hg _ (by simp)]; exact h.inv.r4) (by rw [hg _ (by simp)]; exact h.inv.r5)
    (by rw [hg _ (by simp)]; exact h.inv.r6) (by rw [hg _ (by simp)]; exact h.inv.r7)
    (by rw [hg _ (by simp)]; exact h.inv.r8) (fun hr => by rw [hg _ (by simp)]; exact h.inv.r11 hr)
    (by rw [hsp]; exact h.sp) (by rw [hrd]; exact h.inv.rd) (by rw [hwr]; exact h.wr) ?_ ?_ ?_ ?_
  · exact h.inv.frame.trans (hm.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨belowR S s₀, by simp, bsub⟩)
  · refine Eq.trans (List.map_congr_left fun j hj => ?_) h.inv.data
    have hj := List.mem_range.mp hj
    obtain hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
      VG.Offset.sub_base _ (idx_lt' hj)
    exact VG.Proof.Modes.bytesAt_frame hm (hdis (hp.b_data.symm.sub_left hsub))
      (by have := S.ds_le M; omega_using [hS, hsc, this])
  · refine Eq.trans (VG.Proof.Modes.bytesAt_frame hm (hdis (hp.b_scr.symm.sub_left
      (VG.Offset.sub_base _ (by omega_using [hsc])))) (by omega_using [hS, hsc])) h.inv.o
  · refine Eq.trans (VG.Proof.Modes.bytesAt_frame hm (hdis (hp.b_scr.symm.sub_left
      (VG.Offset.sub_base _ (by omega_using [hsc])))) (by omega_using [hS, hsc])) h.inv.t

/-- The group's data blocks, as on entry. -/
theorem WInv.group (hp : UPre c S M s₀) (hb : M.byte = false) {k G : Nat} (hG : 0 < G) (hk : k + G ≤ N c s₀)
    {s : State} (h : WInv wb c S M s₀ k s) :
    ((xs c s₀ M).drop k).take G =
      (List.range G).map fun j => wmem c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem (.d j) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
  by_cases hi : i < G
  · rw [ite_eq_left hi, List.getElem?_range hi, Option.map_some,
      h.inv.blockAt (Nat.le_add_right _ _) (by omega_using [hi, hk])]
    refine congrArg some ?_
    show bytesAt s.mem (State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * (k + i))) (c.ds M) =
      bytesAt s.mem (State.addr (Dk s₀ c M k) + BitVec.ofNat 64 (c.bs * i)) c.bs
    rw [hp.dk_addr (by omega_using [hG, hk]), ds_of c hb, VG.Offset.add_add, ← Nat.mul_add]
  · rw [ite_eq_right hi, List.getElem?_eq_none (by rw [List.length_range]; omega_using [hi]), Option.map_none]

omit S₀ in
/-- The mode after a group, from the mode before it. -/
theorem rK_group {k G : Nat} (hG : 0 < G) (hk : k + G ≤ N c s₀) :
    rK S s₀ M (k + G) = ((rK S s₀ M k).1 ++
      (runSeq M (ciph S s₀) ⟨[], (rK S s₀ M k).2.o, (rK S s₀ M k).2.t⟩ (((xs c s₀ M).drop k).take G)).1,
      (runSeq M (ciph S s₀) ⟨[], (rK S s₀ M k).2.o, (rK S s₀ M k).2.t⟩ (((xs c s₀ M).drop k).take G)).2) := by
  have hne : ((xs c s₀ M).drop k).take G ≠ [] := by
    intro e
    have := congrArg List.length e
    simp only [List.length_take, List.length_drop, length_blocksOf, List.length_nil] at this
    omega_using [this, hG, hk]
  simp only [rK]
  rw [List.take_add, runSeq_append, runSeq_d _ _ _ _ hne]

end

/-! ## The instructions around the operations -/

theorem wp_addSp {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Nat} (hi : imm < 256)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 32 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.sp + BitVec.ofNat 32 imm)) (by simp [exec, hi])
    (k _ (Upd.setReg _ _ _))

/-- The buffer's address to `r12`. -/
theorem wbuf_wp {s : State} :
    WP isa (.block Core.wbuf) s fun s' => Upd s s' .r12 s.sp := by
  refine wp_addSp (by decide) fun s' u => WP.block_nil ?_
  have e : s.sp + BitVec.ofNat 32 0 = s.sp := BitVec.add_zero _
  rw [e] at u; exact u

/-- What the arguments of a group's call leave. -/
structure WPreA (c : Core) (s₀ : State) (B : BitVec 32) (G : Nat) (s s₂ : State) : Prop where
  regs : ∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → s₂.gpr x = s.gpr x
  r0 : s₂.gpr .r0 = Kp s₀
  r1 : c.rounds = true → s₂.gpr .r1 = Rp s₀
  rD : s₂.gpr c.dReg = B
  rN : s₂.gpr c.nReg = BitVec.ofNat 32 G
  a3 : ∀ k, c.arg3 = some k → s₂.gpr .r3 = BitVec.ofNat 32 k
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  mem : s₂.mem = s.mem

theorem wcallArgs_wp {c : Core} (S : CoreSpec c) {s₀ s : State} {onW : Bool} {G : Nat} {B : BitVec 32}
    (h4 : s.gpr .r4 = Kp s₀) (h11 : c.rounds = true → s.gpr .r11 = Rp s₀)
    (hB : s.gpr (if onW then .r12 else .r6) = B) (enc : encodable (BitVec.ofNat 32 G) = true) :
    WP isa (.block (c.wcallArgs onW G)) s (WPreA c s₀ B G s) := by
  obtain hne : (if onW then Reg.r12 else Reg.r6) ≠ .r0 ∧ (if onW then Reg.r12 else Reg.r6) ≠ .r1 := by
    cases onW <;> decide
  simp only [Core.wcallArgs, mov]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  cases hr : c.rounds
  · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
    obtain hN : c.nReg = .r2 := by unfold Core.nReg; rw [hr]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, hD, hN]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_imm enc) fun s₄ u₄ =>
      arg3_wp S fun s₅ g₅ _ a₅ rd₅ wr₅ sp₅ m₅ =>
      ⟨fun x a b d e => ?_, ?_, fun h => absurd h (by simp [hr]), ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_⟩
    · rw [g₅ _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a]
    · rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h4]
    · rw [hD, g₅ _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ hne.1, hB]
    · rw [hN, g₅ _ (by decide), u₄.gpr]
    · rw [a₅ k hk]
    · rw [rd₅, u₄.rd, u₃.rd, u₂.rd]
    · rw [wr₅, u₄.wr, u₃.wr, u₂.wr]
    · rw [sp₅, u₄.sp, u₃.sp, u₂.sp]
    · rw [m₅, u₄.mem, u₃.mem, u₂.mem]
  · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
    obtain hN : c.nReg = .r3 := by unfold Core.nReg; rw [hr]; rfl
    obtain hn3 : c.arg3 = none := by
      cases h3 : c.arg3
      · rfl
      · have := S.arg3_rounds (by rw [h3]; rfl); rw [hr] at this; cases this
    simp only [↓reduceIte, List.cons_append, List.nil_append, hD, hN]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm enc)
      fun s₅ u₅ => arg3_wp S fun s₆ g₆ n₆ _ rd₆ wr₆ sp₆ m₆ =>
      ⟨fun x a b d e => ?_, ?_, fun _ => ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_⟩
    · rw [g₆ _ e, u₅.other _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a]
    · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h4]
    · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
        h11 hr]
    · rw [hD, g₆ _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ hne.2, u₂.other _ hne.1, hB]
    · rw [hN, n₆ hn3, u₅.gpr]
    · rw [hn3] at hk; cases hk
    · rw [rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
    · rw [wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
    · rw [sp₆, u₅.sp, u₄.sp, u₃.sp, u₂.sp]
    · rw [m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem]

/-! ## The call of a group -/

/-- Block `j` of blocks the cipher was applied to. -/
theorem wcall_in {L : Nat} {m m' : Mem} {p : Addr} {G : Nat} {ciph : Spec.Cbc.Cipher}
    (hout : blocksOf L m' p G = (blocksOf L m p G).map ciph) {j : Nat} (hj : j < G) :
    bytesAt m' (p + BitVec.ofNat 64 (L * j)) L = ciph (bytesAt m (p + BitVec.ofNat 64 (L * j)) L) := by
  have := congrArg (·[j]?) hout
  simp only [getElem?_blocksOf _ _ _ hj, List.getElem?_map, Option.map_some] at this
  exact Option.some.inj this

/-- A block outside the array the cipher was applied to. -/
theorem wcall_other {c : Core} {G : Nat} {D S W : BitVec 32} {wr : List Region} (hL : WLay c G D S W wr)
    {m m' : Mem} {b : WBlks} (hb : WBlkMem c G D S W m b) {a : WArr} {C : Region}
    (hf : Frame [⟨State.addr (a.ptr D S W), a.len c G⟩, C] m m') {x : WBlk} (hx : x.ok G = true)
    (hne : warr x ≠ a) (hC : Region.Disjoint ⟨waddr c D S W x, c.bs⟩ C) :
    bytesAt m' (waddr c D S W x) c.bs = b x := by
  rw [← hb x hx]
  refine VG.Proof.Modes.bytesAt_frame hf (fun r hr => ?_)
    (by have h' : (WArr.scr.ptr D S W).toNat + (oOff + 2 * c.bs) ≤ 2 ^ 32 := hL.fit .scr; omega_using [h'])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hL.sep _ _ hne).sub_left (WLay.sub_arr hx)
  · exact hC

/-- The blocks after the call. -/
theorem wcall_blks {c : Core} {S : CoreSpec c} {G : Nat} {D Sb W K R : BitVec 32} {wr : List Region}
    (hL : WLay c G D Sb W wr) {onW : Bool} {s₂ s₃ : State} {b : WBlks} (hb : WBlkMem c G D Sb W s₂.mem b)
    (cp : CallPostN c S s₂ K R (if onW then W else D) G s₃)
    (hC : ∀ x, x.ok G = true →
      Region.Disjoint ⟨waddr c D Sb W x, c.bs⟩ ⟨State.addr s₂.sp - BitVec.ofNat 64 S.stack, S.stack⟩) :
    WBlkMem c G D Sb W s₃.mem (wciph onW G (S.ciphAt s₂.mem (State.addr K) R) b) := by
  intro x hx
  cases onW
  · have cp' : CallPostN c S s₂ K R D G s₃ := cp
    cases x with
    | d j =>
      have hj : j < G := by simpa [WBlk.ok] using hx
      show bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 (c.bs * j)) c.bs = _
      rw [wcall_in cp'.out hj, show wciph false G (S.ciphAt s₂.mem (State.addr K) R) b (.d j) =
        S.ciphAt s₂.mem (State.addr K) R (b (.d j)) by simp [wciph, hj], ← hb (.d j) hx]
      rfl
    | w j => exact wcall_other hL hb (a := .data) cp'.frame hx (by simp [warr]) (hC _ hx)
    | o => exact wcall_other hL hb (a := .data) cp'.frame hx (by simp [warr]) (hC _ hx)
    | t => exact wcall_other hL hb (a := .data) cp'.frame hx (by simp [warr]) (hC _ hx)
  · have cp' : CallPostN c S s₂ K R W G s₃ := cp
    cases x with
    | w j =>
      have hj : j < G := by simpa [WBlk.ok] using hx
      show bytesAt s₃.mem (State.addr W + BitVec.ofNat 64 (c.bs * j)) c.bs = _
      rw [wcall_in cp'.out hj, show wciph true G (S.ciphAt s₂.mem (State.addr K) R) b (.w j) =
        S.ciphAt s₂.mem (State.addr K) R (b (.w j)) by simp [wciph, hj], ← hb (.w j) hx]
      rfl
    | d j => exact wcall_other hL hb (a := .buf) cp'.frame hx (by simp [warr]) (hC _ hx)
    | o => exact wcall_other hL hb (a := .buf) cp'.frame hx (by simp [warr]) (hC _ hx)
    | t => exact wcall_other hL hb (a := .buf) cp'.frame hx (by simp [warr]) (hC _ hx)

section
variable {c : Core} {S₀ S : CoreSpec c} {M : Mode} {s₀ : State} {wb : Nat}

/-- What the code before a group's call leaves, from `s`: the registers
`s` had but the arguments' and the temporaries, the arguments, and the
blocks as the operations before the call leave them. -/
structure WMid (wb : Nat) (c : Core) (M : Mode) (pre : List WOp) (onW : Bool) (s₀ : State) (G k : Nat)
    (s s₃ : State) : Prop where
  regs : ∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r9 → x ≠ .r10 → x ≠ .r12 → s₃.gpr x = s.gpr x
  r0 : s₃.gpr .r0 = Kp s₀
  r1 : c.rounds = true → s₃.gpr .r1 = Rp s₀
  rD : s₃.gpr c.dReg = if onW then Wp wb s₀ else Dk s₀ c M k
  rN : s₃.gpr c.nReg = BitVec.ofNat 32 G
  a3 : ∀ k, c.arg3 = some k → s₃.gpr .r3 = BitVec.ofNat 32 k
  rd : s₃.rd = s.rd
  wr : s₃.wr = s.wr
  sp : s₃.sp = s.sp
  frame : Frame (wblkRegions c G (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀)) s.mem s₃.mem
  blks : WBlkMem c G (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s₃.mem
    (wrunOps pre (wmem c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem))

/-- The arguments of a group's call make its precondition. -/
theorem WMid.callPre (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hb : M.byte = false) {k G : Nat} (hG : 0 < G)
    (hk : k + G ≤ N c s₀) (hGW : c.bs * G ≤ wb) (hW : wb ≤ 4096) {pre : List WOp} {onW : Bool} {s s₂ : State}
    (h : WInv wb c S M s₀ k s) (a : WMid wb c M pre onW s₀ G k s s₂) :
    CallPreN c S₀ s₂ (Kp s₀) (Rp s₀) (if onW then Wp wb s₀ else Dk s₀ c M k) G := by
  obtain sp : s₂.sp = Wp wb s₀ := by rw [a.sp, h.sp]
  obtain rd : s₂.rd = s₀.rd := by rw [a.rd]; exact h.inv.rd
  obtain wr : s₂.wr = wR wb s₀ :: s₀.wr := by rw [a.wr, h.wr]
  have hL := hp.wlay hd hb hG hk hGW hW
  have hwp := hp.wp_toNat hd
  have hst := hp.stk
  rw [hd.stack] at hst
  have hbs := S.bs_pos
  have hGle : G ≤ c.bs * G := Nat.le_mul_of_pos_left G hbs
  have ek := hd.keyLen
  have hfK : (Kp s₀).toNat + S₀.keyLen ≤ 2 ^ 32 := by rw [← ek]; exact hp.fK
  have hbk : (belowR S s₀).Disjoint ⟨State.addr (Kp s₀), S₀.keyLen⟩ := by rw [← ek]; exact hp.b_key
  have hkd : Region.Disjoint ⟨State.addr (Kp s₀), S₀.keyLen⟩ (dataR c s₀ M) := by rw [← ek]; exact hp.key_data
  have hkin : (⟨State.addr (Kp s₀), S₀.keyLen⟩ : Region) ∈ s₀.rd ++ s₀.wr := by rw [← ek]; exact hp.key_in
  have csub := hp.callee_sub hd
  have eB : (if onW then Wp wb s₀ else Dk s₀ c M k) =
      (if onW then WArr.buf else WArr.data).ptr (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) := by cases onW <;> rfl
  have eL : c.bs * G = (if onW then WArr.buf else WArr.data).len c G := by cases onW <;> rfl
  refine ⟨a.r0, a.r1, fun hr => by rw [← hd.rok]; exact hp.rok hr, a.rD, a.rN, by omega_using [hGle, hGW, hW],
    a.a3, by rw [sp, hwp]; omega_using [hst], hfK, ?_, ?_, by rw [sp]; exact hbk.sub_left csub, ?_, ?_, ?_⟩
  · rw [eB, eL]; exact hL.fit _
  · cases onW
    · exact hkd.sub_right (hp.grp_sub_data hb hG hk)
    · exact hbk.symm.sub_right (hp.buf_sub hd hGW)
  · rw [sp, eB, eL]; exact (hp.arr_callee hd hb hG hk hGW _).symm
  · rw [rd, wr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases List.mem_append.mp hkin with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · rw [wr]
    cases onW
    · exact hL.wD
    · exact hL.wW

/-- The operations before a group's call, and its arguments. -/
theorem wpre_wp (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) {k : Nat} (hk : k + 2 ^ lg ≤ N c s₀) {s s₁ : State}
    (h : WInv wb c S M s₀ k s) (u₁ : Upd s s₁ .r12 s.sp) :
    WP isa (.block (c.wopsCode (wm.pre (2 ^ lg)) ++ c.wcallArgs wm.onW (2 ^ lg))) s₁
      (WMid wb c M (wm.pre (2 ^ lg)) wm.onW s₀ (2 ^ lg) k s) := by
  have hw := hl.ok
  have hL := hp.wlay hd hw.byte hw.pos hk hl.fit hW
  obtain r4 : s.gpr .r4 = Kp s₀ := h.inv.r4
  obtain r6 : s.gpr .r6 = Dk s₀ c M k := h.inv.r6
  obtain r8 : s.gpr .r8 = Sc c s₀ := h.inv.r8
  obtain r11 : c.rounds = true → s.gpr .r11 = Rp s₀ := h.inv.r11
  obtain h12 : s₁.gpr .r12 = Wp wb s₀ := by rw [u₁.gpr, h.sp]
  rw [WP.block_append_iff]
  refine WP.mono (wopsCode_wp (by rw [u₁.wr, h.wr]; exact hL) (by rw [u₁.other _ (by decide), r6])
    (by rw [u₁.other _ (by decide), r8]) h12
    (by rw [u₁.mem]; exact wmem_blk c (2 ^ lg) (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem) hw.pre) fun s₂ h₂ => ?_
  obtain hB : s₂.gpr (if wm.onW then .r12 else .r6) = (if wm.onW then Wp wb s₀ else Dk s₀ c M k) := by
    cases wm.onW
    · show s₂.gpr .r6 = _
      rw [h₂.regs _ (by decide) (by decide), u₁.other _ (by decide), r6]; rfl
    · show s₂.gpr .r12 = _
      rw [h₂.regs _ (by decide) (by decide), h12]; rfl
  refine WP.mono (wcallArgs_wp S₀ (s₀ := s₀)
    (by rw [h₂.regs _ (by decide) (by decide), u₁.other _ (by decide), r4])
    (fun hr => by rw [h₂.regs _ (by decide) (by decide), u₁.other _ (by decide), r11 hr]) hB hl.encG)
    fun s₃ a => ⟨fun x x0 x1 x2 x3 x9 x10 x12 => by rw [a.regs x x0 x1 x2 x3, h₂.regs x x9 x10, u₁.other x x12],
      a.r0, a.r1, a.rD, a.rN, a.a3, by rw [a.rd, h₂.rd, u₁.rd], by rw [a.wr, h₂.wr, u₁.wr],
      by rw [a.sp, h₂.sp, u₁.sp], by rw [a.mem, ← u₁.mem]; exact h₂.frame, by rw [a.mem]; exact h₂.blks⟩

/-- The registers the code after a group's call uses, after it. -/
structure WAfterCall (wb : Nat) (c : Core) (M : Mode) (s₀ : State) (k : Nat) (s₄ : State) : Prop where
  r6 : s₄.gpr .r6 = Dk s₀ c M k
  r7 : s₄.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k)
  r8 : s₄.gpr .r8 = Sc c s₀
  sp : s₄.sp = Wp wb s₀

theorem wafterCall {pre : List WOp} {onW : Bool} {G k : Nat} {s s₃ s₄ : State} (h : WInv wb c S M s₀ k s)
    (a : WMid wb c M pre onW s₀ G k s s₃)
    (cp : CallPostN c S₀ s₃ (Kp s₀) (Rp s₀) (if onW then Wp wb s₀ else Dk s₀ c M k) G s₄) :
    WAfterCall wb c M s₀ k s₄ := by
  have g : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h9 h10
      (by rintro rfl; simp [preserved] at hr)]
  exact ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h.inv.r6,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h.inv.r7,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h.inv.r8, by rw [cp.sp, a.sp, h.sp]⟩

/-- One group of `2 ^ lg` blocks, from `k` blocks. -/
theorem wbody_ok (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hW : wb ≤ 4096)
    {wm : WMode} {lg : Nat} (hl : LevelOk c M wm wb lg) {k : Nat} (hk : k + 2 ^ lg ≤ N c s₀) {s : State}
    (h : WInv wb c S M s₀ k s) :
    WP isa (c.wbody wm lg) s fun s' => WInv wb c S M s₀ (k + 2 ^ lg) s' ∧
      s'.z = decide ((N c s₀ - (k + 2 ^ lg)) / 2 ^ lg = 0) := by
  have hw := hl.ok
  have hG := hw.pos
  have hb := hw.byte
  have hGW := hl.fit
  have hL := hp.wlay hd hb hG hk hGW hW
  have hds := ds_of c hb
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hNlt := N_lt c s₀
  obtain r4 : s.gpr .r4 = Kp s₀ := h.inv.r4
  obtain r5 : s.gpr .r5 = Ivp c s₀ := h.inv.r5
  obtain r6 : s.gpr .r6 = Dk s₀ c M k := h.inv.r6
  obtain r7 : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k) := h.inv.r7
  obtain r8 : s.gpr .r8 = Sc c s₀ := h.inv.r8
  obtain r11 : c.rounds = true → s.gpr .r11 = Rp s₀ := h.inv.r11
  obtain rd : s.rd = s₀.rd := h.inv.rd
  obtain fr : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) s.mem := h.inv.frame
  unfold Core.wbody
  -- The buffer's address, the operations before the call and its arguments.
  refine WP.seq (WP.mono wbuf_wp fun s₁ u₁ => ?_)
  refine WP.seq (WP.mono (wpre_wp hp hd hW hl hk h u₁) fun s₃ a => ?_)
  -- The call.
  obtain sp₃ : s₃.sp = Wp wb s₀ := by rw [a.sp, h.sp]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [a.rd, rd]
  obtain wr₃ : s₃.wr = wR wb s₀ :: s₀.wr := by rw [a.wr, h.wr]
  refine WP.seq (WP.mono (callN_wp S₀ (a.callPre hp hd hb hG hk hGW hW h) h0) fun s₄ cp => ?_)
  obtain hcal : ∀ x : WBlk, x.ok (2 ^ lg) = true →
      Region.Disjoint ⟨waddr c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) x, c.bs⟩
        ⟨State.addr (Wp wb s₀) - BitVec.ofNat 64 S₀.stack, S₀.stack⟩ :=
    fun x hx => (hp.arr_callee hd hb hG hk hGW _).sub_left (WLay.sub_arr hx)
  -- The memory the group has changed so far, and the cipher.
  obtain f₃ : Frame (wblkRegions c (2 ^ lg) (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀)) s.mem s₃.mem := a.frame
  obtain ec : S₀.ciphAt s₃.mem (State.addr (Kp s₀)) (Rp s₀) = ciph S s₀ := by
    rw [← hd.ciphAt]
    exact hp.ciph_eq (wframe_entry (fun r hr => hp.wstep_sub hd hb hG hk hGW r (List.mem_append_left _ hr))
      fr f₃)
  obtain hb₄ := wcall_blks hL a.blks cp (by rw [sp₃]; exact hcal)
  rw [ec] at hb₄
  obtain g₄ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h9 h10
      (by rintro rfl; simp [preserved] at hr)]
  -- The buffer's address again, and the operations after the call.
  refine WP.seq (WP.mono wbuf_wp fun s₅ u₅ => ?_)
  obtain r6₅ : s₅.gpr .r6 = Dk s₀ c M k := by
    rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), r6]
  obtain r8₅ : s₅.gpr .r8 = Sc c s₀ := by
    rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), r8]
  obtain h12₅ : s₅.gpr .r12 = Wp wb s₀ := by rw [u₅.gpr, cp.sp, sp₃]
  rw [WP.block_append_iff]
  refine WP.mono (wopsCode_wp (by rw [u₅.wr, cp.wr, wr₃]; exact hL) r6₅ r8₅ h12₅ (by rw [u₅.mem]; exact hb₄)
    hw.post) fun s₆ h₆ => ?_
  -- What the group computed.
  obtain hb₆ : WBlkMem c (2 ^ lg) (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s₆.mem
      (wstep wm (2 ^ lg) (ciph S s₀) (wmem c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem)) := h₆.blks
  obtain sim := hw.sim.sim (ciph S s₀) (wmem c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem)
  rw [show wmem c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem .o = (rK S s₀ M k).2.o from h.inv.o,
    show wmem c (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) s.mem .t = (rK S s₀ M k).2.t from h.inv.t,
    ← h.group hp hb hG hk] at sim
  obtain eK := rK_group (S := S) (M := M) hG hk
  -- The memory the group changed.
  obtain fstep : Frame (wblkRegions c (2 ^ lg) (Dk s₀ c M k) (Sc c s₀) (Wp wb s₀) ++
      [(⟨State.addr (Wp wb s₀) - BitVec.ofNat 64 S₀.stack, S₀.stack⟩ : Region)]) s.mem s₆.mem := by
    refine ((f₃.mono fun r hr => List.mem_append_left _ hr).trans (cp.frame.sub fun r hr => ?_)).trans
      (by rw [← u₅.mem]; exact h₆.frame.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · cases wm.onW
      · exact ⟨_, List.mem_append_left _ (.head _), fun _ h => h⟩
      · exact ⟨_, List.mem_append_left _ (.tail _ (.tail _ (.head _))), fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (.head _), by rw [sp₃]; exact fun _ h => h⟩
  -- On to the next group.
  obtain g₆ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s₆.gpr r = s.gpr r :=
    fun r hr hl h9 h10 h12' => by rw [h₆.regs r h9 h10, u₅.other r h12', g₄ r hr hl h9 h10]
  simp only [Core.wadvance, Core.groupsLeft, List.cons_append, List.nil_append]
  refine wp_add (op2_imm hl.encB) fun s₇ u₇ => wp_sub (op2_imm hl.encG) fun s₈ u₈ =>
    wp_mov (op2_lsr hl.sh) fun s₉ u₉ => wp_cmp (op2_imm (by decide)) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ⟨?_, ?_⟩
  · obtain em : s₁₀.mem = s₆.mem := by rw [f₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
    obtain r7₈ : s₈.gpr .r7 = BitVec.ofNat 32 (N c s₀ - (k + 2 ^ lg)) := by
      rw [u₈.gpr, u₇.other _ (by decide), g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r7,
        MdStream.Arm.sub_ofNat (by omega_using [hk, hG]), Nat.sub_sub]
    refine WInv.mk' ?_ ?_ ?_ ?_ ?_ (fun hr => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r5]
    · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r6, Dk, VG.Offset.add_add, hds,
        ← Nat.mul_add]
    · rw [f₁₀.gpr, u₉.other _ (by decide), r7₈]
    · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r8]
    · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r11 hr]
    · rw [f₁₀.sp, u₉.sp, u₈.sp, u₇.sp, h₆.sp, u₅.sp, cp.sp, sp₃]
    · rw [f₁₀.rd, u₉.rd, u₈.rd, u₇.rd, h₆.rd, u₅.rd, cp.rd, rd₃]
    · rw [f₁₀.wr, u₉.wr, u₈.wr, u₇.wr, h₆.wr, u₅.wr, cp.wr, wr₃]
    · rw [em]; exact fr.trans (fstep.sub (hp.wstep_sub hd hb hG hk hGW))
    · rw [em, eK]
      obtain hl' : (rK S s₀ M k).1.length = k := by
        rw [runSeq_length, List.length_take, length_blocksOf]; omega_using [hk, hG]
      obtain hy : (runSeq M (ciph S s₀) ⟨[], (rK S s₀ M k).2.o, (rK S s₀ M k).2.t⟩
          (((xs c s₀ M).drop k).take (2 ^ lg))).1.length = 2 ^ lg := by
        rw [runSeq_length, List.length_take, List.length_drop, length_blocksOf]; omega_using [hk, hG]
      rw [blocksOf_splice (L := c.ds M) (m := s.mem) (m' := s₆.mem) (p := State.addr (Dp c s₀)) hk _ hy
        (fun j hj => ?_) (fun i hi ho => ?_),
        show blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀) = _ from h.inv.data]
      · obtain e1 : ((rK S s₀ M k).1 ++ (xs c s₀ M).drop k).take k = (rK S s₀ M k).1 := List.take_left' hl'
        obtain e2 : ((rK S s₀ M k).1 ++ (xs c s₀ M).drop k).drop (k + 2 ^ lg) =
            (xs c s₀ M).drop (k + 2 ^ lg) := by
          rw [List.drop_append, List.drop_eq_nil_of_le (as := (rK S s₀ M k).1) (i := k + 2 ^ lg)
            (by rw [hl']; omega_using [hG]), hl', Nat.add_sub_cancel_left, List.nil_append, List.drop_drop]
        rw [e1, e2]
      · have e := congrArg (·[j]?) sim.1
        simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some] at e
        rw [← e, ← hb₆ (.d j) (by simpa [WBlk.ok] using hj)]
        refine congrArg some ?_
        show bytesAt s₆.mem (State.addr (Dk s₀ c M k) + BitVec.ofNat 64 (c.bs * j)) c.bs =
          bytesAt s₆.mem (State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * (k + j))) (c.ds M)
        rw [hp.dk_addr (by omega_using [hG, hk]), hds, VG.Offset.add_add, ← Nat.mul_add]
      · obtain hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * i), c.ds M⟩ (dataR c s₀ M) :=
          VG.Offset.sub_base _ (idx_lt' hi)
        refine VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) (by have := S.ds_le M; omega_using [hS, hsc, this])
        simp only [wblkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.blk_grp hb hG hk hi ho
        · exact (hp.data_scr.sub_left hsub).sub_right UPre.blk2_sub
        · exact (hp.b_data.symm.sub_left hsub).sub_right (hp.buf_sub hd hGW)
        · exact (hp.b_data.symm.sub_left hsub).sub_right (hp.callee_sub hd)
    · rw [em, eK]; exact (hb₆ .o rfl).trans sim.2.1
    · rw [em, eK]; exact (hb₆ .t rfl).trans sim.2.2
  · rw [z₁₀, u₉.gpr, u₈.gpr, u₇.other _ (by decide),
      g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r7,
      MdStream.Arm.sub_ofNat (by omega_using [hk, hG]), Nat.sub_sub, ofNat_shr (by omega_using [hNlt])]
    exact cmp0 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNlt]))

/-- Whether a group of `2 ^ lg` blocks is left. -/
theorem whead_wp (hp : UPre c S M s₀) (hd : Deep S₀ S wb) {lg : Nat} (hlg : 1 ≤ lg ∧ lg ≤ 31) {k : Nat}
    {s : State} (h : WInv wb c S M s₀ k s) :
    WP isa (.block (Core.groupsLeft lg)) s fun s' => WInv wb c S M s₀ k s' ∧
      s'.z = decide ((N c s₀ - k) / 2 ^ lg = 0) := by
  have hNlt := N_lt c s₀
  obtain r7 : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k) := h.inv.r7
  refine wp_mov (op2_lsr hlg) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ⟨?_, ?_⟩
  · refine h.congr hp hd (fun r hr => ?_) (by rw [f₂.sp, u₁.sp]) (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr])
      (by rw [f₂.mem, u₁.mem]; exact Frame.refl _ _)
    rw [f₂.gpr, u₁.other _ (by rintro rfl; simp at hr)]
  · rw [z₂, u₁.gpr, r7, ofNat_shr (by omega_using [hNlt])]
    exact cmp0 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNlt]))

/-- The groups of `2 ^ lg` blocks. -/
theorem wlevel_ok (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hW : wb ≤ 4096)
    {wm : WMode} {lg : Nat} (hl : LevelOk c M wm wb lg) {k : Nat} (hk : k ≤ N c s₀) {s : State}
    (h : WInv wb c S M s₀ k s) :
    WP isa (c.wlevel wm lg) s fun s' => ∃ k', k' ≤ N c s₀ ∧ WInv wb c S M s₀ k' s' := by
  have hG := hl.ok.pos
  unfold Core.wlevel
  refine WP.seq (WP.mono (whead_wp hp hd hl.sh h) fun s₁ ⟨h₁, z₁⟩ => ?_)
  have ev : isa.eval .eq s₁ = some (decide ((N c s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, z₁]
  by_cases hz : (N c s₀ - k) / 2 ^ lg = 0
  · exact WP.ite true (by rw [ev]; simp [hz]) (fun _ => WP.block_nil ⟨k, hk, h₁⟩) (fun h => by cases h)
  · refine WP.ite false (by rw [ev]; simp [hz]) (fun h => by cases h) fun _ => ?_
    obtain hkG : k + 2 ^ lg ≤ N c s₀ := by
      rw [Nat.div_eq_zero_iff_lt hG] at hz; omega_using [hz, hk]
    refine WP.loop (M := isa) (body := c.wbody wm lg) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ j, n = N c s₀ - j ∧ j + 2 ^ lg ≤ N c s₀ ∧ WInv wb c S M s₀ j t) ?_
      (N c s₀ - k) s₁ ⟨k, rfl, hkG, h₁⟩
    rintro n t ⟨j, rfl, hj, ht⟩
    refine WP.mono (wbody_ok h0 hp hd hW hl hj ht) fun t' ⟨h', hz'⟩ => ?_
    have ev' : isa.eval .ne t' = some !decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0) := by
      show VG.Arm.eval .ne t' = _; rw [eval_ne, hz']
    by_cases hz'' : (N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0
    · left
      exact ⟨by rw [ev']; simp [hz''], j + 2 ^ lg, hj, h'⟩
    · right
      refine ⟨by rw [ev']; simp [hz''], N c s₀ - (j + 2 ^ lg), by omega_using [hj, hG], j + 2 ^ lg, rfl, ?_, h'⟩
      rw [Nat.div_eq_zero_iff_lt hG] at hz''; omega_using [hz'', hj]

/-- The groups of every level. -/
theorem wlevels_ok (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hW : wb ≤ 4096)
    {wm : WMode} {lgs : List Nat} (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) {k : Nat} (hk : k ≤ N c s₀) {s : State}
    (h : WInv wb c S M s₀ k s) :
    WP isa (c.wlevels wm lgs) s fun s' => ∃ k', k' ≤ N c s₀ ∧ WInv wb c S M s₀ k' s' := by
  induction lgs generalizing k s with
  | nil => exact WP.block_nil ⟨k, hk, h⟩
  | cons lg lgs ih =>
    show WP isa (.seq (c.wlevel wm lg) (c.wlevels wm lgs)) s _
    refine WP.seq (WP.mono (wlevel_ok h0 hp hd hW (hl lg List.mem_cons_self) hk h) fun s₁ ⟨k₁, hk₁, h₁⟩ => ?_)
    exact ih (fun lg' h' => hl lg' (List.mem_cons_of_mem _ h')) hk₁ h₁

/-- What the buffer's frame needs of its size. -/
def BufOk (wb : Nat) : Prop :=
  0 < wb ∧ wb < 4096 ∧ wb % 8 = 0 ∧ encodable (BitVec.ofNat 32 wb) = true

/-- The buffer zeroed, through its address in `r12`. -/
theorem wstores_wp (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hwb : wb < 4096) {k : Nat} {s s₁ : State}
    (h : WInv wb c S M s₀ k s) (u₁ : Upd s s₁ .r12 s.sp) :
    WP isa (.block (.mov .r2 (.imm 0) :: Impl.StackScratch.Arm.wipeStores (wb / 4))) s₁ (WInv wb c S M s₀ k) := by
  have hwp := hp.wp_toNat hd
  have hle := hp.wb_le hd
  have hsp := s₀.sp.isLt
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  obtain h12 : s₂.gpr .r12 = Wp wb s₀ := by rw [u₂.other _ (by decide), u₁.gpr, h.sp]
  obtain ⟨m', he, hf⟩ := wipeStores_run (wR wb s₀) s₂ (by rw [u₂.wr, u₁.wr, h.wr]; exact List.mem_cons_self)
    (wb / 4) (by omega_using [hwb]) (fun j hj => by
      rw [h12, addr_add (by omega_using [hwp, hle, hsp, hj])]
      exact VG.Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hwb]))
  refine WP.block ⟨_, he, ?_⟩
  refine h.congr hp hd (fun r hr => ?_) (by show s₂.sp = _; rw [u₂.sp, u₁.sp])
    (by show s₂.rd = _; rw [u₂.rd, u₁.rd]) (by show s₂.wr = _; rw [u₂.wr, u₁.wr])
    (by show Frame _ s.mem m'; rw [← u₁.mem, ← u₂.mem]; exact hf)
  show s₂.gpr r = _
  rw [u₂.other _ (by rintro rfl; simp at hr), u₁.other _ (by rintro rfl; simp at hr)]

/-- The buffer zeroed, in its frame. -/
theorem wwipe_wp (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hwb : wb < 4096) {k : Nat} {s : State}
    (h : WInv wb c S M s₀ k s) :
    WP isa (.seq (.block Core.wbuf) (.block (.mov .r2 (.imm 0) :: Impl.StackScratch.Arm.wipeStores (wb / 4)))) s
      (WInv wb c S M s₀ k) :=
  WP.seq (WP.mono wbuf_wp fun _ u₁ => wstores_wp hp hd hwb h u₁)

/-- The groups, in the buffer's frame. -/
theorem wide_wp (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hd : Deep S₀ S wb) (hwb : BufOk wb)
    {wm : WMode} {lgs : List Nat} (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) {k : Nat} (hk : k ≤ N c s₀) {s : State}
    (h : LInv c S M s₀ k s) :
    WP isa (c.wide wm lgs wb) s fun s' => ∃ k', k' ≤ N c s₀ ∧ LInv c S M s₀ k' s' := by
  unfold Core.wide
  refine WP.alloc hwb (by rw [h.sp]; exact hp.wb_le hd) ?_
  refine WP.seq (WP.mono (wlevels_ok h0 hp hd (Nat.le_of_lt hwb.2.1) hl hk h.toW) fun s₁ ⟨k₁, hk₁, h₁⟩ => ?_)
  refine WP.mono (wwipe_wp hp hd hwb.2.1 h₁) fun s₂ h₂ ml ul hfl => ⟨k₁, hk₁, ?_⟩
  rw [h.sp] at hfl
  have h₃ : WInv wb c S M s₀ k₁ { s₂ with mem := ml, unknowns := ul } :=
    h₂.congr hp hd (fun _ _ => rfl) rfl rfl rfl hfl
  exact h₃.inv.congr rfl rfl rfl rfl rfl

/-- The blocks the groups left, one at a time. -/
theorem mid_wp' (hp : UPre c S M s₀) (hM : ModeOk c M) {k : Nat} (hk : k ≤ N c s₀) {s₁ : State}
    (h : LInv c S M s₀ k s₁) (hz : s₁.z = decide (N c s₀ - k = 0)) (hsy : s₁.syms = s₀.syms) :
    WP isa (.ite .eq (.block []) (.loop (c.body M) .ne)) s₁ (LInv c S M s₀ (N c s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N c s₀ - k = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N c s₀ - k = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    obtain e : k = N c s₀ := by omega_using [hn, hk]
    exact e ▸ h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp hM (by omega_using [hn]) h hsy

end

/-- Whether any blocks are left. -/
theorem cmp7_wp {s : State} :
    WP isa (.block [.cmp .r7 (.imm 0)]) s fun s' => Fupd s s' ∧ s'.z = (s.gpr .r7 - 0 == 0) :=
  wp_cmp (op2_imm (by decide)) fun _ f z => WP.block_nil ⟨f, z⟩

/-- The whole function meets `Core.seq`'s contract, with the buffer's bytes
of stack more. -/
theorem seqW_wp {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M) {wb : Nat}
    (hwb : BufOk wb) {wm : WMode} {lgs : List Nat} (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) {s₀ : State}
    (hpre : (seqArm c (S₀.deeper wb h0) M).pre s₀) :
    WP isa (c.seqW M wm lgs wb) s₀ fun s' => abiPreserved s₀ s' ∧ (seqArm c (S₀.deeper wb h0) M).post s₀ s' := by
  have hp := UPre.of hpre
  have hd := S₀.deeper_deep wb h0
  have hNlt := N_lt c s₀
  unfold Core.seqW
  refine WP.seq (VG.Arm.WP.mono_syms (prologue_wp hp) fun s₁ ⟨h₁, _⟩ sy₁ => ?_)
  refine WP.seq (VG.Arm.WP.mono_syms (wide_wp h0 hp hd hwb hl (Nat.zero_le _) h₁) fun s₂ ⟨k, hk, h₂⟩ sy₂ => ?_)
  refine WP.seq (VG.Arm.WP.mono_syms cmp7_wp fun s₃ ⟨f₃, z₃⟩ sy₃ => ?_)
  obtain h₃ : LInv c (S₀.deeper wb h0) M s₀ k s₃ := h₂.congr f₃.gpr f₃.mem f₃.rd f₃.wr f₃.sp
  refine WP.seq (WP.mono (mid_wp' hp hM hk h₃ (by rw [z₃, h₂.r7]; exact cmp0 (by omega_using [hNlt]))
    (sy₃.trans (sy₂.trans sy₁))) fun _ h₄ => ?_)
  rw [WP.block_append_iff]
  exact WP.mono (finish_wp hp h₄) fun _ h₅ => epilogue_wp hp h₅

end VG.Proof.Modes.Arm

end

end

/-! ### `Modes.Arm.Ctr`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem ctr_ok (c : Core) (hbs : c.bs = 16) : ModeOk c ctr := by
  refine ⟨by rfl, ?_, by decide, ?_⟩
  · simp [ctr, opOk, hbs]
  · simpa [ctr, Core.base, hbs, oOff] using (show encodable (BitVec.ofNat 32 56) = true by decide)

theorem runSeq_ctr (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq ctr ciph b xs).1 = Spec.Ctr.crypt ciph b.o xs ∧
        (runSeq ctr ciph b xs).2.o = Spec.Ctr.next b.o xs.length
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_ctr ciph (stepOf ctr ciph (b.set .d x)) xs
    have ho : (stepOf ctr ciph (b.set .d x)).o = Spec.Ctr.inc b.o := by
      simp [stepOf, runOps, runOp, ctr, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, Spec.Ctr.crypt, List.length_cons, Spec.Ctr.counters,
        List.map_cons, List.zipWith_cons_cons]
      simp [stepOf, runOps, runOp, ctr, Blks.set, Blks.get]
    · simp only [runSeq, ih.2, List.length_cons, AesCtr.next_succ']

theorem ctr_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S ctr).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)
    let iv := Spec.Aes.bytesAt s.mem (State.addr (ivArg c s)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (dArg c s)) (nArg c s).toNat = Spec.Ctr.crypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (ivArg c s)) c.bs = Spec.Ctr.next iv (nArg c s).toNat := by
  have e := runSeq_ctr (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (scArg c s) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat)
  rw [length_blocksOf] at e
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

end VG.Proof.Modes.Arm

end

end

/-! ### `Modes.Arm.WideCT`, which the modules that import this one used -/

section

/-!
# The modes a group of blocks at a time on ARMv7: constant time

Two runs of `Core.seqW` from states that agree on the public arguments are
related piece by piece (`RelCT`), as those of `Core.seq` are (`SeqCT.lean`),
whose proof covers the prologue, the blocks one at a time and the epilogue
here too. Of the groups: the taint analysis covers the code between the
calls, from the registers the correctness proof pins to the public
arguments (`WInv`) and the buffer's address, the stack pointer, which the
analysis is given in `r12` after each `add r12, sp, #0` (a block of its
own, since the analysis does not know the stack pointer of a frame to be
public); each call of the core is constant time by the core's own proof,
its public data (the schedule's and the blocks' addresses, the number of
blocks and the stack pointer) being the same in both runs; and both runs
take the same number of groups, the number of blocks being public.

The code between the calls depends on the core and the wide mode, so its
taint checks are hypotheses (`WideTaint`, with `SeqTaint` for the rest),
which each cipher's instance proves with `taint_decide`.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Proof.MdStream.Arm (Upd eval_eq eval_ne cmp0)

/-- The taint checks of the code between the calls of the groups of
`2 ^ lg` blocks. -/
structure LevelTaint (c : Core) (wm : WMode) (lg : Nat) : Prop where
  head : ∃ h, (taint.check (Taint.ofRegs [.r7]) (.block (Core.groupsLeft lg)) h).isSome = true
  pre : ∃ h, (taint.check (Taint.ofRegs (.r12 :: loopRegs c))
    (.block (c.wopsCode (wm.pre (2 ^ lg)) ++ c.wcallArgs wm.onW (2 ^ lg))) h).isSome = true
  post : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8, .r12])
    (.block (c.wopsCode (wm.post (2 ^ lg)) ++ c.wadvance lg)) h).isSome = true

/-- The taint checks of the code between the calls of `c.wide wm lgs wb`. -/
structure WideTaint (c : Core) (wm : WMode) (lgs : List Nat) (wb : Nat) : Prop where
  levels : ∀ lg ∈ lgs, LevelTaint c wm lg
  wipe : ∃ h, (taint.check (Taint.ofRegs [.r12])
    (.block (.mov .r2 (.imm 0) :: Impl.StackScratch.Arm.wipeStores (wb / 4))) h).isSome = true

theorem wbuf_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block Core.wbuf) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp7_taint : ∃ h, (taint.check (Taint.ofRegs [.r7]) (.block [.cmp .r7 (.imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two runs of no instructions. -/
theorem relCT_nil {P : State → State → Prop} : RelCT isa P (.block []) P := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

/-- Two runs of a frame that reserves stack leak the same trace if the runs
of its body do, and end as the frame's end leaves what the body's runs end
in, whatever memory (differing from the body's only in the released frame)
and unknowns the release leaves. -/
theorem RelCT.allocFrameQ {bytes : Nat} {body : Prog isa} {P Q : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocated bytes s₁ ∧ b = allocated bytes s₂) body Q) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes))
      fun a b => ∃ t₁ t₂, Q t₁ t₂ ∧
        (Frame [⟨State.addr t₁.sp, bytes⟩] t₁.mem a.mem ∧
          a = { freed bytes t₁ with mem := a.mem, unknowns := a.unknowns }) ∧
        (Frame [⟨State.addr t₂.sp, bytes⟩] t₂.mem b.mem ∧
          b = { freed bytes t₂ with mem := b.mem, unknowns := b.unknowns }) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea : ∀ {s a : State}, isa.push (.alloc bytes) s = some a → a = allocated bytes s := by
        intro s a h
        simp only [isa, push] at h
        split at h <;> [cases h; cases h]
        rfl
      have ef : ∀ {a t s' : State}, isa.pop (.free bytes) a t = some s' →
          Frame [⟨State.addr t.sp, bytes⟩] t.mem s'.mem ∧
            s' = { freed bytes t with mem := s'.mem, unknowns := s'.unknowns } := by
        intro a t s' h
        simp only [isa, pop] at h
        split at h <;> [cases h; cases h]
        exact ⟨lose_frame _ _ _ _, rfl⟩
      obtain ⟨ht, hq⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, ea p₁, ea p₂⟩ b₁ b₂
      refine ⟨?_, _, _, hq, ef q₁, ef q₂⟩
      rw [ht]
      simp only [addrs]

/-- The arguments in registers of two calls with the same schedule, number
of rounds, blocks and number of blocks. -/
theorem CallPreN.regs_eq {c : Core} {S : CoreSpec c} {s s' : State} {K R B : BitVec 32} {G : Nat}
    (p : CallPreN c S s K R B G) (p' : CallPreN c S s' K R B G) :
    s.gpr .r0 = s'.gpr .r0 ∧ s.gpr .r1 = s'.gpr .r1 ∧ s.gpr .r2 = s'.gpr .r2 ∧
      (c.r3Pub = true → s.gpr .r3 = s'.gpr .r3) := by
  have rD := p.rd.trans p'.rd.symm
  have rN := p.rn.trans p'.rn.symm
  refine ⟨by rw [p.r0, p'.r0], ?_, ?_, fun hr => ?_⟩
  · cases hr : c.rounds
    · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
      rwa [hD] at rD
    · rw [p.r1 hr, p'.r1 hr]
  · cases hr : c.rounds
    · have hN : c.nReg = .r2 := by unfold Core.nReg; rw [hr]; rfl
      rwa [hN] at rN
    · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
      rwa [hD] at rD
  · cases hr' : c.rounds
    · have hs : c.arg3.isSome = true := by simpa [Core.r3Pub, hr'] using hr
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      rw [p.a3 k hk, p'.a3 k hk]
    · have hN : c.nReg = .r3 := by unfold Core.nReg; rw [hr']; rfl
      rwa [hN] at rN

/-- The relation before a group of `G` blocks, in two runs. -/
def WBRel (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (G : Nat) (s₀ s₀' : State) (k : Nat)
    (s₁ s₂ : State) : Prop :=
  (k + G ≤ N c s₀ ∧ WInv wb c S M s₀ k s₁) ∧ (k + G ≤ N c s₀' ∧ WInv wb c S M s₀' k s₂)

/-- What is known once the buffer's address is in `r12`. -/
def WAfterBuf (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (G : Nat) (s₀ : State) (k : Nat)
    (s₁ : State) : Prop :=
  ∃ s, (k + G ≤ N c s₀ ∧ WInv wb c S M s₀ k s) ∧ Upd s s₁ .r12 s.sp

/-- What is known after the code before a group's call. -/
def WAfterArgs (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (pre : List WOp) (onW : Bool) (G : Nat)
    (s₀ : State) (k : Nat) (s₃ : State) : Prop :=
  ∃ s, (k + G ≤ N c s₀ ∧ WInv wb c S M s₀ k s) ∧ WMid wb c M pre onW s₀ G k s s₃

/-- What is known once the buffer's address is in `r12` again, after the call. -/
def WAfterBuf2 (wb : Nat) (c : Core) (M : Mode) (s₀ : State) (k : Nat) (s₅ : State) : Prop :=
  ∃ s₄, WAfterCall wb c M s₀ k s₄ ∧ Upd s₄ s₅ .r12 s₄.sp

/-- The relation between the groups, in two runs: as many blocks done. -/
def WRel (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N c s₀ ∧ WInv wb c S M s₀ k s₁ ∧ WInv wb c S M s₀' k s₂

/-- The relation of a level's loop, with the number of blocks left. -/
def WLRel (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (lg : Nat) (s₀ s₀' : State) (n : Nat)
    (s₁ s₂ : State) : Prop :=
  ∃ j, n = N c s₀ - j ∧ WBRel wb c S M (2 ^ lg) s₀ s₀' j s₁ s₂

/-- The relation around the groups, in two runs: as many blocks done. -/
def LRelK (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N c s₀ ∧ LInv c S M s₀ k s₁ ∧ LInv c S M s₀' k s₂

section
variable {c : Core} {S₀ S : CoreSpec c} {M : Mode} {s₀ s₀' : State} {wb : Nat}

theorem pub_Wp (hq : (seqArm c S M).pub s₀ s₀') : Wp wb s₀' = Wp wb s₀ := by
  simp only [Wp]; rw [pub_sp hq]

/-- One group from `k` blocks is constant time. -/
theorem wbody_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) (hT : LevelTaint c wm lg) (k : Nat) :
    RelCT isa (WBRel wb c S M (2 ^ lg) s₀ s₀' k) (c.wbody wm lg) fun _ _ => True := by
  have hw := hl.ok
  have eW := pub_Wp (wb := wb) hq
  -- The buffer's address.
  have a := rel_agree (F := fun s => k + 2 ^ lg ≤ N c s₀ ∧ WInv wb c S M s₀ k s)
    (F' := fun s => k + 2 ^ lg ≤ N c s₀' ∧ WInv wb c S M s₀' k s)
    (G := WAfterBuf wb c S M (2 ^ lg) s₀ k) (G' := WAfterBuf wb c S M (2 ^ lg) s₀' k) (Taint.ofRegs [])
    (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) wbuf_taint
    (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩) (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩)
  -- The operations before the call, and its arguments.
  have b := rel_agree (F := WAfterBuf wb c S M (2 ^ lg) s₀ k) (F' := WAfterBuf wb c S M (2 ^ lg) s₀' k)
    (G := WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀ k)
    (G' := WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k) (Taint.ofRegs (.r12 :: loopRegs c))
    (fun s₁ s₂ ⟨s, h, u⟩ ⟨s', h', u'⟩ => Taint.agree_ofRegs fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [u.gpr, u'.gpr, h.2.sp, h'.2.sp, eW]
      · have h12 : r ≠ .r12 := by
          rintro rfl
          revert hr
          unfold loopRegs
          split <;> decide
        rw [u.other _ h12, u'.other _ h12]
        exact LInv.agree hq h.2.inv h'.2.inv r hr)
    hT.pre
    (fun s₁ ⟨s, h, u⟩ => WP.mono (wpre_wp hp hd hW hl h.1 h.2 u) fun _ x => ⟨s, h, x⟩)
    (fun s₁ ⟨s, h, u⟩ => WP.mono (wpre_wp hp' hd hW hl h.1 h.2 u) fun _ x => ⟨s, h, x⟩)
  -- The call, with the same regions in both runs.
  have cpre : ∀ {t₀ : State} (_ : UPre c S M t₀) {s₃ : State},
      WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) t₀ k s₃ →
      CallPreN c S₀ s₃ (Kp t₀) (Rp t₀) (if wm.onW then Wp wb t₀ else Dk t₀ c M k) (2 ^ lg) :=
    fun {_} hpt {_} ⟨_, h, x⟩ => x.callPre hpt hd hw.byte hw.pos h.1 hl.fit hW h.2
  have cpre' : ∀ {s₃ : State}, WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k s₃ →
      CallPreN c S₀ s₃ (Kp s₀) (Rp s₀) (if wm.onW then Wp wb s₀ else Dk s₀ c M k) (2 ^ lg) := fun h => by
    have p := cpre hp' h
    rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, eW] at p
    exact p
  have spA : ∀ {s₃ s₃' : State}, WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀ k s₃ →
      WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k s₃' → s₃.sp = s₃'.sp :=
    fun ⟨_, h, x⟩ ⟨_, h', x'⟩ => by rw [x.sp, h.2.sp, x'.sp, h'.2.sp, eW]
  have callR : RelCT isa (fun s₃ s₃' => WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀ k s₃ ∧
      WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k s₃') (.call c.name c.code)
      fun _ _ => True := by
    refine RelCT.call S₀.correct S₀.ct [⟨State.addr (Kp s₀), S₀.keyLen⟩]
      [⟨State.addr (if wm.onW then Wp wb s₀ else Dk s₀ c M k), c.bs * 2 ^ lg⟩] fun s₃ s₃' ⟨h, h'⟩ => ?_
    have p := cpre hp h
    have p' := cpre' h'
    obtain ⟨r0, r1, r2, r3⟩ := p.regs_eq p'
    refine ⟨S₀.pre_of h0 _ p.ecbPre, S₀.pre_of h0 _ p'.ecbPre, S₀.pub_of h0 _ _ ?_ ?_ ?_ ?_ fun hr => ?_,
      Covers.append_left p.rK (Covers.right p.wB), p.wB, Covers.append_left p'.rK (Covers.right p'.wB), p'.wB⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]; exact spA h h'
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r0]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r1]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r2]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r3 hr]
  have cr := rel_wp (G := WAfterCall wb c M s₀ k) (G' := WAfterCall wb c M s₀' k) callR
    (fun _ h => WP.mono (callN_wp S₀ (cpre hp h) h0) fun _ cp => by
      obtain ⟨_, x, y⟩ := h; exact wafterCall x.2 y cp)
    (fun _ h => WP.mono (callN_wp S₀ (cpre hp' h) h0) fun _ cp => by
      obtain ⟨_, x, y⟩ := h; exact wafterCall x.2 y cp)
  -- The buffer's address again, and the operations after the call.
  have d := rel_agree (F := WAfterCall wb c M s₀ k) (F' := WAfterCall wb c M s₀' k)
    (G := WAfterBuf2 wb c M s₀ k) (G' := WAfterBuf2 wb c M s₀' k) (Taint.ofRegs [])
    (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) wbuf_taint
    (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩) (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩)
  obtain ⟨_, hB⟩ := hT.post
  have e := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => WAfterBuf2 wb c M s₀ k s₁ ∧ WAfterBuf2 wb c M s₀' k s₂)
    (Taint.ofRegs [.r6, .r7, .r8, .r12])
    (fun s₁ s₂ ⟨⟨t, h, u⟩, ⟨t', h', u'⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [u.other _ (by decide), u'.other _ (by decide), h.r6, h'.r6, pub_Dk hq]
      · rw [u.other _ (by decide), u'.other _ (by decide), h.r7, h'.r7, pub_N hq]
      · rw [u.other _ (by decide), u'.other _ (by decide), h.r8, h'.r8, pub_Sc hq]
      · rw [u.gpr, u'.gpr, h.sp, h'.sp, eW]) hB
  unfold Core.wbody
  exact (a.mono (fun _ _ h => h) fun _ _ h => h).seq ((b.mono (fun _ _ h => h) fun _ _ h => h).seq
    ((cr.mono (fun _ _ h => h) fun _ _ h => h).seq ((d.mono (fun _ _ h => h) fun _ _ h => h).seq
      (e.mono (fun _ _ h => h) fun _ _ h => h))))

/-- The loop of a level is constant time. -/
theorem wloop_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) (hT : LevelTaint c wm lg) (n : Nat) :
    RelCT isa (WLRel wb c S M lg s₀ s₀' n) (.loop (c.wbody wm lg) .ne) (WRel wb c S M s₀ s₀') := by
  refine RelCT.loop (M := isa) (WLRel wb c S M lg s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hG := hl.ok.pos
  refine (RelCT.exists_ fun j => ?_).mono (fun s₁ s₂ (h : WLRel wb c S M lg s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N c s₀ - j
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (wbody_ct h0 hp hp' hq hd hW hl hT j).wp
    (F₁ := fun (s : State) => (WInv wb c S M s₀ (j + 2 ^ lg) s ∧
      s.z = decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0)) ∧ j + 2 ^ lg ≤ N c s₀)
    (F₂ := fun (s : State) => WInv wb c S M s₀' (j + 2 ^ lg) s ∧
      s.z = decide ((N c s₀' - (j + 2 ^ lg)) / 2 ^ lg = 0))
    fun _ _ h => ⟨WP.mono (wbody_ok h0 hp hd hW hl h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩,
      wbody_ok h0 hp' hd hW hl h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hj⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun _ => ⟨j + 2 ^ lg, hj, l₁, l₂⟩, fun ht => ?_⟩
  rw [e₁] at ht
  have h0' : ¬ (N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0 := by simpa using ht
  rw [Nat.div_eq_zero_iff_lt hG] at h0'
  exact ⟨N c s₀ - (j + 2 ^ lg), by omega_using [hj, hG], j + 2 ^ lg, rfl, ⟨by omega_using [h0', hj], l₁⟩,
    ⟨by rw [← hN]; omega_using [h0', hj], l₂⟩⟩

/-- A level is constant time. -/
theorem wlevel_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) (hT : LevelTaint c wm lg) :
    RelCT isa (WRel wb c S M s₀ s₀') (c.wlevel wm lg) (WRel wb c S M s₀ s₀') := by
  have hN := pub_N hq
  have hG := hl.ok.pos
  unfold Core.wlevel
  refine RelCT.exists_ fun k => ?_
  have head := rel_agree (F := fun s => k ≤ N c s₀ ∧ WInv wb c S M s₀ k s)
    (F' := fun s => WInv wb c S M s₀' k s)
    (G := fun s => (k ≤ N c s₀ ∧ WInv wb c S M s₀ k s) ∧ s.z = decide ((N c s₀ - k) / 2 ^ lg = 0))
    (G' := fun s => WInv wb c S M s₀' k s ∧ s.z = decide ((N c s₀' - k) / 2 ^ lg = 0))
    (Taint.ofRegs [.r7])
    (fun s s' h h' => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have e : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k) := h.2.inv.r7
      have e' : s'.gpr .r7 = BitVec.ofNat 32 (N c s₀' - k) := h'.inv.r7
      rw [e, e', hN])
    hT.head
    (fun s h => WP.mono (whead_wp hp hd hl.sh h.2) fun _ x => ⟨⟨h.1, x.1⟩, x.2⟩)
    (fun s h => whead_wp hp' hd hl.sh h)
  refine (head.mono (fun s₁ s₂ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun _ _ h => h).seq ?_
  have ev {s : State} (h : s.z = decide ((N c s₀ - k) / 2 ^ lg = 0)) :
      isa.eval .eq s = some (decide ((N c s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide ((N c s₀' - k) / 2 ^ lg = 0)) :
      isa.eval .eq s = some (decide ((N c s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
  · exact relCT_nil.mono (fun _ _ h => h) fun a b h => ⟨k, h.1.1.1.1, h.1.1.1.2, h.1.2.1⟩
  · refine (wloop_ct h0 hp hp' hq hd hW hl hT (N c s₀ - k)).mono (fun a b h => ?_) fun _ _ h => h
    have hf := h.2
    rw [ev h.1.1.2] at hf
    have h0' : ¬ (N c s₀ - k) / 2 ^ lg = 0 := by simpa using hf
    rw [Nat.div_eq_zero_iff_lt hG] at h0'
    exact ⟨k, rfl, ⟨by omega_using [h0', h.1.1.1.1], h.1.1.1.2⟩,
      ⟨by rw [← hN]; omega_using [h0', h.1.1.1.1], h.1.2.1⟩⟩

/-- The levels are constant time. -/
theorem wlevels_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hT : ∀ lg ∈ lgs, LevelTaint c wm lg) :
    RelCT isa (WRel wb c S M s₀ s₀') (c.wlevels wm lgs) (WRel wb c S M s₀ s₀') := by
  induction lgs with
  | nil => exact relCT_nil
  | cons lg lgs ih =>
    show RelCT isa _ (.seq (c.wlevel wm lg) (c.wlevels wm lgs)) _
    exact (wlevel_ct h0 hp hp' hq hd hW (hl lg List.mem_cons_self) (hT lg List.mem_cons_self)).seq
      (ih (fun lg' h' => hl lg' (List.mem_cons_of_mem _ h')) fun lg' h' => hT lg' (List.mem_cons_of_mem _ h'))

/-- The groups, in the buffer's frame, are constant time. -/
theorem wide_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hT : WideTaint c wm lgs wb) :
    RelCT isa (LRelK c S M s₀ s₀') (c.wide wm lgs wb) (LRelK c S M s₀ s₀') := by
  have eW := pub_Wp (wb := wb) hq
  unfold Core.wide
  refine (RelCT.allocFrameQ (Q := WRel wb c S M s₀ s₀') ?_).mono (fun _ _ h => h)
    fun a b ⟨t₁, t₂, ⟨k, hk, h₁, h₂⟩, ⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ => by
      rw [h₁.sp] at f₁
      rw [h₂.sp] at f₂
      have i₁ : WInv wb c S M s₀ k { t₁ with mem := a.mem, unknowns := a.unknowns } :=
        h₁.congr hp hd (fun _ _ => rfl) rfl rfl rfl f₁
      have i₂ : WInv wb c S M s₀' k { t₂ with mem := b.mem, unknowns := b.unknowns } :=
        h₂.congr hp' hd (fun _ _ => rfl) rfl rfl rfl f₂
      exact ⟨k, hk, by rw [e₁]; exact i₁.inv.congr rfl rfl rfl rfl rfl,
        by rw [e₂]; exact i₂.inv.congr rfl rfl rfl rfl rfl⟩
  refine RelCT.seq (R := WRel wb c S M s₀ s₀')
    ((wlevels_ct h0 hp hp' hq hd (Nat.le_of_lt hwb.2.1) hl hT.levels).mono
      (fun a b ⟨s₁, s₂, ⟨k, hk, h₁, h₂⟩, e₁, e₂⟩ => ⟨k, hk, by rw [e₁]; exact h₁.toW, by rw [e₂]; exact h₂.toW⟩)
      fun _ _ h => h) ?_
  -- The buffer zeroed.
  refine RelCT.exists_ fun k => ?_
  by_cases hk : k ≤ N c s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.1
  have a := rel_agree (F := fun s => WInv wb c S M s₀ k s) (F' := fun s => WInv wb c S M s₀' k s)
    (G := fun s₁ => ∃ s, WInv wb c S M s₀ k s ∧ Upd s s₁ .r12 s.sp)
    (G' := fun s₁ => ∃ s, WInv wb c S M s₀' k s ∧ Upd s s₁ .r12 s.sp) (Taint.ofRegs [])
    (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) wbuf_taint
    (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩) (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩)
  obtain ⟨_, hw⟩ := hT.wipe
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (∃ s, WInv wb c S M s₀ k s ∧ Upd s s₁ .r12 s.sp) ∧
      ∃ s, WInv wb c S M s₀' k s ∧ Upd s s₂ .r12 s.sp)
    (Taint.ofRegs [.r12]) (fun s₁ s₂ ⟨⟨t, h, u⟩, ⟨t', h', u'⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [u.gpr, u'.gpr, h.sp, h'.sp, eW]) hw
  exact ((a.seq b).wp (F₁ := WInv wb c S M s₀ k) (F₂ := WInv wb c S M s₀' k) fun s₁ s₂ h =>
    ⟨wwipe_wp hp hd hwb.2.1 h.1, wwipe_wp hp' hd hwb.2.1 h.2⟩).mono (fun s₁ s₂ h => ⟨h.2.1, h.2.2⟩)
    fun s₁ s₂ h => ⟨k, hk, h.2.1, h.2.2⟩

end

theorem seqW_rel {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaint c M) {wb : Nat} (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hTw : WideTaint c wm lgs wb) {s₀ s₀' : State}
    (hpre : (seqArm c (S₀.deeper wb h0) M).pre s₀) (hpre' : (seqArm c (S₀.deeper wb h0) M).pre s₀')
    (hq : (seqArm c (S₀.deeper wb h0) M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (c.seqW M wm lgs wb) fun _ _ => True := by
  have hp := UPre.of hpre
  have hp' := UPre.of hpre'
  have hd := S₀.deeper_deep wb h0
  obtain ⟨_, hepi⟩ := hT.epi
  have hN := pub_N hq
  have hsp := pub_sp hq
  have hNlt := N_lt c s₀
  have wfA : ∀ {s : State}, UPre c (S₀.deeper wb h0) M s →
      s.sp.toNat + argBytes c ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, argBytes c⟩ r :=
    fun {s} h => by
      have e : (⟨State.addr s.sp, argBytes c⟩ : Region) = argR c s := by simp [stackArgAddr]
      exact ⟨h.spF, by rw [e]; exact h.arg_wr⟩
  have hj : argBytes c = 4 * (if c.rounds then 2 else 1) := by unfold argBytes; split <;> rfl
  -- The prologue.
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => (LInv c (S₀.deeper wb h0) M s₀ 0 s ∧ s.z = decide (N c s₀ = 0)) ∧ s.syms = s₀.syms)
    (G' := fun s => (LInv c (S₀.deeper wb h0) M s₀' 0 s ∧ s.z = decide (N c s₀' = 0)) ∧ s.syms = s₀'.syms)
    (argTaint [.r0, .r1, .r2, .r3] (argBytes c))
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (hj ▸ argMem_of (j := if c.rounds then 2 else 1) hsp (hj ▸ hp.spF) fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · cases hr : c.rounds <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at hi
        · rcases (by omega_using [hi] : i = 0) with rfl
          exact hq.2.2.2.2.2.1
        · rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
          · exact hq.2.2.2.2.2.1
          · exact hq.2.2.2.2.2.2.1 hr) hT.pro
    (fun s e => by rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp) fun _ h sy => ⟨h, sy⟩)
    (fun s e => by rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp') fun _ h sy => ⟨h, sy⟩)
  -- The groups.
  have wide := (RelCT.mono
    (P' := fun (a b : State) => LRelK c (S₀.deeper wb h0) M s₀ s₀' a b ∧ a.syms = s₀.syms ∧ b.syms = s₀'.syms)
    (wide_ct h0 hp hp' hq hd hwb hl hTw) (fun _ _ h => h.1) fun _ _ h => h).wp
    (F₁ := fun (s : State) => s.syms = s₀.syms) (F₂ := fun (s : State) => s.syms = s₀'.syms)
    fun a b h => by
      obtain ⟨⟨k, hk, h₁, h₂⟩, sy, sy'⟩ := h
      exact ⟨VG.Arm.WP.mono_syms (wide_wp h0 hp hd hwb hl hk h₁) fun _ _ y => y.trans sy,
        VG.Arm.WP.mono_syms (wide_wp h0 hp' hd hwb hl (by rw [← hN]; exact hk) h₂) fun _ _ y => y.trans sy'⟩
  -- The blocks left, one at a time, and the epilogue.
  have epi := RelCT.taint (A := taint)
    (P := fun a b => LInv c (S₀.deeper wb h0) M s₀ (N c s₀) a ∧ LInv c (S₀.deeper wb h0) M s₀' (N c s₀') b)
    (Taint.ofRegs [.r5, .r8]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, pub_Iv hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hepi
  have rest : RelCT isa
      (fun a b => LRelK c (S₀.deeper wb h0) M s₀ s₀' a b ∧ a.syms = s₀.syms ∧ b.syms = s₀'.syms)
      (.seq (.block [.cmp .r7 (.imm 0)]) (.seq (.ite .eq (.block []) (.loop (c.body M) .ne))
        (.block (c.finish M ++ restore)))) fun _ _ => True := by
    refine (RelCT.exists_ (P := fun k (a b : State) => (k ≤ N c s₀ ∧ LInv c (S₀.deeper wb h0) M s₀ k a ∧
      LInv c (S₀.deeper wb h0) M s₀' k b) ∧ a.syms = s₀.syms ∧ b.syms = s₀'.syms) fun k => ?_).mono
      (fun a b ⟨⟨k, h⟩, sy⟩ => ⟨k, h, sy⟩) fun _ _ h => h
    by_cases hk : k ≤ N c s₀
    swap
    · exact RelCT.of_false fun _ _ h => hk h.1.1
    have cmp := rel_agree
      (F := fun s => LInv c (S₀.deeper wb h0) M s₀ k s ∧ s.syms = s₀.syms)
      (F' := fun s => LInv c (S₀.deeper wb h0) M s₀' k s ∧ s.syms = s₀'.syms)
      (G := fun s => (LInv c (S₀.deeper wb h0) M s₀ k s ∧ s.z = decide (N c s₀ - k = 0)) ∧ s.syms = s₀.syms)
      (G' := fun s => (LInv c (S₀.deeper wb h0) M s₀' k s ∧ s.z = decide (N c s₀' - k = 0)) ∧ s.syms = s₀'.syms)
      (Taint.ofRegs [.r7])
      (fun s s' h h' => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.r7, h'.1.r7, hN])
      cmp7_taint
      (fun s h => VG.Arm.WP.mono_syms cmp7_wp fun s' x sy =>
        ⟨⟨h.1.congr x.1.gpr x.1.mem x.1.rd x.1.wr x.1.sp,
          by rw [x.2, h.1.r7]; exact cmp0 (by omega_using [hNlt])⟩, sy.trans h.2⟩)
      (fun s h => VG.Arm.WP.mono_syms cmp7_wp fun s' x sy =>
        ⟨⟨h.1.congr x.1.gpr x.1.mem x.1.rd x.1.wr x.1.sp,
          by rw [x.2, h.1.r7]; exact cmp0 (by rw [← hN]; omega_using [hNlt])⟩, sy.trans h.2⟩)
    refine (cmp.mono (fun a b h => ⟨⟨h.1.2.1, h.2.1⟩, ⟨h.1.2.2, h.2.2⟩⟩) fun _ _ h => h).seq ?_
    have ev {s : State} (h : s.z = decide (N c s₀ - k = 0)) : isa.eval .eq s = some (decide (N c s₀ - k = 0)) := by
      show VG.Arm.eval .eq s = _; rw [eval_eq, h]
    have ev' {s : State} (h : s.z = decide (N c s₀' - k = 0)) :
        isa.eval .eq s = some (decide (N c s₀ - k = 0)) := by
      show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
    refine RelCT.seq (R := fun a b => LInv c (S₀.deeper wb h0) M s₀ (N c s₀) a ∧
      LInv c (S₀.deeper wb h0) M s₀' (N c s₀') b) (RelCT.ite (fun a b h => by rw [ev h.1.1.2, ev' h.2.1.2]) ?_ ?_)
      epi
    · refine relCT_nil.mono (fun _ _ h => h) fun a b h => ?_
      have ht := h.2
      rw [ev h.1.1.1.2] at ht
      have e : k = N c s₀ := by
        have : N c s₀ - k = 0 := by simpa using ht
        omega_using [this, hk]
      exact ⟨e ▸ h.1.1.1.1, by rw [← hN, ← e]; exact h.1.2.1.1⟩
    · refine (loop_ct hp hp' hq hM hT (N c s₀ - k)).mono (fun a b h => ?_) fun _ _ h => h
      have hf := h.2
      rw [ev h.1.1.1.2] at hf
      have h0' : N c s₀ - k ≠ 0 := by simpa using hf
      exact ⟨k, rfl, ⟨by omega_using [h0'], h.1.1.1.1, h.1.1.2⟩,
        ⟨by rw [← hN]; omega_using [h0'], h.1.2.1.1, h.1.2.2⟩⟩
  unfold Core.seqW
  exact (pro.mono (fun _ _ h => h) fun a b h => ⟨⟨0, Nat.zero_le _, h.1.1.1, h.2.1.1⟩, h.1.2, h.2.2⟩).seq
    ((wide.mono (fun _ _ h => h) fun a b h => ⟨h.1, h.2.1, h.2.2⟩).seq rest)

theorem seqW_ct {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaint c M) {wb : Nat} (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hTw : WideTaint c wm lgs wb) :
    ConstantTime isa (seqArm c (S₀.deeper wb h0) M).pre (seqArm c (S₀.deeper wb h0) M).pub (c.seqW M wm lgs wb) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seqW_rel h0 S₀ hM hT hwb hl hTw h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A core that takes no working space, a mode and a wide mode whose groups
compute its steps, and whose code between the calls passes the taint checks,
give a function that is correct and constant time under `seqArm` with the
buffer's bytes of stack more, and so under any contract that implies. -/
theorem seqW_verified {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaint c M) {wb : Nat} (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hTw : WideTaint c wm lgs wb) {k : Contract isa}
    (hk : (seqArm c (S₀.deeper wb h0) M).Implies k) : Verified Arm.target (c.seqW M wm lgs wb) k :=
  Verified.of_correct (fun _ hs => seqW_wp h0 S₀ hM hwb hl hs) (seqW_ct h0 S₀ hM hT hwb hl hTw) hk

end VG.Proof.Modes.Arm

end

end

/-!
# CTR, CBC decryption and CFB decryption a group at a time on ARMv7

`ctrW`, `cbcDecW` and `cfbDecW` (`Impl/Modes/Arm/Wide.lean`), in groups of
8, 4 and 2 blocks of 16 bytes (`wideLevels`, with the buffer of `wideBuf`
bytes), are what `Core.seqW` needs of a wide mode (`LevelOk`): a group
leaves the data, the chaining block and the spare block as that many steps
of `ctr`, `cbcDecChained` or `cfbDec` do (`WideSim`), which evaluating both
on any blocks shows.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem ctrW_sim : ∀ lg ∈ wideLevels, WideSim ctr ctrW (2 ^ lg) := by
  intro lg h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> constructor <;> intro ciph b <;>
    simp [wstep, ctrW, wrunOps, wrunOp, wset, wciph, runSeq, stepOf, runOps, runOp, ctr, Blks.set, Blks.get,
      List.range_succ]

theorem cbcDecW_sim : ∀ lg ∈ wideLevels, WideSim cbcDecChained cbcDecW (2 ^ lg) := by
  intro lg h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> constructor <;> intro ciph b <;>
    simp [wstep, cbcDecW, wrunOps, wrunOp, wset, wciph, runSeq, stepOf, runOps, runOp, cbcDecChained, cbcDec,
      Blks.set, Blks.get, List.range_succ]

theorem cfbDecW_sim : ∀ lg ∈ wideLevels, WideSim cfbDec cfbDecW (2 ^ lg) := by
  intro lg h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> constructor <;> intro ciph b <;>
    simp [wstep, cfbDecW, wrunOps, wrunOp, wset, wciph, runSeq, stepOf, runOps, runOp, cfbDec, Blks.set, Blks.get,
      List.range_succ]

/-- The levels of a wide mode whose groups compute the steps of `M`, on a
core of 16-byte blocks. -/
theorem levels_of_sim {c : Core} (hbs : c.bs = 16) {M : Mode} {wm : WMode} (hb : M.byte = false)
    (hpre : ∀ lg ∈ wideLevels, (wm.pre (2 ^ lg)).all (wopOk 16 (2 ^ lg)) = true)
    (hpost : ∀ lg ∈ wideLevels, (wm.post (2 ^ lg)).all (wopOk 16 (2 ^ lg)) = true)
    (hsim : ∀ lg ∈ wideLevels, WideSim M wm (2 ^ lg)) : ∀ lg ∈ wideLevels, LevelOk c M wm wideBuf lg := by
  intro lg h
  have h' := h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h'
  refine ⟨⟨?_, hb, by rw [hbs]; exact hpre lg h, by rw [hbs]; exact hpost lg h, hsim lg h⟩, ?_, ?_, ?_, ?_⟩
  · rcases h' with rfl | rfl | rfl <;> decide
  · rcases h' with rfl | rfl | rfl <;> decide
  · rw [hbs]; rcases h' with rfl | rfl | rfl <;> decide
  · rcases h' with rfl | rfl | rfl <;> decide
  · rw [hbs]; rcases h' with rfl | rfl | rfl <;> decide

theorem ctrW_levels {c : Core} (hbs : c.bs = 16) : ∀ lg ∈ wideLevels, LevelOk c ctr ctrW wideBuf lg :=
  levels_of_sim hbs rfl (by decide) (by decide) ctrW_sim

theorem cbcDecW_levels {c : Core} (hbs : c.bs = 16) :
    ∀ lg ∈ wideLevels, LevelOk c cbcDecChained cbcDecW wideBuf lg :=
  levels_of_sim hbs rfl (by decide) (by decide) cbcDecW_sim

theorem cfbDecW_levels {c : Core} (hbs : c.bs = 16) : ∀ lg ∈ wideLevels, LevelOk c cfbDec cfbDecW wideBuf lg :=
  levels_of_sim hbs rfl (by decide) (by decide) cfbDecW_sim

/-- The buffer's frame. -/
theorem wideBuf_ok : BufOk wideBuf := ⟨by decide, by decide, by decide, by decide⟩

end VG.Proof.Modes.Arm
