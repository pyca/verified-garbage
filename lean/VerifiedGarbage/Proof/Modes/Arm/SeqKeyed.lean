module

public import VerifiedGarbage.Proof.Modes.Arm.Cbc
public import VerifiedGarbage.Impl.Modes.Arm.SeqKeyed
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The modes one block at a time on ARMv7, from keys prepared once

`Core.seqK c k M` (`Impl/Modes/Arm/SeqKeyed.lean`) is `Core.seq c M` with the
two functions of `k` in place of the core's ECB function: one call of the
first before the first block, and one of the second for each block. It meets
`seqArm c S M`, the contract of `Core.seq c M` (`seqK_verified`), given what
`KeyedSpec c S k` says of the two:

* the first (`keysContract`), from the schedule and the working space
  (`KeysPre`), leaves `keysIn`, the keys of the schedule in the working
  space, which depend on the bytes of those two alone (`keysIn_frame`);
* the second (`contract`), entered as the core's ECB function is (`EcbPreS`)
  with `keysIn`, does to the blocks what the ECB function does (`post_of`,
  as `CoreSpec.post_ofS`) and keeps `keysIn`.

So the proofs are those of `Core.seq c M`, whose invariant (`LInv`), prologue
and epilogue they share, with `keysIn` beside the invariant: the mode's own
writes, to the data and to the chaining and spare blocks, are apart from the
schedule and from the callee's working space. The core `c` is called by no
code here: it gives the layout, and `S` what the cipher is.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_subs op2_imm op2_reg ofNat_beq_zero eval_eq eval_ne)

/-- What a call of the function that prepares the keys needs, in the state
it is entered in, with only the schedule readable and only the working
space (in the register of the ECB function's data) writable. -/
structure KeysPre (c : Core) (keyLen stack : Nat) (rok : BitVec 32 → Prop) (s : State) : Prop where
  stk : stack ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), keyLen⟩]
  wr : s.wr = [⟨State.addr (s.gpr c.dReg), c.stackScratch⟩]
  ks : Region.Disjoint ⟨State.addr (s.gpr .r0), keyLen⟩ ⟨State.addr (s.gpr c.dReg), c.stackScratch⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 stack, stack⟩ ⟨State.addr (s.gpr .r0), keyLen⟩
  bs : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 stack, stack⟩
    ⟨State.addr (s.gpr c.dReg), c.stackScratch⟩
  fK : (s.gpr .r0).toNat + keyLen ≤ 2 ^ 32
  fS : (s.gpr c.dReg).toNat + c.stackScratch ≤ 2 ^ 32
  rr : c.rounds = true → rok (s.gpr .r1)

/-- What the modes need of the two functions `k` that split the ECB function
of the core `c` (see above). -/
structure KeyedSpec (c : Core) (S : CoreSpec c) (k : Keyed) where
  /-- The keys of the schedule at `K`, for `R` rounds, prepared in the
  working space at `C`. -/
  keysIn : Mem → BitVec 32 → BitVec 32 → BitVec 32 → Prop
  /-- The keys depend only on the schedule's bytes and the working space's. -/
  keysIn_frame : ∀ {rs : List Region} {m m' : Mem} {K R C : BitVec 32}, Frame rs m m' →
    (∀ r ∈ rs, Region.Disjoint ⟨State.addr K, S.keyLen⟩ r) →
    (∀ r ∈ rs, Region.Disjoint ⟨State.addr C, c.stackScratch⟩ r) →
    K.toNat + S.keyLen ≤ 2 ^ 32 → C.toNat + c.stackScratch ≤ 2 ^ 32 → (c.rounds = true → S.rok R) →
    keysIn m K R C → keysIn m' K R C
  /-- A core without a number of rounds ignores `R`. -/
  keysIn_R : c.rounds = false → ∀ m K R R' C, keysIn m K R C → keysIn m K R' C
  scr : c.stackScratch ≠ 0
  /-- The function that prepares the keys: its contract, under which its code
  is correct and constant time, using at most `S.stack` bytes of stack. -/
  keysContract : Contract isa
  keysCorrect : ∀ s, keysContract.pre s →
    ∃ t s', Exec isa k.keysCode s t s' ∧ abiPreserved s s' ∧ keysContract.post s s'
  keysCt : ConstantTime isa keysContract.pre keysContract.pub k.keysCode
  keysDepth : armStack k.keysCode ≤ S.stack
  keysPre : ∀ s, KeysPre c S.keyLen S.stack S.rok s → keysContract.pre s
  keysPost : ∀ s s', KeysPre c S.keyLen S.stack S.rok s → keysContract.post s s' →
    keysIn s'.mem (s.gpr .r0) (s.gpr .r1) (s.gpr c.dReg)
  keysPub : ∀ s₁ s₂, s₁.gpr .r0 = s₂.gpr .r0 → s₁.gpr .r1 = s₂.gpr .r1 →
    (c.rounds = true → s₁.gpr .r2 = s₂.gpr .r2) → keysContract.pub s₁ s₂
  /-- The function that enciphers with the prepared keys: its contract, under
  which its code is correct and constant time, using with its call's push at
  most `S.stack` bytes of stack. -/
  contract : Contract isa
  correct : ∀ s, contract.pre s → ∃ t s', Exec isa k.code s t s' ∧ abiPreserved s s' ∧ contract.post s s'
  ct : ConstantTime isa contract.pre contract.pub k.code
  depth : armStack k.code + 8 ≤ S.stack
  pre_of : ∀ s, EcbPreS c S.keyLen S.stack S.rok S.consts s →
    keysIn s.mem (s.gpr .r0) (s.gpr .r1) (stackArg s 0) → contract.pre s
  post_of : ∀ s s', EcbPreS c S.keyLen S.stack S.rok S.consts s →
    keysIn s.mem (s.gpr .r0) (s.gpr .r1) (stackArg s 0) → contract.post s s' →
    blocksOf c.bs s'.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat =
        (blocksOf c.bs s.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat).map
          (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ∧
      keysIn s'.mem (s.gpr .r0) (s.gpr .r1) (stackArg s 0)
  pub_of : ∀ s₁ s₂, s₁.sp = s₂.sp → s₁.gpr .r0 = s₂.gpr .r0 → s₁.gpr .r1 = s₂.gpr .r1 →
    s₁.gpr .r2 = s₂.gpr .r2 → (c.r3Pub = true → s₁.gpr .r3 = s₂.gpr .r3) → stackArg s₁ 0 = stackArg s₂ 0 →
    (∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1) → contract.pub s₁ s₂

/-! ## The call on one block -/

section
variable {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {s : State} {K R B C : BitVec 32}

/-- The keys as the callee is given them, in its frame: those of the
caller's state. -/
theorem KeyedSpec.view_iff (h : CallPre c S s K R B C) (m : Mem) (rd wr : List Region) :
    X.keysIn m ((Push.view s rd wr).gpr .r0) ((Push.view s rd wr).gpr .r1) (stackArg (Push.view s rd wr) 0) ↔
      X.keysIn m K R C := by
  have h8 := h.sp8 X.scr
  rw [Push.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs), h.r0, Push.arg0 h8, h.r12 X.scr,
    Push.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs)]
  cases hr : c.rounds
  · exact ⟨X.keysIn_R hr _ _ _ _ _, X.keysIn_R hr _ _ _ _ _⟩
  · rw [h.r1 hr]

/-- The keys, on entry to the callee in its frame. -/
theorem KeyedSpec.keys_view (h : CallPre c S s K R B C) (hj : X.keysIn s.mem K R C) (rd wr : List Region) :
    X.keysIn (Push.view s rd wr).mem ((Push.view s rd wr).gpr .r0) ((Push.view s rd wr).gpr .r1)
      (stackArg (Push.view s rd wr) 0) := by
  have hs := X.scr
  have h8 := h.sp8 hs
  have dS := S.depthS hs
  have hst := h.stk
  rw [X.view_iff h, Push.view_mem]
  refine X.keysIn_frame (Push.fA h8) (fun r hr => ?_) (fun r hr => ?_) h.fK (h.fC hs) h.rok hj
  · simp only [List.mem_singleton] at hr; subst hr
    rw [belowA, addr_sub' h8]
    exact (h.bk.sub_left (VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := S.stack) (by omega_arith)
      (by omega_arith))).symm
  · simp only [List.mem_singleton] at hr; subst hr
    rw [belowA, addr_sub' h8]
    exact (h.bC.sub_left (VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := S.stack) (by omega_arith)
      (by omega_arith))).symm

/-- The call of the function that enciphers with the prepared keys, its
working space pushed: what the call of the core's ECB function leaves
(`callScr_wp`), and the keys. -/
theorem callK_wp (h : CallPre c S s K R B C) (hj : X.keysIn s.mem K R C) :
    WP isa k.callStep s fun s' => CallPost c S s K R B C s' ∧ X.keysIn s'.mem K R C := by
  have hs := X.scr
  have h8 := h.sp8 hs
  have dS := S.depthS hs
  have dK := X.depth
  have hst := h.stk
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8) (by simp) ?_
  have hsp' : (pushed [.r12, .lr] s).sp = s.sp - BitVec.ofNat 32 8 := rfl
  have hspN : (pushed [.r12, .lr] s).sp.toNat = s.sp.toNat - 8 := by rw [hsp']; exact sub_toNat' h8
  refine WP.callF X.correct (rd := [⟨State.addr K, S.keyLen⟩, Push.argR s] ++ tabRegs S.consts s)
    (wr := [⟨State.addr B, c.bs⟩, ⟨State.addr C, c.stackScratch⟩])
    (X.pre_of _ (h.ecbPreS hs) (X.keys_view h hj _ _)) (h.cov hs)
    (Push.covW (show Covers ([⟨State.addr B, c.bs⟩] ++ [⟨State.addr C, c.stackScratch⟩]) s.wr from
      Covers.append_left h.wB (h.wC hs)))
    (by rw [hspN]; omega_arith) fun s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost => ?_
  have fK : ∀ i < S.keyLen, (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 i) =
      s.mem (State.addr K + BitVec.ofNat 64 i) := fun i hi =>
    (Push.fA h8).bytes (R := ⟨State.addr K, S.keyLen⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [belowA, addr_sub' h8]
      exact (h.bk.sub_left (VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := S.stack) (by omega_arith) (by omega_arith))).symm)
      (by show S.keyLen ≤ 2 ^ 64; have := h.fK; omega_arith) hi
  have fB : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr B) c.bs = bytesAt s.mem (State.addr B) c.bs :=
    VG.Proof.Modes.bytesAt_frame (Push.fA h8) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [belowA, addr_sub' h8]
      exact (h.bb.sub_left (VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := S.stack) (by omega_arith) (by omega_arith))).symm)
      (by have := h.fB; omega_arith)
  obtain ⟨e, hj₂⟩ := X.post_of _ _ (h.ecbPreS hs) (X.keys_view h hj _ _) hpost
  refine ⟨⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, hsp']; exact BitVec.sub_add_cancel _ _
  · have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    have bel : Region.Sub (belowA s.sp S.stack) ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ := by
      rw [belowA, addr_sub' hst]; exact fun _ h => h
    refine ((Push.fA h8).sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun x hx => bel x (belowA_sub (by omega_arith) hst x hx)⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · refine ⟨_, by simp, fun x hx => bel x ?_⟩
        rw [hsp'] at hx
        exact belowA_inner (k := 8) (by omega_arith) hst x hx
  · have hd := c.dReg_ne
    have hn := c.nReg_ne
    have e0 : ∀ r : Reg, r ≠ .r12 → r ≠ .lr → ∀ rd wr, (Push.view s rd wr).gpr r = s.gpr r :=
      fun r a b rd wr => Push.view_gpr _ _ _ _ (by simp [linkRegs, a, b])
    simp only [e0 .r0 (by decide) (by decide), e0 _ hd.1 hd.2.1, e0 _ hn.1 hn.2.1, e0 .r1 (by decide) (by decide),
      h.r0, h.rd, h.rn, State.withRegions_mem, State.callEntry_mem, blocksOf_one, List.map_cons, List.map_nil,
      show (1 : BitVec 32).toNat = 1 from rfl, fB] at e
    rw [popped_mem, (List.cons.inj e).1, S.ciphAt_congr fK]
    cases hr : c.rounds
    · rw [S.ciphAt_R hr]
    · rw [h.r1 hr]
  · rw [popped_mem]
    exact (X.view_iff h _ _ _).1 hj₂

end

/-! ## The keys' preparation -/

/-- What a call of the function that prepares the keys needs, from the
caller's state `s`: the schedule at `K`, the number of rounds `R` (if the
core takes one), the working space at `C`, room for the callee's stack, and
the regions it is given readable, writable and apart. -/
structure KeysCall (c : Core) (S : CoreSpec c) (s : State) (K R C : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : c.rounds = true → s.gpr .r1 = R
  rok : c.rounds = true → S.rok R
  rC : s.gpr c.dReg = C
  stk : S.stack ≤ s.sp.toNat
  fK : K.toNat + S.keyLen ≤ 2 ^ 32
  fC : C.toNat + c.stackScratch ≤ 2 ^ 32
  kc : Region.Disjoint ⟨State.addr K, S.keyLen⟩ ⟨State.addr C, c.stackScratch⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr K, S.keyLen⟩
  bC : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr C, c.stackScratch⟩
  rK : Covers [⟨State.addr K, S.keyLen⟩] (s.rd ++ s.wr)
  wC : Covers [⟨State.addr C, c.stackScratch⟩] s.wr

/-- What the keys' preparation leaves: the permissions and stack pointer of
`s`, its callee-saved registers but `lr`, memory changed only in the working
space and the stack below the stack pointer, and the keys. -/
structure KeysPost {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) (s : State) (K R C : BitVec 32)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, c.stackScratch⟩, ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩] s.mem s'.mem
  keys : X.keysIn s'.mem K R C

section
variable {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {s : State} {K R C : BitVec 32}

/-- The callee's precondition, on the state it is entered in. -/
theorem KeysCall.pre (h : KeysCall c S s K R C) :
    KeysPre c S.keyLen S.stack S.rok
      (s.callEntry.withRegions [⟨State.addr K, S.keyLen⟩] [⟨State.addr C, c.stackScratch⟩]) := by
  have hd := c.dReg_ne
  refine ⟨by simpa using h.stk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hr => ?_⟩ <;>
    try simp only [entry_gpr _ _ _ (show Reg.r0 ≠ .r12 by decide) (by decide), entry_gpr _ _ _ hd.1 hd.2.1,
      h.r0, h.rC, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp]
  · exact h.kc
  · exact h.bk
  · exact h.bC
  · exact h.fK
  · exact h.fC
  · rw [entry_gpr _ _ _ (by decide) (by decide), h.r1 hr]; exact h.rok hr

/-- The call of the function that prepares the keys. -/
theorem keysCall_wp (h : KeysCall c S s K R C) :
    WP isa (.call k.keysName k.keysCode) s (KeysPost X s K R C) := by
  have hd := c.dReg_ne
  refine WP.callF X.keysCorrect (X.keysPre _ h.pre) (Covers.append_left h.rK (Covers.right h.wC))
    h.wC (Nat.le_trans X.keysDepth h.stk) fun s' hrd hwr hsp hf hsv hpost => ⟨hrd, hwr, hsp, hsv, ?_, ?_⟩
  · refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩, by simp, ?_⟩
      have := belowA_sub (sp := s.sp) (b := S.stack) X.keysDepth h.stk
      rwa [belowA, belowA, addr_sub' h.stk] at this
  · have e := X.keysPost _ _ h.pre hpost
    simp only [entry_gpr _ _ _ (show Reg.r0 ≠ .r12 by decide) (by decide), entry_gpr _ _ _ hd.1 hd.2.1,
      entry_gpr _ _ _ (show Reg.r1 ≠ .r12 by decide) (by decide), h.r0, h.rC, State.withRegions_mem] at e
    cases hr : c.rounds
    · exact X.keysIn_R hr _ _ _ _ _ e
    · rw [h.r1 hr] at e; exact e

end

/-- The arguments of the keys' preparation, from the registers the modes
keep them in. -/
theorem keysArgs_wp {c : Core} (S : CoreSpec c) (hs : c.stackScratch ≠ 0) {s : State} {K R Sb : BitVec 32}
    (h4 : s.gpr .r4 = K) (h8 : s.gpr .r8 = Sb) (h11 : c.rounds = true → s.gpr .r11 = R) {Q : State → Prop}
    (hQ : ∀ s', (∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → s'.gpr x = s.gpr x) → s'.gpr .r0 = K →
      (c.rounds = true → s'.gpr .r1 = R) → s'.gpr c.dReg = Sb + BitVec.ofNat 32 c.csOff →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.mem = s.mem → Q s') :
    WP isa (.block c.keysArgs) s Q := by
  simp only [Core.keysArgs, mov]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  cases hr : c.rounds
  · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, hD]
    refine wp_add (op2_imm (S.cs_enc hs)) fun s₂ u₂ => WP.block_nil (hQ s₂ (fun x a b _ => ?_) ?_
      (fun h => absurd h (by simp [hr])) ?_ ?_ ?_ ?_ ?_)
    · rw [u₂.other _ b, u₁.other _ a]
    · rw [u₂.other _ (by decide), u₁.gpr, h4]
    · rw [hD, u₂.gpr, u₁.other _ (by decide), h8]
    · rw [u₂.rd, u₁.rd]
    · rw [u₂.wr, u₁.wr]
    · rw [u₂.sp, u₁.sp]
    · rw [u₂.mem, u₁.mem]
  · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
    simp only [↓reduceIte, List.cons_append, List.nil_append, hD]
    refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_add (op2_imm (S.cs_enc hs)) fun s₃ u₃ =>
      WP.block_nil (hQ s₃ (fun x a b d => ?_) ?_ (fun _ => ?_) ?_ ?_ ?_ ?_ ?_)
    · rw [u₃.other _ d, u₂.other _ b, u₁.other _ a]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h4]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h11 hr]
    · rw [hD, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h8]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
    · rw [u₃.sp, u₂.sp, u₁.sp]
    · rw [u₃.mem, u₂.mem, u₁.mem]

/-- Blocks outside a frame. -/
theorem blocksOf_frame {L : Nat} {rs : List Region} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n * L⟩ r) (hL : n * L ≤ 2 ^ 64) : blocksOf L m' p n = blocksOf L m p n := by
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have := idx_lt' (L := L) hj
  exact VG.Proof.Modes.bytesAt_frame hf
    (fun r hr => (hd r hr).sub_left (VG.Offset.sub_base _ (by omega_arith))) (by omega_arith)

section
variable {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {M : Mode} {s₀ : State}
  (hp : UPre c S M s₀)
include hp

/-- The call of the keys' preparation, from the invariant before the first
block. -/
theorem LInv.keysCall {s s₁ : State} (h : LInv c S M s₀ 0 s) (hs : c.stackScratch ≠ 0)
    (r0 : s₁.gpr .r0 = Kp s₀) (r1 : c.rounds = true → s₁.gpr .r1 = Rp s₀) (rC : s₁.gpr c.dReg = Cs c s₀)
    (rd₁ : s₁.rd = s.rd) (wr₁ : s₁.wr = s.wr) (sp₁ : s₁.sp = s.sp) :
    KeysCall c S s₁ (Kp s₀) (Rp s₀) (Cs c s₀) := by
  obtain sp : s₁.sp = s₀.sp := by rw [sp₁, h.sp]
  refine ⟨r0, r1, hp.rok, rC, by rw [sp]; exact hp.stk, hp.fK, hp.cs_fit hs, hp.key_scr.sub_right hp.cs_sub_scr,
    by rw [sp]; exact hp.b_key, by rw [sp]; exact hp.b_scr.sub_right hp.cs_sub_scr, ?_, ?_⟩
  · rw [rd₁, wr₁, h.rd, h.wr]; exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.key_in
  · rw [wr₁, h.wr]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, hp.scr_in, c.csOff, hp.cs_addr hs, by show c.csOff + c.stackScratch ≤ c.scratchBytes; rfl⟩

/-- The keys prepared, before the first block: the invariant, and the keys. -/
theorem keysStep_wp (hN : 0 < N c s₀) {s : State} (h : LInv c S M s₀ 0 s) :
    WP isa (c.keysStep k) s fun s' => LInv c S M s₀ 0 s' ∧ X.keysIn s'.mem (Kp s₀) (Rp s₀) (Cs c s₀) := by
  have hs := X.scr
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hcs : c.csOff = oOff + 2 * c.bs := rfl
  refine WP.seq (keysArgs_wp S hs h.r4 h.r8 h.r11 fun s₁ g₁ r0 r1 rC rd₁ wr₁ sp₁ m₁ => ?_)
  refine WP.mono (keysCall_wp X (h.keysCall hp hs r0 r1 rC rd₁ wr₁ sp₁)) fun s₂ p => ?_
  obtain g₂ : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := fun r hr hl => by
    rw [p.saved r hr hl, g₁ r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr)]
  obtain f₂ : Frame [csR c s₀, belowR S s₀] s.mem s₂.mem := by
    have := p.frame
    rwa [m₁, sp₁, h.sp] at this
  -- The callee's working space and stack are apart from the data and the chaining and spare blocks.
  obtain dO : ∀ d, d + c.bs ≤ oOff + 2 * c.bs → oOff ≤ d →
      ∀ r ∈ [csR c s₀, belowR S s₀], Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 d, c.bs⟩ r :=
    fun d hd hd' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨State.addr (Cs c s₀), _⟩
        rw [hp.cs_addr hs]
        exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact (hp.b_scr.sub_right (VG.Offset.sub_base _ (by omega_arith))).symm
  refine ⟨⟨by rw [g₂ _ (by decide) (by decide), h.r4], by rw [g₂ _ (by decide) (by decide), h.r5],
    by rw [g₂ _ (by decide) (by decide), h.r6], by rw [g₂ _ (by decide) (by decide), h.r7],
    by rw [g₂ _ (by decide) (by decide), h.r8], fun hr => by rw [g₂ _ (by decide) (by decide), h.r11 hr],
    by rw [p.sp, sp₁, h.sp], by rw [p.rd, rd₁, h.rd], by rw [p.wr, wr₁, h.wr], ?_, ?_, ?_, ?_⟩, p.keys⟩
  · exact h.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, hp.cs_sub_blk⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  · rw [← h.data]
    refine blocksOf_frame f₂ (fun r hr => ?_) (by have := hp.fD; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_scr.sub_right hp.cs_sub_scr
    · exact hp.b_data.symm
  · rw [← h.o]
    exact VG.Proof.Modes.bytesAt_frame f₂ (dO oOff (by omega_arith) (Nat.le_refl _)) (by omega_arith)
  · rw [← h.t]
    exact VG.Proof.Modes.bytesAt_frame f₂ (dO (oOff + c.bs) (by omega_arith) (by omega_arith)) (by omega_arith)

/-- The keys after the mode's own writes of a step, which are apart from
the schedule and the callee's working space. -/
theorem keysIn_step {kk : Nat} (hk : kk < N c s₀) {m m' : Mem}
    (hf : Frame (blkRegions c (c.ds M) (Dk s₀ c M kk) (Sc c s₀)) m m')
    (hj : X.keysIn m (Kp s₀) (Rp s₀) (Cs c s₀)) : X.keysIn m' (Kp s₀) (Rp s₀) (Cs c s₀) := by
  have hs := X.scr
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hcs : c.csOff = oOff + 2 * c.bs := rfl
  refine X.keysIn_frame hf (fun r hr => ?_) (fun r hr => ?_) hp.fK (hp.cs_fit hs) hp.rok hj
  · simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.key_data.sub_right (hp.blk_sub_data hk)
    · exact hp.key_scr.sub_right UPre.blk2_sub
  · simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.data_scr.sub_left (hp.blk_sub_data hk)).sub_right hp.cs_sub_scr).symm
    · show Region.Disjoint ⟨State.addr (Cs c s₀), _⟩ _
      rw [hp.cs_addr hs]
      exact VG.Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

/-- One block, as `body_ok`, with the keys before and after. -/
theorem bodyK_ok (hM : ModeOk c M) {kk : Nat} (hk : kk < N c s₀) {s : State} (h : LInv c S M s₀ kk s)
    (hsy : s.syms = s₀.syms) (hj : X.keysIn s.mem (Kp s₀) (Rp s₀) (Cs c s₀)) :
    WP isa (c.bodyK k M) s fun s' => (LInv c S M s₀ (kk + 1) s' ∧ s'.z = decide (N c s₀ - (kk + 1) = 0)) ∧
      X.keysIn s'.mem (Kp s₀) (Rp s₀) (Cs c s₀) := by
  obtain hL := hp.lay hk
  obtain hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith
  refine WP.seq (VG.Arm.WP.mono_syms (pre_wp hp hM hk h) fun s₂ a sy₂ => ?_)
  refine WP.seq (WP.mono (callK_wp X (a.callPre hp hM hk h (sy₂.trans hsy)) (keysIn_step X hp hk a.frame hj))
    fun s₃ ⟨cp, j₃⟩ => ?_)
  obtain hb₂ := call_blks hp hM hk h a cp
  obtain g₃ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h9 h10
      (by rintro rfl; simp [preserved] at hr)]
  obtain r6 : s₃.gpr .r6 = Dk s₀ c M kk := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r6]
  obtain r8 : s₃.gpr .r8 = Sc c s₀ := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r8]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [cp.wr, a.wr, h.wr]
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (ds_of c) (wr₃ ▸ hL) r6 r8 hb₂ hM.post) fun s₄ h₄ => ?_
  -- The memory the step changed: block `kk`, the chaining and spare blocks, the stack.
  obtain sp₂ : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  obtain fstep : Frame (blkRegions c (c.ds M) (Dk s₀ c M kk) (Sc c s₀) ++ [csR c s₀, belowR S s₀]) s.mem s₄.mem := by
    refine ((a.frame.mono fun r hr => List.mem_append_left _ hr).trans (cp.frame.sub fun r hr => ?_)).trans
      (h₄.frame.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hL.bt_addr]
      obtain ⟨r', hr', hs'⟩ := Lay.sub (c := c) (ds := c.ds M) (Dp := Dk s₀ c M kk) (S := Sc c s₀) M.tgt
      exact ⟨r', List.mem_append_left _ hr', hM.tgt_sz ▸ hs'⟩
    · exact ⟨csR c s₀, by simp, fun _ h => h⟩
    · exact ⟨belowR S s₀, by simp, by rw [sp₂]; exact fun _ h => h⟩
  obtain r6' : s₄.gpr .r6 = Dk s₀ c M kk := by rw [h₄.regs _ (by decide) (by decide), r6]
  obtain r7 : s₄.gpr .r7 = BitVec.ofNat 32 (N c s₀ - kk) := by
    rw [h₄.regs _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide), h.r7]
  simp only [Core.advance]
  refine wp_add (op2_imm (S.ds_enc M)) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ =>
    WP.block_nil ⟨⟨⟨?_, ?_, ?_, ?_, ?_, fun hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
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
    obtain hl : (rK S s₀ M kk).1.length = kk := by rw [runSeq_length, List.length_take, length_blocksOf]; omega_arith
    rw [blocksOf_set (k := kk) fun j hj hjk => ?_, h.data, set_prefix _ _ _ hl (by rw [length_blocksOf]; exact hk)]
    simp only [rK]
    rw [take_succ_xs hk, runSeq_snoc]
    · congr 2
      rw [← hp.dk_addr hk]
      exact congrArg (fun z => [z]) (h₄.blks .d)
    · refine VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) (by have := S.ds_le M; omega_arith)
      obtain hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
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
  · rw [u₆.mem, u₅.mem]
    exact keysIn_step X hp hk h₄.frame j₃

theorem loopK_ok (hM : ModeOk c M) {kk : Nat} (hk : kk < N c s₀) {s : State} (h : LInv c S M s₀ kk s)
    (hsy : s.syms = s₀.syms) (hj : X.keysIn s.mem (Kp s₀) (Rp s₀) (Cs c s₀)) :
    WP isa (.loop (c.bodyK k M) .ne) s (LInv c S M s₀ (N c s₀)) := by
  refine WP.loop (M := isa) (body := c.bodyK k M) (c := .ne) (Q := LInv c S M s₀ (N c s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N c s₀ - j ∧ j < N c s₀ ∧ LInv c S M s₀ j t ∧ t.syms = s₀.syms ∧
      X.keysIn t.mem (Kp s₀) (Rp s₀) (Cs c s₀)) ?_
    (N c s₀ - kk) s ⟨kk, rfl, hk, h, hsy, hj⟩
  rintro n s ⟨kk, rfl, hk, h, hsy, hj⟩
  refine VG.Arm.WP.mono_syms (bodyK_ok X hp hM hk h hsy hj) fun s' ⟨⟨h', hz⟩, hj'⟩ hsy' => ?_
  have ev : isa.eval .ne s' = some !decide (N c s₀ - (kk + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N c s₀ - (kk + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N c s₀ = kk + 1 by omega_using [hk, hz']]
  · right
    exact ⟨by rw [ev]; simp [hz'], N c s₀ - (kk + 1), by omega_using [hk], kk + 1, rfl, by omega_using [hz'], h',
      hsy'.trans hsy, hj'⟩

include X in
theorem midK_wp (hM : ModeOk c M) {s₁ : State} (h : LInv c S M s₀ 0 s₁) (hz : s₁.z = decide (N c s₀ = 0))
    (hsy : s₁.syms = s₀.syms) :
    WP isa (.ite .eq (.block []) (.seq (c.keysStep k) (.loop (c.bodyK k M) .ne))) s₁ (LInv c S M s₀ (N c s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N c s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    obtain hN : 0 < N c s₀ := by omega_using [hn]
    exact WP.seq (VG.Arm.WP.mono_syms (keysStep_wp X hp hN h) fun s₂ ⟨h₂, j₂⟩ sy₂ =>
      loopK_ok X hp hM hN h₂ (sy₂.trans hsy) j₂)

end

/-- The whole function meets `seqArm`, the contract of `Core.seq c M`. -/
theorem seqK_wp {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {M : Mode} (hM : ModeOk c M)
    {s₀ : State} (h0 : (seqArm c S M).pre s₀) :
    WP isa (c.seqK k M) s₀ fun s' => abiPreserved s₀ s' ∧ (seqArm c S M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (VG.Arm.WP.mono_syms (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ hsy =>
    WP.seq (WP.mono (midK_wp X hp hM h₁ hz hsy) fun _ h₂ => by
      rw [WP.block_append_iff]
      exact WP.mono (finish_wp hp h₂) fun _ h₃ => epilogue_wp hp h₃))

/-! ## Constant time

As `Core.seq c M`'s (`SeqCT.lean`): the taint analysis covers the code
between the calls, and each call is constant time by its function's own
proof, its public data being the same in both runs; both runs have the keys
where the calls need them. -/

/-- The taint checks of the code between the calls of `c.seqK k M`: those of
`c.seq M`, and the arguments of the keys' preparation. -/
structure SeqTaintK (c : Core) (M : Mode) : Prop where
  seq : SeqTaint c M
  keys : ∃ h, (taint.check (Taint.ofRegs (loopRegs c)) (.block c.keysArgs) h).isSome = true

/-- What a run knows before block `kk`: the invariant, and the keys. -/
abbrev KInv {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) (M : Mode) (s₀ : State) (kk : Nat)
    (s : State) : Prop :=
  (kk < N c s₀ ∧ LInv c S M s₀ kk s ∧ s.syms = s₀.syms) ∧ X.keysIn s.mem (Kp s₀) (Rp s₀) (Cs c s₀)

section
variable {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {M : Mode} {s₀ s₀' : State}
  (hp : UPre c S M s₀) (hp' : UPre c S M s₀') (hq : (seqArm c S M).pub s₀ s₀')
include hp hp' hq

/-- One run of the body from `kk` blocks is constant time. -/
theorem bodyK_ct (hM : ModeOk c M) (hT : SeqTaint c M) (kk : Nat) :
    RelCT isa (fun s₁ s₂ => KInv X M s₀ kk s₁ ∧ KInv X M s₀' kk s₂) (c.bodyK k M) fun _ _ => True := by
  have hs := X.scr
  have a := rel_agree (F := KInv X M s₀ kk) (F' := KInv X M s₀' kk)
    (G := fun s => AfterPre c S M s₀ kk s ∧ X.keysIn s.mem (Kp s₀) (Rp s₀) (Cs c s₀))
    (G' := fun s => AfterPre c S M s₀' kk s ∧ X.keysIn s.mem (Kp s₀') (Rp s₀') (Cs c s₀'))
    (Taint.ofRegs (loopRegs c))
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.1.2.1 h'.1.2.1)) hT.pre
    (fun _ h => VG.Arm.WP.mono_syms (pre_wp hp hM h.1.1 h.1.2.1) fun _ x sy =>
      ⟨⟨h.1.1, _, h.1.2.1, x, sy.trans h.1.2.2⟩, keysIn_step X hp h.1.1 x.frame h.2⟩)
    (fun _ h => VG.Arm.WP.mono_syms (pre_wp hp' hM h.1.1 h.1.2.1) fun _ x sy =>
      ⟨⟨h.1.1, _, h.1.2.1, x, sy.trans h.1.2.2⟩, keysIn_step X hp' h.1.1 x.frame h.2⟩)
  have cpre : ∀ {t₀ : State} (hpt : UPre c S M t₀) {s₂ : State} (h : AfterPre c S M t₀ kk s₂),
      CallPre c S s₂ (Kp t₀) (Rp t₀) (bt c (Dk t₀ c M kk) (Sc c t₀) M.tgt) (Cs c t₀) := fun {_} hpt {_} h => by
    obtain ⟨hk, s, hl, pa, sy⟩ := h
    exact PreA.callPre hpt hM hk hl pa sy
  have spA : ∀ {s₂ s₂' : State}, AfterPre c S M s₀ kk s₂ → AfterPre c S M s₀' kk s₂' → s₂.sp = s₂'.sp :=
    fun ⟨_, _, hl, x, _⟩ ⟨_, _, hl', x', _⟩ => by rw [x.sp, hl.sp, x'.sp, hl'.sp, pub_sp hq]
  have syA : ∀ {s₂ s₂' : State}, AfterPre c S M s₀ kk s₂ → AfterPre c S M s₀' kk s₂' →
      ∀ x ∈ S.consts, s₂.syms x.1 = s₂'.syms x.1 :=
    fun ⟨_, _, _, _, sy⟩ ⟨_, _, _, _, sy'⟩ x hx => by rw [sy, sy', pub_syms hq x hx]
  -- The arguments in registers, through the callee's view of a state.
  have regsA : ∀ {s₂ s₂' : State} (h : AfterPre c S M s₀ kk s₂) (h' : AfterPre c S M s₀' kk s₂'),
      s₂.gpr .r0 = s₂'.gpr .r0 ∧ s₂.gpr .r1 = s₂'.gpr .r1 ∧ s₂.gpr .r2 = s₂'.gpr .r2 ∧
        (c.r3Pub = true → s₂.gpr .r3 = s₂'.gpr .r3) := fun h h' => by
    have p := cpre hp h
    have p' := cpre hp' h'
    rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, ← pub_Sc hq] at p'
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
  have callR : RelCT isa (fun s₂ s₂' => (AfterPre c S M s₀ kk s₂ ∧ X.keysIn s₂.mem (Kp s₀) (Rp s₀) (Cs c s₀)) ∧
      (AfterPre c S M s₀' kk s₂' ∧ X.keysIn s₂'.mem (Kp s₀') (Rp s₀') (Cs c s₀'))) k.callStep
      fun _ _ => True := by
    refine RelCT.frame (fun s₂ s₂' h => spA h.1.1 h.2.1) ?_
    intro a b t₁ t₂ a' b' ⟨s₂, s₂', ⟨⟨h, hj⟩, ⟨h', hj'⟩⟩, pa, pb⟩ e₁ e₂
    have p := cpre hp h
    have p' := cpre hp' h'
    have eC : Cs c s₀' = Cs c s₀ := by simp only [Cs]; rw [pub_Sc hq]
    rw [← pub_K hq, ← pub_R hq, eC] at hj'
    rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, eC, ← pub_Sc hq] at p'
    have hsp := spA h h'
    rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using p.sp8 hs), Option.some.injEq] at pa
    rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using p'.sp8 hs), Option.some.injEq] at pb
    subst pa pb
    have eA : Push.argR s₂' = Push.argR s₂ := by rw [Push.argR, Push.argR, hsp]
    have syms := syA h h'
    have eT : tabRegs S.consts s₂' = tabRegs S.consts s₂ := by
      simp only [tabRegs, Abi.constRegions]
      exact List.map_congr_left fun x hx => by rw [syms x hx]
    let wr' : List Region := [⟨State.addr (bt c (Dk s₀ c M kk) (Sc c s₀) M.tgt), c.bs⟩,
      ⟨State.addr (Cs c s₀), c.stackScratch⟩]
    have cw : Covers ([⟨State.addr (bt c (Dk s₀ c M kk) (Sc c s₀) M.tgt), c.bs⟩] ++
        [⟨State.addr (Cs c s₀), c.stackScratch⟩]) s₂.wr := Covers.append_left p.wB (p.wC hs)
    have cw' : Covers ([⟨State.addr (bt c (Dk s₀ c M kk) (Sc c s₀) M.tgt), c.bs⟩] ++
        [⟨State.addr (Cs c s₀), c.stackScratch⟩]) s₂'.wr := Covers.append_left p'.wB (p'.wC hs)
    refine RelCT.call X.correct X.ct ([⟨State.addr (Kp s₀), S.keyLen⟩, Push.argR s₂] ++ tabRegs S.consts s₂) wr'
      (P := fun x y => x = pushed [.r12, .lr] s₂ ∧ y = pushed [.r12, .lr] s₂')
      (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
    subst ex ey
    have v := p.ecbPreS hs
    have v' := p'.ecbPreS hs
    have c' := p'.cov hs
    rw [eA, eT] at v' c'
    obtain ⟨r0, r1, r2, r3⟩ := regsA h h'
    have e0 : ∀ (t : State) (r : Reg), r ≠ .r12 → r ≠ .lr → ∀ rd wr, (Push.view t rd wr).gpr r = t.gpr r :=
      fun t r a b rd wr => Push.view_gpr _ _ _ _ (by simp [linkRegs, a, b])
    refine ⟨X.pre_of _ v (X.keys_view p hj _ _), X.pre_of _ v' (X.keys_view p' hj' _ _),
      X.pub_of _ _ ?_ ?_ ?_ ?_ (fun hr => ?_) ?_ syms, p.cov hs, Push.covW cw, c', Push.covW cw'⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, hsp]
    · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r0]
    · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r1]
    · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r2]
    · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r3 hr]
    · rw [Push.arg0 (p.sp8 hs), Push.arg0 (p'.sp8 hs), p.r12 hs, p'.r12 hs]
  have cr := rel_wp (G := AfterCall c M s₀ kk) (G' := AfterCall c M s₀' kk) callR
    (fun _ h => WP.mono (callK_wp X (cpre hp h.1) h.2) fun _ cp => afterCall h.1 cp.1)
    (fun _ h => WP.mono (callK_wp X (cpre hp' h.1) h.2) fun _ cp => afterCall h.1 cp.1)
  obtain ⟨_, hB⟩ := hT.post
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => AfterCall c M s₀ kk s₁ ∧ AfterCall c M s₀' kk s₂)
    (Taint.ofRegs [.r6, .r7, .r8])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.r6, h.2.r6, pub_Dk hq]
      · rw [h.1.r7, h.2.r7, pub_N hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h).seq ((cr.mono (fun _ _ h => h) fun _ _ h => h).seq
    (b.mono (fun _ _ h => h) fun _ _ h => h))

/-- The loop's relation, with the number of iterations left. -/
def KLRel (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ kk, n = N c s₀ - kk ∧ KInv X M s₀ kk s₁ ∧ KInv X M s₀' kk s₂

theorem loopK_ct (hM : ModeOk c M) (hT : SeqTaint c M) (n : Nat) :
    RelCT isa (KLRel (X := X) (M := M) (s₀ := s₀) (s₀' := s₀') n) (.loop (c.bodyK k M) .ne)
      fun s₁ s₂ => LInv c S M s₀ (N c s₀) s₁ ∧ LInv c S M s₀' (N c s₀') s₂ := by
  refine RelCT.loop (M := isa) (KLRel (X := X) (M := M) (s₀ := s₀) (s₀' := s₀')) (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun kk => ?_).mono (fun s₁ s₂ (h : KLRel X n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N c s₀ - kk
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (bodyK_ct X hp hp' hq hM hT kk).wp
    (F₁ := fun (s : State) => (((LInv c S M s₀ (kk + 1) s ∧ s.z = decide (N c s₀ - (kk + 1) = 0)) ∧
      X.keysIn s.mem (Kp s₀) (Rp s₀) (Cs c s₀)) ∧ kk < N c s₀) ∧ s.syms = s₀.syms)
    (F₂ := fun (s : State) => ((LInv c S M s₀' (kk + 1) s ∧ s.z = decide (N c s₀' - (kk + 1) = 0)) ∧
      X.keysIn s.mem (Kp s₀') (Rp s₀') (Cs c s₀')) ∧ s.syms = s₀'.syms)
    fun _ _ h => ⟨VG.Arm.WP.mono_syms (bodyK_ok X hp hM h.1.1.1 h.1.1.2.1 h.1.1.2.2 h.1.2) fun _ r sy =>
        ⟨⟨r, h.1.1.1⟩, sy.trans h.1.1.2.2⟩,
      VG.Arm.WP.mono_syms (bodyK_ok X hp' hM h.2.1.1 h.2.1.2.1 h.2.1.2.2 h.2.2) fun _ r sy =>
        ⟨r, sy.trans h.2.1.2.2⟩⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨⟨⟨l₁, z₁⟩, j₁⟩, hk⟩, y₁⟩, ⟨⟨⟨l₂, z₂⟩, j₂⟩, y₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N c s₀ - (kk + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N c s₀ - (kk + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N c s₀ = kk + 1 := by
      have : N c s₀ - (kk + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N c s₀ - (kk + 1) ≠ 0 := by simpa using ht
    exact ⟨N c s₀ - (kk + 1), by omega_using [hk], kk + 1, rfl, ⟨⟨by omega_using [h0], l₁, y₁⟩, j₁⟩,
      ⟨⟨by rw [← hN]; omega_using [h0], l₂, y₂⟩, j₂⟩⟩

/-- The keys' preparation is constant time, and leaves the keys in both runs. -/
theorem keysStep_ct (hT : SeqTaintK c M) :
    RelCT isa (fun a b => (0 < N c s₀ ∧ LInv c S M s₀ 0 a ∧ a.syms = s₀.syms) ∧
      (0 < N c s₀' ∧ LInv c S M s₀' 0 b ∧ b.syms = s₀'.syms)) (c.keysStep k)
      fun a b => KInv X M s₀ 0 a ∧ KInv X M s₀' 0 b := by
  have hs := X.scr
  have args := rel_agree (F := fun s => 0 < N c s₀ ∧ LInv c S M s₀ 0 s ∧ s.syms = s₀.syms)
    (F' := fun s => 0 < N c s₀' ∧ LInv c S M s₀' 0 s ∧ s.syms = s₀'.syms)
    (G := fun s => KeysCall c S s (Kp s₀) (Rp s₀) (Cs c s₀))
    (G' := fun s => KeysCall c S s (Kp s₀') (Rp s₀') (Cs c s₀'))
    (Taint.ofRegs (loopRegs c)) (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2.1 h'.2.1)) hT.keys
    (fun _ h => keysArgs_wp S hs h.2.1.r4 h.2.1.r8 h.2.1.r11 fun _ _ r0 r1 rC rd₁ wr₁ sp₁ _ =>
      h.2.1.keysCall hp hs r0 r1 rC rd₁ wr₁ sp₁)
    (fun _ h => keysArgs_wp S hs h.2.1.r4 h.2.1.r8 h.2.1.r11 fun _ _ r0 r1 rC rd₁ wr₁ sp₁ _ =>
      h.2.1.keysCall hp' hs r0 r1 rC rd₁ wr₁ sp₁)
  have call : RelCT isa (fun s₁ s₂ => KeysCall c S s₁ (Kp s₀) (Rp s₀) (Cs c s₀) ∧
      KeysCall c S s₂ (Kp s₀') (Rp s₀') (Cs c s₀')) (.call k.keysName k.keysCode) fun _ _ => True := by
    refine RelCT.call X.keysCorrect X.keysCt [⟨State.addr (Kp s₀), S.keyLen⟩]
      [⟨State.addr (Cs c s₀), c.stackScratch⟩] fun s₁ s₂ ⟨h, h'⟩ => ?_
    have eC : Cs c s₀' = Cs c s₀ := by simp only [Cs]; rw [pub_Sc hq]
    rw [← pub_K hq, ← pub_R hq, eC] at h'
    have rC := h.rC.trans h'.rC.symm
    refine ⟨X.keysPre _ h.pre, X.keysPre _ h'.pre, X.keysPub _ _ ?_ ?_ (fun hr => ?_),
      Covers.append_left h.rK (Covers.right h.wC), h.wC, Covers.append_left h'.rK (Covers.right h'.wC), h'.wC⟩
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), h.r0, h'.r0]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide)]
      cases hr : c.rounds
      · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
        rwa [hD] at rC
      · rw [h.r1 hr, h'.r1 hr]
    · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
      rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide)]
      rwa [hD] at rC
  refine rel_wp ((args.mono (fun _ _ h => h) fun _ _ h => h).seq call)
    (fun _ h => VG.Arm.WP.mono_syms (keysStep_wp X hp h.1 h.2.1) fun _ r sy => ⟨⟨h.1, r.1, sy.trans h.2.2⟩, r.2⟩)
    (fun _ h => VG.Arm.WP.mono_syms (keysStep_wp X hp' h.1 h.2.1) fun _ r sy => ⟨⟨h.1, r.1, sy.trans h.2.2⟩, r.2⟩)

end

theorem seqK_rel {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaintK c M) {s₀ s₀' : State} (h0 : (seqArm c S M).pre s₀) (h0' : (seqArm c S M).pre s₀')
    (hq : (seqArm c S M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (c.seqK k M) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hepi⟩ := hT.seq.epi
  obtain ⟨_, hnil⟩ := nil_taint
  have hN := pub_N hq
  have hsp := pub_sp hq
  have wfA : ∀ {s : State}, UPre c S M s →
      s.sp.toNat + argBytes c ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, argBytes c⟩ r :=
    fun {s} h => by
      have e : (⟨State.addr s.sp, argBytes c⟩ : Region) = argR c s := by simp [stackArgAddr]
      exact ⟨h.spF, by rw [e]; exact h.arg_wr⟩
  have hj : argBytes c = 4 * (if c.rounds then 2 else 1) := by unfold argBytes; split <;> rfl
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => (LInv c S M s₀ 0 s ∧ s.z = decide (N c s₀ = 0)) ∧ s.syms = s₀.syms)
    (G' := fun s => (LInv c S M s₀' 0 s ∧ s.z = decide (N c s₀' = 0)) ∧ s.syms = s₀'.syms)
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
          · exact hq.2.2.2.2.2.2.1 hr) hT.seq.pro
    (fun s e => by rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp) fun _ h sy => ⟨h, sy⟩)
    (fun s e => by rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp') fun _ h sy => ⟨h, sy⟩)
  have ev {s : State} (h : s.z = decide (N c s₀ = 0)) : isa.eval .eq s = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N c s₀' = 0)) : isa.eval .eq s = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (((LInv c S M s₀ 0 a ∧ a.z = decide (N c s₀ = 0)) ∧ a.syms = s₀.syms) ∧
      ((LInv c S M s₀' 0 b ∧ b.z = decide (N c s₀' = 0)) ∧ b.syms = s₀'.syms)) ∧ isa.eval .eq a = some true)
    (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => ((LInv c S M s₀ 0 a ∧ a.z = decide (N c s₀ = 0)) ∧ a.syms = s₀.syms) ∧
      ((LInv c S M s₀' 0 b ∧ b.z = decide (N c s₀' = 0)) ∧ b.syms = s₀'.syms))
      (.ite .eq (.block []) (.seq (c.keysStep k) (.loop (c.bodyK k M) .ne)))
      (fun a b => LInv c S M s₀ (N c s₀) a ∧ LInv c S M s₀' (N c s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.1.2, ev' h.2.1.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv c S M s₀ (N c s₀)) (F₂ := LInv c S M s₀' (N c s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N c s₀ = 0 := by
        have := h.2; rw [ev h.1.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1.1)⟩
    · refine ((keysStep_ct X hp hp' hq hT).seq ((loopK_ct X hp hp' hq hM hT.seq (N c s₀ - 0)).mono
        (fun a b h => ⟨0, rfl, h.1, h.2⟩) fun _ _ h => h)).mono
        (fun a b h => ⟨⟨?_, h.1.1.1.1, h.1.1.2⟩, ⟨?_, h.1.2.1.1, h.1.2.2⟩⟩) fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.1.2] at this
        have : N c s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint)
    (P := fun a b => LInv c S M s₀ (N c s₀) a ∧ LInv c S M s₀' (N c s₀') b)
    (Taint.ofRegs [.r5, .r8]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, pub_Iv hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem seqK_ct {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaintK c M) : ConstantTime isa (seqArm c S M).pre (seqArm c S M).pub (c.seqK k M) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seqK_rel X hM hT h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A core, the two functions that split its ECB function, and a mode whose
code between the calls passes the taint checks, give a function that is
correct and constant time under `seqArm`, and so under any contract `seqArm`
implies. -/
theorem seqK_verified {c : Core} {S : CoreSpec c} {k : Keyed} (X : KeyedSpec c S k) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaintK c M) {ct : Contract isa} (hk : (seqArm c S M).Implies ct) :
    Verified Arm.target (c.seqK k M) ct :=
  Verified.of_correct (fun _ hs => seqK_wp X hM hs) (seqK_ct X hM hT) hk

end VG.Proof.Modes.Arm
