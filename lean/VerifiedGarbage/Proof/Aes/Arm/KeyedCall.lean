module

public import VerifiedGarbage.Proof.AesOcb.Arm.Callee
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesOcb.Arm.Callee
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES on ARMv7: calling the functions that bitslice the round keys once

Untrusted: everything here is checked by Lean. A function that enciphers
its blocks one at a time bitslices the round keys once, by a call of
`vg_aes_blocks_keys` (`keysCall`: `keysCall_wp`, `keysCall_rel`), and enciphers
each block by a call of `vg_aes_encrypt_blocks_keyed` in the frame that
pushes its stack argument (`keyedFrame`: `kblk_call`, `kblk_rel`), which is
a call of `vg_aes_encrypt_blocks` (`BlkCall`, `BlkPost`,
`Proof/AesOcb/Arm/Callee.lean`) where the round keys are in the working
space (`KeysIn`), and leaves them there.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Impl.Aes.Arm
open VG.Proof.Aes (KeysIn)
open VG.Proof.Aes.Arm.Ecb (keysIn_frame)
open VG.Proof.AesOcb.Arm (BlkCall BlkPost blk_frame blk_frame_rel blkRd blkWr encF)
open VG.Proof.AesGcm.Arm (below toNat_ofNat32 fA view_gpr arg0 bytesAt_frame)
open VG.Proof.MdStream.Arm (Upd op2_reg wp_mov)

/-- The key schedule at `K` for `R` rounds, as bytes. -/
abbrev schedAt (m : Mem) (K : BitVec 32) (R : Nat) : List Byte :=
  Spec.Aes.bytesAt m (State.addr K) (16 * (R + 1))

/-! ## `vg_aes_encrypt_blocks_keyed` -/

theorem keyed_noCalls : encryptBlocksKeyed.noCalls = true := by decide +kernel

section
variable {s : State} {K D S : BitVec 32} {R n : Nat} (h : BlkCall s K D S R n)
include h

theorem rounds_le : R ≤ 14 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']

/-- The push changes neither the key schedule nor the round keys. -/
theorem sched_pushed :
    Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K) (16 * (R + 1)) = schedAt s.mem K R := by
  have hR' : 16 * (R + 1) ≤ 240 := by have := rounds_le h; omega_using [this]
  exact bytesAt_frame (fA (s := s) h.hsp) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bk.symm.sub_left (Region.sub_prefix hR')) (by omega_using [hR'])

/-- The keyed function's precondition at its entry in the frame. -/
theorem keyedPre (hk : KeysIn s.mem S R (schedAt s.mem K R)) :
    (Proof.Aes.blocksKeyedArm Spec.Aes.cipher).pre
      ((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)) := by
  refine ⟨h.pre _, ?_⟩
  simp only [stackArg_withRegions, Proof.AesGcm.Arm.stackArg_callEntry, arg0 h.hsp, h.r12,
    view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), h.r0, h.r1, h.toNat_R,
    State.withRegions_mem, State.callEntry_mem]
  rw [sched_pushed h]
  exact keysIn_frame h.fitS (rounds_le h) (fA (s := s) h.hsp) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.bs.symm) hk

/-- The round keys the keyed function leaves, from its postcondition. -/
theorem keyedPost {s₂ : State}
    (hpost : KeysIn (s₂.withRegions (blkRd s.sp K) (blkWr D S n)).mem
      (stackArg ((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)) 0)
      (((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)).gpr .r1).toNat
      (Spec.Aes.bytesAt ((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)).mem
        (State.addr (((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)).gpr .r0))
        (16 * ((((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)).gpr .r1).toNat + 1)))) :
    KeysIn s₂.mem S R (schedAt s.mem K R) := by
  simp only [stackArg_withRegions, Proof.AesGcm.Arm.stackArg_callEntry, arg0 h.hsp, h.r12,
    view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), h.r0, h.r1, h.toNat_R,
    State.withRegions_mem, State.callEntry_mem] at hpost
  rw [sched_pushed h] at hpost
  exact hpost

end

/-- A call of `vg_aes_encrypt_blocks_keyed` in its frame, with the round
keys of the schedule in the working space: what a call of
`vg_aes_encrypt_blocks` leaves, and the round keys. -/
theorem kblk_call {s : State} {K D S : BitVec 32} {R n : Nat} (h : BlkCall s K D S R n)
    (hk : KeysIn s.mem S R (schedAt s.mem K R)) :
    WP isa keyedFrame s fun s' => BlkPost encF s K D S R n s' ∧ KeysIn s'.mem S R (schedAt s.mem K R) :=
  blk_frame Ecb.encryptBlocksKeyed_correct keyed_noCalls h (keyedPre h hk)
    fun _ _ hrd hwr hsp hsv hfr hm hpost =>
      ⟨⟨hrd, hwr, hsp, hsv, hfr, by rw [hm]; exact h.out hpost.1⟩, by rw [hm]; exact keyedPost h hpost.2⟩

theorem kblk_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : BitVec 32, ∃ R n : Nat,
      BlkCall s₁ K D S R n ∧ BlkCall s₂ K D S R n ∧ s₁.sp = s₂.sp ∧
      KeysIn s₁.mem S R (schedAt s₁.mem K R) ∧ KeysIn s₂.mem S R (schedAt s₂.mem K R)) :
    RelCT isa P keyedFrame fun _ _ => True :=
  blk_frame_rel Ecb.encryptBlocksKeyed_correct Ecb.encryptBlocksKeyed_ct fun s₁ s₂ hp => by
    obtain ⟨K, D, S, R, n, h₁, h₂, hsp, k₁, k₂⟩ := h _ _ hp
    have p₂ := keyedPre h₂ k₂
    rw [← hsp] at p₂
    exact ⟨K, D, S, R, n, h₁, h₂, hsp, keyedPre h₁ k₁, p₂, h₁.pub h₂ hsp Spec.Aes.cipher⟩

/-! ## `vg_aes_blocks_keys` -/

theorem keys_noCalls : blocksKeys.noCalls = true := by decide +kernel

/-- What a call of `vg_aes_blocks_keys` needs: the key schedule at `K` for
`R` rounds and the working space at `S`. -/
structure KeysCall (s : State) (K S : BitVec 32) (R : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  fitK : K.toNat + 240 ≤ 2 ^ 32
  fitS : S.toNat + 2048 ≤ 2 ^ 32
  ks : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  reads : Covers [⟨State.addr K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr S, 2048⟩] s.wr

/-- What a call of `vg_aes_blocks_keys` leaves. -/
structure KeysPost (s : State) (K S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr S, 2048⟩] s.mem s'.mem
  keys : KeysIn s'.mem S R (schedAt s.mem K R)

theorem KeysCall.pre {s : State} {K S : BitVec 32} {R : Nat} (h : KeysCall s K S R) :
    Proof.Aes.blocksKeysArm.pre (s.callEntry.withRegions [⟨State.addr K, 240⟩] [⟨State.addr S, 2048⟩]) := by
  have hR := toNat_ofNat32 (n := R) (by rcases h.rounds with h' | h' | h' <;> omega_using [h'])
  simp only [Proof.Aes.blocksKeysArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h.r0, h.r1, h.r2, hR, State.withRegions_rd,
    State.withRegions_wr]
  exact ⟨trivial, trivial, h.ks, h.fitK, h.fitS, h.rounds⟩

theorem KeysCall.cov {s : State} {K S : BitVec 32} {R : Nat} (h : KeysCall s K S R) :
    Covers ([⟨State.addr K, 240⟩] ++ [⟨State.addr S, 2048⟩]) (s.rd ++ s.wr) := fun x n' hi => by
  rcases List.mem_append.mp hi.choose_spec.1 with hm | hm
  · exact h.reads x n' ⟨_, hm, hi.choose_spec.2⟩
  · obtain ⟨r', hr', hc'⟩ := h.writes x n' ⟨_, hm, hi.choose_spec.2⟩
    exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem keys_call {s : State} {K S : BitVec 32} {R : Nat} (h : KeysCall s K S R) :
    WP isa (.call "vg_aes_blocks_keys" blocksKeys) s (KeysPost s K S R) := by
  have hR := toNat_ofNat32 (n := R) (by rcases h.rounds with h' | h' | h' <;> omega_using [h'])
  refine WP.call (k := Proof.Aes.blocksKeysArm) Ecb.keys_correct (rd := [⟨State.addr K, 240⟩])
    (wr := [⟨State.addr S, 2048⟩]) h.pre h.cov h.writes ?_ keys_noCalls
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.blocksKeysArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h.r0, h.r1, h.r2, hR] at hpost
  exact hpost

theorem keys_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K S : BitVec 32, ∃ R : Nat, KeysCall s₁ K S R ∧ KeysCall s₂ K S R) :
    RelCT isa P (.call "vg_aes_blocks_keys" blocksKeys) fun _ _ => True := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨K, S, R, h₁, h₂⟩ := h _ _ hp
  refine RelCT.call (k := Proof.Aes.blocksKeysArm) Ecb.keys_correct Ecb.keys_ct
    [⟨State.addr K, 240⟩] [⟨State.addr S, 2048⟩] (P := fun x y => x = a ∧ y = b)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.cov, h₁.writes, h₂.cov, h₂.writes⟩
  simp only [Proof.Aes.blocksKeysArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h₁.r0, h₁.r1, h₁.r2, h₂.r0, h₂.r1, h₂.r2]
  exact ⟨trivial, trivial, trivial⟩

/-! ## `keysCall` -/

/-- What `keysCall` needs: the key schedule at `K` (in `r4`) for `R` rounds
(in `r5`) and the working space at `S` (in `r10`). -/
structure KeysArgs (s : State) (K S : BitVec 32) (R : Nat) : Prop where
  r4 : s.gpr .r4 = K
  r5 : s.gpr .r5 = BitVec.ofNat 32 R
  r10 : s.gpr .r10 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  fitK : K.toNat + 240 ≤ 2 ^ 32
  fitS : S.toNat + 2048 ≤ 2 ^ 32
  ks : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  reads : Covers [⟨State.addr K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr S, 2048⟩] s.wr

/-- The arguments of `vg_aes_blocks_keys`. -/
theorem keysArgs_wp {s : State} {K S : BitVec 32} {R : Nat} (h : KeysArgs s K S R) :
    WP isa (.block [movR .r0 .r4, movR .r1 .r5, movR .r2 .r10]) s fun s' =>
      KeysCall s' K S R ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    WP.block_nil ?_
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  exact ⟨⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r4],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r5],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r10],
    h.rounds, h.fitK, h.fitS, h.ks, by rw [rd₃, wr₃]; exact h.reads, by rw [wr₃]; exact h.writes⟩,
    fun r h0 h1 h2 => by rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h0],
    by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.sp, u₂.sp, u₁.sp], rd₃, wr₃⟩

/-- `keysCall` leaves the round keys of the schedule in the working space,
of which alone it changes the memory. -/
theorem keysCall_wp {s : State} {K S : BitVec 32} {R : Nat} (h : KeysArgs s K S R) :
    WP isa keysCall s (KeysPost s K S R) := by
  refine WP.seq (WP.mono (keysArgs_wp h) fun s₁ ⟨a, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  refine WP.mono (keys_call a) fun s₂ c => ?_
  refine ⟨by rw [c.rd, rd₁], by rw [c.wr, wr₁], by rw [c.sp, sp₁], fun r hr hlr => ?_,
    by rw [← m₁]; exact c.frame, by rw [← m₁]; exact c.keys⟩
  have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 := by revert hr; cases r <;> decide
  rw [c.saved r hr hlr, g₁ r this.1 this.2.1 this.2.2]

theorem keysArgs_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.r4, .r5, .r10])
    (.block [movR .r0 .r4, movR .r1 .r5, movR .r2 .r10]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `keysCall` is constant time in two runs with the same schedule, rounds
and working space. -/
theorem keysCall_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K S : BitVec 32, ∃ R : Nat, KeysArgs s₁ K S R ∧ KeysArgs s₂ K S R) :
    RelCT isa P keysCall fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ K S : BitVec 32, ∃ R : Nat, KeysArgs a K S R ∧ KeysArgs b K S R) ?_
    h (fun _ _ h => h)
  refine RelCT.exists_ fun K => RelCT.exists_ fun S => RelCT.exists_ fun R => ?_
  exact (rel_agree (F := fun s => KeysArgs s K S R) (F' := fun s => KeysArgs s K S R)
    (G := fun s => KeysCall s K S R) (G' := fun s => KeysCall s K S R) (Taint.ofRegs [.r4, .r5, .r10])
    (fun _ _ h h' => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.r4, h'.r4]
      · rw [h.r5, h'.r5]
      · rw [h.r10, h'.r10]) keysArgs_taint
    (fun _ h => WP.mono (keysArgs_wp h) fun _ h' => h'.1)
    (fun _ h => WP.mono (keysArgs_wp h) fun _ h' => h'.1)).seq
    (keys_rel fun s₁ s₂ h => ⟨K, S, R, h.1, h.2⟩)

end VG.Proof.Aes.Arm
