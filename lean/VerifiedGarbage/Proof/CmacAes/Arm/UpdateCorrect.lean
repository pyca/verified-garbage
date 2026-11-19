module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacAes.Arm.Words
public import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.CmacAes.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesOcb.Arm.Callee
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesOcb.Arm.Callee
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! ### `CmacAes.Arm.UpdateLoop`, which this module and modules that import it used -/

section

/-! ### `Aes.Arm.KeyedCall`, which this module and modules that import it used -/

section

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
open VG.Proof.AesOcb.Arm (BlkCall BlkPost blk_frame blk_frame_rel blkRd blkWr encF statesAt_frame)
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
      ⟨⟨hrd, hwr, hsp, hsv, hfr, by
        rw [statesAt_frame hm (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm)
          (by have h₁ := h.fitD; have h₂ := toNat_ofNat32 h.n_lt; omega_using [h₁, h₂])]
        exact h.out hpost.1⟩,
        keysIn_frame h.fitS (rounds_le h) hm (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.bs.symm) (keyedPost h hpost.2)⟩

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

end

end

/-! ### `CmacAes.Arm.Call`, which only this module used -/

section

/-!
# AES-CMAC on ARMv7: calling `vg_aes_ctr32` on one block

`ctr_call`: the frame that pushes `vg_aes_ctr32`'s stack arguments (`n = 1`
in `ra` and the working space `S` in `rb`) around its call, with the counter
block `C` and one data block `D` holding zeros: `D` then holds `CIPH_K(C)`, as
bytes (`Cmac.aesWith`), and only `C`, `D`, `S` and the 8 bytes below the stack
pointer change in memory.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hR])

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega_using [h]), Nat.mod_eq_of_lt (a := k) (by omega_using [h]),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega_using [])]
  omega_using [h]

/-- The 8 bytes below the stack pointer, where the frame pushes the stack arguments. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : BitVec 32) (R : Nat) (ra rb : Reg) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  hra : s.gpr ra = 1
  hrb : s.gpr rb = S
  regs : regList [ra, rb] = true
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  wd : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr D, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bw : (below s).Disjoint ⟨State.addr W, 240⟩
  bc : (below s).Disjoint ⟨State.addr C, 16⟩
  bd : (below s).Disjoint ⟨State.addr D, 16⟩
  bs : (below s).Disjoint ⟨State.addr S, 2048⟩
  hW : W.toNat + 240 ≤ 2 ^ 32
  hC : C.toNat + 16 ≤ 2 ^ 32
  hD : D.toNat + 16 ≤ 2 ^ 32
  hS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem (State.addr D) 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩, below s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr D) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16)

theorem e8 (ra rb : Reg) : BitVec.ofNat 32 (4 * [ra, rb].length) = 8 := rfl

/-- The regions `vg_aes_ctr32` is called with. -/
abbrev ctrRd (s : State) (W : BitVec 32) : List Region := [⟨State.addr W, 240⟩, below s]
abbrev ctrWr (C D S : BitVec 32) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩]

/-- The state `vg_aes_ctr32` runs from, with the permissions it is given. -/
abbrev ctrView (s : State) (ra rb : Reg) (W C D S : BitVec 32) : State :=
  (pushed [ra, rb] s).callEntry.withRegions (ctrRd s W) (ctrWr C D S)

namespace CallPre
variable {s : State} {W C D S : BitVec 32} {R : Nat} {ra rb : Reg} (h : CallPre s W C D S R ra rb)
include h

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub h.hsp

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h.hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [h.hspA]; omega_using []), h.hA]; rfl

theorem amem : (pushed [ra, rb] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (1 : BitVec 32)).writeW (State.addr s.sp - 8 + 4) S := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra, rb].length)) [s.gpr ra, s.gpr rb] = _
  rw [e8, storeWords_two, h.hA, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl, h.hA4,
    h.hra, h.hrb]

theorem fA : Frame [below s] s.mem (pushed [ra, rb] s).mem := by
  rw [h.amem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

omit h in
theorem sp_view : (ctrView s ra rb W C D S).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]

theorem arg0 : stackArg (ctrView s ra rb W C D S) 0 = 1 := by
  have := h.hsp
  rw [stackArg, show stackArgAddr (ctrView s ra rb W C D S) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [sp_view, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, h.hA],
    State.withRegions_mem, State.callEntry_mem, h.amem, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 : stackArg (ctrView s ra rb W C D S) 1 = S := by
  rw [stackArg, show stackArgAddr (ctrView s ra rb W C D S) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [sp_view]; exact h.hA4,
    State.withRegions_mem, State.callEntry_mem, h.amem, Mem.readW_writeW_self32]

omit h in
theorem view_gpr (r : Reg) (hr : r ∉ linkRegs) : (ctrView s ra rb W C D S).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem pre : Proof.Aes.ctr32Arm.pre (ctrView s ra rb W C D S) := by
  obtain hR := toNat_rounds h.rounds
  obtain hsa : stackArgAddr (ctrView s ra rb W C D S) 0 = State.addr s.sp - 8 := by
    unfold stackArgAddr; rw [sp_view, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
      BitVec.add_zero _, h.hA]
  simp only [Proof.Aes.ctr32Arm, h.arg0, h.arg1, hsa, view_gpr .r0 (by decide), view_gpr .r1 (by decide),
    view_gpr .r2 (by decide), view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, State.withRegions_rd,
    State.withRegions_wr, sp_view, h.hspA, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
  refine ⟨trivial, trivial, h.wc, ?_, h.ws, ?_, h.cs, ?_, h.bc.symm, ?_, h.bs.symm, h.hW, h.hC, ?_, h.hS, ?_,
    h.rounds⟩
  · simpa using h.wd
  · simpa using h.cd
  · simpa using h.ds
  · simpa [below] using h.bd.symm
  · simpa using h.hD
  · have := s.sp.isLt; omega_using []

/-- The stack arguments are the frame. -/
theorem cov : Covers (ctrRd s W ++ ctrWr C D S) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := h.reads x n' ⟨_, List.mem_singleton_self _, hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [e8, h.hA]
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.writes x n' ⟨_, by simp, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (ctrWr C D S) (pushed [ra, rb] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end CallPre

theorem ctr_noCalls : Impl.Aes.Arm.ctr32.noCalls = true := by decide +kernel

theorem ctr_call {s : State} {W C D S : BitVec 32} {R : Nat} {ra rb : Reg} (h : CallPre s W C D S R ra rb) :
    WP isa (ctrCall ra rb) s (CallPost s W C D S R) := by
  refine WP.frame (rs := [ra, rb]) (r := ra) h.regs (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct
    (rd := ctrRd s W) (wr := ctrWr C D S) h.pre h.cov h.covW ?_ ctr_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost ml ul hfl
  have hfl' : Frame [below s] s₂.mem ml := by rw [e8, h.hA] at hfl; exact hfl
  obtain hR := toNat_rounds h.rounds
  obtain hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']
  -- The memory of the frame.
  have fBelow : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩]
      (pushed [ra, rb] s).mem s₂.mem := hf
  obtain bytesW : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr W) (16 * (R + 1)) =
      Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bw.symm.sub_left (Region.sub_prefix hR')).symm.symm) (by omega_using [hR])
  obtain bytesC : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr C) 16 =
      Spec.Aes.bytesAt s.mem (State.addr C) 16 :=
    Proof.Cmac.bytesAt_frame16 h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bc.symm)
  obtain bytesD : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr D) 16 =
      Spec.Aes.bytesAt s.mem (State.addr D) 16 :=
    Proof.Cmac.bytesAt_frame16 h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm)
  obtain ⟨hdata, -⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, CallPre.view_gpr .r0 (by decide),
    CallPre.view_gpr .r1 (by decide), CallPre.view_gpr .r2 (by decide), CallPre.view_gpr .r3 (by decide), h.r0, h.r1, h.r2,
    h.r3, hR, h.arg0, show (1 : BitVec 32).toNat = 1 from rfl] at hdata
  obtain one : ∀ m : Mem, Spec.Gcm.blocksAt m (State.addr D) 1 = [Spec.Gcm.blockAt m (State.addr D)] :=
    fun m => by simp [Spec.Gcm.blocksAt]
  obtain bD : Spec.Gcm.blockAt (pushed [ra, rb] s).mem (State.addr D) = 0 := by
    rw [Spec.Gcm.blockAt, bytesD, h.zero, ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  -- The register the pop loads is the one pushed.
  obtain slot : s₂.mem.readW (State.addr (pushed [ra, rb] s).sp) 32 = 1 := by
    rw [pushed_sp, e8, h.hA]
    have := fBelow.readW (r := ⟨State.addr s.sp - 8, 4⟩) (a := State.addr s.sp - 8) (w := 32)
      (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.bc.sub_left (Region.sub_prefix (by decide))).symm.symm
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide)))) (by decide)
    rw [this, h.amem, Mem.readW_writeW_sep
      (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩ <;> dsimp only
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, e8]; exact BitVec.sub_add_cancel _ _
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot, h.hra]
    · rw [popped_gpr hra, hcs r hr hlr, pushed_gpr]
  · refine ((h.fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fBelow.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)).trans
      (hfl'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  · rw [Proof.Cmac.bytesAt_frame16 hfl' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm),
      Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt, bytesW, bytesC,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem ctr_rel {W C D S sp₀ : BitVec 32} {R : Nat} {ra rb : Reg} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W C D S R ra rb ∧ CallPre s₂ W C D S R ra rb ∧ s₁.sp = sp₀ ∧
      s₂.sp = sp₀) :
    RelCT isa P (ctrCall ra rb) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call Proof.Aes.Arm.ctr32_correct Proof.Aes.Arm.ctr32_ct
    [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] (ctrWr C D S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed h₁.regs (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed h₂.regs (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  obtain e₁ : ctrRd s₁ W = [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] := by rw [ctrRd, below, sp₁]
  obtain e₂ : ctrRd s₂ W = [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] := by rw [ctrRd, below, sp₂]
  obtain p₁ := h₁.pre (C := C) (D := D) (S := S)
  obtain p₂ := h₂.pre (C := C) (D := D) (S := S)
  rw [ctrView, e₁] at p₁
  rw [ctrView, e₂] at p₂
  refine ⟨p₁, p₂, ?_, e₁ ▸ h₁.cov, h₁.covW, e₂ ▸ h₂.cov, h₂.covW⟩
  obtain a₁ := h₁.arg0 (C := C) (D := D) (S := S)
  obtain b₁ := h₁.arg1 (C := C) (D := D) (S := S)
  obtain a₂ := h₂.arg0 (C := C) (D := D) (S := S)
  obtain b₂ := h₂.arg1 (C := C) (D := D) (S := S)
  rw [ctrView, e₁] at a₁ b₁
  rw [ctrView, e₂] at a₂ b₂
  simp only [Proof.Aes.ctr32Arm, a₁, b₁, a₂, b₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Arm

end

end


@[expose] public section

section

section

/-!
# AES-CMAC on ARMv7: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function pushes `vg_aes_ctr32`'s two
stack arguments in the 8 bytes below the stack pointer, which may not overlap
any buffer.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
def updateArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint data ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
      Spec.Cmac.chain (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16)
        (Spec.Cmac.blocksAt s.mem (State.addr (s.gpr .r3)) 16 (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`. -/
def subkeysArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let subk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2176⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      below.Disjoint sched ∧ below.Disjoint subk ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2176 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 16
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2, last = r3, last_len = [sp], scratch = [sp + 4])`. -/
def finalizeArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let last : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint key ∧ below.Disjoint last ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) ∧
      (stackArg s 0).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0) + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (stackArg s 0).toNat) →
      Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update`, the blocks before and in the loop

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r7` the next block, `r8` the blocks left), only the state, the first 2064
bytes of the scratch buffer and the 8 bytes below the stack pointer have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldrSp saveMem
  saveList_ok saveMem_frame readW_writeW_save cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev W : BitVec 32 := s₀.gpr .r0
abbrev R : Nat := (s₀.gpr .r1).toNat
abbrev St : BitVec 32 := s₀.gpr .r2
abbrev Dp : BitVec 32 := s₀.gpr .r3
abbrev N : Nat := (stackArg s₀ 0).toNat
abbrev S : BitVec 32 := stackArg s₀ 1

abbrev schR : Region := ⟨State.addr (W s₀), 240⟩
abbrev stR : Region := ⟨State.addr (St s₀), 16⟩
abbrev dataR : Region := ⟨State.addr (Dp s₀), 16 * N s₀⟩
abbrev scrR : Region := ⟨State.addr (S s₀), 2176⟩
abbrev argsR : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev belowR : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (State.addr (W s₀)) (R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (State.addr (Dp s₀)) 16 (N s₀)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := saveMem s₀.mem (State.addr (S s₀)) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  st_args : (stR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_data : (belowR s₀).Disjoint (dataR s₀)
  b_st : (belowR s₀).Disjoint (stR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateArm.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = St s₀
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16) ((blks s₀).take k)

/-! ## Addresses and regions -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (S s₀).isLt; omega_arith)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) :
    State.addr (Dp s₀ + BitVec.ofNat 32 (16 * k)) = State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k) :=
  addr_add (by have := hp.data_fit; have := (Dp s₀).isLt; omega_arith)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) :
    (Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

omit hp in
theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

omit hp in
theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem UPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_arith), addr_add (by omega_arith)]
  simp

theorem UPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

omit hp in
theorem UPre.arg_sub : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argsR s₀) := Region.sub_prefix (by decide)

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2096 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

export VG.Arm.Spill (saveMem_congr)

theorem saved_slots : Spill.Slots 2064 2096 saved := by decide

theorem savedMem_frame (s₀ : State) : Frame [⟨State.addr (S s₀), 2096⟩] s₀.mem (savedMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr (S s₀)) s₀.gpr s₀.mem saved saved_slots (r, d) h

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => LInv s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega_arith, by omega_arith, ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩⟩
  obtain hm₂ : s₂.mem = savedMem s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  obtain harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (savedMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.scr_args.symm.sub_left UPre.arg_sub).sub_right (Region.sub_prefix (by decide))) (by decide)
  simp only [setup, mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  obtain r8 : s₉.gpr .r8 = stackArg s₀ 0 := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg]
  obtain mm : s₉.mem = savedMem s₀ := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 32 (N s₀) := by simp [N]
  obtain stS : Spec.Aes.bytesAt (savedMem s₀) (State.addr (St s₀)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
    exact (BitVec.add_zero _).symm
  · rw [r8, a0]; rfl
  · simp (disch := decide) only [f₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, h12]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other]
  · rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [mm]; exact Frame.refl _ _
  · rw [mm, stS]; rfl
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: the loop of `vg_cmac_aes_update`

One block keeps the loop invariant, with the round keys in the working space
(`body_ok`, `KInv`): the state becomes `C ⊕ Mᵢ` (`Cmac.xor4Mem`), and the
call of `vg_aes_encrypt_blocks_keyed` leaves `CIPH_K(C ⊕ Mᵢ)` there, and the
round keys where `vg_aes_blocks_keys` put them before the first block
(`keysCall_wp`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs eval_ne ofNat_beq_zero sub_ofNat)
open VG.Impl.Aes.Arm (keyedFrame keysCall)
open VG.Proof.Aes (KeysIn)
open VG.Proof.Aes.Arm (schedAt KeysArgs kblk_call)
open VG.Proof.AesOcb.Arm (BlkCall BlkPost encF)

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega_arith)]
  simp [Spec.Cmac.blocksAt]

/-! ## Memory outside the writable regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [stR s₀, scrR s₀, belowR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (State.addr (W s₀)) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  obtain hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.b_data.symm.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  obtain f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩)

end

/-! ## The round keys bitsliced once -/

/-- The round keys of the key schedule on entry are in the working space. -/
abbrev Keys (s₀ : State) (m : Mem) : Prop := KeysIn m (S s₀) (R s₀) (schedAt s₀.mem (W s₀) (R s₀))

/-- The loop invariant, with the round keys in the working space. -/
def KInv (s₀ : State) (k : Nat) (s : State) : Prop := LInv s₀ k s ∧ Keys s₀ s.mem

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.rounds_le : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith

theorem UPre.work_fit : (S s₀).toNat + 2048 ≤ 2 ^ 32 := by have := hp.scr_fit; omega_arith

/-- The round keys stay where the memory changes only apart from the working
space. -/
theorem keys_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr (S s₀), 2048⟩ : Region).Disjoint r) (h : Keys s₀ m) : Keys s₀ m' :=
  Proof.Aes.Arm.Ecb.keysIn_frame hp.work_fit hp.rounds_le hf hd h

/-- The round keys at a call: those of the key schedule as the memory then
holds it, which is as on entry. -/
theorem keys_call {m : Mem} (hf : Frame (Big s₀) s₀.mem m) (h : Keys s₀ m) :
    KeysIn m (S s₀) (R s₀) (schedAt m (W s₀) (R s₀)) := by
  rw [show schedAt m (W s₀) (R s₀) = schedAt s₀.mem (W s₀) (R s₀) from hp.sched_bytes hf]; exact h

/-- The round keys a call leaves are those of the key schedule on entry. -/
theorem keys_of_call {m m' : Mem} (hf : Frame (Big s₀) s₀.mem m)
    (h : KeysIn m' (S s₀) (R s₀) (schedAt m (W s₀) (R s₀))) : Keys s₀ m' := by
  rw [show schedAt m (W s₀) (R s₀) = schedAt s₀.mem (W s₀) (R s₀) from hp.sched_bytes hf] at h; exact h

/-- The arguments of the call that bitslices the round keys, from the
invariant. -/
theorem LInv.keysArgs {k : Nat} {s : State} (h : LInv s₀ k s) : KeysArgs s (W s₀) (S s₀) (R s₀) := by
  refine ⟨h.r4, by rw [h.r5]; simp [R], h.r10, hp.rounds, hp.sch_fit, hp.work_fit,
    hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The call that bitslices the round keys keeps the invariant, and leaves
them in the working space. -/
theorem keysCall_wp {k : Nat} {s : State} (h : LInv s₀ k s) : WP isa keysCall s (KInv s₀ k) := by
  refine WP.mono (Proof.Aes.Arm.keysCall_wp (h.keysArgs hp)) fun s₂ c => ?_
  obtain g : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := c.saved
  refine ⟨⟨by rw [g _ (by simp [preserved]) (by decide), h.r4], by rw [g _ (by simp [preserved]) (by decide), h.r5],
    by rw [g _ (by simp [preserved]) (by decide), h.r6], by rw [g _ (by simp [preserved]) (by decide), h.r7],
    by rw [g _ (by simp [preserved]) (by decide), h.r8], by rw [g _ (by simp [preserved]) (by decide), h.r10],
    by rw [g _ (by simp [preserved]) (by decide), h.r11],
    by rw [c.sp, h.sp], by rw [c.rd, h.rd], by rw [c.wr, h.wr], ?_, ?_⟩, ?_⟩
  · exact h.frame.trans (c.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩)
  · rw [Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Region.sub_prefix (by decide))) (by decide), h.state]
  · exact keys_of_call hp (UPre.big_of h.frame) c.keys

end

/-! ## One block -/

/-- `CIPH_K` of a block in memory, from AES on its state. -/
theorem aesWith_state (nr : Nat) (w : List Byte) (m : Mem) (p : Addr) :
    Spec.Cmac.aesWith nr w (Spec.Aes.bytesAt m p 16) = (Spec.Aes.cipher nr w (Spec.Aes.stateAt m p)).toList := by
  rw [Spec.Cmac.aesWith, Proof.AesCbc.ofFn_bytesAt]

/-- The address of block `k` of the data. -/
abbrev blk (s₀ : State) (k : Nat) : Addr := State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (St s₀) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = Proof.Cmac.xor4Mem s.mem (State.addr (St s₀)) (State.addr (St s₀)) (blk s₀ k)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem chainIn_eq : chainIn ++ updArgs = xorBlk .r12 .lr .r6 .r7 .r6 0 0 0 ++
    ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6), .mov .r3 (.imm 1),
      .mov .r12 (.reg .r10)] : List Instr) := rfl

theorem bodyA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (BodyA s₀ k s) := by
  obtain hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hW : s.wr = [stR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hsc := hp.scr_fit
  have hst := hp.st_fit
  have hdf := hp.data_fit
  obtain qN := hp.dataN hk
  obtain cSt : Covers [stR s₀] [stR s₀, scrR s₀] := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  rw [chainIn_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r6]; omega_arith) (by rw [h.r7, qN]; omega_arith)
    (by rw [h.r6]; omega_arith) ?_ ?_ ?_ fun s₁ g₁ => ?_
  · rw [h.r6, add0, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.r7, add0, hp.dataA hk, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_arith⟩
  · rw [h.r6, add0, hW]; exact cSt
  have e₁ : ∀ r, r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r := g₁.gpr
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 hlr => by
      rw [u₆.other _ h12, u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, u₂.other _ h0, e₁ _ h12 hlr]
  obtain sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, g₁.sp, h.sp]
  obtain rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, g₁.rd]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, g₁.wr]
  obtain mem₆ : s₆.mem = Proof.Cmac.xor4Mem s.mem (State.addr (St s₀)) (State.addr (St s₀)) (blk s₀ k) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, g₁.mem, h.r6, h.r7, add0, add0, hp.dataA hk]
  obtain hb : Proof.AesGcm.Arm.below s₆.sp = belowR s₀ := by rw [sp₆]; rfl
  refine ⟨⟨?_, ?_, ?_, by rw [u₆.other _ (by decide), u₅.gpr]; rfl, ?_, hp.rounds, by rw [sp₆]; exact hp.sp8,
    hp.sch_fit, by omega_arith, hp.work_fit, hp.sch_st,
    hp.sch_scr.sub_right (Region.sub_prefix (by decide)), hp.st_scr.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_st,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩, keep, by rw [sp₆, h.sp], mem₆,
    rd₆, wr₆⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      e₁ _ (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      e₁ _ (by decide) (by decide), h.r5]
    simp [R]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      e₁ _ (by decide) (by decide), h.r6]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      e₁ _ (by decide) (by decide), h.r10]
  · rw [rd₆, wr₆, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₆, hW]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The memory before the call, and the round keys there: the state is apart
from the working space. -/
theorem BodyA.keys {s₀ : State} (hp : UPre s₀) {k : Nat} {s s₁ : State} (h : LInv s₀ k s)
    (a : BodyA s₀ k s s₁) (hkeys : Keys s₀ s.mem) :
    Frame (Big s₀) s₀.mem s₁.mem ∧ KeysIn s₁.mem (S s₀) (R s₀) (schedAt s₁.mem (W s₀) (R s₀)) := by
  obtain f₁ : Frame [stR s₀] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, fun _ h => h⟩)
  exact ⟨big₁, keys_call hp big₁ (keys_frame hp f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_scr.sub_right (Region.sub_prefix (by decide))).symm) hkeys)⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : KInv s₀ k s) :
    WP isa body s fun s' => KInv s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  obtain ⟨h, hkeys⟩ := h
  have hdf := hp.data_fit
  obtain hN := (stackArg s₀ 0).isLt
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ a => ?_)
  obtain ⟨big₁, k₁⟩ := a.keys hp h hkeys
  refine WP.seq (WP.mono (kblk_call a.pre k₁) fun s₂ ⟨h₂, k₂⟩ => ?_)
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have g (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) (h7 : r ≠ .r7) (h8 : r ≠ .r8) :
      s₄.gpr r = s.gpr r := by
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ h8, u₃.other _ h7, h₂.saved r hr hlr,
      a.keep r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2 hlr]
  obtain r7₂ : s₂.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [h₂.saved .r7 (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h.r7]
  obtain r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [u₃.other _ (by decide), h₂.saved .r8 (by simp [preserved]) (by decide),
      a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  obtain dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  -- Memory.
  obtain bigS := UPre.big_of h.frame
  obtain f₁ : Frame [stR s₀] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain stq : (stR s₀).Disjoint ⟨blk s₀ k, 16⟩ := hp.data_st.symm.sub_right (UPre.data_sub hk)
  obtain out : Spec.Aes.bytesAt s₂.mem (State.addr (St s₀)) 16 =
      ciph s₀ (Spec.Cmac.xor (Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16)
        ((blks s₀).take k)) (Spec.Aes.bytesAt s₀.mem (blk s₀ k) 16)) := by
    rw [Proof.AesCbc.bytesAt_of_statesAt h₂.out, show encF.f = Spec.Aes.cipher from rfl, ← aesWith_state,
      UPre.sched_bytes hp big₁, a.mem,
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint stq), h.state,
      UPre.block_bytes hp bigS hk]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [g .r4 (by simp [preserved]) (by decide) (by decide) (by decide), h.r4]
  · rw [g .r5 (by simp [preserved]) (by decide) (by decide) (by decide), h.r5]
  · rw [g .r6 (by simp [preserved]) (by decide) (by decide) (by decide), h.r6]
  · rw [u₄.other _ (by decide), u₃.gpr, r7₂, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_arith)]
  · rw [u₄.gpr, r8₃, dec]
  · rw [g .r10 (by simp [preserved]) (by decide) (by decide) (by decide), h.r10]
  · rw [g .r11 (by simp [preserved]) (by decide) (by decide) (by decide), h.r11]
  · rw [u₄.sp, u₃.sp, h₂.sp, a.sp, h.sp]
  · rw [u₄.rd, u₃.rd, h₂.rd, a.rd, h.rd]
  · rw [u₄.wr, u₃.wr, h₂.wr, a.wr, h.wr]
  · have hb : Proof.AesGcm.Arm.below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
    rw [u₄.mem, u₃.mem]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨belowR s₀, by simp, by rw [hb]; exact fun _ h => h⟩
  · rw [u₄.mem, u₃.mem, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [u₄.mem, u₃.mem]; exact keys_of_call hp big₁ k₂
  · rw [z₄, r8₃, dec]; exact ofNat_beq_zero (by omega_arith)

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : KInv s₀ k s) :
    WP isa (.loop body .ne) s (KInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := KInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ KInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

end VG.Proof.CmacAes.Arm

end

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is correct
-/

@[expose] public section

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd wp_ldr eval_eq)
open VG.Impl.Aes.Arm (keysCall)

/-! ## Restoring the registers -/

theorem saved_eq : saved = saved.take 7 ++ [(.r10, 2088)] := rfl

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by omega_using [h₂])
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ (N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hsc := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₂ ld ho m₁ _ _ sp₁ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hb := saved_bound p (by rw [saved_eq]; exact hp')
    exact ⟨by omega_using [hb], by rw [h.r10]; omega_using [hsc, hb], by rw [h.r10]; exact inS _ (by omega_using [hb])⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      rw [ld p (by rw [← saved_eq]; exact hp'), h.r10, sl _ _ hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho _ (by decide), h.r11]
  · rw [sp₁, h.sp]
  · show Spec.Aes.bytesAt s₂.mem (State.addr (St s₀)) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [m₁, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

/-! ## The whole function -/

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.seq keysCall (.loop body .ne))) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (keysCall_wp hp h) fun _ h' =>
      WP.mono (loop_ok hp (by omega_using [hn]) h') fun _ h'' => h''.1)

theorem update_wp {s₀ : State} (h0 : updateArm.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.Arm
