module

public import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
public import VerifiedGarbage.Impl.CmacTripleDes.Arm
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.Arm.CT
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Arm.Lost

/-! ### `CmacTripleDes.Arm.FinalizeCorrect`, which only this module used -/

section

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finalize` is correct

Untrusted: everything here is checked by Lean. After the branch on the
length, `r4:r5` holds `Mₙ` (`BPost`); the function saves the state pointer,
XORs in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as
the state, the MAC (`macFull_split8`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_str wp_rev)

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  obtain hp := FPre.of h0
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have tf := hp.st_fit
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  obtain rdwr₁ : s₁.rd ++ s₁.wr = [keyR s₀, lastR s₀, fargsR s₀, fstR s₀, fscrR s₀] := by
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain stIn : ∀ d, d + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) (State.addr (FSt s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr₁]; exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  -- `finMid`.
  refine WP.seq ?_
  simp only [finMid]
  refine wp_str (by decide) (by rw [h₁.r10, hp.scrAddr (by decide)]) (by rw [h₁.wr]; exact hp.inScr (by decide) (by decide))
    fun s₂ w₂ => ?_
  refine wp_ldr (by decide) (by rw [w₂.gpr, h₁.r1, add0]) (by rw [w₂.rd, w₂.wr]; simpa using stIn 0 (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldr (a := State.addr (FSt s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), w₂.gpr, h₁.r1]; exact addr_add (by omega_arith))
    (by rw [u₃.rd, u₃.wr, w₂.rd, w₂.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => wp_eor (op2_reg _ _) fun s₆ u₆ => wp_rev fun s₇ u₇ =>
    wp_rev fun s₈ u₈ => WP.block_nil ?_
  obtain g₈ : ∀ r, r ∉ [Reg.r0, .r1, .r4, .r5, .r6, .r7] → s₈.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.2.1, u₅.other _ hr.2.2.1, u₄.other _ hr.2.2.2.2.2,
      u₃.other _ hr.2.2.2.2.1, w₂.gpr]
  let A := State.addr (FS s₀)
  obtain mem₈ : s₈.mem = s₁.mem.writeW (A + BitVec.ofNat 64 112) (FSt s₀) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, w₂.mem, h₁.r1]
  obtain stSep : ∀ d, d + 4 ≤ 8 →
      (s₁.mem.writeW (A + BitVec.ofNat 64 112) (FSt s₀)).readW (State.addr (FSt s₀) + BitVec.ofNat 64 d) 32 =
        s₁.mem.readW (State.addr (FSt s₀) + BitVec.ofNat 64 d) 32 := fun d hd =>
    Mem.readW_writeW_sep ((hp.st_scr.sub_right (Offset.sub_base _ (by decide))).sub_left
      (Offset.sub_base _ (by omega_arith)) |>.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
  obtain ax₈ : s₈.gpr .r0 ++ s₈.gpr .r1 =
      byteRev64 ((s₁.gpr .r5 ++ s₁.gpr .r4) ^^^ s₁.mem.readW (State.addr (FSt s₀)) 64) := by
    obtain e0 := stSep 0 (by decide)
    obtain e4 := stSep 4 (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e0
    rw [u₈.gpr, u₈.other .r0 (by decide), u₇.gpr, u₇.other .r5 (by decide), u₆.gpr, u₆.other .r4 (by decide),
      u₅.gpr, u₅.other .r5 (by decide), u₅.other .r7 (by decide), u₄.gpr, u₄.other .r4 (by decide),
      u₄.other .r5 (by decide), u₄.other .r6 (by decide), u₃.gpr, u₃.other .r4 (by decide), u₃.other .r5 (by decide),
      u₃.mem, w₂.mem, w₂.gpr, h₁.r1, e0, e4, rev_xor_append, readW64_split s₁.mem]
  obtain r9₈ : s₈.gpr .r9 = FW s₀ := by rw [g₈ _ (by decide), h₁.r9]
  obtain r10₈ : s₈.gpr .r10 = FS s₀ := by rw [g₈ _ (by decide), h₁.r10]
  obtain rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, w₂.rd, h₁.rd]
  obtain wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂.wr, h₁.wr]
  obtain bp : BlockPre s₈ :=
    { sched := ⟨400, (by rw [r9₈, rd₈, wr₈, hp.rd]; simp), (by decide), (by rw [r9₈]; exact kf)⟩
      scr := ⟨640, (by rw [r10₈, wr₈, hp.wr]; simp), (by decide), (by rw [r10₈]; exact sf)⟩
      disj := by
        rw [r9₈, r10₈]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₉ ⟨same₉, r9₉, ax₉⟩ => ?_)
  obtain r10₉ : s₉.gpr .r10 = FS s₀ := by rw [same₉.r10, g₈ _ (by decide), h₁.r10]
  obtain xR₈ : xR s₈ = ⟨A, 52⟩ := by rw [xR, g₈ _ (by decide), h₁.r10]
  obtain f₉ : Frame [⟨A, 52⟩] s₈.mem s₉.mem := by rw [← xR₈]; exact same₉.frame
  obtain outBlock : ∀ d, 52 ≤ d → d + 4 ≤ 640 →
      s₉.mem.readW (A + BitVec.ofNat 64 d) 32 = s₈.mem.readW (A + BitVec.ofNat 64 d) 32 := fun d h₁' h₂' =>
    f₉.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  obtain rdwr₉ : s₉.rd ++ s₉.wr = [keyR s₀, lastR s₀, fargsR s₀, fstR s₀, fscrR s₀] := by
    rw [same₉.rd, same₉.wr, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, w₂.rd, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr,
      u₃.wr, w₂.wr, rdwr₁]
  obtain wr₉ : s₉.wr = [fstR s₀, fscrR s₀] := by
    rw [same₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂.wr, h₁.wr, hp.wr]
  rw [WP.block_append_iff]
  refine wp_ldr (by decide) (by rw [r10₉, hp.scrAddr (by decide)])
    (by rw [rdwr₉]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega_arith)))
    fun s₁₀ u₁₀ => ?_
  obtain r2₁₀ : s₁₀.gpr .r2 = FSt s₀ := by
    rw [u₁₀.gpr, outBlock 112 (by decide) (by decide), mem₈, Mem.readW_writeW_self32]
  refine wp_rev fun s₁₁ u₁₁ => wp_rev fun s₁₂ u₁₂ => ?_
  obtain stW : ∀ d, d + 4 ≤ 8 → InRegions s₁₂.wr (State.addr (FSt s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]
    exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  refine wp_str (by decide) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), r2₁₀, add0])
    (by simpa using stW 0 (by decide)) fun s₁₃ w₁₃ => ?_
  refine wp_str (a := State.addr (FSt s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [w₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), r2₁₀]; exact addr_add (by omega_arith))
    (by rw [w₁₃.wr]; exact stW 4 (by decide)) fun s₁₄ w₁₄ => WP.block_nil ?_
  obtain r10₁₄ : s₁₄.gpr .r10 = FS s₀ := by
    rw [w₁₄.gpr, w₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), r10₉]
  obtain mem₁₄ : s₁₄.mem = (s₉.mem.writeW (State.addr (FSt s₀)) (rev (s₉.gpr .r0))).writeW
      (State.addr (FSt s₀) + BitVec.ofNat 64 4) (rev (s₉.gpr .r1)) := by
    rw [w₁₄.mem, w₁₃.mem, w₁₃.gpr, u₁₂.gpr, u₁₂.other .r0 (by decide), u₁₁.gpr, u₁₂.mem, u₁₁.mem,
      u₁₁.other .r1 (by decide), u₁₀.other .r0 (by decide), u₁₀.other .r1 (by decide), u₁₀.mem]
  obtain rdwr₁₄ : s₁₄.rd ++ s₁₄.wr = [keyR s₀, lastR s₀, fargsR s₀, fstR s₀, fscrR s₀] := by
    rw [w₁₄.rd, w₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, w₁₄.wr, w₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, rdwr₉]
  -- The slots of the saved registers.
  obtain slots : ∀ d, 52 ≤ d → d + 4 ≤ 88 →
      s₁₄.mem.readW (A + BitVec.ofNat 64 d) 32 = (savedMem s₀ (FS s₀)).readW (A + BitVec.ofNat 64 d) 32 := by
    intro d h₁' h₂'
    obtain sd : ∀ e, e + 4 ≤ 8 → Mem.Sep (A + BitVec.ofNat 64 d) (32 / 8) (State.addr (FSt s₀) + BitVec.ofNat 64 e) (32 / 8) :=
      fun e he => (hp.st_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm.sub_right (Offset.sub_base _ (by omega_arith))
        |>.sep (Region.contains_self _ _) (Region.contains_self _ _)
    obtain sd0 := sd 0 (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at sd0
    rw [mem₁₄, Mem.readW_writeW_sep (sd 4 (by decide)) (by decide), Mem.readW_writeW_sep sd0 (by decide),
      outBlock d (by omega_arith) (by omega_arith), mem₈, readW_writeW_far _ _ _ (by omega_arith) (by decide) (by omega_arith)]
    refine h₁.frame.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (restore_ok r10₁₄ (by omega_arith) fun d h₁' h₂' => by
      rw [rdwr₁₄]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    fun s' ⟨hl, sp', m', _, _⟩ => ⟨restored slots hl (by
      rw [sp', w₁₄.sp, w₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, same₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, w₂.sp,
        h₁.sp]), ?_⟩
  intro hk msg hml hne hst
  obtain scrSub : ∀ r ∈ [mnR s₀], ∃ r' ∈ [fscrR s₀], Region.Sub r r' := fun r hr => ⟨fscrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩
  obtain F₁ : Frame [fscrR s₀] s₀.mem s₁.mem :=
    ((savedMem_frame s₀ (FS s₀)).sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₁.frame.sub scrSub)
  obtain F₈ : Frame [fscrR s₀] s₀.mem s₈.mem := by
    rw [mem₈]; exact F₁.writeW (r := fscrR s₀) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_arith))
  obtain hS' : sch s₈ = Spec.TripleDes.scheduleAt s₀.mem (State.addr (FW s₀)) := by
    show Spec.TripleDes.scheduleAt s₈.mem (State.addr (s₈.gpr .r9)) = _
    rw [r9₈]
    exact scheduleAt_frame F₈ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.key_scr.sub_left (Region.sub_prefix (by decide))
  obtain hst₁ : le8 (s₁.mem.readW (State.addr (FSt s₀)) 64) = Spec.Aes.bytesAt s₀.mem (State.addr (FSt s₀)) 8 := by
    rw [le8_readW]
    exact bytesAt_frame F₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr) (by decide)
  obtain hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem (State.addr (FW s₀)))
  obtain hk' : Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (ciphAt s₀.mem (State.addr (FW s₀))) 8).1 ++
        (Spec.Cmac.subkeys (ciphAt s₀.mem (State.addr (FW s₀))) 8).2 := by
    rw [show State.addr (FW s₀) + BitVec.ofNat 64 392 =
        State.addr (FW s₀) + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add _ 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s'.mem (State.addr (FSt s₀)) 8 = _
  rw [m', mem₁₄, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, rev_eq, rev_eq,
    byteRev32_append, ax₉, ax₈, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, Proof.Cmac.xor_comm]

end VG.Proof.CmacTripleDes.Arm

end

end


/-!
# Streaming TDEA-CMAC on ARMv7: the code of `init`, `update` and `finalize`, inline

Each run of the code of `vg_cmac_triple_des_init`, `_update` and `_finalize`
inside the streaming functions, from its contract (`WP.inline`): what it
needs (`…Args`), what it leaves (`…Post`, in terms of the memory before it),
and that two runs with the same arguments leak the same (`…_rel`). `update`
and `finalize` take the working space on the stack: they run in a frame that
pushes its address (`WP.frameInline`, `RelCT.frameInline`), in the 4 bytes
below the stack pointer (`blw4`), which the pop loads back.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm
open VG.Arm.FrameStack (addr_sub' sub_toNat')
open VG.Proof.CmacTripleDes.Arm (updateArm finalizeArm initArm ciphAt scheduleAt_frame)

/-! ## Inlining in a frame -/

/-- The 4 bytes below the stack pointer. -/
abbrev blw4 (s : State) : Region := ⟨State.addr s.sp - 4, 4⟩

/-- The state code run in a frame pushing `ra` runs from, with the
permissions it is given. -/
abbrev view (ra : Reg) (s : State) (rd wr : List Region) : State := (pushed [ra] s).withRegions rd wr

theorem e4 (ra : Reg) : BitVec.ofNat 32 (4 * [ra].length) = 4 := rfl

theorem view_gpr {ra : Reg} {s : State} {rd wr : List Region} (r : Reg) : (view ra s rd wr).gpr r = s.gpr r := rfl

theorem view_sp {ra : Reg} {s : State} {rd wr : List Region} : (view ra s rd wr).sp = s.sp - 4 := rfl

section
variable {s : State} (hsp : 4 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 4) = State.addr s.sp - 4 := addr_sub' (k := 4) hsp

theorem spA : (s.sp - 4).toNat = s.sp.toNat - 4 := sub_toNat' (k := 4) hsp

theorem amem (ra : Reg) : (pushed [ra] s).mem = s.mem.writeW (State.addr s.sp - 4) (s.gpr ra) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra].length)) [s.gpr ra] = _
  rw [e4]
  show s.mem.writeW (State.addr (s.sp - 4)) (s.gpr ra) = _
  rw [hA hsp]

theorem push_frame (ra : Reg) : Frame [blw4 s] s.mem (pushed [ra] s).mem := by
  rw [amem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []

theorem push_slot (ra : Reg) : (pushed [ra] s).mem.readW (State.addr s.sp - 4) 32 = s.gpr ra := by
  rw [amem hsp, Mem.readW_writeW_self32]

theorem view_argAddr {ra : Reg} {rd wr : List Region} : stackArgAddr (view ra s rd wr) 0 = State.addr s.sp - 4 := by
  unfold stackArgAddr; rw [view_sp, show s.sp - 4 + BitVec.ofNat 32 (4 * 0) = s.sp - 4 from
    BitVec.add_zero _, hA hsp]

/-- The stack argument, as the code reads it. -/
theorem view_arg0 {ra : Reg} {rd wr : List Region} : stackArg (view ra s rd wr) 0 = s.gpr ra := by
  rw [stackArg, view_argAddr hsp]; exact push_slot hsp ra

theorem view_spf {ra : Reg} {rd wr : List Region} : (view ra s rd wr).sp.toNat + 4 ≤ 2 ^ 32 := by
  rw [view_sp, spA hsp]; have := s.sp.isLt; omega_using []

/-- The covering of the code's regions, from those of the frame's owner. -/
theorem cov_push {ra : Reg} {rd₀ wr : List Region} (hr : Covers rd₀ (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers ((rd₀ ++ [blw4 s]) ++ wr) ((pushed [ra] s).rd ++ (pushed [ra] s).wr) := by
  intro x n ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨r', hr'', hc'⟩ := hr x n ⟨r, hr', hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr'' with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
    · rw [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
      rwa [e4, hA hsp]
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

end

theorem covW_push {ra : Reg} {s : State} {wr : List Region} (hw : Covers wr s.wr) :
    Covers wr (pushed [ra] s).wr := by
  intro x n hi
  obtain ⟨r', hr', hc'⟩ := hw x n hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

/-- Verified code without calls, in the frame that pushes its stack argument
`ra`, from its contract `k`: it runs from `view`, and changes memory only
within the regions it may write and the 4 bytes below the stack pointer; the
pop loads `ra` back, so it changes no callee-saved register. Once the frame is
released, memory is the body's but in those 4 bytes. -/
theorem WP.frameInline {ra : Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) {s : State} (hsp : 4 ≤ s.sp.toNat)
    {rd wr : List Region} (hpre : k.pre (view ra s rd wr))
    (hc : Covers (rd ++ wr) ((pushed [ra] s).rd ++ (pushed [ra] s).wr))
    (hw : Covers wr (pushed [ra] s).wr) (hb : ∀ r ∈ wr, (blw4 s).Disjoint r) {Q : State → Prop}
    (hQ : ∀ s' s₂ : State, s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [blw4 s]) s.mem s'.mem → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [blw4 s] s₂.mem s'.mem → k.post (view ra s rd wr) (s₂.withRegions rd wr) → Q s') :
    WP isa (.frame (.push [ra]) c (.pop ra 4)) s Q := by
  refine WP.frameLost (rs := [ra]) (r := ra) rfl (by simpa using hsp) (by simp) ?_
  refine WP.inline (k := k) hv hpre hc hw (fun s₂ hrd₂ hwr₂ ha hf _ hpost ml ul hfl => ?_) hn
  have hfl' : Frame [blw4 s] s₂.mem ml := by rw [e4, hA hsp] at hfl; exact hfl
  have hsp₂ : s₂.sp = s.sp - 4 := ha.2
  -- The slot the pop loads.
  obtain slot : s₂.mem.readW (State.addr s₂.sp) 32 = s.gpr ra := by
    rw [hsp₂, hA hsp, hf.readW (r := blw4 s) (Region.contains_self _ _) (fun r hr => (hb r hr)) (by decide),
      push_slot hsp]
  refine hQ _ s₂ ?_ ?_ ?_ ?_ (fun r hr => ?_) hfl' hpost <;> dsimp only
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂]; exact BitVec.sub_add_cancel _ _
  · refine (((push_frame hsp ra).mono fun r hr => ?_).trans (hf.mono fun r hr => ?_)).trans
      (hfl'.mono fun r hr => ?_)
    · exact List.mem_append_right _ hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ hr
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, slot]
    · rw [popped_gpr hra, ha.1 r hr, pushed_gpr]

/-- Two runs of such code leak the same if its contract holds in both, its
public data agree, and the stack pointers are the same. -/
theorem RelCT.frameInline {ra : Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {rd wr : List Region} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ 4 ≤ s₁.sp.toNat ∧ 4 ≤ s₂.sp.toNat ∧
      k.pre (view ra s₁ rd wr) ∧ k.pre (view ra s₂ rd wr) ∧ k.pub (view ra s₁ rd wr) (view ra s₂ rd wr) ∧
      Covers (rd ++ wr) ((pushed [ra] s₁).rd ++ (pushed [ra] s₁).wr) ∧ Covers wr (pushed [ra] s₁).wr ∧
      Covers (rd ++ wr) ((pushed [ra] s₂).rd ++ (pushed [ra] s₂).wr) ∧ Covers wr (pushed [ra] s₂).wr) :
    RelCT isa P (.frame (.push [ra]) c (.pop ra 4)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h _ _ hp).1) ?_
  refine relCT_inline regionModel (Post := fun s s' => abiPreserved s s' ∧ k.post s s') hv hct
    fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨-, h₁, h₂, p₁, p₂, q, c₁, w₁, c₂, w₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂), Option.some.injEq] at pb
  subst pa pb
  exact ⟨rd, wr, rd, wr, p₁, p₂, q, c₁, w₁, c₂, w₂⟩

/-! ## `update` -/

/-- The regions the code of `update` runs with. -/
abbrev uRd (s : State) (W D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++ [blw4 s]
abbrev uWr (C S : BitVec 32) : List Region := [⟨State.addr C, 8⟩, ⟨State.addr S, 640⟩]

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`, in `r10`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = C
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r10 : s.gpr .r10 = S
  hn : 8 * n < 2 ^ 32
  hsp : 4 ≤ s.sp.toNat
  wc : (⟨State.addr W, 384⟩ : Region).Disjoint ⟨State.addr C, 8⟩
  ws : (⟨State.addr W, 384⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  dc : (⟨State.addr D, 8 * n⟩ : Region).Disjoint ⟨State.addr C, 8⟩
  ds : (⟨State.addr D, 8 * n⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  cs : (⟨State.addr C, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  bw : (blw4 s).Disjoint ⟨State.addr W, 384⟩
  bd : (blw4 s).Disjoint ⟨State.addr D, 8 * n⟩
  bc : (blw4 s).Disjoint ⟨State.addr C, 8⟩
  bs : (blw4 s).Disjoint ⟨State.addr S, 640⟩
  fW : W.toNat + 384 ≤ 2 ^ 32
  fC : C.toNat + 8 ≤ 2 ^ 32
  fD : D.toNat + 8 * n ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 8⟩, ⟨State.addr S, 640⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 8⟩, ⟨State.addr S, 640⟩, blw4 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 8 =
    Spec.Cmac.chain (ciphAt s.mem (State.addr W)) (Spec.Aes.bytesAt s.mem (State.addr C) 8)
      (Spec.Cmac.blocksAt s.mem (State.addr D) 8 n)

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    updateArm.pre (view .r10 s (uRd s W D n) (uWr C S)) := by
  obtain hN := toNat_ofNat32 (n := n) (by have := h.hn; omega_using [this])
  simp only [updateArm, view_arg0 h.hsp, view_argAddr h.hsp, view_gpr, h.r0, h.r1, h.r2, h.r3, h.r10, hN,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.bc.symm, h.bs.symm, h.fW, h.fC, h.fD, h.fS,
    view_spf h.hsp⟩

theorem keep_push {s : State} (hsp : 4 ≤ s.sp.toNat) (ra : Reg) {p : Addr} {k : Nat}
    (hd : (blw4 s).Disjoint ⟨p, k⟩) (hk : k ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (pushed [ra] s).mem p k = Spec.Aes.bytesAt s.mem p k :=
  Proof.Cmac.bytesAt_frame (push_frame hsp ra) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd.symm) hk

theorem upd_wp {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.Stream.Arm.updFrame s (UPost s W C D S n) := by
  obtain hN := toNat_ofNat32 (n := n) (by have := h.hn; omega_using [this])
  refine WP.frameInline (k := updateArm) (fun _ hs => Proof.CmacTripleDes.Arm.update_wp hs) (by lit_decide)
    h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [updateArm, view_gpr, h.r0, h.r1, h.r2, h.r3, hN, State.withRegions_mem] at hpost
  obtain hsch : ciphAt (pushed [.r10] s).mem (State.addr W) = ciphAt s.mem (State.addr W) := by
    simp only [ciphAt]
    rw [scheduleAt_frame (push_frame h.hsp .r10) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h.bw.symm]
  rw [Proof.Cmac.bytesAt_frame hm (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h.bc.symm) (by decide),
    hpost, hsch, keep_push h.hsp .r10 h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep_push h.hsp .r10 (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega_using [hi]

theorem upd_rel {W C D S sp₀ : BitVec 32} {n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S n ∧ UArgs s₂ W C D S n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.CmacTripleDes.Stream.Arm.updFrame fun _ _ => True := by
  refine RelCT.frameInline (k := updateArm) (rd := [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++
    [⟨State.addr sp₀ - 4, 4⟩]) (wr := uWr C S)
    (fun _ hs => Proof.CmacTripleDes.Arm.update_wp hs) Proof.CmacTripleDes.Arm.update_ct fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  obtain r₁ : uRd s₁ W D n = [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [uRd, blw4, e₁]
  obtain r₂ : uRd s₂ W D n = [⟨State.addr W, 384⟩, ⟨State.addr D, 8 * n⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [uRd, blw4, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  obtain c₁ := cov_push (ra := .r10) h₁.hsp h₁.reads h₁.writes
  obtain c₂ := cov_push (ra := .r10) h₂.hsp h₂.reads h₂.writes
  rw [blw4, e₁] at c₁
  rw [blw4, e₂] at c₂
  refine ⟨e₁.trans e₂.symm, h₁.hsp, h₂.hsp, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂, covW_push h₂.writes⟩
  simp only [updateArm, view_sp, view_arg0 h₁.hsp, view_arg0 h₂.hsp, view_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3,
    h₁.r10, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r10, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `finalize` -/

/-- The regions the code of `finalize` runs with. -/
abbrev fRd (s : State) (K P : BitVec 32) (L : Nat) : List Region :=
  [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++ [blw4 s]
abbrev fWr (St S : BitVec 32) : List Region := [⟨State.addr St, 8⟩, ⟨State.addr S, 640⟩]

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`, in `r12`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = St
  r2 : s.gpr .r2 = P
  r3 : s.gpr .r3 = BitVec.ofNat 32 L
  r12 : s.gpr .r12 = S
  len : L ≤ 8
  hsp : 4 ≤ s.sp.toNat
  kst : (⟨State.addr K, 400⟩ : Region).Disjoint ⟨State.addr St, 8⟩
  ks : (⟨State.addr K, 400⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  pst : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr St, 8⟩
  ps : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  sts : (⟨State.addr St, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  bk : (blw4 s).Disjoint ⟨State.addr K, 400⟩
  bp : (blw4 s).Disjoint ⟨State.addr P, L⟩
  bst : (blw4 s).Disjoint ⟨State.addr St, 8⟩
  bs : (blw4 s).Disjoint ⟨State.addr S, 640⟩
  fK : K.toNat + 400 ≤ 2 ^ 32
  fSt : St.toNat + 8 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr St, 8⟩, ⟨State.addr S, 640⟩] s.wr

/-- What a run of `finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr St, 8⟩, ⟨State.addr S, 640⟩, blw4 s] s.mem s'.mem
  out : let ciph := ciphAt s.mem (State.addr K)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (State.addr K + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (State.addr St) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr St) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (State.addr P) L)

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L) :
    finalizeArm.pre (view .r12 s (fRd s K P L) (fWr St S)) := by
  obtain hL := toNat_ofNat32 (n := L) (by have := h.len; omega_using [this])
  simp only [finalizeArm, view_arg0 h.hsp, view_argAddr h.hsp, view_gpr, h.r0, h.r1, h.r2, h.r3, h.r12, hL,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.bst.symm, h.bs.symm, h.fK, h.fSt, h.fP, h.fS,
    view_spf h.hsp, h.len⟩

theorem fin_wp {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.Stream.Arm.finFrame s (FPost s K St P S L) := by
  obtain hL := toNat_ofNat32 (n := L) (by have := h.len; omega_using [this])
  refine WP.frameInline (k := finalizeArm) (fun _ hs => Proof.CmacTripleDes.Arm.finalize_wp hs) (by lit_decide)
    h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bst
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [finalizeArm, view_gpr, h.r0, h.r1, h.r2, h.r3, hL, State.withRegions_mem] at hpost
  obtain hsch : ciphAt (pushed [.r12] s).mem (State.addr K) = ciphAt s.mem (State.addr K) := by
    simp only [ciphAt]
    rw [scheduleAt_frame (push_frame h.hsp .r12) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix (by decide))).symm]
  obtain eK2 := keep_push h.hsp .r12 (p := State.addr K + 384) (k := 16)
    (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 384) (n := 16) (by decide))) (by decide)
  obtain eSt := keep_push h.hsp .r12 h.bst (by decide)
  obtain eP := keep_push h.hsp .r12 h.bp (by have := h.len; omega_using [hL])
  intro _ _ hk msg hmod hne hst
  rw [hsch, eK2, eSt, eP] at hpost
  rw [Proof.Cmac.bytesAt_frame hm (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact h.bst.symm) (by decide)]
  exact hpost hk msg hmod hne hst

theorem fin_rel {K St P S sp₀ : BitVec 32} {L : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → FArgs s₁ K St P S L ∧ FArgs s₂ K St P S L ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa Pr Impl.CmacTripleDes.Stream.Arm.finFrame fun _ _ => True := by
  refine RelCT.frameInline (k := finalizeArm) (rd := [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++
    [⟨State.addr sp₀ - 4, 4⟩]) (wr := fWr St S)
    (fun _ hs => Proof.CmacTripleDes.Arm.finalize_wp hs) Proof.CmacTripleDes.Arm.finalize_ct fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  obtain r₁ : fRd s₁ K P L = [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [fRd, blw4, e₁]
  obtain r₂ : fRd s₂ K P L = [⟨State.addr K, 400⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 4, 4⟩] := by
    rw [fRd, blw4, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  obtain c₁ := cov_push (ra := .r12) h₁.hsp h₁.reads h₁.writes
  obtain c₂ := cov_push (ra := .r12) h₂.hsp h₂.reads h₂.writes
  rw [blw4, e₁] at c₁
  rw [blw4, e₂] at c₂
  refine ⟨e₁.trans e₂.symm, h₁.hsp, h₂.hsp, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂, covW_push h₂.writes⟩
  simp only [finalizeArm, view_sp, view_arg0 h₁.hsp, view_arg0 h₂.hsp, view_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3,
    h₁.r12, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `init` -/

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O`
and the working space `S`. -/
structure IArgs (s : State) (Kp O S : BitVec 32) (KL : Nat) : Prop where
  r0 : s.gpr .r0 = Kp
  r1 : s.gpr .r1 = BitVec.ofNat 32 KL
  r2 : s.gpr .r2 = O
  r3 : s.gpr .r3 = S
  klen : Spec.TripleDes.validKey KL
  ko : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr O, 400⟩
  ks : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  os : (⟨State.addr O, 400⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fO : O.toNat + 400 ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers ([⟨State.addr Kp, KL⟩] ++ [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (State.addr Kp) KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (State.addr O) = k ∧
      Spec.Aes.bytesAt s'.mem (State.addr O + 384) 16 = ks.1 ++ ks.2

theorem IArgs.pre {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL) :
    initArm.pre (s.withRegions [⟨State.addr Kp, KL⟩] [⟨State.addr O, 400⟩, ⟨State.addr S, 640⟩]) := by
  obtain hK := toNat_ofNat32 (n := KL) (by rcases h.klen with h | h <;> omega_using [h])
  simp only [initArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.r0, h.r1, h.r2,
    h.r3, hK]
  exact ⟨trivial, trivial, h.ko, h.ks, h.os, h.fK, h.fO, h.fS, h.klen⟩

theorem init_inline_wp {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.Arm.init s (IPost s Kp O S KL) := by
  obtain hK := toNat_ofNat32 (n := KL) (by rcases h.klen with h | h <;> omega_using [h])
  refine WP.inline (k := initArm) (fun _ hs => Proof.CmacTripleDes.Arm.init_wp hs) h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.2, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [initArm, State.withRegions_gpr, State.withRegions_mem, h.r0, h.r1, h.r2, hK] at hpost
  exact hpost

end VG.Proof.CmacTripleDes.Stream.Arm
