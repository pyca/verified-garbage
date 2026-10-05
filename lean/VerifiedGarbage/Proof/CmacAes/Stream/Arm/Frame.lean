import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Impl.CmacAes.Stream.Arm
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call`. -/
section

section

/-!
# Streaming AES-CMAC on ARMv7: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). `init` calls `vg_cmac_aes_subkeys`, whose
frame uses the 8 bytes below the stack pointer; `absorb` and `finish` push the
two stack arguments of `vg_cmac_aes_update` and `vg_cmac_aes_finalize` below
the stack pointer, and those functions' frames use the 8 bytes below that: so
the 8 or 16 bytes below the stack pointer may not overlap any buffer.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm

/-- `vg_cmac_aes_init(state = r0, key = r1, key_len = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 304⟩
    let key : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2304⟩
    let blw : Region := ⟨State.addr s.sp - 8, 8⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint key ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 304 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2304 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r2).toNat = 16 ∨ (s.gpr .r2).toNat = 24 ∨ (s.gpr .r2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (State.addr (s.gpr .r0))
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) []
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `count`, in `r2:r3` (AAPCS: the low word in `r2`). -/
def countArm (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

/-- `vg_cmac_aes_absorb(state = r0, rounds = r1, count = r2:r3, data = [sp], len = [sp, #4], scratch = [sp, #8])`. -/
def absorbArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 304⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 2304⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let blw : Region := ⟨State.addr s.sp - 16, 16⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint data ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 304 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 2304 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (State.addr (s.gpr .r0)) key msg →
      (s.gpr .r1).toNat = Spec.Aes.rounds (key.length / 4) →
      VG.Proof.CmacAes.Stream.Arm.countArm s = BitVec.ofNat 64 msg.length → msg.length + (stackArg s 1).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (State.addr (s.gpr .r0)) key
        (msg ++ Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2

/-- `vg_cmac_aes_finish(state = r0, rounds = r1, count = r2:r3, out = [sp], scratch = [sp, #4])`. -/
def finishArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 304⟩
    let out : Region := ⟨State.addr (stackArg s 0), 16⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2304⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let blw : Region := ⟨State.addr s.sp - 16, 16⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint out ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 304 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 2304 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (State.addr (s.gpr .r0)) key msg →
      (s.gpr .r1).toNat = Spec.Aes.rounds (key.length / 4) →
      VG.Proof.CmacAes.Stream.Arm.countArm s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (State.addr (stackArg s 0)) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacAes.Stream.Arm

end

/-!
# Streaming AES-CMAC on ARMv7: the calls

A call of each function the streaming functions call (`vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys`, and `vg_cmac_aes_update` and `vg_cmac_aes_finalize` in
the frame that pushes their two stack arguments), from its contract: what it
needs (`…Args`), what it leaves (`…Post`, in terms of the memory before the
call), and that two calls with the same arguments leak the same (`…_rel`).

`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize` have
frames of their own (`WP.callF`), 8 bytes below their stack pointer; with
the pushed stack arguments, a call of the last two uses the 16 bytes below
ours (`blw16`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Arm (addr_sub storeWords_two e8 toNat_rounds)

theorem sub8_8 (p : Addr) : p - 8 - 8 = p - 16 := Offset.sub_sub_ofNat p 8 8

/-- The 16 bytes below the stack pointer. -/
abbrev blw16 (s : State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- The state a function called in a frame pushing `ra` and `rb` runs from,
with the permissions it is given. -/
abbrev view (ra rb : Reg) (s : State) (rd wr : List Region) : State :=
  (pushed [ra, rb] s).callEntry.withRegions rd wr

theorem view_gpr {ra rb : Reg} {s : State} {rd wr : List Region} (r : Reg) (hr : r ∉ linkRegs) :
    (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem view_sp {ra rb : Reg} {s : State} {rd wr : List Region} : (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]

section
variable {s : State} (hsp : 16 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub (k := 8) (by omega)

theorem spA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_trans (by decide) hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [VG.Proof.CmacAes.Stream.Arm.spA hsp]; omega), VG.Proof.CmacAes.Stream.Arm.hA hsp]; rfl

theorem amem (ra rb : Reg) : (pushed [ra, rb] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr ra)).writeW (State.addr s.sp - 8 + 4) (s.gpr rb) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra, rb].length)) [s.gpr ra, s.gpr rb] = _
  rw [e8, storeWords_two, VG.Proof.CmacAes.Stream.Arm.hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    VG.Proof.CmacAes.Stream.Arm.hA4 hsp]

theorem push_frame (ra rb : Reg) : Frame [⟨State.addr s.sp - 8, 8⟩] s.mem (pushed [ra, rb] s).mem := by
  rw [VG.Proof.CmacAes.Stream.Arm.amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

theorem push_slot (ra rb : Reg) : (pushed [ra, rb] s).mem.readW (State.addr s.sp - 8) 32 = s.gpr ra := by
  rw [VG.Proof.CmacAes.Stream.Arm.amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem push_slot1 (ra rb : Reg) : (pushed [ra, rb] s).mem.readW (State.addr s.sp - 8 + 4) 32 = s.gpr rb := by
  rw [VG.Proof.CmacAes.Stream.Arm.amem hsp, Mem.readW_writeW_self32]

/-- The stack arguments, as the callee reads them. -/
theorem view_arg0 {ra rb : Reg} {rd wr : List Region} : stackArg (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr) 0 = s.gpr ra := by
  rw [stackArg, show stackArgAddr (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [VG.Proof.CmacAes.Stream.Arm.view_sp, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, VG.Proof.CmacAes.Stream.Arm.hA hsp],
    State.withRegions_mem, State.callEntry_mem, VG.Proof.CmacAes.Stream.Arm.push_slot hsp]

theorem view_arg1 {ra rb : Reg} {rd wr : List Region} : stackArg (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr) 1 = s.gpr rb := by
  rw [stackArg, show stackArgAddr (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [VG.Proof.CmacAes.Stream.Arm.view_sp]; exact VG.Proof.CmacAes.Stream.Arm.hA4 hsp,
    State.withRegions_mem, State.callEntry_mem, VG.Proof.CmacAes.Stream.Arm.push_slot1 hsp]

theorem view_argAddr {ra rb : Reg} {rd wr : List Region} :
    stackArgAddr (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [VG.Proof.CmacAes.Stream.Arm.view_sp, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
    BitVec.add_zero _, VG.Proof.CmacAes.Stream.Arm.hA hsp]

theorem view_below {ra rb : Reg} {rd wr : List Region} :
    State.addr (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr).sp - 8 = State.addr s.sp - 16 := by
  rw [VG.Proof.CmacAes.Stream.Arm.view_sp, VG.Proof.CmacAes.Stream.Arm.hA hsp, VG.Proof.CmacAes.Stream.Arm.sub8_8]

omit hsp in
theorem slot_sub : Region.Sub ⟨State.addr s.sp - 8, 8⟩ (VG.Proof.CmacAes.Stream.Arm.blw16 s) :=
  Offset.sub_below (State.addr s.sp) (a := 8) (b := 16) (by decide) (by decide)

omit hsp in
theorem lo_sub : Region.Sub ⟨State.addr s.sp - 16, 8⟩ (VG.Proof.CmacAes.Stream.Arm.blw16 s) := Region.sub_prefix (by decide)

end

/-- A call of `c` (with frames using 8 bytes of stack) in the frame that
pushes its two stack arguments `ra` and `rb`, from its contract `k`: it
runs from `view`, and changes memory only within the regions it may write
and the 16 bytes below the stack pointer; the pop loads `ra` back, so it
changes no callee-saved register but `lr`. -/
theorem WP.frameCallF {ra rb : Reg} {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : stackUse c = 8) (hregs : regList [ra, rb] = true) {s : State} (hsp : 16 ≤ s.sp.toNat)
    {rd wr : List Region} (hpre : k.pre (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr))
    (hc : Covers (rd ++ wr) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr))
    (hw : Covers wr (pushed [ra, rb] s).wr) (hb : ∀ r ∈ wr, (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint r) {Q : State → Prop}
    (hQ : ∀ s' s₂ : State, s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [VG.Proof.CmacAes.Stream.Arm.blw16 s]) s.mem s'.mem → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = s₂.mem → k.post (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr) (s₂.withRegions rd wr) → Q s') :
    WP isa (.frame (.push [ra, rb]) (.call name c) (.pop ra 8)) s Q := by
  have hspA := VG.Proof.CmacAes.Stream.Arm.spA hsp
  refine WP.frame (rs := [ra, rb]) (r := ra) hregs (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp) ?_
  refine WP.callF hv hpre hc hw (by rw [hsu, pushed_sp, e8, hspA]; omega)
    fun s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost => ?_
  rw [pushed_sp, e8, hsu] at hf
  rw [pushed_sp, e8] at hsp₂
  have hbA : VG.Arm.belowA (s.sp - 8) 8 = ⟨State.addr s.sp - 16, 8⟩ := by
    simp only [VG.Arm.belowA, VG.Proof.CmacAes.Stream.Arm.hA hsp]; exact congrArg (fun b => (⟨b, 8⟩ : Region)) (VG.Proof.CmacAes.Stream.Arm.sub8_8 _)
  rw [hbA] at hf
  -- The slot the pop loads.
  have slot : s₂.mem.readW (State.addr s₂.sp) 32 = s.gpr ra := by
    rw [hsp₂, VG.Proof.CmacAes.Stream.Arm.hA hsp]
    rw [hf.readW (r := ⟨State.addr s.sp - 8, 4⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ((hb r hr).sub_left (VG.Proof.CmacAes.Stream.Arm.slot_sub (s := s))).sub_left (Region.sub_prefix (by decide))
      · rw [List.mem_singleton] at hr; subst hr
        have := Offset.below_disjoint (State.addr s.sp - 8) (m := 8) (l := 4) (by decide)
        exact (Offset.sub_sub_ofNat (State.addr s.sp) 8 8 ▸ this).symm) (by decide), VG.Proof.CmacAes.Stream.Arm.push_slot hsp]
  refine hQ _ s₂ ?_ ?_ ?_ ?_ (fun r hr hlr => ?_) (popped_mem _ _ _) hpost
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem]
    refine ((VG.Proof.CmacAes.Stream.Arm.push_frame hsp ra rb).sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.CmacAes.Stream.Arm.slot_sub⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.CmacAes.Stream.Arm.lo_sub⟩
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, slot]
    · rw [popped_gpr hra, hcs r hr hlr, pushed_gpr]

/-- Two runs of such a call leak the same if the callee's contract holds
in both, its public data agree, and the stack pointers are the same. -/
theorem RelCT.frameCall {ra rb : Reg} {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hregs : regList [ra, rb] = true) {rd wr : List Region}
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ 8 ≤ s₁.sp.toNat ∧ 8 ≤ s₂.sp.toNat ∧
      k.pre (VG.Proof.CmacAes.Stream.Arm.view ra rb s₁ rd wr) ∧ k.pre (VG.Proof.CmacAes.Stream.Arm.view ra rb s₂ rd wr) ∧
      k.pub (VG.Proof.CmacAes.Stream.Arm.view ra rb s₁ rd wr) (VG.Proof.CmacAes.Stream.Arm.view ra rb s₂ rd wr) ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₁).rd ++ (pushed [ra, rb] s₁).wr) ∧
      Covers wr (pushed [ra, rb] s₁).wr ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₂).rd ++ (pushed [ra, rb] s₂).wr) ∧
      Covers wr (pushed [ra, rb] s₂).wr) :
    RelCT isa P (.frame (.push [ra, rb]) (.call name c) (.pop ra 8)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h _ _ hp).1) ?_
  refine RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨-, h₁, h₂, p₁, p₂, q, c₁, w₁, c₂, w₂⟩ := h _ _ hp
  rw [push_pushed hregs (by simpa using h₁), Option.some.injEq] at pa
  rw [push_pushed hregs (by simpa using h₂), Option.some.injEq] at pb
  subst pa pb
  exact ⟨p₁, p₂, q, c₁, w₁, c₂, w₂⟩


/-- The 8 bytes below a callee's stack pointer, for a call in the frame. -/
theorem view_blw {ra rb : Reg} {s : State} {rd wr : List Region} (hsp : 16 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr).sp - BitVec.ofNat 64 8, 8⟩ (VG.Proof.CmacAes.Stream.Arm.blw16 s) := by
  show Region.Sub ⟨State.addr (VG.Proof.CmacAes.Stream.Arm.view ra rb s rd wr).sp - 8, 8⟩ (VG.Proof.CmacAes.Stream.Arm.blw16 s)
  rw [VG.Proof.CmacAes.Stream.Arm.view_below hsp]; exact VG.Proof.CmacAes.Stream.Arm.lo_sub

/-- The covering of a call's regions, from those of the caller. -/
theorem cov_push {ra rb : Reg} {s : State} (hsp : 16 ≤ s.sp.toNat) {rd₀ wr : List Region}
    (hr : Covers rd₀ (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers ((rd₀ ++ [⟨State.addr s.sp - 8, 8⟩]) ++ wr) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr) := by
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
      rwa [e8, VG.Proof.CmacAes.Stream.Arm.hA hsp]
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

theorem covW_push {ra rb : Reg} {s : State} {wr : List Region} (hw : Covers wr s.wr) :
    Covers wr (pushed [ra, rb] s).wr := by
  intro x n hi
  obtain ⟨r', hr', hc'⟩ := hw x n hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

/-! ## `vg_cmac_aes_update` -/

theorem stackUse_update : stackUse Impl.CmacAes.Arm.update = 8 := by decide +kernel

/-- The regions `vg_cmac_aes_update` is called with. -/
abbrev uRd (s : State) (W D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr s.sp - 8, 8⟩]
abbrev uWr (C S : BitVec 32) : List Region := [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩]

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r9 : s.gpr .r9 = BitVec.ofNat 32 n
  r10 : s.gpr .r10 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 32
  hsp : 16 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  dc : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr W, 240⟩
  bd : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr D, 16 * n⟩
  bc : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr C, 16⟩
  bs : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16) (Spec.Cmac.blocksAt s.mem (State.addr D) 16 n)

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {R n : Nat} (h : VG.Proof.CmacAes.Stream.Arm.UArgs s W C D S R n) :
    Proof.CmacAes.Arm.updateArm.pre (VG.Proof.CmacAes.Stream.Arm.view .r9 .r10 s (VG.Proof.CmacAes.Stream.Arm.uRd s W D n) (VG.Proof.CmacAes.Stream.Arm.uWr C S)) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega)
  have hb := VG.Proof.CmacAes.Stream.Arm.view_blw (ra := .r9) (rb := .r10) (rd := VG.Proof.CmacAes.Stream.Arm.uRd s W D n) (wr := VG.Proof.CmacAes.Stream.Arm.uWr C S) h.hsp
  have hslot : Region.Sub ⟨stackArgAddr (VG.Proof.CmacAes.Stream.Arm.view .r9 .r10 s (VG.Proof.CmacAes.Stream.Arm.uRd s W D n) (VG.Proof.CmacAes.Stream.Arm.uWr C S)) 0, 8⟩ (VG.Proof.CmacAes.Stream.Arm.blw16 s) := by
    rw [VG.Proof.CmacAes.Stream.Arm.view_argAddr h.hsp]; exact VG.Proof.CmacAes.Stream.Arm.slot_sub
  simp only [Proof.CmacAes.Arm.updateArm, VG.Proof.CmacAes.Stream.Arm.view_arg0 h.hsp, VG.Proof.CmacAes.Stream.Arm.view_arg1 h.hsp, VG.Proof.CmacAes.Stream.Arm.view_argAddr h.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r9, h.r10, hR, hN, State.withRegions_rd, State.withRegions_wr]
  rw [VG.Proof.CmacAes.Stream.Arm.view_argAddr h.hsp] at hslot
  have hspv := VG.Proof.CmacAes.Stream.Arm.spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, (h.bc.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm,
    (h.bs.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm, h.bw.sub_left hb, h.bd.sub_left hb, h.bc.sub_left hb, h.bs.sub_left hb,
    h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
  · rw [VG.Proof.CmacAes.Stream.Arm.view_sp, hspv]; omega
  · rw [VG.Proof.CmacAes.Stream.Arm.view_sp, hspv]; have := s.sp.isLt; omega

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : VG.Proof.CmacAes.Stream.Arm.UArgs s W C D S R n) :
    WP isa Impl.CmacAes.Stream.Arm.updCall s (VG.Proof.CmacAes.Stream.Arm.UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.updateArm) (fun _ hs => Proof.CmacAes.Arm.update_wp hs)
    VG.Proof.CmacAes.Stream.Arm.stackUse_update rfl h.hsp h.pre (VG.Proof.CmacAes.Stream.Arm.cov_push h.hsp h.reads h.writes) (VG.Proof.CmacAes.Stream.Arm.covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := VG.Proof.CmacAes.Stream.Arm.push_frame h.hsp .r9 .r10
  have keep : ∀ {p : Addr} {k : Nat}, (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r9, .r10] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.updateArm, Proof.CmacAes.Arm.ciphAt, VG.Proof.CmacAes.Stream.Arm.view_arg0 h.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r9, hR, hN, State.withRegions_mem, State.callEntry_mem] at hpost
  rw [hm, hpost, keep (h.bw.sub_right (Region.sub_prefix hRb)) (by omega), keep h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega

theorem upd_rel {W C D S sp₀ : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.Arm.UArgs s₁ W C D S R n ∧ VG.Proof.CmacAes.Stream.Arm.UArgs s₂ W C D S R n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.CmacAes.Stream.Arm.updCall fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.updateArm) (rd := [⟨State.addr W, 240⟩,
    ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := VG.Proof.CmacAes.Stream.Arm.uWr C S)
    (fun _ hs => Proof.CmacAes.Arm.update_wp hs) Proof.CmacAes.Arm.update_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : VG.Proof.CmacAes.Stream.Arm.uRd s₁ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [VG.Proof.CmacAes.Stream.Arm.uRd, e₁]
  have r₂ : VG.Proof.CmacAes.Stream.Arm.uRd s₂ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [VG.Proof.CmacAes.Stream.Arm.uRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := VG.Proof.CmacAes.Stream.Arm.cov_push (ra := .r9) (rb := .r10) h₁.hsp h₁.reads h₁.writes
  have c₂ := VG.Proof.CmacAes.Stream.Arm.cov_push (ra := .r9) (rb := .r10) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega, by have := h₂.hsp; omega, p₁, p₂, ?_, c₁, VG.Proof.CmacAes.Stream.Arm.covW_push h₁.writes, c₂,
    VG.Proof.CmacAes.Stream.Arm.covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.updateArm, VG.Proof.CmacAes.Stream.Arm.view_sp, VG.Proof.CmacAes.Stream.Arm.view_arg0 h₁.hsp, VG.Proof.CmacAes.Stream.Arm.view_arg1 h₁.hsp, VG.Proof.CmacAes.Stream.Arm.view_arg0 h₂.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_arg1 h₂.hsp, VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide),
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r9, h₁.r10, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r9,
    h₂.r10, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩


/-! ## `vg_cmac_aes_finalize` -/

theorem stackUse_finalize : stackUse Impl.CmacAes.Arm.finalize = 8 := by decide +kernel

/-- The regions `vg_cmac_aes_finalize` is called with. -/
abbrev fRd (s : State) (K P : BitVec 32) (L : Nat) : List Region :=
  [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr s.sp - 8, 8⟩]
abbrev fWr (St S : BitVec 32) : List Region := [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩]

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L R : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = St
  r3 : s.gpr .r3 = P
  r4 : s.gpr .r4 = BitVec.ofNat 32 L
  r5 : s.gpr .r5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  hsp : 16 ≤ s.sp.toNat
  kst : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ks : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  pst : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ps : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  sts : (⟨State.addr St, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bk : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr K, 272⟩
  bp : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr P, L⟩
  bst : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr St, 16⟩
  bs : (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fK : K.toNat + 272 ≤ 2 ^ 32
  fSt : St.toNat + 16 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw16 s] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (State.addr K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (State.addr St) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr St) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (State.addr P) L)

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L R : Nat} (h : VG.Proof.CmacAes.Stream.Arm.FArgs s K St P S L R) :
    Proof.CmacAes.Arm.finalizeArm.pre (VG.Proof.CmacAes.Stream.Arm.view .r4 .r5 s (VG.Proof.CmacAes.Stream.Arm.fRd s K P L) (VG.Proof.CmacAes.Stream.Arm.fWr St S)) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  have hb := VG.Proof.CmacAes.Stream.Arm.view_blw (ra := .r4) (rb := .r5) (rd := VG.Proof.CmacAes.Stream.Arm.fRd s K P L) (wr := VG.Proof.CmacAes.Stream.Arm.fWr St S) h.hsp
  simp only [Proof.CmacAes.Arm.finalizeArm, VG.Proof.CmacAes.Stream.Arm.view_arg0 h.hsp, VG.Proof.CmacAes.Stream.Arm.view_arg1 h.hsp, VG.Proof.CmacAes.Stream.Arm.view_argAddr h.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r4, h.r5, hR, hL, State.withRegions_rd, State.withRegions_wr]
  have hspv := VG.Proof.CmacAes.Stream.Arm.spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, (h.bst.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm,
    (h.bs.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm, h.bk.sub_left hb, h.bp.sub_left hb, h.bst.sub_left hb, h.bs.sub_left hb,
    h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
  · rw [VG.Proof.CmacAes.Stream.Arm.view_sp, hspv]; omega
  · rw [VG.Proof.CmacAes.Stream.Arm.view_sp, hspv]; have := s.sp.isLt; omega

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : VG.Proof.CmacAes.Stream.Arm.FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.Arm.finCall s (VG.Proof.CmacAes.Stream.Arm.FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.finalizeArm) (fun _ hs => Proof.CmacAes.Arm.finalize_wp hs)
    VG.Proof.CmacAes.Stream.Arm.stackUse_finalize rfl h.hsp h.pre (VG.Proof.CmacAes.Stream.Arm.cov_push h.hsp h.reads h.writes) (VG.Proof.CmacAes.Stream.Arm.covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bst
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := VG.Proof.CmacAes.Stream.Arm.push_frame h.hsp .r4 .r5
  have keep : ∀ {p : Addr} {k : Nat}, (VG.Proof.CmacAes.Stream.Arm.blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r4, .r5] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.finalizeArm, Proof.CmacAes.Arm.ciphAt, VG.Proof.CmacAes.Stream.Arm.view_arg0 h.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r4, hR, hL, State.withRegions_mem, State.callEntry_mem] at hpost
  have eK := keep (h.bk.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK2 : Spec.Aes.bytesAt (pushed [.r4, .r5] s).mem (State.addr K + 240) 32 =
      Spec.Aes.bytesAt s.mem (State.addr K + 240) 32 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := keep h.bst (by decide)
  have eP := keep h.bp (by have := h.len; omega)
  intro _ _ hk msg hmod hne hst
  rw [eK, eK2, eSt, eP] at hpost
  rw [hm]
  exact hpost hk msg hmod hne hst

theorem fin_rel {K St P S sp₀ : BitVec 32} {L R : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → VG.Proof.CmacAes.Stream.Arm.FArgs s₁ K St P S L R ∧ VG.Proof.CmacAes.Stream.Arm.FArgs s₂ K St P S L R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa Pr Impl.CmacAes.Stream.Arm.finCall fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.finalizeArm) (rd := [⟨State.addr K, 272⟩,
    ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := VG.Proof.CmacAes.Stream.Arm.fWr St S)
    (fun _ hs => Proof.CmacAes.Arm.finalize_wp hs) Proof.CmacAes.Arm.finalize_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : VG.Proof.CmacAes.Stream.Arm.fRd s₁ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [VG.Proof.CmacAes.Stream.Arm.fRd, e₁]
  have r₂ : VG.Proof.CmacAes.Stream.Arm.fRd s₂ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [VG.Proof.CmacAes.Stream.Arm.fRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := VG.Proof.CmacAes.Stream.Arm.cov_push (ra := .r4) (rb := .r5) h₁.hsp h₁.reads h₁.writes
  have c₂ := VG.Proof.CmacAes.Stream.Arm.cov_push (ra := .r4) (rb := .r5) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega, by have := h₂.hsp; omega, p₁, p₂, ?_, c₁, VG.Proof.CmacAes.Stream.Arm.covW_push h₁.writes, c₂,
    VG.Proof.CmacAes.Stream.Arm.covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.finalizeArm, VG.Proof.CmacAes.Stream.Arm.view_sp, VG.Proof.CmacAes.Stream.Arm.view_arg0 h₁.hsp, VG.Proof.CmacAes.Stream.Arm.view_arg1 h₁.hsp, VG.Proof.CmacAes.Stream.Arm.view_arg0 h₂.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_arg1 h₂.hsp, VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide),
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r4, h₁.r5, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r4,
    h₂.r5, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

theorem stackUse_subkeys : stackUse Impl.CmacAes.Arm.subkeys = 8 := by decide +kernel

theorem cov_app {s : State} {rd wr : List Region} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := by
  intro x n ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact hr x n ⟨r, hr', hc⟩
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hc⟩
    exact ⟨r', List.mem_append_right _ hr'', hc'⟩

/-- The 8 bytes below the stack pointer. -/
abbrev blw8 (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : BitVec 32) (R : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = K
  r3 : s.gpr .r3 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  wk : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr K, 32⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  ks : (⟨State.addr K, 32⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (VG.Proof.CmacAes.Stream.Arm.blw8 s).Disjoint ⟨State.addr W, 240⟩
  bk : (VG.Proof.CmacAes.Stream.Arm.blw8 s).Disjoint ⟨State.addr K, 32⟩
  bs : (VG.Proof.CmacAes.Stream.Arm.blw8 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fK : K.toNat + 32 ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw8 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr K) 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : BitVec 32} {R : Nat} (h : VG.Proof.CmacAes.Stream.Arm.SArgs s W K S R) :
    Proof.CmacAes.Arm.subkeysArm.pre
      (s.callEntry.withRegions [⟨State.addr W, 240⟩] [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.CmacAes.Arm.subkeysArm, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h.r0, h.r1, h.r2, h.r3, hR, State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.bw, h.bk, h.bs, h.fW, h.fK, h.fS, h.hsp, h.rounds⟩

theorem sub_call {s : State} {W K S : BitVec 32} {R : Nat} (h : VG.Proof.CmacAes.Stream.Arm.SArgs s W K S R) :
    WP isa (.call "vg_cmac_aes_subkeys" Impl.CmacAes.Arm.subkeys) s (VG.Proof.CmacAes.Stream.Arm.SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.callF (k := Proof.CmacAes.Arm.subkeysArm) (fun _ hs => Proof.CmacAes.Arm.subkeys_wp hs) h.pre
    (VG.Proof.CmacAes.Stream.Arm.cov_app h.reads h.writes) h.writes (by rw [VG.Proof.CmacAes.Stream.Arm.stackUse_subkeys]; exact h.hsp)
    fun s' hrd hwr hsp hf hcs hpost => ?_
  rw [VG.Proof.CmacAes.Stream.Arm.stackUse_subkeys] at hf
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.CmacAes.Arm.subkeysArm, Proof.CmacAes.Arm.ciphAt, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    h.r0, h.r1, h.r2, hR] at hpost
  exact hpost

theorem sub_rel {W K S sp₀ : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.Arm.SArgs s₁ W K S R ∧ VG.Proof.CmacAes.Stream.Arm.SArgs s₂ W K S R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P (.call "vg_cmac_aes_subkeys" Impl.CmacAes.Arm.subkeys) fun _ _ => True := by
  refine RelCT.call (fun _ hs => Proof.CmacAes.Arm.subkeys_wp hs) Proof.CmacAes.Arm.subkeys_ct
    [⟨State.addr W, 240⟩] [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, VG.Proof.CmacAes.Stream.Arm.cov_app h₁.reads h₁.writes, h₁.writes, VG.Proof.CmacAes.Stream.Arm.cov_app h₂.reads h₂.writes, h₂.writes⟩
  simp only [Proof.CmacAes.Arm.subkeysArm, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : BitVec 32) (KL : Nat) : Prop where
  r0 : s.gpr .r0 = Kp
  r1 : s.gpr .r1 = BitVec.ofNat 32 KL
  r2 : s.gpr .r2 = W
  r3 : s.gpr .r3 = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr W, 240⟩
  ks : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fW : W.toNat + 240 ≤ 2 ^ 32
  fS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr Kp, KL⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure EPost (s : State) (Kp W S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr W) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (State.addr Kp) KL)

theorem toNat_klen {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) : (BitVec.ofNat 32 KL).toNat = KL := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem EArgs.pre {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : VG.Proof.CmacAes.Stream.Arm.EArgs s Kp W S KL) :
    Proof.Aes.expandKeyArm.pre
      (s.callEntry.withRegions [⟨State.addr Kp, KL⟩] [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩]) := by
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h.r0, h.r1, h.r2, h.r3, VG.Proof.CmacAes.Stream.Arm.toNat_klen h.klen, State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.fK, h.fW, h.fS, h.klen⟩

theorem ek_call {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) s (EPost s Kp W S KL) := by
  refine WP.call (k := Proof.Aes.expandKeyArm) Proof.Aes.Arm.expandKey_correct h.pre
    (VG.Proof.CmacAes.Stream.Arm.cov_app h.reads h.writes) h.writes fun s' hrd hwr hsp hf hcs _ hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    h.r0, h.r1, h.r2, VG.Proof.CmacAes.Stream.Arm.toNat_klen h.klen] at hpost
  exact hpost

theorem ek_rel {Kp W S : BitVec 32} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL) :
    RelCT isa P (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) fun _ _ => True := by
  refine RelCT.call Proof.Aes.Arm.expandKey_correct Proof.Aes.Arm.expandKey_ct
    [⟨State.addr Kp, KL⟩] [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, VG.Proof.CmacAes.Stream.Arm.cov_app h₁.reads h₁.writes, h₁.writes, VG.Proof.CmacAes.Stream.Arm.cov_app h₂.reads h₂.writes, h₂.writes⟩
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Common`. -/
section

/-!
# Streaming AES-CMAC on ARMv7: arithmetic and memory

`count` in a register pair (`toNat_append32`, `or_beq_zero`), the number of
bytes held back as the code computes it from the low word of `count`
(`held_lo`), conditions, and bytes written.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm
open VG.Proof.Cmac.Stream (held held_pos held_zero)
open VG.Proof.MdStream.Arm (eval_eq eval_ne ofNat_beq_zero sub_ofNat cmp0)

/-! ## `count` in a register pair -/

theorem toNat_append32 (hi lo : BitVec 32) : (hi ++ lo : BitVec 64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [VG.Proof.CmacAes.Stream.Arm.toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [show (lo ||| hi) - 0 = lo ||| hi from BitVec.sub_zero _]
  by_cases hx0 : x = 0
  · have h1 : lo = 0 := BitVec.eq_of_toNat_eq (by show lo.toNat = 0; omega)
    have h2 : hi = 0 := BitVec.eq_of_toNat_eq (by show hi.toNat = 0; omega)
    simp [h1, h2, hx0]
  · rw [decide_eq_false hx0, beq_eq_false_iff_ne]
    intro h0
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h0
    rw [h1, h2] at e
    rw [BitVec.toNat_zero] at e
    omega

theorem count_eq (s : State) : (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.Arm.countArm s).toNat :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; rfl)

theorem and15 (x : BitVec 32) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero count, as `sub 1; and 15;
add 1` computes it from its low word. -/
theorem held_lo {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) (h0 : x ≠ 0) : ((lo - 1) &&& 15) + 1 = BitVec.ofNat 32 (held x) := by
  have e := congrArg BitVec.toNat h
  rw [VG.Proof.CmacAes.Stream.Arm.toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, VG.Proof.CmacAes.Stream.Arm.and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  have := lo.isLt
  have := hi.isLt
  omega

/-! ## Conditions -/

theorem ne_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k - 0 == 0)) (hk : k < 2 ^ 32) :
    isa.eval .ne s = some (decide (k ≠ 0)) := by
  show VG.Arm.eval .ne s = _
  rw [eval_ne, h, cmp0 hk]
  simp

theorem eq_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k - 0 == 0)) (hk : k < 2 ^ 32) :
    isa.eval .eq s = some (decide (k = 0)) := by
  show VG.Arm.eval .eq s = _
  rw [eval_eq, h, cmp0 hk]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Bytes written -/

section
open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    VG.WriteBytes.writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (VG.WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.CmacAes.Stream.Arm.writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, VG.Proof.CmacAes.Stream.Arm.bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact VG.WriteBytes.writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

end

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.AbsorbBlocks`. -/
section

section

/-!
# Streaming AES-CMAC on ARMv7: copying bytes

`copy` copies the `r1` bytes at `r6` to `r2`, a byte at a time (none if `r1`
is 0), advancing `r6` past them and taking them off `r7`, and changing only
`r1`, `r2`, `r6`, `r7`, `r12` and the flags.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_add wp_sub wp_subs wp_cmp wp_ldrb wp_strb eval_ne
  ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.Arm (byte_rt32)

/-- What `copy` leaves. -/
structure Copied (s : State) (p c : BitVec 32) (L x : Nat) (s' : State) : Prop where
  mem : s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L)
  r6 : s'.gpr .r6 = p + BitVec.ofNat 32 L
  r7 : s'.gpr .r7 = BitVec.ofNat 32 (x - L)
  other : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop, for `L > 0` bytes. -/
theorem copyLoop_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + L ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, L⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩) :
    WP isa (.loop (.block VG.Impl.CmacAes.Stream.Arm.copyBody) .ne) s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = p + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block VG.Impl.CmacAes.Stream.Arm.copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r6 = p + BitVec.ofNat 32 i ∧
      t.gpr .r2 = c + BitVec.ofNat 32 i ∧ t.gpr .r1 = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h6]; exact (BitVec.add_zero p).symm, by rw [h2]; exact (BitVec.add_zero c).symm,
      by rw [h1, Nat.sub_zero], by simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x6, x2, x1, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x6, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x2, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have x1' : t₅.gpr .r1 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r h₁ h₂ h₆ h₁₂ => by
    rw [u₅.other _ h₁, u₄.other _ h₂, u₃.other _ h₆, v₂.gpr, u₁.other _ h₁₂, g r h₁ h₂ h₆ h₁₂]
  have x2' : t₅.gpr .r2 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x6' : t₅.gpr .r6 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, x6', x2', x1', hmem, gg,
      sp', rd', wr'⟩

/-- What copying `L > 0` bytes from `p` to `c` needs. -/
structure CopyOk (s : State) (p c : BitVec 32) (L : Nat) : Prop where
  fp : p.toNat + L ≤ 2 ^ 32
  fc : c.toNat + L ≤ 2 ^ 32
  hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)
  hw : Covers [⟨State.addr c, L⟩] s.wr
  hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩

theorem copy_wp {s : State} {p c : BitVec 32} {L x : Nat} (hLx : L ≤ x) (hx : x < 2 ^ 32)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (ok : 0 < L → VG.Proof.CmacAes.Stream.Arm.CopyOk s p c L) :
    WP isa copy s (VG.Proof.CmacAes.Stream.Arm.Copied s p c L x) := by
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_)
  have g₂ : ∀ r, r ≠ .r7 → s₂.gpr r = s.gpr r := fun r hr => by rw [f₂.gpr, u₁.other _ hr]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (x - L) := by rw [f₂.gpr, u₁.gpr, h7, h1, sub_ofNat hLx]
  rw [show s₁.gpr .r1 = BitVec.ofNat 32 L by rw [u₁.other _ (by decide), h1]] at z₂
  have ev := VG.Proof.CmacAes.Stream.Arm.eq_iff s₂ z₂ (by omega)
  have sp₂ : s₂.sp = s.sp := by rw [f₂.sp, u₁.sp]
  have rd₂ : s₂.rd = s.rd := by rw [f₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [f₂.wr, u₁.wr]
  have m₂ : s₂.mem = s.mem := by rw [f₂.mem, u₁.mem]
  by_cases hL : L = 0
  · subst hL
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₂]; simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil],
      (by rw [g₂ _ (by decide), h6]; exact (BitVec.add_zero p).symm), r7₂, fun r _ _ _ h₇ _ => g₂ r h₇, sp₂, rd₂,
      wr₂⟩
  · obtain ⟨fp, fc, hr, hw, hd⟩ := ok (by omega)
    refine WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h) fun _ => ?_
    refine WP.mono (VG.Proof.CmacAes.Stream.Arm.copyLoop_wp (by omega) (by rw [g₂ _ (by decide), h6]) (by rw [g₂ _ (by decide), h2])
      (by rw [g₂ _ (by decide), h1]) fp fc (by rw [rd₂, wr₂]; exact hr) (by rw [wr₂]; exact hw) hd)
      fun s' ⟨mm, r6, g, sp, rd, wr⟩ => ⟨by rw [mm, m₂], r6, by rw [g _ (by decide) (by decide) (by decide)
        (by decide), r7₂], fun r h₁ h₂ h₆ h₇ h₁₂ => by rw [g r h₁ h₂ h₆ h₁₂, g₂ r h₇], by rw [sp, sp₂],
        by rw [rd, rd₂], by rw [wr, wr₂]⟩

end VG.Proof.CmacAes.Stream.Arm

end

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (16 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_orr
  wp_cmp cmp0 sub_ofNat ofNat_shr)
open VG.Proof.Cmac.Stream (held held_le held_zero)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - VG.Proof.CmacAes.Stream.Arm.fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.Arm.leftOf c L = 0 then 0 else 1

/-- The number of whole blocks of `x` bytes but its last 1 to 16 (none for none). -/
def nbx (x : Nat) : Nat := if x = 0 then 0 else (x - 1) / 16

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := VG.Proof.CmacAes.Stream.Arm.nbx (VG.Proof.CmacAes.Stream.Arm.leftOf c L)

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := VG.Proof.CmacAes.Stream.Arm.leftOf c L - 16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L

theorem f_le (c L : Nat) : VG.Proof.CmacAes.Stream.Arm.fOf c L ≤ L ∧ VG.Proof.CmacAes.Stream.Arm.fOf c L + held c ≤ 16 := by
  have := held_le c; unfold VG.Proof.CmacAes.Stream.Arm.fOf; omega

theorem nb_le (c L : Nat) : VG.Proof.CmacAes.Stream.Arm.fOf c L + 16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L + VG.Proof.CmacAes.Stream.Arm.restOf c L = L := by
  have := VG.Proof.CmacAes.Stream.Arm.f_le c L; unfold VG.Proof.CmacAes.Stream.Arm.restOf VG.Proof.CmacAes.Stream.Arm.nbOf VG.Proof.CmacAes.Stream.Arm.nbx VG.Proof.CmacAes.Stream.Arm.leftOf; split <;> omega

theorem rest_le (c L : Nat) : VG.Proof.CmacAes.Stream.Arm.restOf c L ≤ 16 := by
  unfold VG.Proof.CmacAes.Stream.Arm.restOf VG.Proof.CmacAes.Stream.Arm.nbOf VG.Proof.CmacAes.Stream.Arm.nbx VG.Proof.CmacAes.Stream.Arm.leftOf; split <;> omega

/-! ## Arithmetic on registers -/

theorem ite_neg' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬p) : (if p then a else b) = b := by
  simp [h]

theorem ite_pos' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

theorem shl4 (n : Nat) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem shr4 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 4 = BitVec.ofNat 32 (a / 16) := ofNat_shr h

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64)
    (hcnt : (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .r0 = BitVec.ofNat 32 (held c) ∧
      (∀ r, r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_orr (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r0 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [f₅.gpr, u₄.other _ b, u₃.other _ a, u₂.other _ a, u₁.other _ a]
  have ev : isa.eval .eq s₅ = some (decide (c = 0)) := by
    show VG.Arm.eval .eq s₅ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, z₅, u₄.gpr]
    simp (disch := decide) only [u₃.other, u₂.other, u₁.other]
    exact congrArg some (VG.Proof.CmacAes.Stream.Arm.or_beq_zero hcnt hc)
  have r0 : s₅.gpr .r0 = ((s.gpr .r2 - 1) &&& 15) + 1 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  have m : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have sp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have rd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_)
      (fun h => by cases h)
    exact ⟨by rw [u.gpr, held_zero]; rfl, fun r a b => by rw [u.other _ a, g r a b], by rw [u.mem, m],
      by rw [u.sp, sp], by rw [u.rd, rd], by rw [u.wr, wr]⟩
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    exact ⟨by rw [r0]; exact VG.Proof.CmacAes.Stream.Arm.held_lo hcnt hc h0, g, m, sp, rd, wr⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : BitVec 32} {h L : Nat} (hh : h ≤ 16) (hL : L < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 h) (h7 : s.gpr .r7 = BitVec.ofNat 32 L) (h4 : s.gpr .r4 = St) :
    WP isa fill s fun s' => s'.gpr .r1 = BitVec.ofNat 32 (min L (16 - h)) ∧
      s'.gpr .r2 = St + BitVec.ofNat 32 (288 + h) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have g₄ : ∀ r, r ≠ .r1 → r ≠ .r12 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [f₄.gpr, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (16 - h) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h0]; exact sub_ofNat hh
  have z : s₄.z = (BitVec.ofNat 32 (L / 16) - 0 == 0) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h7, VG.Proof.CmacAes.Stream.Arm.shr4 hL]
  have ev := VG.Proof.CmacAes.Stream.Arm.eq_iff s₄ z (by omega)
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .r1 = BitVec.ofNat 32 (min L (16 - h)) ∧
    (∀ r, r ≠ .r1 → r ≠ .r12 → s₅.gpr r = s.gpr r) ∧ s₅.mem = s.mem ∧ s₅.sp = s.sp ∧ s₅.rd = s.rd ∧
      s₅.wr = s.wr) ?_ ?_)
  · refine WP.mono (Q := fun (s₅ : State) => s₅.gpr .r1 = BitVec.ofNat 32 (min L (16 - h)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r12 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.sp = s₄.sp ∧ s₅.rd = s₄.rd ∧
        s₅.wr = s₄.wr) ?_ fun s₅ ⟨r1, g, m, sp, rd, wr⟩ => ⟨r1, fun r a b => by rw [g r a b, g₄ r a b],
          by rw [m, f₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [sp, f₄.sp, u₃.sp, u₂.sp, u₁.sp],
          by rw [rd, f₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [wr, f₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    by_cases hl : L / 16 = 0
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.seq (wp_add (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_cmp (op2_imm (by decide)) fun t₃ e₃ y₃ => WP.block_nil ?_)
      have zz : t₃.z = (BitVec.ofNat 32 ((L + h) / 16) - 0 == 0) := by
        rw [y₃, v₂.gpr, v₁.gpr, g₄ .r7 (by decide) (by decide), g₄ .r0 (by decide) (by decide), h7, h0,
          ← BitVec.ofNat_add, VG.Proof.CmacAes.Stream.Arm.shr4 (by omega)]
      have ev' := VG.Proof.CmacAes.Stream.Arm.eq_iff t₃ zz (by omega)
      have gt : ∀ r, r ≠ .r12 → t₃.gpr r = s₄.gpr r := fun r a => by rw [e₃.gpr, v₂.other _ a, v₁.other _ a]
      have mt : t₃.mem = s₄.mem := by rw [e₃.mem, v₂.mem, v₁.mem]
      have spt : t₃.sp = s₄.sp := by rw [e₃.sp, v₂.sp, v₁.sp]
      have rdt : t₃.rd = s₄.rd := by rw [e₃.rd, v₂.rd, v₁.rd]
      have wrt : t₃.wr = s₄.wr := by rw [e₃.wr, v₂.wr, v₁.wr]
      by_cases hl' : (L + h) / 16 = 0
      · refine WP.ite true (by rw [ev']; simp [hl']) (fun _ => wp_mov (op2_reg _ _) fun t₄ v₄ =>
          WP.block_nil ?_) (fun h => by cases h)
        refine ⟨by rw [v₄.gpr, gt _ (by decide), g₄ _ (by decide) (by decide), h7, Nat.min_eq_left (by omega)],
          fun r a b => by rw [v₄.other _ a, gt _ b], by rw [v₄.mem, mt], by rw [v₄.sp, spt], by rw [v₄.rd, rdt],
          by rw [v₄.wr, wrt]⟩
      · refine WP.ite false (by rw [ev']; simp [hl']) (fun h => by cases h) fun _ => WP.block_nil ?_
        exact ⟨by rw [gt _ (by decide), r1₄, Nat.min_eq_right (by omega)], fun r _ b => gt r b, mt, spt, rdt,
          wrt⟩
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨by rw [r1₄, Nat.min_eq_right (by omega)], fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · intro s₅ ⟨r1, g, m, sp, rd, wr⟩
    refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_add (op2_imm (by decide)) fun t₂ v₂ => WP.block_nil ?_
    refine ⟨by rw [v₂.other _ (by decide), v₁.other _ (by decide), r1], ?_,
      fun r a b c => by rw [v₂.other _ b, v₁.other _ b, g r a c], by rw [v₂.mem, v₁.mem, m],
      by rw [v₂.sp, v₁.sp, sp], by rw [v₂.rd, v₁.rd, rd], by rw [v₂.wr, v₁.wr, wr]⟩
    rw [v₂.gpr, v₁.gpr, g _ (by decide) (by decide), g _ (by decide) (by decide), h4, h0, BitVec.add_assoc,
      show (288 : BitVec 32) = BitVec.ofNat 32 288 from rfl, ← BitVec.ofNat_add, Nat.add_comm]

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St : BitVec 32} {x : Nat} (hx : x < 2 ^ 32) (h7 : s.gpr .r7 = BitVec.ofNat 32 x)
    (h4 : s.gpr .r4 = St) :
    WP isa chain1 s fun s' => s'.gpr .r9 = BitVec.ofNat 32 (if x = 0 then 0 else 1) ∧ s'.gpr .r0 = St ∧
      s'.gpr .r1 = s.gpr .r5 ∧ s'.gpr .r2 = St + BitVec.ofNat 32 272 ∧ s'.gpr .r3 = St + BitVec.ofNat 32 288 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have ev := VG.Proof.CmacAes.Stream.Arm.eq_iff s₂ (k := x) (by rw [z₂, u₁.other _ (by decide), h7]) hx
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r9 = BitVec.ofNat 32 (if x = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r9 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.sp = s.sp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_ ?_)
  · have g₂ : ∀ r, r ≠ .r9 → s₂.gpr r = s.gpr r := fun r a => by rw [f₂.gpr, u₁.other _ a]
    by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [f₂.gpr, u₁.gpr, h0]; rfl, g₂, by rw [f₂.mem, u₁.mem], by rw [f₂.sp, u₁.sp],
        by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ =>
        wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
      exact ⟨by rw [u.gpr, VG.Proof.CmacAes.Stream.Arm.ite_neg' h0]; rfl, fun r a => by rw [u.other _ a, g₂ r a],
        by rw [u.mem, f₂.mem, u₁.mem], by rw [u.sp, f₂.sp, u₁.sp], by rw [u.rd, f₂.rd, u₁.rd],
        by rw [u.wr, f₂.wr, u₁.wr]⟩
  · intro s₃ ⟨r9, g, m, sp, rd, wr⟩
    refine wp_mov (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_reg _ _) fun t₂ v₂ => wp_add (op2_imm (by decide))
      fun t₃ v₃ => wp_add (op2_imm (by decide)) fun t₄ v₄ => WP.block_nil ?_
    refine ⟨by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.other, r9],
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.gpr, g, h4],
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.gpr, v₁.other, g],
      by simp (disch := decide) only [v₄.other, v₃.gpr, v₂.other, v₁.other, g, h4]; rfl,
      by simp (disch := decide) only [v₄.gpr, v₃.other, v₂.other, v₁.other, g, h4]; rfl,
      fun r a b c d e => by rw [v₄.other _ d, v₃.other _ c, v₂.other _ b, v₁.other _ a, g r e],
      by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, m], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp],
      by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr]⟩

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {St Dd : BitVec 32} {x : Nat} (hx : x < 2 ^ 32) (h7 : s.gpr .r7 = BitVec.ofNat 32 x)
    (h4 : s.gpr .r4 = St) (h6 : s.gpr .r6 = Dd) :
    WP isa chain2 s fun s' => s'.gpr .r9 = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.nbx x) ∧
      s'.gpr .r8 = BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbx x) ∧ s'.gpr .r3 = (if x = 0 then St else Dd) ∧
      s'.gpr .r0 = St ∧ s'.gpr .r1 = s.gpr .r5 ∧ s'.gpr .r2 = St + BitVec.ofNat 32 272 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have ev := VG.Proof.CmacAes.Stream.Arm.eq_iff s₁ (k := x) (by rw [z₁, h7]) hx
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r9 = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.nbx x) ∧
    s₂.gpr .r8 = BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbx x) ∧ s₂.gpr .r3 = (if x = 0 then St else Dd) ∧
    (∀ r, r ≠ .r3 → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr) ?_ ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => wp_mov (op2_imm (by decide)) fun t₁ v₁ =>
        wp_mov (op2_imm (by decide)) fun t₂ v₂ => wp_mov (op2_reg _ _) fun t₃ v₃ => WP.block_nil ?_)
        (fun h => by cases h)
      refine ⟨by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, VG.Proof.CmacAes.Stream.Arm.nbx, VG.Proof.CmacAes.Stream.Arm.ite_pos' h0]; rfl,
        by rw [v₃.other _ (by decide), v₂.gpr, VG.Proof.CmacAes.Stream.Arm.nbx, VG.Proof.CmacAes.Stream.Arm.ite_pos' h0]; rfl,
        by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), f₁.gpr, h4, VG.Proof.CmacAes.Stream.Arm.ite_pos' h0],
        fun r a b c => by rw [v₃.other _ a, v₂.other _ b, v₁.other _ c, f₁.gpr],
        by rw [v₃.mem, v₂.mem, v₁.mem, f₁.mem], by rw [v₃.sp, v₂.sp, v₁.sp, f₁.sp],
        by rw [v₃.rd, v₂.rd, v₁.rd, f₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr, f₁.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ =>
        wp_sub (op2_imm (by decide)) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_mov (op2_lsl (by decide)) fun t₃ v₃ => wp_mov (op2_reg _ _) fun t₄ v₄ => WP.block_nil ?_
      have e9 : t₂.gpr .r9 = BitVec.ofNat 32 ((x - 1) / 16) := by
        rw [v₂.gpr, v₁.gpr, f₁.gpr, h7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega),
          VG.Proof.CmacAes.Stream.Arm.shr4 (by omega)]
      refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), e9, VG.Proof.CmacAes.Stream.Arm.nbx, VG.Proof.CmacAes.Stream.Arm.ite_neg' h0],
        by rw [v₄.other _ (by decide), v₃.gpr, e9, VG.Proof.CmacAes.Stream.Arm.shl4, VG.Proof.CmacAes.Stream.Arm.nbx, VG.Proof.CmacAes.Stream.Arm.ite_neg' h0],
        by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), f₁.gpr, h6,
          VG.Proof.CmacAes.Stream.Arm.ite_neg' h0],
        fun r a b c => by rw [v₄.other _ a, v₃.other _ b, v₂.other _ c, v₁.other _ c, f₁.gpr],
        by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, f₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, f₁.sp],
        by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, f₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, f₁.wr]⟩
  · intro s₂ ⟨r9, r8, r3, g, m, sp, rd, wr⟩
    refine wp_mov (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_reg _ _) fun t₂ v₂ => wp_add (op2_imm (by decide))
      fun t₃ v₃ => WP.block_nil ?_
    refine ⟨by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r9],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r8],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r3],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.gpr, g, h4],
      by simp (disch := decide) only [v₃.other, v₂.gpr, v₁.other, g],
      by simp (disch := decide) only [v₃.gpr, v₂.other, v₁.other, g, h4]; rfl,
      fun r a b c d e f => by rw [v₃.other _ c, v₂.other _ b, v₁.other _ a, g r d e f],
      by rw [v₃.mem, v₂.mem, v₁.mem, m], by rw [v₃.sp, v₂.sp, v₁.sp, sp],
      by rw [v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₃.wr, v₂.wr, v₁.wr, wr]⟩

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {St P : BitVec 32} {x n : Nat} (hn : 16 * n ≤ x)
    (h6 : s.gpr .r6 = P) (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (h8 : s.gpr .r8 = BitVec.ofNat 32 (16 * n))
    (h4 : s.gpr .r4 = St) :
    WP isa (.block rest) s fun s' => s'.gpr .r6 = P + BitVec.ofNat 32 (16 * n) ∧
      s'.gpr .r7 = BitVec.ofNat 32 (x - 16 * n) ∧ s'.gpr .r1 = BitVec.ofNat 32 (x - 16 * n) ∧
      s'.gpr .r2 = St + BitVec.ofNat 32 288 ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_sub (op2_reg _ _) fun t₂ v₂ => wp_mov (op2_reg _ _) fun t₃ v₃ =>
    wp_add (op2_imm (by decide)) fun t₄ v₄ => WP.block_nil ?_
  have r7 : t₂.gpr .r7 = BitVec.ofNat 32 (x - 16 * n) := by
    rw [v₂.gpr, v₁.other _ (by decide), v₁.other _ (by decide), h7, h8, sub_ofNat hn]
  refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, h6, h8],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), r7], by rw [v₄.other _ (by decide), v₃.gpr, r7],
    by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), h4]; rfl,
    fun r a b c d => by rw [v₄.other _ b, v₃.other _ a, v₂.other _ d, v₁.other _ c],
    by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp],
    by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]⟩

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Absorb`. -/
section

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_mov wp_ldrSp saveMem saveList_ok saveMem_frame
  readW_writeW_save)
open VG.Proof.CmacAes.Arm (saveMem_congr)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : BitVec 32) (L R : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = D
  a1 : (stackArg s₀ 1).toNat = L
  a2 : stackArg s₀ 2 = S
  r1 : (s₀.gpr .r1).toNat = R
  rd : s₀.rd = [⟨State.addr D, L⟩, ⟨stackArgAddr s₀ 0, 12⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩]
  st_d : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr D, L⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  d_s : (⟨State.addr D, L⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  a_st : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr St, 304⟩
  a_s : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr St, 304⟩
  b_d : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr D, L⟩
  b_s : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fD : D.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 12 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbArm.pre s₀) :
    VG.Proof.CmacAes.Stream.Arm.APre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩

section
variable {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 32 := by rw [← hp.a1]; exact BitVec.isLt _

theorem APre.a1' : stackArg s₀ 1 = BitVec.ofNat 32 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.a1, VG.Proof.CmacAes.Stream.Arm.toNat_ofNat32 hp.lt])

theorem APre.r1' : s₀.gpr .r1 = BitVec.ofNat 32 R :=
  BitVec.eq_of_toNat_eq (by rw [hp.r1, VG.Proof.CmacAes.Stream.Arm.toNat_ofNat32 (by rcases hp.rounds with h | h | h <;> omega)])

theorem APre.argAddr {k : Nat} (hk : k < 3) : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.spf
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem APre.arg_sub {k : Nat} (hk : k < 3) : Region.Sub ⟨stackArgAddr s₀ k, 4⟩ ⟨stackArgAddr s₀ 0, 12⟩ := by
  rw [hp.argAddr hk]; exact Offset.sub_base _ (by omega)

theorem APre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨⟨stackArgAddr s₀ 0, 12⟩, by rw [hp.rd]; simp, ?_⟩
  rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega) (by omega)

/-- Offsets in the state. -/
theorem APre.aS {k : Nat} (hk : k < 304) : State.addr (St + BitVec.ofNat 32 k) = State.addr St + BitVec.ofNat 64 k :=
  addr_add (by have := hp.fSt; omega)

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) :
    Covers [⟨State.addr St + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr St, 304⟩, by simp, d, rfl, h⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) :
    Covers [⟨State.addr S + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr S, 2304⟩, by simp, d, rfl, h⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) :
    Covers [⟨State.addr D + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, L⟩, by simp, d, rfl, h⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : BitVec 32} {n : Nat} (hr0 : s.gpr .r0 = St) (hr1 : s.gpr .r1 = s₀.gpr .r1)
    (hr2 : s.gpr .r2 = St + BitVec.ofNat 32 272) (hr3 : s.gpr .r3 = Dd) (hr9 : s.gpr .r9 = BitVec.ofNat 32 n)
    (hr10 : s.gpr .r10 = S) (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hn : 16 * n < 2 ^ 32)
    (hdc : (⟨State.addr Dd, 16 * n⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨State.addr Dd, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2304⟩)
    (hbd : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr Dd, 16 * n⟩) (hfD : Dd.toNat + 16 * n ≤ 2 ^ 32)
    (hcov : Covers [⟨State.addr Dd, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    VG.Proof.CmacAes.Stream.Arm.UArgs s St (St + BitVec.ofNat 32 272) Dd S R n := by
  have hw := hp.fSt
  have a272 := hp.aS (k := 272) (by decide)
  have c272 : Region.Sub ⟨State.addr St + BitVec.ofNat 64 272, 16⟩ ⟨State.addr St, 304⟩ :=
    Offset.sub_base _ (by decide)
  have hb : VG.Proof.CmacAes.Stream.Arm.blw16 s = VG.Proof.CmacAes.Stream.Arm.blw16 s₀ := by rw [VG.Proof.CmacAes.Stream.Arm.blw16, hsp]
  exact
  { r0 := hr0, r2 := hr2, r3 := hr3, r9 := hr9, r10 := hr10, rounds := hp.rounds, hn := hn
    r1 := by rw [hr1]; exact hp.r1'
    hsp := by rw [hsp]; exact hp.sp
    wc := by rw [a272]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [a272]; exact hdc
    ds := hds.sub_right (Region.sub_prefix (by decide))
    cs := by rw [a272]; exact (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    bw := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bd := by rw [hb]; exact hbd
    bc := by rw [hb, a272]; exact hp.b_st.sub_right c272
    bs := by rw [hb]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fC := by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega
    fD := hfD
    fS := by have := hp.fS; omega
    reads := by
      rw [hrd, hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Covers.right (hp.inSt (d := 0) (n := 240) (by decide)) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩
      · exact hcov a k ⟨_, List.mem_singleton_self _, hc⟩
    writes := by
      rw [hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a272] at hc; exact hp.inSt (d := 272) (n := 16) (by decide) a k ⟨_, List.mem_singleton_self _, hc⟩
      · exact hp.inS (d := 0) (n := 2176) (by decide) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩ }

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2208 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem save_eq : save = .ldrSp .r12 8 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    [mov .r4 .r0, mov .r5 .r1, .ldrSp .r6 0, .ldrSp .r7 4, mov .r10 .r12]) := rfl

/-- The memory after saving the registers. -/
def aMem (s₀ : State) (S : BitVec 32) : Mem := VG.Arm.Spill.saveMem s₀.mem (State.addr S) s₀.gpr saved

theorem saved_slots : Spill.Slots 2176 2208 saved := by decide

theorem aMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr S) s₀.gpr s₀.mem saved VG.Proof.CmacAes.Stream.Arm.saved_slots (r, d) h

theorem aMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

/-- What the saves leave. -/
structure ASave (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r2 : s.gpr .r2 = s₀.gpr .r2
  r3 : s.gpr .r3 = s₀.gpr .r3
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 32 L
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = VG.Proof.CmacAes.Stream.Arm.aMem s₀ S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.APre s₀ St D S L R) :
    WP isa (.block save) s₀ (VG.Proof.CmacAes.Stream.Arm.ASave s₀ St D S L) := by
  have hS := hp.fS
  rw [VG.Proof.CmacAes.Stream.Arm.save_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S := by rw [u₁.gpr]; exact hp.a2
  refine VG.Arm.Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := VG.Proof.CmacAes.Stream.Arm.saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Stream.Arm.aMem s₀ S := by
    rw [m₂, u₁.mem, h12, VG.Proof.CmacAes.Stream.Arm.aMem]
    exact VG.Arm.Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (VG.Proof.CmacAes.Stream.Arm.saved_ne_r12 p hp')
  have arg (k : Nat) (hk : k < 3) : (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k :=
    (VG.Proof.CmacAes.Stream.Arm.aMem_frame s₀ S).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.sub_left (hp.arg_sub hk)) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have mm : ∀ {t : State}, t.mem = s₂.mem → t.mem = VG.Proof.CmacAes.Stream.Arm.aMem s₀ S := fun h => h.trans hm₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other, hp.r0]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, hm₂, arg 0 (by decide), hp.a0]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂, arg 1 (by decide), hp.a1']
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, h12]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : BitVec 32) (c L : Nat) : Mem :=
  VG.WriteBytes.writeBytes (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr (St + BitVec.ofNat 32 (288 + held c)))
    (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr D) (VG.Proof.CmacAes.Stream.Arm.fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : BitVec 32) (L R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.Arm.UArgs s St (St + BitVec.ofNat 32 272) (St + BitVec.ofNat 32 288) S R (VG.Proof.CmacAes.Stream.Arm.b1Of (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = VG.Proof.CmacAes.Stream.Arm.m4 s₀ St D S (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.APre s₀ St D S L R) :
    WP isa absorbPre s₀ (VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀ St D S L R) := by
  generalize hc : (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hL := hp.lt
  have hw := hp.fSt
  have hD := hp.fD
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.Arm.f_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.save_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.held_wp (c := c) hcl (by rw [h₁.r3, h₁.r2, VG.Proof.CmacAes.Stream.Arm.count_eq, hc]))
    fun s₂ ⟨r0₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.fill_wp (St := St) (held_le c) hL r0₂ (by rw [g₂ _ (by decide) (by decide), h₁.r7])
    (by rw [g₂ _ (by decide) (by decide), h₁.r4])) fun s₃ ⟨r1₃, r2₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c d, g₂ r a d]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.copy_wp (p := D) (c := St + BitVec.ofNat 32 (288 + held c)) (L := VG.Proof.CmacAes.Stream.Arm.fOf c L) (x := L)
    hfL hL (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r6]) r2₃ (by rw [r1₃]; rfl)
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r7]) fun hpos => ?_) fun s₄ h₄ => ?_)
  · have hlt : 288 + held c < 304 := by unfold VG.Proof.CmacAes.Stream.Arm.fOf at hpos; omega
    have aDst' : State.addr (St + BitVec.ofNat 32 (288 + held c)) = State.addr St + BitVec.ofNat 64 (288 + held c) :=
      hp.aS hlt
    exact
    { fp := by omega
      fc := by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega
      hr := by
        rw [rd₃', wr₃']
        have := hp.inD (d := 0) (n := VG.Proof.CmacAes.Stream.Arm.fOf c L) (by omega)
        rwa [BitVec.add_zero] at this
      hw := by rw [wr₃', aDst']; exact hp.inSt (by omega)
      hd := by
        rw [aDst']
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Region.sub_prefix hfL) }
  have g' (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) (e : r ≠ .r6) (f : r ≠ .r7) :
      s₄.gpr r = s₁.gpr r := by rw [h₄.other r b c e f d, g r a b c d]
  refine WP.mono (VG.Proof.CmacAes.Stream.Arm.chain1_wp (x := VG.Proof.CmacAes.Stream.Arm.leftOf c L) (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf; omega) (by rw [h₄.r7]; rfl)
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4])) fun s₅ h₅ => ?_
  obtain ⟨r9₅, r0₅, r1₅, r2₅, r3₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (e : r ≠ .r9) (f : r ≠ .r12) (i : r ≠ .r6)
      (j : r ≠ .r7) : s₅.gpr r = s₁.gpr r := by rw [g₅ r a b c d e, g' r a b c f i j]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  have hsp : s₅.sp = s₀.sp := by rw [sp₅, h₄.sp, sp₃, sp₂, h₁.sp]
  have hb1 : 16 * VG.Proof.CmacAes.Stream.Arm.b1Of c L ≤ 16 := by unfold VG.Proof.CmacAes.Stream.Arm.b1Of; split <;> omega
  have a288 := hp.aS (k := 288) (by decide)
  have c288 : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 288), 16 * VG.Proof.CmacAes.Stream.Arm.b1Of c L⟩ ⟨State.addr St, 304⟩ := by
    rw [a288]; exact Offset.sub_base _ (by omega)
  subst hc
  refine ⟨hp.uargs (Dd := St + BitVec.ofNat 32 288) r0₅ (by rw [r1₅, h₄.other _ (by decide) (by decide) (by decide)
      (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide), h₁.r5]) r2₅ r3₅
      (by rw [r9₅, VG.Proof.CmacAes.Stream.Arm.b1Of, VG.Proof.CmacAes.Stream.Arm.leftOf]) (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                                                                (by decide) (by decide), h₁.r10]) hsp hrd hwr (by omega)
      (by rw [a288]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288))
      (hp.b_st.sub_right c288) (by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega)
      (Covers.right (by rw [a288]; exact hp.inSt (by omega))), ?_, ?_, ?_, ?_, ?_, hsp, ?_, ?_, hrd, hwr⟩
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4]
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r5]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₄.r6]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₄.r7]; rfl
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r10]
  · intro r hr a b c d e f
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k r this.1 this.2.1 this.2.2.1 this.2.2.2.1 e this.2.2.2.2 c d, h₁.keep r hr a b c d f]
  · rw [m₅, h₄.mem, m₃, m₂, h₁.mem, VG.Proof.CmacAes.Stream.Arm.m4]

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.AbsorbCorrect`. -/
section

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd wp_ldr)
open VG.Proof.Cmac.Stream (held held_le)

theorem disjoint_zero (p : Addr) (r : Region) : (⟨p, 0⟩ : Region).Disjoint r := fun a h _ => by
  simp only [Region.Contains] at h; omega

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

/-- The data of the second call: the state if no data is left. -/
abbrev d2Of (St D : BitVec 32) (c L : Nat) : BitVec 32 :=
  if VG.Proof.CmacAes.Stream.Arm.leftOf c L = 0 then St else D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf c L)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {s₀ s : State} {St D S : BitVec 32} {L R : Nat} (h : VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀ St D S L R s) :
    WP isa updCall s (VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀ St D S L) :=
  WP.mono (VG.Proof.CmacAes.Stream.Arm.upd_call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r4],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r5],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r6],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r7],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r10],
      by rw [h₆.saved _ (by simp [preserved]) (by decide), h.keep _ (by simp [preserved]) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)], by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd],
      by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : BitVec 32) (L R : Nat) (m : Mem) (s : State) : Prop where
  mem : s.mem = m
  args : VG.Proof.CmacAes.Stream.Arm.UArgs s St (St + BitVec.ofNat 32 272) (VG.Proof.CmacAes.Stream.Arm.d2Of St D (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) S R (VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem chain2_mid {s₀ s : State} {St D S : BitVec 32} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.APre s₀ St D S L R)
    (h : VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀ St D S L s) : WP isa chain2 s (VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀ St D S L R s.mem) := by
  have hL := hp.lt
  have hD := hp.fD
  have hw := hp.fSt
  have ⟨hfL, _⟩ := VG.Proof.CmacAes.Stream.Arm.f_le (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L
  have hsum := VG.Proof.CmacAes.Stream.Arm.nb_le (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L
  refine WP.mono (VG.Proof.CmacAes.Stream.Arm.chain2_wp (x := VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf; omega) h.r7 h.r4 h.r6) fun s₇ h₇ => ?_
  obtain ⟨r9₇, r8₇, r3₇, r0₇, r1₇, r2₇, g₇, m₇, sp₇, rd₇, wr₇⟩ := h₇
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (e : r ≠ .r8) (f : r ≠ .r9) :
      s₇.gpr r = s.gpr r := g₇ r a b c d e f
  have hsp : s₇.sp = s₀.sp := by rw [sp₇, h.sp]
  have hrd : s₇.rd = s₀.rd := by rw [rd₇, h.rd]
  have hwr : s₇.wr = s₀.wr := by rw [wr₇, h.wr]
  refine ⟨m₇, ?_, by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r4],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7], r8₇,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r11], hsp, hrd, hwr⟩
  have common := @APre.uargs _ _ _ _ _ _ hp s₇ (VG.Proof.CmacAes.Stream.Arm.d2Of St D (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) (VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) r0₇
    (by rw [r1₇, h.r5]) r2₇ r3₇ r9₇ (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r10]) hsp hrd hwr
  by_cases h0 : VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L = 0
  · have hn : VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L = 0 := by simp [VG.Proof.CmacAes.Stream.Arm.nbOf, VG.Proof.CmacAes.Stream.Arm.nbx, h0]
    simp only [VG.Proof.CmacAes.Stream.Arm.d2Of, h0, ↓reduceIte, hn, Nat.mul_zero] at common ⊢
    refine common (by decide) (VG.Proof.CmacAes.Stream.Arm.disjoint_zero _ _) (VG.Proof.CmacAes.Stream.Arm.disjoint_zero _ _) ((VG.Proof.CmacAes.Stream.Arm.disjoint_zero _ _).symm) (by omega)
      (Covers.right (by have := hp.inSt (d := 0) (n := 0) (by decide); rwa [BitVec.add_zero] at this))
  · simp only [VG.Proof.CmacAes.Stream.Arm.d2Of, h0, ↓reduceIte] at common ⊢
    have hn : 16 * VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L < VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L := by
      simp only [VG.Proof.CmacAes.Stream.Arm.nbOf, VG.Proof.CmacAes.Stream.Arm.nbx, h0, ↓reduceIte]; omega
    have aD : State.addr (D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)) =
        State.addr D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) := addr_add (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf at h0; omega)
    have dD : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L),
        16 * VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L⟩ ⟨State.addr D, L⟩ := Offset.sub_base _ (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf at hn; omega)
    rw [aD] at common
    refine common (by omega) ((hp.st_d.sub_left (Offset.sub_base _ (by decide))).symm.sub_left dD)
      (hp.d_s.sub_left dD) (hp.b_d.sub_right dD)
      (by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf at h0; omega)]; unfold VG.Proof.CmacAes.Stream.Arm.leftOf at hn; omega)
      (hp.inD (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf at hn; omega))

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.leftOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AMid₂.after {s₀ s s' : State} {St D S : BitVec 32} {L R : Nat} {m : Mem} (h : VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀ St D S L R m s)
    (h₈ : VG.Proof.CmacAes.Stream.Arm.UPost s St (St + BitVec.ofNat 32 272) (VG.Proof.CmacAes.Stream.Arm.d2Of St D (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) S R (VG.Proof.CmacAes.Stream.Arm.nbOf (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) s') :
    VG.Proof.CmacAes.Stream.Arm.AAfter₂ s₀ St D S L s' :=
  ⟨by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r4],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r6],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r7],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r8],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r10],
    by rw [h₈.saved _ (by simp [preserved]) (by decide), h.r11], by rw [h₈.sp, h.sp], by rw [h₈.rd, h.rd],
    by rw [h₈.wr, h.wr]⟩

theorem call2_after {s₀ s : State} {St D S : BitVec 32} {L R : Nat} {m : Mem} (h : VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀ St D S L R m s) :
    WP isa updCall s (VG.Proof.CmacAes.Stream.Arm.AAfter₂ s₀ St D S L) :=
  WP.mono (VG.Proof.CmacAes.Stream.Arm.upd_call h.args) fun _ h₈ => h.after h₈

theorem AMid₁.after {s₀ s s' : State} {St D S : BitVec 32} {L R : Nat} (h : VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀ St D S L R s)
    (h₆ : VG.Proof.CmacAes.Stream.Arm.UPost s St (St + BitVec.ofNat 32 272) (St + BitVec.ofNat 32 288) S R (VG.Proof.CmacAes.Stream.Arm.b1Of (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat L) s') :
    VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀ St D S L s' :=
  ⟨by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r4],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r5],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r6],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r7],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.r10],
    by rw [h₆.saved _ (by simp [preserved]) (by decide), h.keep _ (by simp [preserved]) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)], by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd],
    by rw [h₆.wr, h.wr]⟩

theorem saved_eq : saved = saved.take 7 ++ [(.r10, 2200)] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbArm.pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ absorbArm.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = D at hp
  generalize stackArg s₀ 2 = S at hp
  generalize (stackArg s₀ 1).toNat = L at hp
  generalize (s₀.gpr .r1).toNat = R at hp
  have hL := hp.lt
  have hw := hp.fSt
  have hsw := hp.fS
  have hD := hp.fD
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.upd_call h₅.args) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.chain2_mid hp (h₅.after h₆)) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.upd_call h₇.args) fun s₈ h₈ => ?_)
  obtain ⟨c, hc⟩ : ∃ c, (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat = c := ⟨_, rfl⟩
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.Arm.f_le c L
  have hsum := VG.Proof.CmacAes.Stream.Arm.nb_le c L
  have hrr := VG.Proof.CmacAes.Stream.Arm.rest_le c L
  have hh := held_le c
  obtain ⟨r4₈, r6₈, r7₈, r8₈, r10₈, r11₈, sp₈, rd₈, wr₈⟩ := h₇.after h₈
  rw [hc] at r6₈ r7₈ r8₈
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.rest_wp (St := St) (x := VG.Proof.CmacAes.Stream.Arm.leftOf c L) (n := VG.Proof.CmacAes.Stream.Arm.nbOf c L) (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf; omega) r6₈ r7₈
    r8₈ r4₈) fun s₉ h₉ => ?_)
  obtain ⟨r6₉, r7₉, r1₉, r2₉, g₉, m₉, sp₉, rd₉, wr₉⟩ := h₉
  have restEq : VG.Proof.CmacAes.Stream.Arm.leftOf c L - 16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L = VG.Proof.CmacAes.Stream.Arm.restOf c L := rfl
  rw [restEq] at r7₉ r1₉
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈]
  have a288 := hp.aS (k := 288) (by decide)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.copy_wp (p := D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf c L) + BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L))
    (c := St + BitVec.ofNat 32 288) (L := VG.Proof.CmacAes.Stream.Arm.restOf c L) (x := VG.Proof.CmacAes.Stream.Arm.restOf c L) (Nat.le_refl _) (by omega) r6₉ r2₉ r1₉ r7₉
    fun hpos => ?_) fun s₁₀ h₁₀ => ?_)
  · have aP : State.addr (D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf c L) + BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L)) =
        State.addr D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.Arm.fOf c L + 16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L) := by
      rw [VG.Proof.CmacAes.Stream.Arm.add_ofNat32]; exact addr_add (by omega)
    exact
    { fp := by rw [VG.Proof.CmacAes.Stream.Arm.add_ofNat32, VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega
      fc := by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega
      hr := by rw [rd₉', wr₉', aP]; exact hp.inD (by omega)
      hw := by rw [wr₉', a288]; exact hp.inSt (by omega)
      hd := by
        rw [aP, a288]
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Offset.sub_base _ (by omega)) }
  have r10₁₀ : s₁₀.gpr .r10 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), r10₈]
  have inS : ∀ d, d + 4 ≤ 2304 → InRegions (s₁₀.rd ++ s₁₀.wr) (State.addr S + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      exact Covers.right (hp.inS hd) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [restore, VG.Proof.CmacAes.Stream.Arm.saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₁₂ ld₁₂ ho₁₂ m₁₂ _ _ sp₁₂ => WP.block_nil ?_
  · have hb := VG.Proof.CmacAes.Stream.Arm.saved_bound p (by rw [VG.Proof.CmacAes.Stream.Arm.saved_eq]; exact hp')
    exact ⟨by omega, by rw [r10₁₀]; omega, by rw [r10₁₀]; exact inS _ (by omega)⟩
  -- The frames.
  have hm5 : s₅.mem = VG.Proof.CmacAes.Stream.Arm.m4 s₀ St D S c L := by rw [h₅.mem, hc]
  have hlr : (Spec.Aes.bytesAt s₉.mem (State.addr (D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf c L) + BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf c L)))
      (VG.Proof.CmacAes.Stream.Arm.restOf c L)).length = VG.Proof.CmacAes.Stream.Arm.restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨State.addr S, 2304⟩] s₀.mem (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) := VG.Proof.CmacAes.Stream.Arm.aMem_frame _ _
  have fC1 : Frame [⟨State.addr St + BitVec.ofNat 64 288, 16⟩] (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) s₅.mem := by
    rw [hm5, VG.Proof.CmacAes.Stream.Arm.m4]
    by_cases hf0 : VG.Proof.CmacAes.Stream.Arm.fOf c L = 0
    · rw [hf0, show Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr D) 0 = [] from rfl, VG.WriteBytes.writeBytes_nil]
      exact Frame.refl _ _
    · have hlt : 288 + held c < 304 := by unfold VG.Proof.CmacAes.Stream.Arm.fOf at hf0; omega
      refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
      rw [Proof.Cmac.bytesAt_length, hp.aS hlt]
      exact Offset.contains (State.addr St) (d := 288 + held c) (n := VG.Proof.CmacAes.Stream.Arm.fOf c L) (e := 288) (k := 16) (by omega)
        (by omega) (by omega)
  have hb5 : VG.Proof.CmacAes.Stream.Arm.blw16 s₅ = VG.Proof.CmacAes.Stream.Arm.blw16 s₀ := by rw [VG.Proof.CmacAes.Stream.Arm.blw16, h₅.sp]
  have hb7 : VG.Proof.CmacAes.Stream.Arm.blw16 s₇ = VG.Proof.CmacAes.Stream.Arm.blw16 s₀ := by rw [VG.Proof.CmacAes.Stream.Arm.blw16, h₇.sp]
  have f6 : Frame [⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw16 s₀] s₅.mem s₆.mem := by
    have := h₆.frame; rwa [hb5] at this
  have f8 : Frame [⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw16 s₀] s₆.mem s₈.mem := by
    have := h₈.frame; rwa [hb7, h₇.mem] at this
  have fC2 : Frame [⟨State.addr St + BitVec.ofNat 64 288, 16⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
    rw [← m₉, hlr, a288]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  let K : List Region := [⟨State.addr S, 2304⟩, ⟨State.addr St + BitVec.ofNat 64 288, 16⟩,
    ⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw16 s₀]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  have a272 := hp.aS (k := 272) (by decide)
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₂, h₁₀.sp, sp₉, sp₈]⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 4 ≤ 2208) :
        s₁₀.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 =
          (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
      have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 2304⟩ := Offset.sub_base _ (by omega)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
      · rw [a272]; exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hp.b_s.symm.sub_left sub
    by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      have hb := VG.Proof.CmacAes.Stream.Arm.saved_bound _ hp'
      rw [ld₁₂ p (by rw [← VG.Proof.CmacAes.Stream.Arm.saved_eq]; exact hp'), r10₁₀, slot p.2 hb.1 hb.2, VG.Proof.CmacAes.Stream.Arm.aMem_slot s₀ S hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho₁₂ _ (by decide), h₁₀.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), r11₈]
  · intro key msg hr hR hcnt hlen
    rw [hp.r0] at hr ⊢
    rw [hp.a0, hp.a1, m₁₂]
    rw [hp.a1] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, VG.Proof.CmacAes.Stream.Arm.toNat_ofNat64 (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r1]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    have dK : ∀ r ∈ K, (⟨State.addr St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.st_s.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · rw [a272]; exact Offset.base_disjoint _ (by decide) (by decide)
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    have dDat : ∀ r ∈ K, (⟨State.addr D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s
      · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
      · rw [a272]; exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.b_d.symm
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m (State.addr St) (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (State.addr D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem (State.addr D) L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m (State.addr D) hab, Proof.Cmac.bytesAt_frame hf dDat (by omega)]
    have fS' : Frame K s₀.mem (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) := fS.mono (by simp [K])
    have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 272) 16 := by
      rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (State.addr St) (d := 272) (n := 16) (e := 288) (k := 16) (by decide) (by decide)
            (by decide)) (by decide),
        Proof.Cmac.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_s.sub_left (Offset.sub_base _ (by decide))) (by decide)]
    have cv10 : Spec.Aes.bytesAt s₁₀.mem (State.addr St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (State.addr St + BitVec.ofNat 64 272) 16 :=
      Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint (State.addr St) (d := 272) (n := 16) (e := 288) (k := 16) (by decide) (by decide)
          (by decide)) (by decide)
    have out6 := h₆.out
    rw [a272, a288, ciph _ F5, hc] at out6
    have out8 := h₈.out
    rw [a272, h₇.mem, ciph _ F6, hc] at out8
    have hk : ∀ i < 272, s₁₀.mem (State.addr St + BitVec.ofNat 64 i) = s₀.mem (State.addr St + BitVec.ofNat 64 i) :=
      fun i hi => F10.bytes (R := ⟨State.addr St, 272⟩) dK (by show 272 ≤ 2 ^ 64; decide) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem (State.addr D) L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 288) (held msg.length + VG.Proof.CmacAes.Stream.Arm.fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem (State.addr D) L).take (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L) := by
      have e₀ : Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr St + BitVec.ofNat 64 288) (held msg.length) =
          Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 288) (held msg.length) :=
        Proof.Cmac.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_s.sub_left (Offset.sub_base _ (by omega))) (by omega)
      rw [hm5, VG.Proof.CmacAes.Stream.Arm.m4]
      by_cases hf0 : VG.Proof.CmacAes.Stream.Arm.fOf msg.length L = 0
      · rw [hf0, show Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr D) 0 = [] from rfl, VG.WriteBytes.writeBytes_nil, Nat.add_zero, e₀,
          List.take_zero, List.append_nil]
      · have hlt : 288 + held msg.length < 304 := by unfold VG.Proof.CmacAes.Stream.Arm.fOf at hf0; omega
        have hlf : (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr D) (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L)).length = VG.Proof.CmacAes.Stream.Arm.fOf msg.length L :=
          Proof.Cmac.bytesAt_length _ _ _
        have e := VG.Proof.CmacAes.Stream.Arm.bytesAt_writeBytes (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr St + BitVec.ofNat 64 288) (held msg.length)
          (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.aMem s₀ S) (State.addr D) (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L)) (by rw [hlf]; omega)
        rw [hlf] at e
        rw [hp.aS hlt, ← Offset.add_add, e, e₀]
        refine congrArg (_ ++ ·) ?_
        have := dat _ fS' 0 (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L) (by omega)
        rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem (State.addr D) L = d at hdl hb5 dat ⊢
    by_cases hx : VG.Proof.CmacAes.Stream.Arm.leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : VG.Proof.CmacAes.Stream.Arm.fOf msg.length L = L := by unfold VG.Proof.CmacAes.Stream.Arm.leftOf at hx; omega
      have hb : VG.Proof.CmacAes.Stream.Arm.b1Of msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.Arm.b1Of, hx]
      have hn : VG.Proof.CmacAes.Stream.Arm.nbOf msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.Arm.nbOf, VG.Proof.CmacAes.Stream.Arm.nbx, hx]
      have hr0 : VG.Proof.CmacAes.Stream.Arm.restOf msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.Arm.restOf, hn, hx]
      have m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem _ 0 = [] from rfl, VG.WriteBytes.writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (VG.Proof.CmacAes.Stream.Arm.f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _ =
          Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, VG.Proof.CmacAes.Stream.Arm.blocksAt_zero, out6, hb, VG.Proof.CmacAes.Stream.Arm.blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ =
          Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨State.addr St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨State.addr St, 304⟩ :=
          Offset.sub_base _ (by omega)
        have dj : ∀ r ∈ [⟨State.addr (St + BitVec.ofNat 32 272), 16⟩, ⟨State.addr S, 2176⟩, VG.Proof.CmacAes.Stream.Arm.blw16 s₀],
            (⟨State.addr St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [a272]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · exact (hp.b_st.sub_right sub).symm
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, Proof.Cmac.bytesAt_frame f8 dj (by omega), Proof.Cmac.bytesAt_frame f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold VG.Proof.CmacAes.Stream.Arm.leftOf VG.Proof.CmacAes.Stream.Arm.fOf at hx; omega
      have hf' : VG.Proof.CmacAes.Stream.Arm.fOf msg.length L = 16 - held msg.length := by unfold VG.Proof.CmacAes.Stream.Arm.fOf; omega
      have hb : VG.Proof.CmacAes.Stream.Arm.b1Of msg.length L = 1 := by simp [VG.Proof.CmacAes.Stream.Arm.b1Of, hx]
      have hn : VG.Proof.CmacAes.Stream.Arm.nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [VG.Proof.CmacAes.Stream.Arm.nbOf, VG.Proof.CmacAes.Stream.Arm.nbx, hx, ↓reduceIte]
        unfold VG.Proof.CmacAes.Stream.Arm.leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have aD2 : State.addr (VG.Proof.CmacAes.Stream.Arm.d2Of St D msg.length L) = State.addr D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L) := by
        simp only [VG.Proof.CmacAes.Stream.Arm.d2Of, hx, ↓reduceIte]; exact addr_add (by unfold VG.Proof.CmacAes.Stream.Arm.leftOf at hx; omega)
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' (held_le _)] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv10, out8, out6, hb, VG.Proof.CmacAes.Stream.Arm.blocksAt_one, cv5, Proof.Cmac.chain_append, aD2, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            VG.Proof.CmacAes.Stream.Arm.restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        have aP : State.addr (D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L) + BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf msg.length L)) =
            State.addr D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L + 16 * VG.Proof.CmacAes.Stream.Arm.nbOf msg.length L) := by
          have hpos : 0 < VG.Proof.CmacAes.Stream.Arm.restOf msg.length L := by
            unfold VG.Proof.CmacAes.Stream.Arm.restOf VG.Proof.CmacAes.Stream.Arm.nbOf VG.Proof.CmacAes.Stream.Arm.nbx; simp only [hx, ↓reduceIte]; omega
          rw [VG.Proof.CmacAes.Stream.Arm.add_ofNat32]; exact addr_add (by omega)
        have e := VG.Proof.CmacAes.Stream.Arm.bytesAt_writeBytes_self s₈.mem (State.addr (St + BitVec.ofNat 32 288))
          (xs := Spec.Aes.bytesAt s₈.mem (State.addr (D + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.Arm.fOf msg.length L) +
            BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.Arm.nbOf msg.length L))) (VG.Proof.CmacAes.Stream.Arm.restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 288) _ = _
        rw [hr', h₁₀.mem, m₉, ← a288, e, aP, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold VG.Proof.CmacAes.Stream.Arm.restOf VG.Proof.CmacAes.Stream.Arm.leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Finish`. -/
section

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_finish`

The code saves `r4`, `r5` and `lr`, copies the chaining value to `out`,
computes the number of bytes held back, and calls `vg_cmac_aes_finalize` with
the state as its key and `out` as its state: its result is the MAC of the
message the state represents (`repr_finish`). The code before the call is
constant time by the taint analysis, and the call by its own proof
(`fin_rel`), its arguments pinned by `HMid`.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_and wp_orr wp_cmp wp_ldr
  wp_str wp_ldrSp saveMem saveList_ok saveMem_frame readW_writeW_save)
open VG.Proof.CmacAes.Arm (saveMem_congr addr_word in_word in_word0)
open VG.Proof.Cmac.Stream (held held_le held_zero)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : BitVec 32) (R : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = O
  a1 : stackArg s₀ 1 = S
  r1 : (s₀.gpr .r1).toNat = R
  rd : s₀.rd = [⟨stackArgAddr s₀ 0, 8⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr O, 16⟩, ⟨State.addr S, 2304⟩]
  st_o : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  o_s : (⟨State.addr O, 16⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  a_st : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr St, 304⟩
  a_o : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  a_s : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr St, 304⟩
  b_o : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr O, 16⟩
  b_s : (VG.Proof.CmacAes.Stream.Arm.blw16 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fO : O.toNat + 16 ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishArm.pre s₀) :
    VG.Proof.CmacAes.Stream.Arm.HPre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q, r⟩

/-! ## Arguments on the stack -/

theorem arg1_eq {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) :
    stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem arg_in {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) {rs : List Region} (hr : ⟨stackArgAddr s 0, 8⟩ ∈ rs)
    {k : Nat} (hk : k < 2) : InRegions rs (stackArgAddr s k) 4 := by
  refine ⟨_, hr, ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [VG.Proof.CmacAes.Stream.Arm.arg1_eq h]; exact Offset.contains_base _ (by decide) (by decide)

/-! ## Saving the registers, and copying the chaining value -/

def fsaved : List (Reg × Nat) := [(.r4, 2176), (.r5, 2180), (.lr, 2184)]

theorem fsaved_bound : ∀ p ∈ VG.Proof.CmacAes.Stream.Arm.fsaved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2188 := by decide

/-- The copy of the chaining value, a word at a time through `lr`. -/
def cvCopy : List Instr :=
  [.ldr .lr .r0 272, .str .lr .r12 0, .ldr .lr .r0 276, .str .lr .r12 4, .ldr .lr .r0 280, .str .lr .r12 8,
   .ldr .lr .r0 284, .str .lr .r12 12]

/-- `count`'s bytes held back, and whether `count` is 0. -/
def heldBlk : List Instr :=
  [.dp .sub .r4 .r2 (.imm 1), .dp .and .r4 .r4 (.imm 15), .dp .add .r4 .r4 (.imm 1),
   .dp .orr .r2 .r2 (.reg .r3), .cmp .r2 (.imm 0)]

theorem finishPre_eq : finishPre = .ldrSp .r12 4 :: (fsaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    (mov .r5 .r12 :: .ldrSp .r12 0 :: (VG.Proof.CmacAes.Stream.Arm.cvCopy ++ VG.Proof.CmacAes.Stream.Arm.heldBlk))) := rfl

/-- The memory after saving the registers. -/
def fsMem (s₀ : State) (S : BitVec 32) : Mem := VG.Arm.Spill.saveMem s₀.mem (State.addr S) s₀.gpr VG.Proof.CmacAes.Stream.Arm.fsaved

theorem fsMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ VG.Proof.CmacAes.Stream.Arm.fsaved) :
    (VG.Proof.CmacAes.Stream.Arm.fsMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (lo := 2176) (hi := 2188) (State.addr S) s₀.gpr s₀.mem VG.Proof.CmacAes.Stream.Arm.fsaved (by decide) (r, d) h

theorem fsMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (VG.Proof.CmacAes.Stream.Arm.fsMem s₀ S) :=
  Spill.saveMem_frame _ _ _ (by decide) VG.Proof.CmacAes.Stream.Arm.fsaved (by decide)

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def cvMem (m : Mem) (o p : Addr) : Mem :=
  Proof.Cmac.store4 m o (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) (m.readW (p + BitVec.ofNat 64 8) 32)
    (m.readW (p + BitVec.ofNat 64 12) 32)

theorem cvMem_bytes (m : Mem) (o p : Addr) : Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.Arm.cvMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  rw [VG.Proof.CmacAes.Stream.Arm.cvMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

theorem cvMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (VG.Proof.CmacAes.Stream.Arm.cvMem m o p) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem cvCopy_ok {is : List Instr} {s : State} {Q : State → Prop} {St O : BitVec 32}
    (h0 : s.gpr .r0 = St) (h12 : s.gpr .r12 = O) (fSt : St.toNat + 288 ≤ 2 ^ 32) (fO : O.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr St + BitVec.ofNat 64 272, 16⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr O, 16⟩] s.wr)
    (hd : (⟨State.addr O, 16⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272, 16⟩)
    (k : ∀ s', (∀ r, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = VG.Proof.CmacAes.Stream.Arm.cvMem s.mem (State.addr O) (State.addr St + BitVec.ofNat 64 272) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Proof.CmacAes.Stream.Arm.cvCopy ++ is)) s Q := by
  have aP (i : Nat) (hi : i ≤ 12) : State.addr (St + BitVec.ofNat 32 (272 + i)) =
      State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 i := addr_word i (by omega) hi
  have aO (i : Nat) (hi : i ≤ 12) : State.addr (O + BitVec.ofNat 32 (0 + i)) =
      State.addr O + BitVec.ofNat 64 0 + BitVec.ofNat 64 i := addr_word i (by omega) hi
  have o0 : State.addr O + BitVec.ofNat 64 0 = State.addr O := BitVec.add_zero _
  rw [o0] at aO
  have dW (i j : Nat) (hi : i ≤ 12) (hj : j ≤ 12) :
      (⟨State.addr O + BitVec.ofNat 64 i, 4⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 j, 4⟩ :=
    (hd.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have dW0 (j : Nat) (hj : j ≤ 12) :
      (⟨State.addr O, 4⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 j, 4⟩ := by
    have := dW 0 j (by decide) hj; rwa [BitVec.add_zero] at this
  simp only [VG.Proof.CmacAes.Stream.Arm.cvCopy, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272) (by decide) (by rw [h0]; exact addr_add (by omega))
    (in_word0 hr) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr O) (by decide)
    (by rw [u₁.other _ (by decide), h12, BitVec.add_zero]) (by rw [u₁.wr]; exact in_word0 hw) fun s₂ v₂ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₂.gpr, u₁.other _ (by decide), h0]; exact aP 4 (by decide))
    (by rw [v₂.rd, v₂.wr, u₁.rd, u₁.wr]; exact in_word hr (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h12]; exact aO 4 (by decide))
    (by rw [u₃.wr, v₂.wr, u₁.wr]; exact in_word hw (by decide)) fun s₄ v₄ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (by decide)
    (by rw [v₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h0]; exact aP 8 (by decide))
    (by rw [v₄.rd, v₄.wr, u₃.rd, u₃.wr, v₂.rd, v₂.wr, u₁.rd, u₁.wr]; exact in_word hr (by decide))
    fun s₅ u₅ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 8) (by decide)
    (by rw [u₅.other _ (by decide), v₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h12]
        exact aO 8 (by decide))
    (by rw [u₅.wr, v₄.wr, u₃.wr, v₂.wr, u₁.wr]; exact in_word hw (by decide)) fun s₆ v₆ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 12) (by decide)
    (by rw [v₆.gpr, u₅.other _ (by decide), v₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h0]
        exact aP 12 (by decide))
    (by rw [v₆.rd, v₆.wr, u₅.rd, u₅.wr, v₄.rd, v₄.wr, u₃.rd, u₃.wr, v₂.rd, v₂.wr, u₁.rd, u₁.wr]
        exact in_word hr (by decide)) fun s₇ u₇ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 12) (by decide)
    (by rw [u₇.other _ (by decide), v₆.gpr, u₅.other _ (by decide), v₄.gpr, u₃.other _ (by decide), v₂.gpr,
          u₁.other _ (by decide), h12]
        exact aO 12 (by decide))
    (by rw [u₇.wr, v₆.wr, u₅.wr, v₄.wr, u₃.wr, v₂.wr, u₁.wr]; exact in_word hw (by decide)) fun s₈ v₈ => ?_
  refine k s₈ (fun r hr => ?_) ?_ ?_ ?_ ?_
  · rw [v₈.gpr, u₇.other _ hr, v₆.gpr, u₅.other _ hr, v₄.gpr, u₃.other _ hr, v₂.gpr, u₁.other _ hr]
  · rw [v₈.mem, u₇.gpr, u₇.mem, v₆.mem, u₅.gpr, u₅.mem, v₄.mem, u₃.gpr, u₃.mem, v₂.mem, u₁.gpr, u₁.mem]
    simp only [Proof.Cmac.readW_writeW_disj _ (dW0 4 (by decide)), Proof.Cmac.readW_writeW_disj _ (dW0 8 (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW0 12 (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW 4 8 (by decide) (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW 4 12 (by decide) (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW 8 12 (by decide) (by decide))]
    rfl
  · rw [v₈.rd, u₇.rd, v₆.rd, u₅.rd, v₄.rd, u₃.rd, v₂.rd, u₁.rd]
  · rw [v₈.wr, u₇.wr, v₆.wr, u₅.wr, v₄.wr, u₃.wr, v₂.wr, u₁.wr]
  · rw [v₈.sp, u₇.sp, v₆.sp, u₅.sp, v₄.sp, u₃.sp, v₂.sp, u₁.sp]

/-! ## Before the call -/

/-- What the block before `lastLen` leaves. -/
structure HBlk (s₀ : State) (St O S : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = St
  r1 : s.gpr .r1 = s₀.gpr .r1
  r4 : s.gpr .r4 = ((s₀.gpr .r2 - 1) &&& 15) + 1
  r5 : s.gpr .r5 = S
  r12 : s.gpr .r12 = O
  z : s.z = ((s₀.gpr .r2 ||| s₀.gpr .r3) - 0 == 0)
  mem : s.mem = VG.Proof.CmacAes.Stream.Arm.cvMem (VG.Proof.CmacAes.Stream.Arm.fsMem s₀ S) (State.addr O) (State.addr St + BitVec.ofNat 64 272)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r

theorem finishPre_wp {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.HPre s₀ St O S R) :
    WP isa (.block finishPre) s₀ (VG.Proof.CmacAes.Stream.Arm.HBlk s₀ St O S) := by
  have hS := hp.fS
  have hSt := hp.fSt
  rw [VG.Proof.CmacAes.Stream.Arm.finishPre_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl
    (VG.Proof.CmacAes.Stream.Arm.arg_in hp.spf (by rw [hp.rd]; simp) (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S := by rw [u₁.gpr]; exact hp.a1
  refine VG.Arm.Spill.saveList_ok VG.Proof.CmacAes.Stream.Arm.fsaved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := VG.Proof.CmacAes.Stream.Arm.fsaved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Stream.Arm.fsMem s₀ S := by
    rw [m₂, u₁.mem, h12, VG.Proof.CmacAes.Stream.Arm.fsMem]
    exact VG.Arm.Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (by
      simp only [VG.Proof.CmacAes.Stream.Arm.fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.Stream.Arm.arg_in hp.spf (by rw [hp.rd]; simp) (by decide))
    fun s₄ u₄ => ?_
  have hO : s₄.gpr .r12 = O := by
    rw [u₄.gpr, u₃.mem, hm₂, ← hp.a0]
    exact (VG.Proof.CmacAes.Stream.Arm.fsMem_frame s₀ S).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.sub_left (Region.sub_prefix (by decide))) (by decide)
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂, u₁.wr]
  have c272 : Region.Sub ⟨State.addr St + BitVec.ofNat 64 272, 16⟩ ⟨State.addr St, 304⟩ :=
    Offset.sub_base _ (by decide)
  refine VG.Proof.CmacAes.Stream.Arm.cvCopy_ok (St := St) (O := O)
    (by simp (disch := decide) only [u₄.other, u₃.other, g₂, u₁.other, hp.r0]) hO (by omega) hp.fO
    (by
      rw [rd₄, wr₄, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr St, 304⟩, by simp, 272, rfl, by simp⟩)
    (by
      rw [wr₄, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr O, 16⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩)
    (hp.st_o.symm.sub_right c272) fun s₅ g₅ m₅ rd₅ wr₅ sp₅ => ?_
  simp only [VG.Proof.CmacAes.Stream.Arm.heldBlk]
  refine wp_sub (op2_imm (by decide)) fun s₆ u₆ => wp_and (op2_imm (by decide)) fun s₇ u₇ =>
    wp_add (op2_imm (by decide)) fun s₈ u₈ => wp_orr (op2_reg _ _) fun s₉ u₉ =>
    wp_cmp (op2_imm (by decide)) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ?_
  have g : ∀ r, r ≠ .lr → r ≠ .r2 → r ≠ .r4 → r ≠ .r12 → r ≠ .r5 → s₁₀.gpr r = s₀.gpr r := fun r a b c d e => by
    rw [f₁₀.gpr, u₉.other _ b, u₈.other _ c, u₇.other _ c, u₆.other _ c, g₅ _ a, u₄.other _ d, u₃.other _ e, g₂,
      u₁.other _ d]
  refine ⟨by rw [g .r0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp.r0,
    g .r1 (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, g₅ _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide), hO]
  · rw [z₁₀, u₉.gpr]
    simp (disch := decide) only [u₈.other, u₇.other, u₆.other, g₅, u₄.other, u₃.other, g₂, u₁.other]
  · rw [f₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, hm₂]
  · rw [f₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, sp₅, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, rd₄]
  · rw [f₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅, wr₄]
  · intro r hr a b c
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact g _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : BitVec 32) (R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.Arm.FArgs s St O (St + BitVec.ofNat 32 288) S (held (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat) R
  mem : s.mem = VG.Proof.CmacAes.Stream.Arm.cvMem (VG.Proof.CmacAes.Stream.Arm.fsMem s₀ S) (State.addr O) (State.addr St + BitVec.ofNat 64 272)
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.aL {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.HPre s₀ St O S R) :
    State.addr (St + BitVec.ofNat 32 288) = State.addr St + BitVec.ofNat 64 288 := addr_add (by have := hp.fSt; omega)

theorem HPre.fargs {s₀ s : State} {St O S : BitVec 32} {R L : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.HPre s₀ St O S R) (hL : L ≤ 16)
    (r0 : s.gpr .r0 = St) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = O)
    (r3 : s.gpr .r3 = St + BitVec.ofNat 32 288) (r4 : s.gpr .r4 = BitVec.ofNat 32 L) (r5 : s.gpr .r5 = S)
    (sp : s.sp = s₀.sp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    VG.Proof.CmacAes.Stream.Arm.FArgs s St O (St + BitVec.ofNat 32 288) S L R := by
  have hw := hp.fSt
  have pSt : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 288), L⟩ ⟨State.addr St, 304⟩ := by
    rw [hp.aL]; exact Offset.sub_base _ (by omega)
  have hb : VG.Proof.CmacAes.Stream.Arm.blw16 s = VG.Proof.CmacAes.Stream.Arm.blw16 s₀ := by rw [VG.Proof.CmacAes.Stream.Arm.blw16, sp]
  exact
  { r0 := r0, r2 := r2, r3 := r3, r4 := r4, r5 := r5
    r1 := by rw [r1]; exact BitVec.eq_of_toNat_eq (by rw [hp.r1, VG.Proof.CmacAes.Stream.Arm.toNat_ofNat32 (by rcases hp.rounds with h | h | h <;> omega)])
    rounds := hp.rounds, len := hL
    hsp := by rw [sp]; exact hp.sp
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bk := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bp := by rw [hb]; exact hp.b_st.sub_right pSt
    bst := by rw [hb]; exact hp.b_o
    bs := by rw [hb]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega
    fSt := hp.fO
    fP := by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega
    fS := by have := hp.fS; omega
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr St, 304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr St, 304⟩, by simp, 288, hp.aL, by simp; omega⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr O, 16⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr S, 2304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.HPre s₀ St O S R) :
    WP isa finPre s₀ (VG.Proof.CmacAes.Stream.Arm.HMid s₀ St O S R) := by
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.finishPre_wp hp) fun s₁ h₁ => ?_)
  have hc := (VG.Proof.CmacAes.Stream.Arm.countArm s₀).isLt
  have ev : isa.eval .eq s₁ = some (decide ((VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, h₁.z, VG.Proof.CmacAes.Stream.Arm.or_beq_zero (VG.Proof.CmacAes.Stream.Arm.count_eq s₀) hc]
  have tail : ∀ {t : State} {L : Nat}, L ≤ 16 → t.gpr .r4 = BitVec.ofNat 32 L → L = held (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat →
      (∀ r, r ≠ .r4 → t.gpr r = s₁.gpr r) → t.mem = s₁.mem → t.sp = s₁.sp → t.rd = s₁.rd → t.wr = s₁.wr →
      WP isa (.block finArgs) t (VG.Proof.CmacAes.Stream.Arm.HMid s₀ St O S R) := fun {t L} hL h4 hLe g m sp rd wr => by
    refine wp_mov (op2_reg _ _) fun t₁ u₁ => wp_add (op2_imm (by decide)) fun t₂ u₂ => WP.block_nil ?_
    have g₂ : ∀ r, r ≠ .r2 → r ≠ .r3 → t₂.gpr r = t.gpr r := fun r a b => by rw [u₂.other _ b, u₁.other _ a]
    refine ⟨hLe ▸ hp.fargs hL (by rw [g₂ _ (by decide) (by decide), g _ (by decide), h₁.r0])
      (by rw [g₂ _ (by decide) (by decide), g _ (by decide), h₁.r1])
      (by rw [u₂.other _ (by decide), u₁.gpr, g _ (by decide), h₁.r12])
      (by rw [u₂.gpr, u₁.other _ (by decide), g _ (by decide), h₁.r0]; rfl)
      (by rw [g₂ _ (by decide) (by decide), h4]) (by rw [g₂ _ (by decide) (by decide), g _ (by decide), h₁.r5])
      (by rw [u₂.sp, u₁.sp, sp, h₁.sp]) (by rw [u₂.rd, u₁.rd, rd, h₁.rd]) (by rw [u₂.wr, u₁.wr, wr, h₁.wr]),
      by rw [u₂.mem, u₁.mem, m, h₁.mem], fun r hr a b c => ?_, by rw [u₂.sp, u₁.sp, sp, h₁.sp],
      by rw [u₂.rd, u₁.rd, rd, h₁.rd], by rw [u₂.wr, u₁.wr, wr, h₁.wr]⟩
    have : r ≠ .r2 ∧ r ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₂ _ this.1 this.2, g _ a, h₁.keep r hr a b c]
  refine WP.seq ?_
  by_cases h0 : (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    exact tail (L := 0) (by decide) u.gpr (by rw [h0]; rfl) (fun r h => u.other r h) u.mem u.sp u.rd u.wr
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    refine tail (held_le _) ?_ rfl (fun _ _ => rfl) rfl rfl rfl rfl
    rw [h₁.r4]
    exact VG.Proof.CmacAes.Stream.Arm.held_lo (VG.Proof.CmacAes.Stream.Arm.count_eq s₀) hc h0

/-! ## The whole function -/

theorem finishPost_eq : finishPost = ([(.r4, 2176), (.lr, 2184)] : List (Reg × Nat)).map
    (fun p => Instr.ldr p.1 .r5 p.2) ++ ([.ldr .r5 .r5 2180] : List Instr) := rfl

theorem finish_wp {s₀ : State} (h0 : finishArm.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishArm.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = O at hp
  generalize stackArg s₀ 1 = S at hp
  generalize (s₀.gpr .r1).toNat = R at hp
  have hSt := hp.fSt
  have hS := hp.fS
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.fin_call h₁.args) fun s₂ h₂ => ?_)
  have e5 : s₂.gpr .r5 = S := by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.args.r5]
  have rdwr : s₂.rd ++ s₂.wr = [⟨stackArgAddr s₀ 0, 8⟩, ⟨State.addr St, 304⟩, ⟨State.addr O, 16⟩,
      ⟨State.addr S, 2304⟩] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have inS (d : Nat) (hd : d + 4 ≤ 2304) : InRegions (s₂.rd ++ s₂.wr) (State.addr S + BitVec.ofNat 64 d) 4 := by
    rw [rdwr]; exact ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  rw [VG.Proof.CmacAes.Stream.Arm.finishPost_eq]
  refine Spill.restoreList_ok [(.r4, 2176), (.lr, 2184)] s₂ _ (by decide) (fun p hp' => ?_)
    fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [e5]
    rcases hp' with rfl | rfl
    · exact ⟨by decide, by decide, by omega, inS _ (by decide)⟩
    · exact ⟨by decide, by decide, by omega, inS _ (by decide)⟩
  refine wp_ldr (a := State.addr S + BitVec.ofNat 64 2180) (by decide)
    (by rw [ho₃ _ (by decide), e5]; exact addr_add (by omega))
    (by rw [rd₃, wr₃]; exact inS _ (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, m₃]
  -- The saved registers.
  have slot (d : Nat) (hd : 2176 ≤ d) (hd' : d + 4 ≤ 2188) :
      s₂.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacAes.Stream.Arm.fsMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
    have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 2304⟩ := Offset.sub_base _ (by omega)
    have c := Region.contains_self (State.addr S + BitVec.ofNat 64 d) 4
    rw [h₂.frame.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ hd (by omega)
        · rw [VG.Proof.CmacAes.Stream.Arm.blw16, h₁.sp]; exact (hp.b_s.sub_right sub).symm) (by decide), h₁.mem,
      (VG.Proof.CmacAes.Stream.Arm.cvMem_frame _ _ _).readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.o_s.symm.sub_left sub) (by decide)]
  refine ⟨⟨fun r hr => ?_, by rw [u₄.sp, sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), ld₃ (.r4, 2176) (by simp), e5, slot 2176 (by decide) (by decide),
        VG.Proof.CmacAes.Stream.Arm.fsMem_slot s₀ S (r := .r4) (d := 2176) (by decide)]
    · rw [u₄.gpr, m₃, slot 2180 (by decide) (by decide), VG.Proof.CmacAes.Stream.Arm.fsMem_slot s₀ S (r := .r5) (d := 2180) (by decide)]
    all_goals first
      | rw [u₄.other _ (by decide), ld₃ (.lr, 2184) (by simp), e5, slot 2184 (by decide) (by decide),
          VG.Proof.CmacAes.Stream.Arm.fsMem_slot s₀ S (r := .lr) (d := 2184) (by decide)]
      | rw [u₄.other _ (by decide), ho₃ _ (by decide), h₂.saved _ hr' (by decide),
          h₁.keep _ hr' (by decide) (by decide) (by decide)]
  · intro key msg hr hR hcnt hlen
    rw [hp.r0] at hr
    rw [hp.a0, m₄]
    have hc : (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat = msg.length := by rw [hcnt, VG.Proof.CmacAes.Stream.Arm.toNat_ofNat64 hlen]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r1]; exact hR
    -- The state is unchanged before the call.
    have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (State.addr St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      have sub : Region.Sub ⟨State.addr St + BitVec.ofNat 64 d, n⟩ ⟨State.addr St, 304⟩ := Offset.sub_base _ hd
      rw [h₁.mem, Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Stream.Arm.cvMem_frame _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o.sub_left sub) (by omega),
        Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Stream.Arm.fsMem_frame _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.st_s.sub_left sub) (by omega)]
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := (Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr
    have hsch : Spec.Aes.bytesAt s₁.mem (State.addr St) (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [BitVec.add_zero] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem (State.addr St) (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (State.addr St + 240) 32 = Spec.Aes.bytesAt s₀.mem (State.addr St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem (State.addr O) 16 = Spec.Aes.bytesAt s₀.mem (State.addr St + 272) 16 := by
      rw [h₁.mem, VG.Proof.CmacAes.Stream.Arm.cvMem_bytes]
      exact Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Stream.Arm.fsMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_s.sub_left (Offset.sub_base _ (by decide))) (by decide)
    have e₃ : Spec.Aes.bytesAt s₁.mem (State.addr (St + BitVec.ofNat 32 288)) (held (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat) =
        Spec.Aes.bytesAt s₀.mem (State.addr St + 288) (held msg.length) := by
      rw [hp.aL, hc]; exact fSt (by have := held_le msg.length; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hc]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem HPre.wfA {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.HPre s₀ St O S R) :
    s₀.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 8⟩ r := by
  have e : (⟨State.addr s₀.sp, 8⟩ : Region) = ⟨stackArgAddr s₀ 0, 8⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.a_st
  · exact hp.a_o
  · exact hp.a_s

theorem finish_rel {s₀ s₀' : State} (h0 : finishArm.pre s₀) (h0' : finishArm.pre s₀')
    (hq : finishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := HPre.of h0
  have hp' : VG.Proof.CmacAes.Stream.Arm.HPre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) (s₀.gpr .r1).toNat := by
    rw [q2, q3, q6, q7]; exact HPre.of h0'
  have hc : (VG.Proof.CmacAes.Stream.Arm.countArm s₀').toNat = (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat := by simp only [VG.Proof.CmacAes.Stream.Arm.countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = O at hp hp'
  generalize stackArg s₀ 1 = S at hp hp'
  generalize (s₀.gpr .r1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.CmacAes.Stream.Arm.HMid s₀ St O S R)
    (G' := VG.Proof.CmacAes.Stream.Arm.HMid s₀' St O S R) (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 2) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact q6
        · exact q7) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.CmacAes.Stream.Arm.finPre_wp hp) (fun s e => by rw [e]; exact VG.Proof.CmacAes.Stream.Arm.finPre_wp hp')
  have c := rel_wp (F := VG.Proof.CmacAes.Stream.Arm.HMid s₀ St O S R) (F' := VG.Proof.CmacAes.Stream.Arm.HMid s₀' St O S R)
    (G := fun s => s.gpr .r5 = S) (G' := fun s => s.gpr .r5 = S)
    (VG.Proof.CmacAes.Stream.Arm.fin_rel (sp₀ := s₀.sp) fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩)
    (fun _ h => WP.mono (VG.Proof.CmacAes.Stream.Arm.fin_call h.args) fun _ h' => by
      rw [h'.saved _ (by simp [preserved]) (by decide)]; exact h.args.r5)
    (fun _ h => WP.mono (VG.Proof.CmacAes.Stream.Arm.fin_call h.args) fun _ h' => by
      rw [h'.saved _ (by simp [preserved]) (by decide)]; exact h.args.r5)
  have p := RelCT.taint (A := taint) (P := fun a b => a.gpr .r5 = S ∧ b.gpr .r5 = S)
    (Taint.ofRegs [.r5]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2]) hB
  exact a.seq (c.seq p)

theorem finish_ct : ConstantTime isa finishArm.pre finishArm.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.Arm.finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Init`. -/
section

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_init`

The code saves `r4`–`r6` and `lr` in the scratch buffer, expands the key into
the state, derives the subkeys after the schedule, zeroes the chaining value
and restores the registers: the state then represents the empty message. The
code between the calls is constant time by the taint analysis, and the calls
by their own proofs (`ek_rel`, `sub_rel`), their arguments pinned by `IMid₁`
and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_ldr wp_str saveMem
  saveList_ok saveMem_frame readW_writeW_save)
open VG.Proof.CmacAes.Arm (zeroBlk zeroBlk_ok)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : BitVec 32) (KL : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  r1 : s₀.gpr .r1 = Kp
  r2 : (s₀.gpr .r2).toNat = KL
  r3 : s₀.gpr .r3 = S
  rd : s₀.rd = [⟨State.addr Kp, KL⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩]
  st_k : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr Kp, KL⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  k_s : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (VG.Proof.CmacAes.Stream.Arm.blw8 s₀).Disjoint ⟨State.addr St, 304⟩
  b_k : (VG.Proof.CmacAes.Stream.Arm.blw8 s₀).Disjoint ⟨State.addr Kp, KL⟩
  b_s : (VG.Proof.CmacAes.Stream.Arm.blw8 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 8 ≤ s₀.sp.toNat
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) :
    VG.Proof.CmacAes.Stream.Arm.IPre s₀ (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r3) (s₀.gpr .r2).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n⟩

/-- The registers saved, and where. -/
def isaved : List (Reg × Nat) := [(.r4, 2176), (.r5, 2180), (.r6, 2184), (.lr, 2188)]

theorem isaved_bound : ∀ p ∈ VG.Proof.CmacAes.Stream.Arm.isaved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2192 := by decide

theorem initPre_eq : initPre = isaved.map (fun p => Instr.str p.1 .r3 p.2) ++
    [mov .r4 .r0, mov .r5 .r3, .mov .r6 (.shifted .r2 .lsr 2), .dp .add .r6 .r6 (.imm 6), mov .r0 .r1,
      mov .r1 .r2, mov .r2 .r4] := rfl

/-- The memory after saving the registers. -/
def iMem (s₀ : State) (S : BitVec 32) : Mem := VG.Arm.Spill.saveMem s₀.mem (State.addr S) s₀.gpr VG.Proof.CmacAes.Stream.Arm.isaved

theorem iMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ VG.Proof.CmacAes.Stream.Arm.isaved) :
    (VG.Proof.CmacAes.Stream.Arm.iMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (lo := 2176) (hi := 2192) (State.addr S) s₀.gpr s₀.mem VG.Proof.CmacAes.Stream.Arm.isaved (by decide) (r, d) h

theorem iMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (VG.Proof.CmacAes.Stream.Arm.iMem s₀ S) :=
  Spill.saveMem_frame _ _ _ (by decide) VG.Proof.CmacAes.Stream.Arm.isaved (by decide)

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 32 KL >>> 2 + 6 = BitVec.ofNat 32 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem IPre.rounds {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : BitVec 32) (KL : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.Arm.EArgs s Kp St S KL
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = S
  r6 : s.gpr .r6 = BitVec.ofNat 32 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s.gpr r = s₀.gpr r
  mem : s.mem = VG.Proof.CmacAes.Stream.Arm.iMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (VG.Proof.CmacAes.Stream.Arm.IMid₁ s₀ St Kp S KL) := by
  have hS := hp.fS
  have hSt := hp.fSt
  rw [VG.Proof.CmacAes.Stream.Arm.initPre_eq]
  refine VG.Arm.Spill.saveList_ok VG.Proof.CmacAes.Stream.Arm.isaved s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have := VG.Proof.CmacAes.Stream.Arm.isaved_bound p hp'
    rw [hp.r3, hp.wr]
    exact ⟨by omega, by omega, ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    WP.block_nil ?_
  have hKL : s₀.gpr .r2 = BitVec.ofNat 32 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.r2, VG.Proof.CmacAes.Stream.Arm.toNat_ofNat32 (by rcases hp.klen with h | h | h <;> omega)])
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have r4 : s₈.gpr .r4 = St := by
    simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁, hp.r0]
  have r5 : s₈.gpr .r5 = S := by
    simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁, hp.r3]
  refine ⟨?_, r4, r5, ?_, by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁], fun r hr h4 h5 h6 => ?_,
    by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hp.r3]; rfl, rd₈, wr₈⟩
  · refine
    { r0 := by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other,
          g₁, hp.r1]
      r1 := by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          g₁, hKL]
      r2 := by rw [u₈.gpr, ← r4, u₈.other _ (by decide)]
      r3 := by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          g₁, hp.r3]
      klen := hp.klen
      kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
      ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      fK := hp.fK, fW := by omega, fS := by omega
      reads := by
        rw [rd₈, wr₈, hp.rd, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨⟨State.addr Kp, KL⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      writes := by
        rw [wr₈, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨State.addr St, 304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
        · exact ⟨⟨State.addr S, 2304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, g₁, hKL]
    exact VG.Proof.CmacAes.Stream.Arm.rounds_bv hp.klen
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h4
    | exact absurd rfl h5
    | exact absurd rfl h6
    | simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁]

/-! ## Between the calls -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : BitVec 32) (KL : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = S
  r6 : s.gpr .r6 = BitVec.ofNat 32 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after {s₀ s : State} {St Kp S : BitVec 32} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) s (IAfter s₀ St S KL) :=
  WP.mono (ek_call h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h.r4],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.r5],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.r6], by rw [h₂.sp, h.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h.keep r hr a b c], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

/-- The subkeys, after the schedule. -/
abbrev Kof (St : BitVec 32) : BitVec 32 := St + BitVec.ofNat 32 240

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : BitVec 32) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.Arm.SArgs s St (VG.Proof.CmacAes.Stream.Arm.Kof St) S (KL / 4 + 6)
  mem : s.mem = m
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = S
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IPre.aK {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.IPre s₀ St Kp S KL) :
    State.addr (VG.Proof.CmacAes.Stream.Arm.Kof St) = State.addr St + BitVec.ofNat 64 240 := addr_add (by have := hp.fSt; omega)

theorem initMid_wp {s₀ s : State} {St Kp S : BitVec 32} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.IPre s₀ St Kp S KL)
    (h : VG.Proof.CmacAes.Stream.Arm.IAfter s₀ St S KL s) : WP isa (.block initMid) s (VG.Proof.CmacAes.Stream.Arm.IMid₂ s₀ St S KL s.mem) := by
  have hSt := hp.fSt
  have hS := hp.fS
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_add (op2_imm (by decide))
    fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₄ : s₄.sp = s₀.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  have kSt : Region.Sub ⟨State.addr (VG.Proof.CmacAes.Stream.Arm.Kof St), 32⟩ ⟨State.addr St, 304⟩ := by
    rw [hp.aK]; exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r4],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r5], sp₄,
    fun r hr a b c d => ?_, rd₄, wr₄⟩
  · exact
    { r0 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h.r4]
      r1 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h.r6]
      r2 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h.r4]; rfl
      r3 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h.r5]
      rounds := hp.rounds
      hsp := by rw [sp₄]; exact hp.sp
      wk := by rw [hp.aK]; exact Offset.base_disjoint _ (by decide) (by omega)
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
      bw := by rw [VG.Proof.CmacAes.Stream.Arm.blw8, sp₄]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
      bk := by rw [VG.Proof.CmacAes.Stream.Arm.blw8, sp₄]; exact hp.b_st.sub_right kSt
      bs := by rw [VG.Proof.CmacAes.Stream.Arm.blw8, sp₄]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
      fW := by omega
      fK := by rw [VG.Proof.CmacAes.Stream.Arm.toNat_add_ofNat (by omega)]; omega
      fS := by omega
      reads := by
        rw [rd₄, wr₄, hp.rd, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨⟨State.addr St, 304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      writes := by
        rw [wr₄, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨State.addr St, 304⟩, by simp, 240, hp.aK, by simp⟩
        · exact ⟨⟨State.addr S, 2304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | (simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other]
       exact h.keep _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide))

/-! ## After the calls -/

theorem initPost_eq : initPost = .mov .r12 (.imm 0) :: (zeroBlk .r12 .r4 272 ++
    ([(.r4, 2176), (.r6, 2184), (.lr, 2188)] : List (Reg × Nat)).map (fun p => Instr.ldr p.1 .r5 p.2) ++
    ([.ldr .r5 .r5 2180] : List Instr)) := rfl

/-- The memory after zeroing the chaining value. -/
abbrev zcv (m : Mem) (St : BitVec 32) : Mem := Proof.Cmac.zero4 m (State.addr St + BitVec.ofNat 64 272)

theorem initPost_wp {s : State} {St S : BitVec 32} (hSt : St.toNat + 304 ≤ 2 ^ 32) (hS : S.toNat + 2304 ≤ 2 ^ 32)
    (h4 : s.gpr .r4 = St) (h5 : s.gpr .r5 = S)
    (w : Covers [⟨State.addr St + BitVec.ofNat 64 272, 16⟩] s.wr)
    (r : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 d) 4) :
    WP isa (.block initPost) s fun s' =>
      s'.gpr .r4 = (VG.Proof.CmacAes.Stream.Arm.zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2176) 32 ∧
      s'.gpr .r5 = (VG.Proof.CmacAes.Stream.Arm.zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2180) 32 ∧
      s'.gpr .r6 = (VG.Proof.CmacAes.Stream.Arm.zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2184) 32 ∧
      s'.gpr .lr = (VG.Proof.CmacAes.Stream.Arm.zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2188) 32 ∧
      (∀ x, x ≠ .r4 → x ≠ .r5 → x ≠ .r6 → x ≠ .lr → x ≠ .r12 → s'.gpr x = s.gpr x) ∧
      s'.sp = s.sp ∧ s'.mem = VG.Proof.CmacAes.Stream.Arm.zcv s.mem St := by
  rw [VG.Proof.CmacAes.Stream.Arm.initPost_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine zeroBlk_ok (by rw [u₁.gpr]) (by decide) (by rw [u₁.other _ (by decide), h4]; omega)
    (by rw [u₁.wr, u₁.other _ (by decide), h4]; exact w) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have e5 : s₂.gpr .r5 = S := by rw [g₂, u₁.other _ (by decide), h5]
  have mm : s₂.mem = VG.Proof.CmacAes.Stream.Arm.zcv s.mem St := by rw [m₂, u₁.mem, u₁.other _ (by decide), h4]
  refine Spill.restoreList_ok [(.r4, 2176), (.r6, 2184), (.lr, 2188)] s₂ _ (by decide) (fun p hp' => ?_) fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [e5, rd₂, wr₂, u₁.rd, u₁.wr]
    rcases hp' with rfl | rfl | rfl
    · exact ⟨by decide, by decide, by omega, r _ (by decide) (by decide)⟩
    · exact ⟨by decide, by decide, by omega, r _ (by decide) (by decide)⟩
    · exact ⟨by decide, by decide, by omega, r _ (by decide) (by decide)⟩
  refine wp_ldr (a := State.addr S + BitVec.ofNat 64 2180) (by decide)
    (by rw [ho₃ _ (by decide), e5]; exact addr_add (by omega))
    (by rw [rd₃, wr₃, rd₂, wr₂, u₁.rd, u₁.wr]; exact r _ (by decide) (by decide)) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun x a b c d e => ?_, by rw [u₄.sp, sp₃, sp₂, u₁.sp], by rw [u₄.mem, m₃, mm]⟩
  · rw [u₄.other _ (by decide), ld₃ (.r4, 2176) (by simp), e5, mm]
  · rw [u₄.gpr, m₃, mm]
  · rw [u₄.other _ (by decide), ld₃ (.r6, 2184) (by simp), e5, mm]
  · rw [u₄.other _ (by decide), ld₃ (.lr, 2188) (by simp), e5, mm]
  · rw [u₄.other _ b, ho₃ _ (by simp [a, c, d]), g₂, u₁.other _ e]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize s₀.gpr .r1 = Kp at hp
  generalize s₀.gpr .r3 = S at hp
  generalize (s₀.gpr .r2).toNat = KL at hp
  have hSt := hp.fSt
  have hS := hp.fS
  have hR := hp.rounds
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.ek_call h₁.args) fun s₂ h₂ => ?_)
  have a₂ : VG.Proof.CmacAes.Stream.Arm.IAfter s₀ St S KL s₂ :=
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.r4],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.r5],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.r6], by rw [h₂.sp, h₁.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h₁.keep r hr a b c], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr]⟩
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.initMid_wp hp a₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.Arm.sub_call h₃.args) fun s₄ h₄ => ?_)
  have rdwr₄ : s₄.rd ++ s₄.wr = [⟨State.addr Kp, KL⟩, ⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩] := by
    rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, hp.rd, hp.wr]; rfl
  refine WP.mono (VG.Proof.CmacAes.Stream.Arm.initPost_wp (s := s₄) hSt hS
    (by rw [h₄.saved _ (by simp [preserved]) (by decide), h₃.r4])
    (by rw [h₄.saved _ (by simp [preserved]) (by decide), h₃.r5])
    (by
      rw [h₄.wr, h₃.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr St, 304⟩, by simp, 272, rfl, by simp⟩)
    (fun d _ hd => by
      rw [rdwr₄]; exact ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩))
    fun s₅ ⟨r4₅, r5₅, r6₅, lr₅, g₅, sp₅, m₅⟩ => ?_
  -- The memory, step by step.
  have f₁ : Frame [⟨State.addr S, 2304⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact VG.Proof.CmacAes.Stream.Arm.iMem_frame _ _
  have f₂ := h₂.frame
  have f₄ := h₄.frame
  have fz : Frame [⟨State.addr St + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  have sp₃ : s₃.sp = s₀.sp := h₃.sp
  have aK := hp.aK
  -- The saved registers.
  have slot (d : Nat) (hd : 2176 ≤ d) (hd' : d + 4 ≤ 2192) :
      (VG.Proof.CmacAes.Stream.Arm.zcv s₄.mem St).readW (State.addr S + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacAes.Stream.Arm.iMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
    have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 2304⟩ := Offset.sub_base _ (by omega)
    have c := Region.contains_self (State.addr S + BitVec.ofNat 64 d) 4
    rw [← m₅, fz.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub) (by decide),
      f₄.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [aK]; exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
        · exact Offset.disjoint_base _ hd (by omega)
        · rw [VG.Proof.CmacAes.Stream.Arm.blw8, sp₃]; exact (hp.b_s.sub_right sub).symm) (by decide), m₃,
      f₂.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), h₁.mem]
  have keep₄ : ∀ x ∈ preserved, x ≠ .r4 → x ≠ .r5 → x ≠ .r6 → x ≠ .lr → s₄.gpr x = s₀.gpr x :=
    fun x hx a b c d => by rw [h₄.saved x hx d, h₃.keep x hx a b c d]
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, h₄.sp, sp₃]⟩, ?_⟩
  · have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r4₅, slot 2176 (by decide) (by decide), VG.Proof.CmacAes.Stream.Arm.iMem_slot s₀ S (r := .r4) (d := 2176) (by decide)]
    · rw [r5₅, slot 2180 (by decide) (by decide), VG.Proof.CmacAes.Stream.Arm.iMem_slot s₀ S (r := .r5) (d := 2180) (by decide)]
    · rw [r6₅, slot 2184 (by decide) (by decide), VG.Proof.CmacAes.Stream.Arm.iMem_slot s₀ S (r := .r6) (d := 2184) (by decide)]
    all_goals first
      | rw [lr₅, slot 2188 (by decide) (by decide), VG.Proof.CmacAes.Stream.Arm.iMem_slot s₀ S (r := .lr) (d := 2188) (by decide)]
      | rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide),
          keep₄ _ hr' (by decide) (by decide) (by decide) (by decide)]
  · show Spec.Cmac.Repr s₅.mem (State.addr (s₀.gpr .r0))
      (Spec.Aes.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) []
    rw [hp.r0, hp.r1, hp.r2, Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem (State.addr Kp) KL = Spec.Aes.bytesAt s₀.mem (State.addr Kp) KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s) (by have := hp.fK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr Kp) KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
    -- The schedule, from the first call on.
    have sch : Spec.Aes.bytesAt s₅.mem (State.addr St) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.bytesAt s₂.mem (State.addr St) (16 * (Spec.Aes.rounds (KL / 4) + 1)) := by
      have sub : Region.Sub ⟨State.addr St, 16 * (Spec.Aes.rounds (KL / 4) + 1)⟩ ⟨State.addr St, 304⟩ :=
        Region.sub_prefix (by omega)
      rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint _ (by omega) (by decide))
          (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [aK]; exact Offset.base_disjoint _ (by omega) (by decide)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · rw [VG.Proof.CmacAes.Stream.Arm.blw8, sp₃]; exact (hp.b_st.sub_right sub).symm) (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem (State.addr St) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (State.addr Kp) KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, by rw [hlen, sch, hsch], ?_⟩, ?_, ?_⟩
    · show Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 240) 32 = _
      rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
          (by decide), ← aK, h₄.out, m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · show Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 272) 16 = _
      rw [m₅]; exact Proof.Cmac.zero4_bytes _ _
    · simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]

/-! ## Constant time -/

theorem init_rel {s₀ s₀' : State} (h0 : initArm.pre s₀) (h0' : initArm.pre s₀') (hq : initArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := IPre.of h0
  have hp' : VG.Proof.CmacAes.Stream.Arm.IPre s₀' (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r3) (s₀.gpr .r2).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h0'
  generalize s₀.gpr .r0 = St at hp hp'
  generalize s₀.gpr .r1 = Kp at hp hp'
  generalize s₀.gpr .r3 = S at hp hp'
  generalize (s₀.gpr .r2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) (.block initPre) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5, .r6]) (.block initMid) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.CmacAes.Stream.Arm.IMid₁ s₀ St Kp S KL)
    (G' := VG.Proof.CmacAes.Stream.Arm.IMid₁ s₀' St Kp S KL) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.CmacAes.Stream.Arm.initPre_wp hp) (fun s e => by rw [e]; exact VG.Proof.CmacAes.Stream.Arm.initPre_wp hp')
  have e := rel_wp (F := VG.Proof.CmacAes.Stream.Arm.IMid₁ s₀ St Kp S KL) (F' := VG.Proof.CmacAes.Stream.Arm.IMid₁ s₀' St Kp S KL) (G := VG.Proof.CmacAes.Stream.Arm.IAfter s₀ St S KL)
    (G' := VG.Proof.CmacAes.Stream.Arm.IAfter s₀' St S KL) (VG.Proof.CmacAes.Stream.Arm.ek_rel fun _ _ h => ⟨h.1.args, h.2.args⟩) (fun _ h => VG.Proof.CmacAes.Stream.Arm.ek_after h)
    (fun _ h => VG.Proof.CmacAes.Stream.Arm.ek_after h)
  have m := rel_agree (F := VG.Proof.CmacAes.Stream.Arm.IAfter s₀ St S KL) (F' := VG.Proof.CmacAes.Stream.Arm.IAfter s₀' St S KL)
    (G := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.IMid₂ s₀ St S KL m s) (G' := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.IMid₂ s₀' St S KL m s)
    (Taint.ofRegs [.r4, .r5, .r6])
    (fun s s' h h' => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.r4, h'.r4]
      · rw [h.r5, h'.r5]
      · rw [h.r6, h'.r6]) ⟨_, hB⟩
    (fun s h => WP.mono (VG.Proof.CmacAes.Stream.Arm.initMid_wp hp h) fun _ h => ⟨_, h⟩)
    (fun s h => WP.mono (VG.Proof.CmacAes.Stream.Arm.initMid_wp hp' h) fun _ h => ⟨_, h⟩)
  have sk := rel_wp (F := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.IMid₂ s₀ St S KL m s) (F' := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.IMid₂ s₀' St S KL m s)
    (G := fun s => s.gpr .r4 = St ∧ s.gpr .r5 = S) (G' := fun s => s.gpr .r4 = St ∧ s.gpr .r5 = S)
    (VG.Proof.CmacAes.Stream.Arm.sub_rel (sp₀ := s₀.sp) fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨h₁.args, h₂.args, h₁.sp, h₂.sp.trans q1.symm⟩)
    (fun _ ⟨_, h⟩ => WP.mono (VG.Proof.CmacAes.Stream.Arm.sub_call h.args) fun _ h' =>
      ⟨by rw [h'.saved _ (by simp [preserved]) (by decide), h.r4],
        by rw [h'.saved _ (by simp [preserved]) (by decide), h.r5]⟩)
    (fun _ ⟨_, h⟩ => WP.mono (VG.Proof.CmacAes.Stream.Arm.sub_call h.args) fun _ h' =>
      ⟨by rw [h'.saved _ (by simp [preserved]) (by decide), h.r4],
        by rw [h'.saved _ (by simp [preserved]) (by decide), h.r5]⟩)
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .r4 = St ∧ a.gpr .r5 = S) ∧ b.gpr .r4 = St ∧ b.gpr .r5 = S)
    (Taint.ofRegs [.r4, .r5]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hC
  exact a.seq (e.seq (m.seq (sk.seq p)))

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.Arm.init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Verified`. -/
section

section

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from the public arguments for
`absorbPre` and from the registers the correctness proof pins to values of the
public arguments afterwards (`AAfter₁`, `AAfter₂`), and each call of
`vg_cmac_aes_update`, in its frame, is constant time by its own proof
(`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem APre.wfA {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.Arm.APre s₀ St D S L R) :
    s₀.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 12⟩ r := by
  have e : (⟨State.addr s₀.sp, 12⟩ : Region) = ⟨stackArgAddr s₀ 0, 12⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.a_st
  · exact hp.a_s

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbArm.pre s₀) (h0' : absorbArm.pre s₀')
    (hq : absorbArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have hp := APre.of h0
  have hp' : VG.Proof.CmacAes.Stream.Arm.APre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat (s₀.gpr .r1).toNat := by
    rw [q2, q3, q6, q7, q8]; exact APre.of h0'
  have hc : (VG.Proof.CmacAes.Stream.Arm.countArm s₀').toNat = (VG.Proof.CmacAes.Stream.Arm.countArm s₀).toNat := by simp only [VG.Proof.CmacAes.Stream.Arm.countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = D at hp hp'
  generalize stackArg s₀ 2 = S at hp hp'
  generalize (stackArg s₀ 1).toNat = L at hp hp'
  generalize (s₀.gpr .r1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 12) absorbPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7, .r10]) chain2 h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r6, .r7, .r8, .r10]) absorbPost h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀ St D S L R)
    (G' := VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀' St D S L R) (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 3) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact q6
        · exact q7
        · exact q8) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.CmacAes.Stream.Arm.absorbPre_wp hp) (fun s e => by rw [e]; exact VG.Proof.CmacAes.Stream.Arm.absorbPre_wp hp')
  have c₁ := rel_wp (F := VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀ St D S L R) (F' := VG.Proof.CmacAes.Stream.Arm.AMid₁ s₀' St D S L R) (G := VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀ St D S L)
    (G' := VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀' St D S L)
    (VG.Proof.CmacAes.Stream.Arm.upd_rel (sp₀ := s₀.sp) fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩)
    (fun _ h => VG.Proof.CmacAes.Stream.Arm.call1_after h) (fun _ h => VG.Proof.CmacAes.Stream.Arm.call1_after h)
  have m := rel_agree (F := VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀ St D S L) (F' := VG.Proof.CmacAes.Stream.Arm.AAfter₁ s₀' St D S L)
    (G := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀ St D S L R m s) (G' := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀' St D S L R m s)
    (Taint.ofRegs [.r4, .r5, .r6, .r7, .r10])
    (fun s s' h h' => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.r4, h'.r4]
      · rw [h.r5, h'.r5, q3]
      · rw [h.r6, h'.r6, hc]
      · rw [h.r7, h'.r7, hc]
      · rw [h.r10, h'.r10]) ⟨_, hB⟩
    (fun s h => WP.mono (VG.Proof.CmacAes.Stream.Arm.chain2_mid hp h) fun _ h => ⟨_, h⟩)
    (fun s h => WP.mono (VG.Proof.CmacAes.Stream.Arm.chain2_mid hp' h) fun _ h => ⟨_, h⟩)
  have c₂ := rel_wp (F := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀ St D S L R m s) (F' := fun s => ∃ m, VG.Proof.CmacAes.Stream.Arm.AMid₂ s₀' St D S L R m s)
    (G := VG.Proof.CmacAes.Stream.Arm.AAfter₂ s₀ St D S L) (G' := VG.Proof.CmacAes.Stream.Arm.AAfter₂ s₀' St D S L)
    (VG.Proof.CmacAes.Stream.Arm.upd_rel (sp₀ := s₀.sp) fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨h₁.args, by rw [← hc]; exact h₂.args, h₁.sp, h₂.sp.trans q1.symm⟩)
    (fun _ ⟨_, h⟩ => VG.Proof.CmacAes.Stream.Arm.call2_after h) (fun _ ⟨_, h⟩ => VG.Proof.CmacAes.Stream.Arm.call2_after h)
  have p := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.Arm.AAfter₂ s₀ St D S L a ∧ VG.Proof.CmacAes.Stream.Arm.AAfter₂ s₀' St D S L b)
    (Taint.ofRegs [.r4, .r6, .r7, .r8, .r10]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r4, h.2.r4]
      · rw [h.1.r6, h.2.r6, hc]
      · rw [h.1.r7, h.2.r7, hc]
      · rw [h.1.r8, h.2.r8, hc]
      · rw [h.1.r10, h.2.r10]) hC
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbArm.pre absorbArm.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.Arm.absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.Arm

end

/-!
# Streaming AES-CMAC on ARMv7: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`: with 8 bytes of stack for
`init` (the frame of `vg_cmac_aes_subkeys`), and 16 for `absorb` and `finish`
(the stack arguments they push, and the frame of the function they call below
them).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 16 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified Arm.target init (initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.Stream.Arm.init_wp hs) VG.Proof.CmacAes.Stream.Arm.init_ct (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, VG.Proof.CmacAes.Stream.Arm.initArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat] using VG.Proof.CmacAes.Stream.Arm.initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data):
`state` at `0x1000`, `data` at `0x3000`, `scratch` at `0x4000`, the stack
arguments at `0x8000`. -/
def absorbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else if a = 0x8009 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified Arm.target absorb (absorbScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.Stream.Arm.absorb_wp hs) VG.Proof.CmacAes.Stream.Arm.absorb_ct (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, VG.Proof.CmacAes.Stream.Arm.absorbArm, VG.Proof.CmacAes.Stream.Arm.countArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Stream.Arm.absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition: `state` at
`0x1000`, `out` at `0x2000`, `scratch` at `0x4000`, the stack arguments at
`0x8000`. -/
def finishSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8005 then 0x40 else 0
  rd := [⟨0x8000, 8⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified Arm.target finish (finishScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.Stream.Arm.finish_wp hs) VG.Proof.CmacAes.Stream.Arm.finish_ct (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, VG.Proof.CmacAes.Stream.Arm.finishArm, VG.Proof.CmacAes.Stream.Arm.countArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Stream.Arm.finishSat)

end VG.Proof.CmacAes.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame`. -/
section

/-!
# Streaming AES-CMAC on ARMv7, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is its fourth argument, in `r3`: its frame is the 2304 bytes of
working space (`Verified.regScratch`). That of `absorb` and `finish` follows
their arguments on the stack (`data` and `len`, `out`): their frames copy
those and hold the saved registers too, 2320 bytes (`Verified.stackScratch`).
The copies are read only where the pre- and postconditions read the buffers
(`Proof/CmacAes/Stream/Scratch.lean`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { VG.Proof.CmacAes.Stream.Arm.initSat with
                                           wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract Arm.abi 2312).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSat] using VG.Proof.CmacAes.Stream.Arm.initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { VG.Proof.CmacAes.Stream.Arm.absorbSat with
                   rd := [⟨0x3000, 0⟩, ⟨0x8000, 8⟩], wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract Arm.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, VG.Proof.CmacAes.Stream.Arm.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [absorbFrameSat, absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.CmacAes.Stream.Arm.absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space: as `finishSat`. -/
def finishFrameSat : State :=
  { VG.Proof.CmacAes.Stream.Arm.finishSat with
                   rd := [⟨0x8000, 4⟩], wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract Arm.abi 2336).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, VG.Proof.CmacAes.Stream.Arm.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [finishFrameSat, finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.CmacAes.Stream.Arm.finishFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2304 .r3 init)
    (Spec.Cmac.aesInitContract Arm.abi 2312) :=
  Arm.Verified.regScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesInitPre Arm.abi.ptrBits) (post := Spec.Cmac.aesInitPost Arm.abi.ptrBits)
    (wa := false) (stack := 8) VG.Proof.CmacAes.Stream.Arm.init_verified (by decide) (by decide) (by decide) VG.Proof.CmacAes.Stream.Arm.initFrameSat_pre

theorem absorb_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2320 2 absorb)
    (Spec.Cmac.aesAbsorbContract Arm.abi 2336) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesAbsorbPre Arm.abi.ptrBits) (post := Spec.Cmac.aesAbsorbPost Arm.abi.ptrBits)
    (wa := false) (stack := 16) (m := 2) VG.Proof.CmacAes.Stream.Arm.absorb_verified (by decide) (by decide) (by decide)
    (by decide) (absorbPre_local _) (absorbPost_local _) VG.Proof.CmacAes.Stream.Arm.absorbFrameSat_pre

theorem finish_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2320 1 finish)
    (Spec.Cmac.aesFinishContract Arm.abi 2336) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesFinishPre Arm.abi.ptrBits) (post := Spec.Cmac.aesFinishPost Arm.abi.ptrBits)
    (wa := false) (stack := 16) (m := 1) VG.Proof.CmacAes.Stream.Arm.finish_verified (by decide) (by decide) (by decide)
    (by decide) (finishPre_local _) (finishPost_local _) VG.Proof.CmacAes.Stream.Arm.finishFrameSat_pre

end VG.Proof.CmacAes.Stream.Arm

end
