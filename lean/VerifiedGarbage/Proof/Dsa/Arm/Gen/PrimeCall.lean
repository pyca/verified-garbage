module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PrimeIface
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Tape
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ReadHalves

/-! # DSA parameter generation on ARMv7: calling the probable-prime test

`primeCall_vp`: `callWith name code`, its stack argument (the count's
address, in `r4`) pushed, calls the test on the candidate at `sA` with the
witnesses from `u` on: its status in `r0`, its count in the frame word
`fUsedOut` when the tape sufficed, and `scratch` changed only from `sA` to the
key working space.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)
open VG.Proof.X25519.Arm (Rest Upd Mupd)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Arm.FrameStack (armStack belowA)

/-- The words a call pushes. -/
abbrev callPush : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- A push's first word is its first register. -/
theorem pushed_arg0 {s : State} {r : Reg} {rs : List Reg} (h : 4 * (rs.length + 1) ≤ s.sp.toNat) :
    stackArg (pushed (r :: rs) s) 0 = s.gpr r := by
  have hs := FrameStack.sub_toNat' h
  have := s.sp.isLt
  simp only [stackArg, stackArgAddr, pushed, List.map_cons, storeWords, Nat.mul_zero, BitVec.add_zero,
    List.length_cons]
  generalize s.sp - BitVec.ofNat 32 (4 * (rs.length + 1)) = a at hs ⊢
  have ha : a.toNat + 4 * (rs.length + 1) ≤ 2 ^ 32 := by rw [hs]; omega
  have h4 : (a + 4).toNat = a.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [(FrameStack.storeWords_frame (rs.map s.gpr) _ (a + 4) (by rw [h4, List.length_map]; omega)).readW
    (r := ⟨State.addr a, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add (by omega)]
      exact (Offset.disjoint_base _ (Nat.le_refl 4) (by
        have := VG.Proof.X25519.Arm.addr_toNat a; rw [List.length_map]; omega)).symm)
    (by decide), Mem.readW_writeW_self32]

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

theorem GI.sp176 (h : GI G σ V LS s) : 176 ≤ G.sp.toNat := by
  have := h.spN; have := h.pre.spLo; simp only [F] at *; omega

/-- The witnesses from `u` on. -/
abbrev GP.rRand (G : GP) (u : Nat) : Region :=
  ⟨State.addr (G.wit + BitVec.ofNat 32 u), (BitVec.ofNat 32 (G.witLen - u)).toNat⟩

theorem GI.witFit (h : GI G σ V LS s) : G.wit.toNat + G.witLen ≤ 2 ^ 32 := by
  have := h.pre.nW; rw [← h.hG]; exact this

theorem GI.witLt (h : GI G σ V LS s) : G.witLen < 2 ^ 32 := by
  rw [← h.hG]; exact (stackArg σ 5).isLt

theorem GI.randLen (h : GI G σ V LS s) (u : Nat) : (BitVec.ofNat 32 (G.witLen - u)).toNat = G.witLen - u := by
  have := h.witLt; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem GI.randSub (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : Region.Sub (G.rRand u) G.rWit := by
  have := h.witFit
  rw [GP.rRand, h.randLen]
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [addr_add (by omega)]; exact Offset.sub_base _ (by omega)
  · rw [show G.witLen - u = 0 by omega]
    intro a ha; simp [Region.Contains] at ha

theorem GI.randFit (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.wit + BitVec.ofNat 32 u).toNat + (G.witLen - u) ≤ 2 ^ 32 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have := (G.wit + BitVec.ofNat 32 u).isLt; omega

/-- The stack the call uses, below the frame: the pushed words and the test's 144 bytes. -/
theorem GI.pushSub (h : GI G σ V LS s) :
    Region.Sub (belowA G.sp 32) G.rBelow := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32), 32⟩ ⟨State.addr G.sp - 176#64, 176⟩
  rw [FrameStack.addr_sub' (by omega)]
  exact Offset.sub_below _ (by omega) (by omega)

theorem GI.testSub (h : GI G σ V LS s) :
    Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length)) - 144#64, 144⟩ G.rBelow := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32) - BitVec.ofNat 64 144, 144⟩ ⟨State.addr G.sp - 176#64, 176⟩
  rw [FrameStack.addr_sub' (by omega), BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem GI.argSub (h : GI G σ V LS s) :
    Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 4⟩
      (belowA G.sp 32) := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32 + 0#32), 4⟩ ⟨State.addr (G.sp - BitVec.ofNat 32 32), 32⟩
  rw [BitVec.add_zero]; exact fun _ h => by simp only [Region.Contains] at h ⊢; omega

/-- The count's 8 bytes. -/
theorem GI.usedAddr (h : GI G σ V LS s) :
    State.addr (G.sp + BitVec.ofNat 32 fUsedOut) = State.addr G.sp + BitVec.ofNat 64 fUsedOut := by
  have := h.spHi; exact addr_add (by simp only [fUsedOut, F] at *; omega)

/-- The test's arguments, in `r0`–`r4`. -/
abbrev TArgs (G : GP) (L u : Nat) (s : State) : Prop :=
  s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa L / 8) ∧
  s.gpr .r2 = G.wit + BitVec.ofNat 32 u ∧ s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧
  s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut

/-- The regions the test is given. -/
abbrev tRd (G : GP) (u : Nat) : List Region :=
  [G.rRand u, ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 4⟩]
abbrev tWr (G : GP) (L : Nat) : List Region :=
  [⟨State.addr (G.scr + BitVec.ofNat 32 sA), (BitVec.ofNat 32 (wa L / 8)).toNat * 8⟩,
    ⟨State.addr (G.sp + BitVec.ofNat 32 fUsedOut), 8⟩]

/-- The test's entry. -/
abbrev tEntry (G : GP) (L u : Nat) (s : State) : State := (pushed callPush s).callEntry.withRegions (tRd G u) (tWr G L)

theorem wa_toNat {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : (BitVec.ofNat 32 (wa L / 8)).toNat * 8 = wa L := by
  simp only [wa]; rcases hL with rfl | rfl | rfl <;> decide

theorem tEntry_gpr {G : GP} {L u : Nat} {s : State} {r : Reg} (hr : r ∉ linkRegs) :
    (tEntry G L u s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem tEntry_sp {G : GP} {L u : Nat} {s : State} :
    (tEntry G L u s).sp = s.sp - BitVec.ofNat 32 (4 * callPush.length) := rfl

theorem tEntry_mem {G : GP} {L u : Nat} {s : State} : (tEntry G L u s).mem = (pushed callPush s).mem := rfl

variable {c : Cfg}

theorem SS.tEntry_arg0 (h : SS G σ c s) {L u : Nat} (regs : TArgs G L u s) :
    stackArg (tEntry G L u s) 0 = G.sp + BitVec.ofNat 32 fUsedOut := by
  have := h.gi.sp176
  show stackArg (pushed (.r4 :: [.r5, .r6, .r7, .r8, .r9, .r10, .r11]) s) 0 = _
  rw [pushed_arg0 (by rw [h.gi.sp]; show 4 * (7 + 1) ≤ G.sp.toNat; omega), regs.2.2.2.2]

/-- The pushed words leave `scratch`. -/
theorem SS.push_scr (h : SS G σ c s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) {k : Nat} (hk : k < n) :
    (pushed callPush s).mem (G.sa o + BitVec.ofNat 64 k) = s.mem (G.sa o + BitVec.ofNat 64 k) := by
  have := h.gi.sp176
  refine (FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [h.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega)).bytes
    (R := G.rs o n) (fun r hr => ?_) (by have := h.gi.scrFit; show n ≤ 2 ^ 64; omega) hk
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.gi.sp]
  exact (h.gi.scr_below ho).sub_right h.gi.pushSub

/-- The test's arguments meet its precondition. -/
theorem SS.tEntry_pin (h : SS G σ c s) {L u bits : Nat} (hL : L = G.pLen) (regs : TArgs G L u s)
    (hu : u ≤ G.witLen) (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) :
    PIn bits (tEntry G L u s) := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  have spHi := gi.spHi
  have hLv := h.lens
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  obtain ⟨r0, r1, r2, r3, r4⟩ := regs
  have sp : s.sp = G.sp := gi.sp
  have esp : (tEntry G L u s).sp = G.sp - BitVec.ofNat 32 32 := by rw [tEntry_sp, sp]; rfl
  have espN : (tEntry G L u s).sp.toNat = G.sp.toNat - 32 := by rw [esp, FrameStack.sub_toNat' (by omega)]
  have a0 := h.tEntry_arg0 (L := L) ⟨r0, r1, r2, r3, r4⟩
  have e0 : (tEntry G L u s).gpr .r0 = G.scr + BitVec.ofNat 32 sA := by rw [tEntry_gpr (by decide), r0]
  have e1 : (tEntry G L u s).gpr .r1 = BitVec.ofNat 32 (wa L / 8) := by rw [tEntry_gpr (by decide), r1]
  have e2 : (tEntry G L u s).gpr .r2 = G.wit + BitVec.ofNat 32 u := by rw [tEntry_gpr (by decide), r2]
  have e3 : (tEntry G L u s).gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by rw [tEntry_gpr (by decide), r3]
  subst hL
  have wl := wa_toNat hLv
  have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega)
    (by simp only [wa]; omega)
  have aA : stackArgAddr (tEntry G G.pLen u s) 0 =
      State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)) := by
    rw [stackArgAddr, esp]; rfl
  -- The regions, as the search sees them.
  have scrW : Region.Sub ⟨State.addr (G.scr + BitVec.ofNat 32 sA), (BitVec.ofNat 32 (wa G.pLen / 8)).toNat * 8⟩
      G.rScr := by rw [aS, wl]; exact sw G (by simp only [sK] at big; omega)
  have usedF : Region.Sub ⟨State.addr (G.sp + BitVec.ofNat 32 fUsedOut), 8⟩ G.rFrame := by
    rw [gi.usedAddr]; exact Offset.sub_base _ (by simp only [fUsedOut, F]; omega)
  have argB : Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 4⟩
      G.rBelow := fun a ha => gi.pushSub a (gi.argSub a ha)
  have randW := gi.randSub hu
  have pre := gi.pre
  have fW := pre.fW; have wC := pre.wC; rw [gi.hG] at fW wC
  have stk : Region.Sub ⟨State.addr (tEntry G G.pLen u s).sp - 144#64, 144⟩ G.rBelow := by
    rw [esp]; exact gi.testSub
  have sv := pre.spLo
  refine ⟨by omega, by omega, by rw [State.withRegions_rd, e2, e3, aA], by rw [State.withRegions_wr, e0, e1, a0],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, e1, e2, e3]; exact (wC.symm.sub_left scrW).sub_right randW
  · rw [e0, e1, a0]; exact (gi.frame_scr.symm.sub_left scrW).sub_right usedF
  · rw [e0, e1, aA]; exact ((gi.scr_below (o := sA) (n := wa G.pLen) (by simp only [sK] at big; omega)).sub_left
      (by rw [aS, wl]; exact fun _ h => h)).sub_right argB
  · rw [e2, e3, a0]; exact ((fW.symm.sub_left randW).sub_right gi.frameSub).sub_right usedF
  · rw [a0, aA]; exact (gi.frame_below.sub_left usedF).sub_right argB
  · rw [e0, e1]; exact ((gi.scr_below (o := sA) (n := wa G.pLen) (by simp only [sK] at big; omega)).sub_left
      (by rw [aS, wl]; exact fun _ h => h)).symm.sub_left stk
  · rw [e2, e3]; exact ((fW.symm.sub_left randW).sub_right gi.belowSub).symm.sub_left stk
  · rw [a0]; exact (gi.frame_below.sub_left usedF).symm.sub_left stk
  · rw [aA, esp]
    have : State.addr (G.sp - BitVec.ofNat 32 32 + BitVec.ofNat 32 (4 * 0)) = State.addr (G.sp - BitVec.ofNat 32 32) := by
      rw [Nat.mul_zero, BitVec.add_zero]
    rw [show (4 * callPush.length) = 32 from rfl, this]
    exact (Offset.base_disjoint_below _ (n := 144) (k := 4) (by omega)).symm
  · rw [e0, e1, wl, h.toNat (by simp only [sK]; omega)]; simp only [sK] at big; omega
  · rw [e2, e3, gi.randLen]; exact gi.randFit hu
  · rw [a0, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by decide),
      Nat.mod_eq_of_lt (by simp only [fUsedOut, F] at *; omega)]; simp only [fUsedOut, F] at *; omega
  · rw [e1]; have := wl; omega
  all_goals
    have hc : candOf bits (tEntry G G.pLen u s) = Spec.Dsa.decodeBE cb := by
      show Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (pushed callPush s).mem
        (State.addr ((tEntry G G.pLen u s).gpr .r0) + BitVec.ofNat 64 0) (bits / 8)) = _
      rw [e0, aS, BitVec.add_zero, ← hcb]
      refine congrArg _ (List.map_congr_left fun k hk => ?_)
      exact h.push_scr (o := sA) (n := bits / 8) (by simp only [sK] at big; omega) (List.mem_range.mp hk)
    rw [hc]
  · exact hodd
  · exact hbl

end

end VG.Proof.Dsa.Arm.Gen
