module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PrimeIface
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Tape
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT

/-! # DSA parameter generation on ARMv7: calling the probable-prime test

`primeCall_vp`: `callWith name code`, its stack arguments (the count's
address, in `r4`, and the size, in `r5`) pushed, calls the test on the
candidate at `sA` with the witnesses from `u` on: its status in `r0`, its count in the frame word
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
  have ha : a.toNat + 4 * (rs.length + 1) ≤ 2 ^ 32 := by rw [hs]; omega_arith
  have h4 : (a + 4).toNat = a.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [(FrameStack.storeWords_frame (rs.map s.gpr) _ (a + 4) (by rw [h4, List.length_map]; omega_arith)).readW
    (r := ⟨State.addr a, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add (by omega_arith)]
      exact (Offset.disjoint_base _ (Nat.le_refl 4) (by
        have := VG.Proof.X25519.Arm.addr_toNat a; rw [List.length_map]; omega_arith)).symm)
    (by decide), Mem.readW_writeW_self32]

/-- A push's word at `b` is its first register. -/
theorem storeWords_head (m : Mem) (b v : BitVec 32) (vs : List (BitVec 32))
    (h : b.toNat + 4 * (vs.length + 1) < 2 ^ 32) : (storeWords m b (v :: vs)).readW (State.addr b) 32 = v := by
  have h4 : (b + 4).toNat = b.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [storeWords, (FrameStack.storeWords_frame vs _ (b + 4) (by rw [h4]; omega_arith)).readW
    (r := ⟨State.addr b, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add (by omega_arith)]
      exact (Offset.disjoint_base _ (Nat.le_refl 4) (by
        have := VG.Proof.X25519.Arm.addr_toNat b; omega_arith)).symm)
    (by decide), Mem.readW_writeW_self32]

/-- A push's second word is its second register. -/
theorem pushed_arg1 {s : State} {r r' : Reg} {rs : List Reg} (h : 4 * (rs.length + 2) ≤ s.sp.toNat) :
    stackArg (pushed (r :: r' :: rs) s) 1 = s.gpr r' := by
  have hs := FrameStack.sub_toNat' h
  have := s.sp.isLt
  show (storeWords ((s.mem).writeW (State.addr (s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)))) (s.gpr r))
    (s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)) + 4) (s.gpr r' :: rs.map s.gpr)).readW
    (State.addr (s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)) + 4)) 32 = _
  generalize s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)) = a at hs ⊢
  have ha : a.toNat + 4 * (rs.length + 2) < 2 ^ 32 := by rw [hs]; omega_arith
  have h4 : (a + 4).toNat = a.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  exact storeWords_head _ _ _ _ (by rw [h4, List.length_map]; omega_arith)

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

theorem GI.sp176 (h : GI G σ V LS s) : 176 ≤ G.sp.toNat := by
  have := h.spN; have := h.pre.spLo; simp only [F] at *; omega_arith

/-- Where the witnesses from `u` on start: `witnesses` itself when none is left. -/
abbrev GP.randP (G : GP) (u : Nat) : BitVec 32 := if u = G.witLen then G.wit else G.wit + BitVec.ofNat 32 u

/-- The witnesses from `u` on. -/
abbrev GP.rRand (G : GP) (u : Nat) : Region :=
  ⟨State.addr (G.randP u), (BitVec.ofNat 32 (G.witLen - u)).toNat⟩

theorem GI.witFit (h : GI G σ V LS s) : G.wit.toNat + G.witLen ≤ 2 ^ 32 := by
  have := h.pre.nW; rw [← h.hG]; exact this

theorem GI.witLt (h : GI G σ V LS s) : G.witLen < 2 ^ 32 := by
  rw [← h.hG]; exact (stackArg σ 5).isLt

theorem GI.randLen (h : GI G σ V LS s) (u : Nat) : (BitVec.ofNat 32 (G.witLen - u)).toNat = G.witLen - u := by
  have := h.witLt; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem GI.randAddr (h : GI G σ V LS s) {u : Nat} (hu : u < G.witLen) :
    State.addr (G.randP u) = State.addr G.wit + BitVec.ofNat 64 u := by
  have := h.witFit
  rw [GP.randP, ite_eq_right (by omega_arith)]; exact addr_add (by omega_arith)

/-- The witnesses from `u` on are within the tape. -/
theorem GI.randIn (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : G.rWit.Contains (State.addr (G.randP u))
    (BitVec.ofNat 32 (G.witLen - u)).toNat := by
  have := h.witFit
  rw [h.randLen]
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [h.randAddr hl]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · rw [GP.randP, ite_eq_left (by omega_arith), show G.witLen - u = 0 by omega_arith]
    show (_ - _ : Addr).toNat + 0 ≤ G.witLen
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem GI.randSub (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : Region.Sub (G.rRand u) G.rWit := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · show Region.Sub ⟨_, _⟩ _
    rw [h.randLen, h.randAddr hl]; exact Offset.sub_base _ (by omega_arith)
  · show Region.Sub ⟨_, _⟩ _
    rw [h.randLen, show G.witLen - u = 0 by omega_arith]
    intro a ha; simp [Region.Contains] at ha

theorem GI.randFit (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.randP u).toNat + (G.witLen - u) ≤ 2 ^ 32 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega_arith), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · have := (G.randP u).isLt; omega_arith

/-- The witnesses from `u` on, in memory. -/
theorem GI.randBytes (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt s.mem (State.addr (G.randP u)) (G.witLen - u) = G.witB.drop u := by
  have wl : G.witB.length = G.witLen := by rw [← h.hG]; exact bytesAt_length' _ _ _
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega_arith), h.keeps h.witFit (fun r hr => h.wit_apart r hr) (k := u) (n := G.witLen - u)
      (by omega_arith)]
    rw [show Spec.Rsa.bytesAt σ.mem (State.addr G.wit) G.witLen = G.witB by rw [← h.hG]; rfl,
      List.take_of_length_le (by rw [List.length_drop]; omega_arith)]
  · rw [show G.witLen - u = 0 by omega_arith, List.drop_of_length_le (by omega_arith)]; rfl

/-- The stack the call uses, below the frame: the pushed words and the test's 144 bytes. -/
theorem GI.pushSub (h : GI G σ V LS s) :
    Region.Sub (belowA G.sp 32) G.rBelow := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32), 32⟩ ⟨State.addr G.sp - 176#64, 176⟩
  rw [FrameStack.addr_sub' (by omega_arith)]
  exact Offset.sub_below _ (by omega_arith) (by omega_arith)

theorem GI.testSub (h : GI G σ V LS s) :
    Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length)) - 144#64, 144⟩ G.rBelow := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32) - BitVec.ofNat 64 144, 144⟩ ⟨State.addr G.sp - 176#64, 176⟩
  rw [FrameStack.addr_sub' (by omega_arith), BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega_arith) (by omega_arith)

theorem GI.argSub (h : GI G σ V LS s) :
    Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 8⟩
      (belowA G.sp 32) := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32 + 0#32), 8⟩ ⟨State.addr (G.sp - BitVec.ofNat 32 32), 32⟩
  rw [BitVec.add_zero]; exact fun _ h => by simp only [Region.Contains] at h ⊢; omega_arith

/-- The count's 8 bytes. -/
theorem GI.usedAddr (h : GI G σ V LS s) :
    State.addr (G.sp + BitVec.ofNat 32 fUsedOut) = State.addr G.sp + BitVec.ofNat 64 fUsedOut := by
  have := h.spHi; exact addr_add (by simp only [fUsedOut, F] at *; omega_arith)

/-- The test's arguments, in `r0`–`r5`. -/
abbrev TArgs (G : GP) (L u bits : Nat) (s : State) : Prop :=
  s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa L / 8) ∧
  s.gpr .r2 = G.randP u ∧ s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧
  s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut ∧ s.gpr .r5 = BitVec.ofNat 32 bits

/-- The regions the test is given. -/
abbrev tRd (G : GP) (u : Nat) : List Region :=
  [G.rRand u, ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 8⟩]
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

theorem SS.tEntry_arg0 (h : SS G σ c s) {L u bits : Nat} (regs : TArgs G L u bits s) :
    stackArg (tEntry G L u s) 0 = G.sp + BitVec.ofNat 32 fUsedOut := by
  have := h.gi.sp176
  show stackArg (pushed (.r4 :: [.r5, .r6, .r7, .r8, .r9, .r10, .r11]) s) 0 = _
  rw [pushed_arg0 (by rw [h.gi.sp]; show 4 * (7 + 1) ≤ G.sp.toNat; omega_arith), regs.2.2.2.2.1]

theorem SS.tEntry_arg1 (h : SS G σ c s) {L u bits : Nat} (regs : TArgs G L u bits s) :
    stackArg (tEntry G L u s) 1 = BitVec.ofNat 32 bits := by
  have := h.gi.sp176
  show stackArg (pushed (.r4 :: .r5 :: [.r6, .r7, .r8, .r9, .r10, .r11]) s) 1 = _
  rw [pushed_arg1 (by rw [h.gi.sp]; show 4 * (6 + 2) ≤ G.sp.toNat; omega_arith), regs.2.2.2.2.2]

/-- The pushed words leave `scratch`. -/
theorem SS.push_scr (h : SS G σ c s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) {k : Nat} (hk : k < n) :
    (pushed callPush s).mem (G.sa o + BitVec.ofNat 64 k) = s.mem (G.sa o + BitVec.ofNat 64 k) := by
  have := h.gi.sp176
  refine (FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [h.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)).bytes
    (R := G.rs o n) (fun r hr => ?_) (by have := h.gi.scrFit; show n ≤ 2 ^ 64; omega_arith) hk
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.gi.sp]
  exact (h.gi.scr_below ho).sub_right h.gi.pushSub

/-- The test's arguments meet its precondition. -/
theorem SS.tEntry_pin (h : SS G σ c s) {L u bits : Nat} (hL : L = G.pLen) (regs : TArgs G L u bits s)
    (hbits : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes) (hu : u ≤ G.witLen) (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) :
    PIn bits (tEntry G L u s) := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  have spHi := gi.spHi
  have hLv := h.lens
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  have a1 := h.tEntry_arg1 (L := L) (u := u) regs
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := regs
  have sp : s.sp = G.sp := gi.sp
  have esp : (tEntry G L u s).sp = G.sp - BitVec.ofNat 32 32 := by rw [tEntry_sp, sp]; rfl
  have espN : (tEntry G L u s).sp.toNat = G.sp.toNat - 32 := by rw [esp, FrameStack.sub_toNat' (by omega_arith)]
  have a0 := h.tEntry_arg0 (L := L) ⟨r0, r1, r2, r3, r4, r5⟩
  have e0 : (tEntry G L u s).gpr .r0 = G.scr + BitVec.ofNat 32 sA := by rw [tEntry_gpr (by decide), r0]
  have e1 : (tEntry G L u s).gpr .r1 = BitVec.ofNat 32 (wa L / 8) := by rw [tEntry_gpr (by decide), r1]
  have e2 : (tEntry G L u s).gpr .r2 = G.randP u := by rw [tEntry_gpr (by decide), r2]
  have e3 : (tEntry G L u s).gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by rw [tEntry_gpr (by decide), r3]
  subst hL
  have wl := wa_toNat hLv
  have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (by simp only [wa]; omega_arith)
  have aA : stackArgAddr (tEntry G G.pLen u s) 0 =
      State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)) := by
    rw [stackArgAddr, esp]; rfl
  -- The regions, as the search sees them.
  have scrW : Region.Sub ⟨State.addr (G.scr + BitVec.ofNat 32 sA), (BitVec.ofNat 32 (wa G.pLen / 8)).toNat * 8⟩
      G.rScr := by rw [aS, wl]; exact sw G (by simp only [sK] at big; omega_arith)
  have usedF : Region.Sub ⟨State.addr (G.sp + BitVec.ofNat 32 fUsedOut), 8⟩ G.rFrame := by
    rw [gi.usedAddr]; exact Offset.sub_base _ (by simp only [fUsedOut, F]; omega_arith)
  have argB : Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 8⟩
      G.rBelow := fun a ha => gi.pushSub a (gi.argSub a ha)
  have randW := gi.randSub hu
  have pre := gi.pre
  have fW := pre.fW; have wC := pre.wC; rw [gi.hG] at fW wC
  have stk : Region.Sub ⟨State.addr (tEntry G G.pLen u s).sp - 144#64, 144⟩ G.rBelow := by
    rw [esp]; exact gi.testSub
  have sv := pre.spLo
  refine ⟨hbits, a1, by omega_arith, by omega_arith, by rw [State.withRegions_rd, e2, e3, aA],
    by rw [State.withRegions_wr, e0, e1, a0],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, e1, e2, e3]; exact (wC.symm.sub_left scrW).sub_right randW
  · rw [e0, e1, a0]; exact (gi.frame_scr.symm.sub_left scrW).sub_right usedF
  · rw [e0, e1, aA]; exact ((gi.scr_below (o := sA) (n := wa G.pLen) (by simp only [sK] at big; omega_arith)).sub_left
      (by rw [aS, wl]; exact fun _ h => h)).sub_right argB
  · rw [e2, e3, a0]; exact ((fW.symm.sub_left randW).sub_right gi.frameSub).sub_right usedF
  · rw [a0, aA]; exact (gi.frame_below.sub_left usedF).sub_right argB
  · rw [e0, e1]; exact ((gi.scr_below (o := sA) (n := wa G.pLen) (by simp only [sK] at big; omega_arith)).sub_left
      (by rw [aS, wl]; exact fun _ h => h)).symm.sub_left stk
  · rw [e2, e3]; exact ((fW.symm.sub_left randW).sub_right gi.belowSub).symm.sub_left stk
  · rw [a0]; exact (gi.frame_below.sub_left usedF).symm.sub_left stk
  · rw [aA, esp]
    have : State.addr (G.sp - BitVec.ofNat 32 32 + BitVec.ofNat 32 (4 * 0)) = State.addr (G.sp - BitVec.ofNat 32 32) := by
      rw [Nat.mul_zero, BitVec.add_zero]
    rw [show (4 * callPush.length) = 32 from rfl, this]
    exact (Offset.base_disjoint_below _ (n := 144) (k := 8) (by omega_arith)).symm
  · rw [e0, e1, wl, h.toNat (by simp only [sK]; omega_arith)]; simp only [sK] at big; omega_arith
  · rw [e2, e3, gi.randLen]; exact gi.randFit hu
  · rw [a0, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by decide),
      Nat.mod_eq_of_lt (by simp only [fUsedOut, F] at *; omega_arith)]; simp only [fUsedOut, F] at *; omega_arith
  · rw [e1]; have := wl; omega_arith
  all_goals
    have hc : candOf bits (tEntry G G.pLen u s) = Spec.Dsa.decodeBE cb := by
      show Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (pushed callPush s).mem
        (State.addr ((tEntry G G.pLen u s).gpr .r0) + BitVec.ofNat 64 0) (bits / 8)) = _
      rw [e0, aS, BitVec.add_zero, ← hcb]
      refine congrArg _ (List.map_congr_left fun k hk => ?_)
      exact h.push_scr (o := sA) (n := bits / 8) (by simp only [sK] at big; omega_arith) (List.mem_range.mp hk)
    rw [hc]
  · exact hodd
  · exact hbl

/-- The regions the test is given are the caller's, the push's and the frame's. -/
theorem SS.tCovers (h : SS G σ c s) {L u : Nat} (hL : L = G.pLen) (hu : u ≤ G.witLen) :
    Covers (tRd G u ++ tWr G L) ((pushed callPush s).rd ++ (pushed callPush s).wr) ∧
      Covers (tWr G L) (pushed callPush s).wr := by
  have gi := h.gi
  have big := gi.scrBig
  have s176 := gi.sp176
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  have wl := wa_toNat h.lens
  have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (by simp only [wa]; omega_arith)
  have hpw : (pushed callPush s).wr = belowA G.sp 32 :: G.rFrame :: σ.wr := by
    rw [pushed_wr, gi.wr, gi.sp]; rfl
  have hpr : (pushed callPush s).rd = σ.rd := by rw [pushed_rd, gi.rd]
  have hw : Covers (tWr G G.pLen) (pushed callPush s).wr := by
    rw [hpw]
    refine Covers.pair (Covers.one ⟨G.rScr, by rw [gi.pre.wr, gi.hG]; simp, ?_⟩)
      (Covers.one ⟨G.rFrame, by simp, ?_⟩)
    · have : sA = 4096 := rfl
      rw [aS, wl]; exact Offset.contains_base _ (by simp only [sK] at big; omega_arith) (by have := gi.scrFit; omega_arith)
    · rw [gi.usedAddr]; exact Offset.contains_base _ (by simp only [fUsedOut, F]; omega_arith) (by decide)
  refine ⟨Covers.append_left (Covers.pair ?_ ?_) hw.right, hw⟩
  · exact Covers.left (Covers.one ⟨G.rWit, by rw [hpr, gi.pre.rd, gi.hG]; simp, gi.randIn hu⟩)
  · refine Covers.right (Covers.one ⟨belowA G.sp 32, by rw [hpw]; simp, ?_⟩)
    show (_ - _ : Addr).toNat + 8 ≤ 32
    rw [show (4 * callPush.length) = 32 from rfl, Nat.mul_zero, BitVec.add_zero, BitVec.sub_self,
      BitVec.toNat_zero]; omega_arith

theorem SS.tEntry_cand (h : SS G σ c s) {L u bits b : Nat} (hL : L = G.pLen) (regs : TArgs G L u b s)
    (hb8 : bits / 8 ≤ wa L) {cb : List Byte} (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb) :
    candOf bits (tEntry G L u s) = Spec.Dsa.decodeBE cb := by
  have big := h.gi.scrBig
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (by simp only [wa]; omega_arith)
  show Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (pushed callPush s).mem
    (State.addr ((tEntry G G.pLen u s).gpr .r0) + BitVec.ofNat 64 0) (bits / 8)) = _
  rw [tEntry_gpr (by decide), regs.1, aS, BitVec.add_zero, ← hcb]
  refine congrArg _ (List.map_congr_left fun k hk => ?_)
  exact h.push_scr (o := sA) (n := bits / 8) (by simp only [sK] at big; omega_arith) (List.mem_range.mp hk)

theorem SS.tEntry_rand (h : SS G σ c s) {L u bits : Nat} (regs : TArgs G L u bits s) (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt (tEntry G L u s).mem (State.addr ((tEntry G L u s).gpr .r2))
      ((tEntry G L u s).gpr .r3).toNat = G.witB.drop u := by
  have gi := h.gi
  have s176 := gi.sp176
  rw [tEntry_gpr (by decide), tEntry_gpr (by decide), regs.2.2.1, regs.2.2.2.1, gi.randLen, tEntry_mem,
    ← gi.randBytes hu]
  refine VG.Proof.Dsa.Generation.frame_bytesAt (FrameStack.pushed_frameA (rs := callPush) (s := s)
    (by rw [gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)) (fun r hr => ?_) (by have := gi.witLt; omega_arith)
  simp only [List.mem_singleton] at hr; subst hr
  have fW := gi.pre.fW; rw [gi.hG] at fW
  rw [gi.sp]
  have rs := gi.randSub hu
  rw [GP.rRand, gi.randLen] at rs
  exact ((fW.symm.sub_left rs).sub_right gi.belowSub).sub_right gi.pushSub

/-- The test's call: its effects. -/
theorem SS.primeCall_ok (h : SS G σ c s) {L u bits : Nat} {name : String} {code : Prog isa}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (regs : TArgs G L u bits s) (hu : u ≤ G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], t.gpr r = s.gpr r) → t.sp = s.sp → t.rd = s.rd →
      t.wr = s.wr → Frame [G.rs sA (wa L), G.rU, G.rBelow] s.mem t.mem →
      (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u)) →
      (∀ b rest, Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u) = some (b, rest) →
        t.mem.readW (State.addr G.sp + BitVec.ofNat 64 fUsedOut) 64 = BitVec.ofNat 64 (G.witLen - u - rest.length)) →
      Q t) :
    WP isa (callWith name code) s Q := by
  have gi := h.gi
  have s176 := gi.sp176
  have pin := h.tEntry_pin hL regs ok.sized hu hsize hb8 hcb hodd hbl
  obtain ⟨hc, hw⟩ := h.tCovers (u := u) hL hu
  have sp : s.sp = G.sp := gi.sp
  have big := gi.scrBig
  unfold callWith
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith) (by decide) ?_
  refine FrameStack.WP.callF ok.verified.1 (pre_of_pin pin) hc hw
    (by rw [pushed_sp, sp, FrameStack.sub_toNat' (by show 4 * 8 ≤ G.sp.toNat; omega_arith)]; have := ok.stack
        show armStack code ≤ G.sp.toNat - 4 * 8; omega_arith)
    fun s₂ hrd hwr hsp hf hg hpost => ?_
  have pp := ppost_of_post pin.bits hpost
  obtain ⟨r0, -, used⟩ := pp
  simp only [State.withRegions_gpr, State.withRegions_mem] at r0 used
  -- The test's result, in terms of the search.
  have res : resOf bits (tEntry G L u s) = Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u) := by
    unfold resOf; rw [h.tEntry_cand hL regs hb8 hcb, h.tEntry_rand regs hu]
  rw [res] at r0 used
  have pg : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → (popped .r4 (4 * callPush.length) s₂).gpr r = s.gpr r :=
    fun r h4 hp hl => by rw [popped_gpr h4, hg r hp hl, pushed_gpr]
  have mem : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], r ≠ .r4 ∧ r ∈ preserved ∧ r ≠ .lr := by decide
  refine k _ (fun r hr => pg r (mem r hr).1 (mem r hr).2.1 (mem r hr).2.2)
    (by rw [popped_sp, hsp, pushed_sp, BitVec.sub_add_cancel])
    (by rw [popped_rd, hrd, pushed_rd]) (by rw [popped_wr, hwr, pushed_wr, List.tail_cons]) ?_
    (by rw [popped_gpr (by decide)]; exact r0) fun b rest e => ?_
  · have bl : Region.Sub (belowA G.sp 176) G.rBelow := by
      show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 176), 176⟩ ⟨State.addr G.sp - 176#64, 176⟩
      rw [FrameStack.addr_sub' (by omega_arith)]; exact fun _ h => h
    have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
    have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen)
      (by simp only [sK] at big ⊢; omega_arith) (by simp only [wa]; omega_arith)
    rw [popped_mem]
    refine ((FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)).sub
      fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨G.rBelow, by simp, by rw [sp]; exact gi.pushSub⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · refine ⟨G.rs sA (wa L), List.mem_cons_self, ?_⟩
        rw [aS, wa_toNat (hL ▸ h.lens)]; exact fun _ h => h
      · exact ⟨G.rU, by simp, by rw [gi.usedAddr]; exact fun _ h => h⟩
      · refine ⟨G.rBelow, by simp, fun a ha => bl a ?_⟩
        rw [pushed_sp, sp] at ha
        exact FrameStack.belowA_inner (a := armStack code) (k := 4 * callPush.length) (b := 176)
          (by have := ok.stack; show armStack code + 32 ≤ 176; omega_arith) (by omega_arith) a ha
  · have := used b rest e
    rw [h.tEntry_arg0 regs, gi.usedAddr, State.callEntry_gpr _ (by decide), pushed_gpr, regs.2.2.2.1,
      gi.randLen] at this
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      List.cons.injEq, and_true] at this
    rw [popped_mem]; exact this

end

/-- The test's call in two runs at the same stage, with the same candidate. -/
theorem primeCall_ct {G : GP} {c : Cfg} {L u bits : Nat} {name : String} {code : Prog isa}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (hu : u ≤ G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) :
    RelCT isa (fun s₁ s₂ => (∃ σ, SS G σ c s₁) ∧ TArgs G L u bits s₁ ∧
        Spec.Rsa.bytesAt s₁.mem (G.sa sA) (bits / 8) = cb ∧
        (∃ σ, SS G σ c s₂) ∧ TArgs G L u bits s₂ ∧ Spec.Rsa.bytesAt s₂.mem (G.sa sA) (bits / 8) = cb)
      (callWith name code) fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun s₁ s₂ ⟨⟨_, h₁⟩, _, _, ⟨_, h₂⟩, _, _⟩ => by rw [h₁.gi.sp, h₂.gi.sp]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨⟨σ₁, h₁⟩, g₁, c₁, ⟨σ₂, h₂⟩, g₂, c₂⟩, p₁, p₂⟩ := hp
  have s₁ := h₁.gi.sp176
  have s₂ := h₂.gi.sp176
  rw [push_pushed (by decide) (by rw [h₁.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (by rw [h₂.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := primeK)
    ok.verified.1 ok.verified.2.1 (tRd G u) (tWr G L) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨cv₁, w₁⟩ := h₁.tCovers (u := u) hL hu
  obtain ⟨cv₂, w₂⟩ := h₂.tCovers (u := u) hL hu
  have pin₁ := h₁.tEntry_pin hL g₁ ok.sized hu hsize hb8 c₁ hodd hbl
  refine ⟨pre_of_pin pin₁, pre_of_pin (h₂.tEntry_pin hL g₂ ok.sized hu hsize hb8 c₂ hodd hbl),
    pub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ pin₁.bits ?_ ?_, cv₁, w₁, cv₂, w₂⟩
  · show (pushed callPush t₁).sp = (pushed callPush t₂).sp
    rw [pushed_sp, pushed_sp, h₁.gi.sp, h₂.gi.sp]
  · show (tEntry G L u t₁).gpr .r0 = (tEntry G L u t₂).gpr .r0
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.1, g₂.1]
  · show (tEntry G L u t₁).gpr .r1 = (tEntry G L u t₂).gpr .r1
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.2.1, g₂.2.1]
  · show (tEntry G L u t₁).gpr .r2 = (tEntry G L u t₂).gpr .r2
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.2.2.1, g₂.2.2.1]
  · show (tEntry G L u t₁).gpr .r3 = (tEntry G L u t₂).gpr .r3
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.2.2.2.1, g₂.2.2.2.1]
  · rw [h₁.tEntry_arg0 g₁, h₂.tEntry_arg0 g₂]
  · rw [h₁.tEntry_arg1 g₁, h₂.tEntry_arg1 g₂]
  · rw [h₁.tEntry_cand hL g₁ hb8 c₁, h₂.tEntry_cand hL g₂ hb8 c₂]
  · rw [h₁.tEntry_rand g₁ hu, h₂.tEntry_rand g₂ hu]

end VG.Proof.Dsa.Arm.Gen
