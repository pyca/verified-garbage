module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSLoad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Arm.Gen.PArith
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PLoop
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GPart
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-! ### `Dsa.Arm.Gen.SLoop`, which the modules that import this one used -/

section

/-! ### `Dsa.Arm.Gen.Attempt`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.CheckPart`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.CheckCall`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: calling the domain check

`SS.checkCall_ok`: `callWith name Generate.checkParameters`, its stack
arguments (`scratch` from `sA` and its words, in `r4` and `r5`) pushed,
checks p‖q‖g at `sPacked`: its verdict in `r0`, and `scratch` changed only
from `sA` on. `checkCall_ct`: two runs with the same p‖q‖g.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Arm.FrameStack (armStack belowA)
open VG.Proof.Dsa.Arm (checkPre checkArm checkParams checkRes)

variable {umaal : Bool}

/-- The bytes of p‖q‖g. -/
abbrev nPk (G : GP) : Nat := 2 * G.pLen + G.qLen

/-- The check's arguments, in `r0`–`r5`. -/
abbrev CArgs (G : GP) (s : State) : Prop :=
  s.gpr .r0 = G.scr + BitVec.ofNat 32 sPacked ∧ s.gpr .r1 = BitVec.ofNat 32 (nPk G) ∧
  s.gpr .r2 = BitVec.ofNat 32 G.pLen ∧ s.gpr .r3 = BitVec.ofNat 32 G.qLen ∧
  s.gpr .r4 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r5 = BitVec.ofNat 32 (wa G.pLen / 8)

/-- The regions the check is given. -/
abbrev cRd (G : GP) : List Region :=
  [⟨State.addr (G.scr + BitVec.ofNat 32 sPacked), (BitVec.ofNat 32 (nPk G)).toNat⟩,
    ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length)), 8⟩]
abbrev cWr (G : GP) : List Region :=
  [⟨State.addr (G.scr + BitVec.ofNat 32 sA), (BitVec.ofNat 32 (wa G.pLen / 8)).toNat * 8⟩]

/-- The check's entry. -/
abbrev cEntry (G : GP) (s : State) : State := (pushed callPush s).callEntry.withRegions (cRd G) (cWr G)

theorem cEntry_gpr {G : GP} {s : State} {r : Reg} (hr : r ∉ linkRegs) : (cEntry G s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem cEntry_sp {G : GP} {s : State} : (cEntry G s).sp = s.sp - BitVec.ofNat 32 (4 * callPush.length) := rfl

section
variable {G : GP} {σ s : State} {c : Cfg}

/-- The check's stack argument `i`: the pushed register. -/
theorem SS.cEntry_arg (h : SS G σ c s) {i : Nat} (hi : i < 8) : stackArg (cEntry G s) i = s.gpr callPush[i] := by
  have := h.gi.sp176
  have := G.sp.isLt
  obtain hs : (s.sp - BitVec.ofNat 32 32).toNat = G.sp.toNat - 32 := by
    rw [h.gi.sp]; exact FrameStack.sub_toNat' (by omega_arith)
  have := VG.Proof.Dsa.Arm.Key.storeWords_read (callPush.map s.gpr) s.mem (s.sp - BitVec.ofNat 32 32)
    (by rw [List.length_map]; show (s.sp - BitVec.ofNat 32 32).toNat + 4 * 8 ≤ 2 ^ 32; omega_arith) i
    (by rw [List.length_map]; exact hi)
  simpa only [List.getElem_map, stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp, pushed, List.length_cons, List.length_nil] using this

theorem nPk_le (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) : nPk G ≤ 800 := by
  unfold Spec.Dsa.generationLengthsValid at hlq; simp only [nPk]; omega_arith

/-- The check's arguments meet its precondition. -/
theorem SS.cEntry_pre (h : SS G σ c s) (regs : CArgs G s) (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    checkPre (cEntry G s) := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  have spHi := gi.spHi
  have hLv := h.lens
  obtain np := nPk_le hlq
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := regs
  have sp : s.sp = G.sp := gi.sp
  obtain esp : (cEntry G s).sp = G.sp - BitVec.ofNat 32 32 := by rw [cEntry_sp, sp]; rfl
  obtain espN : (cEntry G s).sp.toNat = G.sp.toNat - 32 := by rw [esp, FrameStack.sub_toNat' (by omega_arith)]
  obtain e0 : (cEntry G s).gpr .r0 = G.scr + BitVec.ofNat 32 sPacked := by rw [cEntry_gpr (by decide), r0]
  obtain e1 : (cEntry G s).gpr .r1 = BitVec.ofNat 32 (nPk G) := by rw [cEntry_gpr (by decide), r1]
  obtain e2 : (cEntry G s).gpr .r2 = BitVec.ofNat 32 G.pLen := by rw [cEntry_gpr (by decide), r2]
  obtain e3 : (cEntry G s).gpr .r3 = BitVec.ofNat 32 G.qLen := by rw [cEntry_gpr (by decide), r3]
  obtain a0 : stackArg (cEntry G s) 0 = G.scr + BitVec.ofNat 32 sA := by rw [h.cEntry_arg (by decide)]; exact r4
  obtain a1 : stackArg (cEntry G s) 1 = BitVec.ofNat 32 (wa G.pLen / 8) := by
    rw [h.cEntry_arg (by decide)]; exact r5
  obtain wl := wa_toNat hLv
  obtain nl : (BitVec.ofNat 32 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain hpk : sPacked + nPk G ≤ sA := by simp only [sPacked, sA]; omega_arith
  obtain hsA : sA + wa G.pLen ≤ sK G.pLen := by simp only [sK]; omega_arith
  obtain aP : State.addr (G.scr + BitVec.ofNat 32 sPacked) = G.sa sPacked :=
    h.addr (n := nPk G) (by omega_arith) (by simp only [nPk]; omega_arith)
  obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) hsA (by simp only [wa]; omega_arith)
  obtain argB : Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32), 8⟩ G.rBelow :=
    fun a ha => gi.pushSub a (by simp only [Region.Contains] at ha ⊢; omega_arith)
  obtain spT : (G.sp - BitVec.ofNat 32 32).toNat = G.sp.toNat - 32 := by rw [← esp]; exact espN
  obtain hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  unfold checkPre
  simp only [State.withRegions_rd, State.withRegions_wr, e0, e1, e2, e3, VG.Proof.Dsa.Arm.arg, a0, a1, esp]
  refine ⟨by omega_arith, rfl, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aP, aS, nl, wl]; exact gi.sdisj (.inl hpk) (by omega_arith) (by omega_arith)
  · rw [aS, wl]; exact (gi.scr_below (by omega_arith)).sub_right argB
  · rw [nl, h.toNat (by omega_arith)]; omega_arith
  · rw [wl, h.toNat (by omega_arith)]; omega_arith
  · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    unfold Spec.Dsa.generationLengthsValid at hlq; unfold Spec.Dsa.lengthsValid; omega_arith
  · rw [nl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by simp only [wa]; omega_arith)]
    unfold Spec.Dsa.scratchWords; simp only [wa]; omega_arith

/-- The regions the check is given are the push's and `scratch`'s. -/
theorem SS.cCovers (h : SS G σ c s) (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    Covers (cRd G ++ cWr G) ((pushed callPush s).rd ++ (pushed callPush s).wr) ∧
      Covers (cWr G) (pushed callPush s).wr := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  obtain np := nPk_le hlq
  have hLv := h.lens
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain wl := wa_toNat h.lens
  obtain nl : (BitVec.ofNat 32 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain hpk : sPacked + nPk G ≤ sA := by simp only [sPacked, sA]; omega_arith
  obtain hsA : sA + wa G.pLen ≤ sK G.pLen := by simp only [sK]; omega_arith
  obtain aP : State.addr (G.scr + BitVec.ofNat 32 sPacked) = G.sa sPacked :=
    h.addr (n := nPk G) (by omega_arith) (by simp only [nPk]; omega_arith)
  obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) hsA (by simp only [wa]; omega_arith)
  obtain hpw : (pushed callPush s).wr = belowA G.sp 32 :: G.rFrame :: σ.wr := by
    rw [pushed_wr, gi.wr, gi.sp]; rfl
  obtain inScr : ∀ {o n : Nat}, o + n ≤ sK G.pLen → InRegions (pushed callPush s).wr (G.sa o) n := fun hon =>
    ⟨G.rScr, by rw [hpw, gi.pre.wr, gi.hG]; simp,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hw : Covers (cWr G) (pushed callPush s).wr := Covers.one (by rw [aS, wl]; exact inScr hsA)
  refine ⟨Covers.append_left (Covers.right (Covers.pair (Covers.one ?_) (Covers.one ?_))) hw.right, hw⟩
  · rw [aP, nl]; exact inScr (by omega_arith)
  · refine ⟨belowA G.sp 32, by rw [hpw]; simp, ?_⟩
    show (_ - _ : Addr).toNat + 8 ≤ 32
    rw [show (4 * callPush.length) = 32 from rfl, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

/-- The bytes the check reads: p‖q‖g at `sPacked`. -/
theorem SS.cEntry_params (h : SS G σ c s) (regs : CArgs G s) (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    checkParams (cEntry G s) = Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) := by
  have big := h.gi.scrBig
  obtain np := nPk_le hlq
  have hLv := h.lens
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain nl : (BitVec.ofNat 32 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain aP : State.addr (G.scr + BitVec.ofNat 32 sPacked) = G.sa sPacked :=
    h.addr (n := nPk G) (by simp only [sK, sPacked, sA] at *; omega_arith) (by simp only [nPk]; omega_arith)
  show Spec.Rsa.bytesAt (pushed callPush s).mem (State.addr ((cEntry G s).gpr .r0)) ((cEntry G s).gpr .r1).toNat = _
  rw [cEntry_gpr (by decide), cEntry_gpr (by decide), regs.1, regs.2.1, aP, nl]
  refine List.map_congr_left fun k hk => ?_
  exact h.push_scr (o := sPacked) (n := nPk G) (by simp only [sK, sPacked, sA] at *; omega_arith) (List.mem_range.mp hk)

/-- The check's call: its effects. -/
theorem SS.checkCall_ok (h : SS G σ c s) {name : String} (regs : CArgs G s)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], t.gpr r = s.gpr r) → t.sp = s.sp → t.rd = s.rd →
      t.wr = s.wr → Frame [G.rs sA (wa G.pLen), G.rU, G.rBelow] s.mem t.mem →
      t.gpr .r0 = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen
        (Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G)) then 1 else 0) → Q t) :
    WP isa (callWith name (VG.Impl.Dsa.Arm.Generate.checkParameters umaal)) s Q := by
  have gi := h.gi
  have s176 := gi.sp176
  obtain pre := h.cEntry_pre regs hlq
  obtain ⟨hc, hw⟩ := h.cCovers hlq
  have sp : s.sp = G.sp := gi.sp
  have big := gi.scrBig
  unfold callWith
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith) (by decide) ?_
  refine FrameStack.WP.callF (k := checkArm) (fun s hs => by
      obtain ⟨t, s', e, ha, hp⟩ := VG.Proof.Dsa.Arm.check_correct hs; exact ⟨t, s', e, ha, hp⟩) pre hc hw
    (by rw [VG.Proof.Dsa.Arm.Key.check_armStack]; exact Nat.zero_le _)
    fun s₂ hrd hwr hsp hf hg hpost => ?_
  rw [VG.Proof.Dsa.Arm.Key.check_armStack] at hf
  intro lm lu hfl
  obtain fl : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 (4 * callPush.length)), 4 * callPush.length⟩ G.rBelow := by
    rw [sp]; exact gi.pushSub
  have r0 := hpost
  dsimp only [checkArm] at r0
  rw [State.withRegions_gpr, BitVec.setWidth_append_eq_right] at r0
  obtain res : checkRes (cEntry G s) = Spec.Dsa.checkParametersBytes G.pLen G.qLen
      (Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G)) := by
    have hLv := h.lens
    obtain hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
    unfold checkRes
    rw [h.cEntry_params regs hlq, cEntry_gpr (by decide), cEntry_gpr (by decide), regs.2.2.1, regs.2.2.2.1,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [res] at r0
  obtain pg : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → (popped .r4 (4 * callPush.length) s₂).gpr r = s.gpr r :=
    fun r h4 hp hl => by rw [popped_gpr h4, hg r hp hl, pushed_gpr]
  obtain mem : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], r ≠ .r4 ∧ r ∈ preserved ∧ r ≠ .lr := by decide
  refine k _ (fun r hr => pg r (mem r hr).1 (mem r hr).2.1 (mem r hr).2.2)
    (by rw [popped_sp, hsp, pushed_sp, BitVec.sub_add_cancel])
    (by rw [popped_rd, hrd, pushed_rd]) (by rw [popped_wr, hwr, pushed_wr, List.tail_cons]) ?_ ?_
  · have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
    obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen)
      (by simp only [sK] at big ⊢; omega_arith) (by simp only [wa]; omega_arith)
    dsimp only
    refine (((FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)).sub
      fun r hr => ?_).trans (hf.sub fun r hr => ?_)).trans
      (hfl.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨G.rBelow, by simp, fl⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨G.rBelow, by simp, by rw [sp]; exact gi.pushSub⟩
    · simp only [cWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨G.rs sA (wa G.pLen), List.mem_cons_self, ?_⟩
        rw [aS, wa_toNat h.lens]; exact fun _ h => h
      · exact ⟨G.rBelow, by simp, fun _ hc => absurd hc (by simp [Region.Contains])⟩
  · dsimp only; rw [popped_gpr (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [r0]; split <;> rfl

end

/-- The check's call in two runs at the same stage, with the same p‖q‖g. -/
theorem checkCall_ct {G : GP} {c : Cfg} {name : String} (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen)
    {pk : List Byte} :
    RelCT isa (fun s₁ s₂ => (∃ σ, SS G σ c s₁) ∧ CArgs G s₁ ∧ Spec.Rsa.bytesAt s₁.mem (G.sa sPacked) (nPk G) = pk ∧
        (∃ σ, SS G σ c s₂) ∧ CArgs G s₂ ∧ Spec.Rsa.bytesAt s₂.mem (G.sa sPacked) (nPk G) = pk)
      (callWith name (VG.Impl.Dsa.Arm.Generate.checkParameters umaal)) fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun s₁ s₂ ⟨⟨_, h₁⟩, _, _, ⟨_, h₂⟩, _, _⟩ => by rw [h₁.gi.sp, h₂.gi.sp]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨⟨σ₁, h₁⟩, g₁, c₁, ⟨σ₂, h₂⟩, g₂, c₂⟩, p₁, p₂⟩ := hp
  have s₁ := h₁.gi.sp176
  have s₂ := h₂.gi.sp176
  rw [push_pushed (by decide) (by rw [h₁.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (by rw [h₂.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := checkArm)
    (fun s hs => by obtain ⟨t, s', e, ha, hp⟩ := VG.Proof.Dsa.Arm.check_correct hs; exact ⟨t, s', e, ha, hp⟩)
    VG.Proof.Dsa.Arm.check_constantTime (cRd G) (cWr G) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨cv₁, w₁⟩ := h₁.cCovers hlq
  obtain ⟨cv₂, w₂⟩ := h₂.cCovers hlq
  refine ⟨h₁.cEntry_pre g₁ hlq, h₂.cEntry_pre g₂ hlq, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, cv₁, w₁, cv₂, w₂⟩
  · show (pushed callPush t₁).sp = (pushed callPush t₂).sp
    rw [pushed_sp, pushed_sp, h₁.gi.sp, h₂.gi.sp]
  · rw [h₁.cEntry_params g₁ hlq, h₂.cEntry_params g₂ hlq, c₁, c₂]
  · show (cEntry G t₁).gpr .r0 = (cEntry G t₂).gpr .r0
    rw [cEntry_gpr (by decide), cEntry_gpr (by decide), g₁.1, g₂.1]
  · show (cEntry G t₁).gpr .r1 = (cEntry G t₂).gpr .r1
    rw [cEntry_gpr (by decide), cEntry_gpr (by decide), g₁.2.1, g₂.2.1]
  · show (cEntry G t₁).gpr .r2 = (cEntry G t₂).gpr .r2
    rw [cEntry_gpr (by decide), cEntry_gpr (by decide), g₁.2.2.1, g₂.2.2.1]
  · show (cEntry G t₁).gpr .r3 = (cEntry G t₂).gpr .r3
    rw [cEntry_gpr (by decide), cEntry_gpr (by decide), g₁.2.2.2.1, g₂.2.2.2.1]
  · show stackArg (cEntry G t₁) i = stackArg (cEntry G t₂) i
    rw [h₁.cEntry_arg (by omega_arith), h₂.cEntry_arg (by omega_arith)]
    rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl
    · exact g₁.2.2.2.2.1.trans g₂.2.2.2.2.1.symm
    · exact g₁.2.2.2.2.2.trans g₂.2.2.2.2.2.symm

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The check's call, at a stage that claims p‖q‖g at `sPacked`. -/
theorem checkCall_vp {name : String} {pk : List Byte} {cl' : Claims}
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) (hpk : (sPacked, pk) ∈ c.cl) (hpkl : pk.length = nPk G)
    (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS) (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa G.pLen) x) :
    VP (fun σ s => St G c X σ s ∧ CArgs G s) (callWith name (VG.Impl.Dsa.Arm.Generate.checkParameters umaal))
      (fun σ t => St G { c with cl := cl' } X σ t ∧
        t.gpr .r0 = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0)) := by
  obtain bytes : ∀ σ s, SS G σ c s → Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk := fun σ s h => by
    have := h.sb _ hpk; rwa [hpkl] at this
  refine VP.of_ct (fun σ₁ σ₂ => (checkCall_ct (c := c) (name := name) hlq).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ => ⟨⟨σ₁, h₁⟩, g₁, bytes _ _ h₁, ⟨σ₂, h₂⟩, g₂, bytes _ _ h₂⟩)
    fun _ _ _ => trivial) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  refine h.checkCall_ok (name := name) regs hlq fun t g sp rd wr f r0 => ⟨⟨?_, x⟩, by rw [r0, bytes _ _ h]⟩
  exact h.of_call rfl (fun r hr => g r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    sp rd wr f h88 h92 hcl

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: checking p‖q‖g

`checkPart_vp`: p (at `sPBE`), q (at `sQ`) and g (at `sG`) copied side by
side to `sPacked`, checked by `vg_dsa_check_parameters`: `fStatus` := 1 if
`Spec.Dsa.checkParametersBytes` accepts them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_movw wp_mov wp_cmp op2_imm eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {umaal : Bool}

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The check's arguments. -/
theorem cargs_vp (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    VP (St G c X) (.block (scr G.pLen .r0 sPacked ++ ([.movw .r1 (BitVec.ofNat 16 (2 * G.pLen + G.qLen)),
        .movw .r2 (BitVec.ofNat 16 G.pLen), .mov .r3 (.imm (BitVec.ofNat 32 G.qLen))] : List Instr) ++ scr G.pLen .r4 sA ++
        ([.movw .r5 (BitVec.ofNat 16 (wa G.pLen / 8))] : List Instr)))
      (fun σ s => St G c X σ s ∧ CArgs G s) := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sPacked ++ [.movw .r1 (BitVec.ofNat 16 1), .movw .r2 (BitVec.ofNat 16 1),
        .mov .r3 (.imm (BitVec.ofNat 32 1))] ++ scr 128 .r4 sA ++ [.movw .r5 (BitVec.ofNat 16 1)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8])
    fun σ s ⟨h, x⟩ => ?_
  have big := h.gi.scrBig
  have hLv := h.lens
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hsK : sA ≤ sK G.pLen := by simp only [sK]; omega_arith
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok (d := .r0) h.r8 rfl hLv (by simp only [sPacked, sK, sA]; omega_arith) fun s₁ v₁ R₁ M₁ => ?_
  refine wp_movw fun s₂ u₂ => wp_movw fun s₃ u₃ => wp_mov (op2_imm (encodable_lt (by omega_arith))) fun s₄ u₄ => ?_
  have h4 : SS G σ c s₄ := ((((h.of_rest R₁ M₁).of_rest (u₂.rest (ws := [.r1]) (by simp)) u₂.mem).of_rest
    (u₃.rest (ws := [.r2]) (by simp)) u₃.mem).of_rest (u₄.rest (ws := [.r3]) (by simp)) u₄.mem)
  refine scr_ok (d := .r4) h4.r8 rfl hLv hsK fun s₅ v₅ R₅ M₅ => wp_movw fun t u => WP.block_nil ?_
  refine ⟨⟨(h4.of_rest R₅ M₅).of_rest (u.rest (ws := [.r5]) (by simp)) u.mem, x⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), v₁]
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      setWidth_ofNat16 (by omega_arith)]
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.other _ (by decide), u₃.gpr, setWidth_ofNat16 (by omega_arith)]
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.gpr]
  · rw [u.other _ (by decide), v₅]
  · rw [u.gpr, setWidth_ofNat16 (by simp only [wa]; omega_arith)]

/-- p‖q‖g. -/
abbrev pkOf (pB qB gB : List Byte) : List Byte := pB ++ qB ++ gB

/-- The stage after the check. -/
abbrev ckCfg (c : Cfg) (pk : List Byte) (ok : Bool) : Cfg :=
  if ok then ({ c with cl := (sPacked, pk) :: c.cl }).setV fStatus 1 else { c with cl := (sPacked, pk) :: c.cl }

theorem checkPart_vp {g : Geo} (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters umaal)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) {pB qB gB : List Byte}
    (hP : (sPBE, pB) ∈ c.cl) (hQ : (sQ, qB) ∈ c.cl) (hG : (sG, gB) ∈ c.cl)
    (hPl : pB.length = G.pLen) (hQl : qB.length = G.qLen) (hGl : gB.length = G.pLen)
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sPacked) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS) :
    VP (St G c X) g.checkPart
      (St G (ckCfg c (pkOf pB qB gB) (Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB))) X) := by
  unfold Geo.checkPart
  rw [hp, hq, hck]
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hp384 : G.pLen ≤ 384 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hp0 : 0 < G.pLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hq0 : 0 < G.qLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have e1 : sPacked = 2112 := rfl
  have e2 : sPBE = 576 := rfl
  have e3 : sQ = 128 := rfl
  have e4 : sG = 1728 := rfl
  have e5 : sA = 4096 := rfl
  have hK : ∀ n, n ≤ 4096 → n ≤ sK G.pLen := fun n hn => by simp only [sK, sA] at *; omega_arith
  -- The copies.
  refine VP.seq (G := St G { c with cl := (sPacked, pB) :: c.cl } X) (copyS_vp (c := fun _ => c) (fun σ s h => h.1) rfl hp0 (by omega_arith)
    (hK _ (by omega_arith)) (hK _ (by omega_arith)) (.inr (by omega_arith)) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩) ?_
  · have b := h.sb _ hP
    refine h.of_scr R (o := sPacked) (n := G.pLen) (hK _ (by omega_arith)) (f.mono (by simp))
      (cl' := (sPacked, pB) :: c.cl) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [hPl, e, ← hPl]; exact b, by rw [hPl]; exact hK _ (by omega_arith)⟩
    · exact .inl ⟨hy, .inl (hcl y hy)⟩
  refine VP.seq (G := St G { c with cl := (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl } X)
    (copyS_vp (c := fun _ => { c with cl := (sPacked, pB) :: c.cl }) (fun σ s h => h.1) rfl hq0 (by omega_arith)
    (hK _ (by omega_arith)) (hK _ (by omega_arith)) (.inr (by omega_arith)) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩) ?_
  · have b := h.sb _ (show (sQ, qB) ∈ (sPacked, pB) :: c.cl from List.mem_cons_of_mem _ hQ)
    refine h.of_scr R (o := sPacked + G.pLen) (n := G.qLen) (hK _ (by omega_arith)) (f.mono (by simp))
      (cl' := (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    swap
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl ⟨List.mem_cons_self, .inl (by rw [hPl])⟩
    · exact .inl ⟨List.mem_cons_of_mem _ hy, .inl (by have := hcl y hy; omega_arith)⟩
    · exact .inr ⟨by rw [hQl, e, ← hQl]; exact b, by rw [hQl]; exact hK _ (by omega_arith)⟩
  refine VP.seq (G := St G { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl } X)
    (copyS_vp (c := fun _ => { c with cl := (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl }) (fun σ s h => h.1) rfl hp0 (by omega_arith)
    (hK _ (by omega_arith)) (hK _ (by omega_arith)) (.inr (by omega_arith)) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩) ?_
  · have b := h.sb _ (show (sG, gB) ∈ (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl from
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hG))
    refine h.of_scr R (o := sPacked + G.pLen + G.qLen) (n := G.pLen) (hK _ (by omega_arith)) (f.mono (by simp))
      (cl' := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [hGl, e, ← hGl]; exact b, by rw [hGl]; exact hK _ (by omega_arith)⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl ⟨List.mem_cons_self, .inl (by rw [hQl])⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl ⟨List.mem_cons_of_mem _ List.mem_cons_self, .inl (by rw [hPl]; omega_arith)⟩
    · exact .inl ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy), .inl (by have := hcl y hy; omega_arith)⟩
  -- p‖q‖g, as one claim.
  have join : ∀ σ s, SS G σ { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl } s → SS G σ { c with cl := (sPacked, pkOf pB qB gB) :: c.cl } s := fun σ s h => by
    have hc : ∀ y ∈ (sPacked, pkOf pB qB gB) :: c.cl,
        Spec.Rsa.bytesAt s.mem (G.sa y.1) y.2.length = y.2 ∧ y.1 + y.2.length ≤ sK G.pLen := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · have bp := h.sb (sPacked, pB) (by simp)
        have bq := h.sb (sPacked + G.pLen, qB) (by simp)
        have bg := h.sb (sPacked + G.pLen + G.qLen, gB) (by simp)
        have offe : ∀ o n, VG.Proof.Bignum.off (G.sa o) n = G.sa (o + n) := fun o n => by
          simp only [VG.Proof.Bignum.off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        simp only at bp bq bg
        refine ⟨?_, by simp only [pkOf, List.length_append, hPl, hQl, hGl]; exact hK _ (by omega_arith)⟩
        show Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pB ++ qB ++ gB).length = pB ++ qB ++ gB
        rw [List.length_append, List.length_append, VG.Proof.Dsa.Generation.bytesAt_append,
          VG.Proof.Dsa.Generation.bytesAt_append, offe, offe, ← Nat.add_assoc, bp, hPl, bq, hQl, bg]
      · exact ⟨h.sb _ (by simp [hy]), h.clOk _ (by simp [hy])⟩
    exact ⟨h.gi, h.r7, h.r8, h.r9, fun y hy => (hc y hy).1, fun y hy => (hc y hy).2, h.arrs, h.liveOk, h.ksl,
      h.kslOk⟩
  refine VP.seq ((cargs_vp (c := { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl }) (X := X) hlq).mono (G' := fun σ s => St G { c with cl := (sPacked, pkOf pB qB gB) ::
        c.cl } X σ s ∧ CArgs G s) (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, a⟩ => ⟨⟨join σ s h, x⟩, a⟩) ?_
  -- The check.
  have hpkl : (pkOf pB qB gB).length = nPk G := by simp only [pkOf, List.length_append, hPl, hQl, hGl, nPk]; omega_arith
  refine VP.seq (checkCall_vp (c := { c with cl := (sPacked, pkOf pB qB gB) :: c.cl })
    (cl' := (sPacked, pkOf pB qB gB) :: c.cl) hlq (by simp) hpkl h88 h92 fun y hy =>
    ⟨hy, .inl (by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hpkl]; simp only [nPk, sPacked, sA]; omega_arith
      · have := hcl y hy; simp only [sPacked, sA] at *; omega_arith)⟩) ?_
  generalize hb : Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB) = b
  refine VP.seq (G := fun σ s => St G { c with cl := (sPacked, pkOf pB qB gB) :: c.cl } X σ s ∧ isa.eval .eq s = some b)
    (VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (.block [.cmp .r0 (.imm 1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r0⟩ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
        ⟨⟨h.of_rest (f.rest []) f.mem, x⟩, by rw [eval_eq, z, r0]; cases b <;> decide⟩) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · cases b
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
    · exact stImm_vp (c := fun _ => { c with cl := (sPacked, pkOf pB qB gB) :: c.cl }) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
  · cases b
    · exact VP.block_nil fun σ s h => h.1.1
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: a seed

`attempt_vp`: q from the seed and its test, the search for p, the search for
g over the window after p's witnesses and the check, as
`VG.Proof.Dsa.Generation.refillAttempt` describes them: `fStatus` := 2 when
`rand` runs out, 1 with p‖q‖g at `sPacked` when the domain passes, and
`fUsed` the octets read.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (Rest Upd wp_dp op2_reg dpVal)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
open VG.Proof.Dsa.Generation (windowCandidates generatorCount refillAttempt)

variable {umaal : Bool}

/-! ## The result of a seed -/

/-- The search for g over the window after p's witnesses `r`, and the check:
`refillAttempt`'s last stage. -/
def winResult (pLen p q : Nat) (r : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.generator p q (windowCandidates pLen Spec.Dsa.generatorAttempts r) with
  | none =>
    if Spec.Dsa.generatorAttempts * pLen ≤ r.length then some (none, r.drop (Spec.Dsa.generatorAttempts * pLen))
    else none
  | some g =>
    some (if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none,
      r.drop (pLen * generatorCount p q (windowCandidates pLen Spec.Dsa.generatorAttempts r)))

/-- The search for p from the seed, then `winResult`. -/
def primeRes (pLen qLen q : Nat) (seed r : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) q seed r with
  | none => none
  | some (none, r') => some (none, r')
  | some (some p, r') => winResult pLen p q r'

theorem refillAttempt_eq (pLen qLen : Nat) (seed rest : List Byte) :
    refillAttempt pLen qLen seed rest =
      match Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * qLen) seed) rest with
      | none => none
      | some (false, r) => some (none, r)
      | some (true, r) => primeRes pLen qLen (Spec.Dsa.qCandidate (8 * qLen) seed) seed r := by
  unfold refillAttempt primeRes winResult
  rfl

theorem generatorCount_none {p q : Nat} :
    ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none → generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, e => by
    rw [VG.Proof.Dsa.Generation.generator_cons'] at e
    simp only [generatorCount, List.length_cons]
    split at e
    · cases e
    · next hh => rw [ite_eq_right_of_eq_false _ _ (eq_false hh), generatorCount_none e]

theorem take_window {l : List Byte} {n : Nat} : l.take (min l.length n) = l.take n := by
  rcases Nat.le_total l.length n with h | h
  · rw [Nat.min_eq_left h, List.take_length, List.take_of_length_le h]
  · rw [Nat.min_eq_right h]

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The search's stage at the seed at `k`, with `n` seeds left: the cursor
`fC`, `fSeed`, `fSeedLeft`, `fStatus` and the padding. -/
abbrev aBase (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) : Cfg :=
  (((({ cl := [(G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 32 k)).setV fSeed
    (G.seeds + BitVec.ofNat 32 k)).setV fSeedLeft n).setV fStatus 0

/-- The stage after a seed. -/
def aOut (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) : Option (Option Spec.Dsa.Params × List Byte) → Cfg
  | none => (aBase G HO k n).setV fStatus 2
  | some (none, rest) => (aBase G HO k n).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))
  | some (some a, rest) =>
    (({ aBase G HO k n with cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] }).setV fUsed
      (BitVec.ofNat 32 (G.witLen - rest.length))).setV fStatus 1

theorem aBase_pnot (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) : PNot (aBase G HO k n) := by
  simp only [PNot]; decide

/-- The stage after p from the seed at `k`, with the witnesses up to `rest` read. -/
abbrev aPCfg (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) (p : Nat) (rest : List Byte) : Cfg :=
  ((pFound (aBase G HO k n) HO G k p).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))).setV fP 1

/-- The window: `fHs` := `rand + w`, `fHsLen` := its length. -/
theorem gWindow_vp {g : Geo} (hg : g.pLen = G.pLen) {c : Cfg} {w : Nat} (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 32 w) (hw : w ≤ G.witLen) :
    VP (St G c X) g.gWindow
      (St G ((c.setV fHs (G.wit + BitVec.ofNat 32 w)).setV fHsLen
        (BitVec.ofNat 32 (min (G.witLen - w) (128 * G.pLen)))) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  obtain hb : 128 * G.pLen < 2 ^ 32 := by omega_arith
  let c₁ : Cfg := c.setV fHs (G.wit + BitVec.ofNat 32 w)
  unfold Geo.gWindow
  rw [hg]
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hU).trans hUv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w) ∧ s.gpr .r0 = G.wit)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => h.1.1.fixedV (by simp [fixedWords])) fun σ s t ⟨⟨h, x⟩, r1⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w) ∧
      s.gpr .r0 = G.wit + BitVec.ofNat 32 w)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .add .r0 .r0 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2, h₂.2]
        · rw [h₁.1.2, h₂.1.2])
      fun σ s ⟨⟨⟨h, x⟩, r1⟩, r0⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩,
          by rw [u.gpr, dpVal, r0, r1]⟩) ?_
  refine VP.seq (G := fun σ s => St G c₁ X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w)
    (st_vp (c := fun _ => c) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r1⟩, r0⟩ h' R => ⟨⟨by rw [r0] at h'; exact h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  refine VP.seq (G := fun σ s => (St G c₁ X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w) ∧
      s.gpr .r0 = BitVec.ofNat 32 G.witLen)
    (ld_vp (c := fun _ => c₁) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => h.1.1.fixedV (by simp [fixedWords])) fun σ s t ⟨⟨h, x⟩, r1⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c₁ X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (G.witLen - w) ∧
      s.gpr .r1 = BitVec.ofNat 32 (128 * G.pLen)) ∧ isa.eval .eq s = some (decide (G.witLen - w < 128 * G.pLen)))
    (VP.block_append (G := fun σ s => St G c₁ X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (G.witLen - w) ∧
        s.gpr .r1 = BitVec.ofNat 32 (128 * G.pLen))
      (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
        (.block ([.dp .sub .r0 .r0 (.reg .r1)] ++ cst .r1 0)), rfl⟩
        (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.2, h₂.2]
          · rw [h₁.1.2, h₂.1.2])
        fun σ s ⟨⟨⟨h, x⟩, r1⟩, r0⟩ => ?_)
      (less_vp (x := BitVec.ofNat 32 (G.witLen - w)) (y := BitVec.ofNat 32 (128 * G.pLen)) (fun σ s h => h.2.1)
        (fun σ s h => h.2.2) fun σ s t ⟨⟨h, x⟩, r0, r1⟩ R m e => ⟨⟨⟨h.of_rest R m, x⟩, by rw [R.gpr _ (by decide), r0],
          by rw [R.gpr _ (by decide), r1]⟩, by
            have := h.gi.witLt
            rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
              Nat.mod_eq_of_lt hb]⟩)) ?_
  · have := h.gi.witLt
    simp only [List.cons_append, List.nil_append]
    refine wp_dp (op2_reg _ _) fun s₁ u₁ => ?_
    rw [← List.append_nil (cst .r1 _)]
    refine wp_cst hb fun t u => WP.block_nil ⟨⟨(h.of_rest (u₁.rest (ws := [.r0]) (by simp)) u₁.mem).of_rest
      (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, ?_, u.gpr⟩
    rw [u.other _ (by decide), u₁.gpr, dpVal, r0, r1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · refine st_vp (c := fun _ => c₁) (fun σ s h => h.1.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨⟨_, x⟩, r0, _⟩, e⟩, z⟩ h' _ => ⟨?_, x⟩
    obtain hl : G.witLen - w < 128 * G.pLen := by rw [e] at z; simpa using z
    rw [r0] at h'
    rw [Nat.min_eq_left (Nat.le_of_lt hl)]; exact h'
  · refine st_vp (c := fun _ => c₁) (fun σ s h => h.1.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨⟨_, x⟩, _, r1⟩, e⟩, z⟩ h' _ => ⟨?_, x⟩
    obtain hl : ¬G.witLen - w < 128 * G.pLen := by rw [e] at z; simpa using z
    rw [r1] at h'
    rw [Nat.min_eq_right (by omega_arith)]; exact h'

/-- `fUsed` := past the candidates the search for g read. -/
theorem gUsed_vp {c : Cfg} {x : Nat} (hH : fH ∈ c.LS) (hHv : c.V fH = G.wit + BitVec.ofNat 32 x) :
    VP (St G c X) Geo.gUsed (St G (c.setV fUsed (BitVec.ofNat 32 x)) X) := by
  unfold Geo.gUsed
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = G.wit + BitVec.ofNat 32 x)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hH).trans hHv)
      fun σ s t ⟨h, x'⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x'⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r0 = G.wit + BitVec.ofNat 32 x) ∧ s.gpr .r1 = G.wit)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => h.1.1.fixedV (by simp [fixedWords])) fun σ s t ⟨⟨h, x'⟩, r0⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x'⟩, by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 x)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .sub .r0 .r0 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x'⟩, r0⟩, r1⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x'⟩,
          by rw [u.gpr, dpVal, r0, r1, BitVec.add_comm, BitVec.add_sub_cancel]⟩) ?_
  exact st_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
    fun σ s t ⟨⟨_, x'⟩, r0⟩ h' _ => ⟨r0 ▸ h', x'⟩

/-- Without a g: `fStatus` := 2 if the window was short. -/
theorem gShort_vp {g : Geo} (hg : g.pLen = G.pLen) {c : Cfg} {HL : Nat} (hL : fHsLen ∈ c.LS)
    (hLv : c.V fHsLen = BitVec.ofNat 32 HL) (h32 : HL < 2 ^ 32) :
    VP (St G c X) g.gShort (St G (if HL < 128 * G.pLen then c.setV fStatus 2 else c) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  obtain hb : 128 * G.pLen < 2 ^ 32 := by omega_arith
  unfold Geo.gShort
  rw [hg]
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 HL)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hL).trans hLv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G c X σ s ∧ isa.eval .eq s = some (decide (HL < 128 * G.pLen)))
    (VP.block_append (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 HL ∧
        s.gpr .r1 = BitVec.ofNat 32 (128 * G.pLen))
      (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block (cst .r1 0)), rfl⟩
        (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨⟨h, x⟩, r0⟩ => by
          rw [← List.append_nil (cst .r1 _)]
          exact wp_cst hb fun t u => WP.block_nil ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
            by rw [u.other _ (by decide), r0], u.gpr⟩)
      (less_vp (x := BitVec.ofNat 32 HL) (y := BitVec.ofNat 32 (128 * G.pLen)) (fun σ s h => h.2.1)
        (fun σ s h => h.2.2) fun σ s t ⟨⟨h, x⟩, _, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by
          rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt hb]⟩)) ?_
  by_cases hs : HL < 128 * G.pLen
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => c) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hs] at z)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
    exact VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hs] at z)
      (VP.block_nil fun σ s h => h.1.1)

/-- The search for g over the window after `rest` and the check, after p. -/
theorem attemptG_vp {g : Geo} {n : Nat} (HO : HashOk Gh) (certs : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters umaal)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e) (hL : HO.P.L = 8) (hwl : G.witB.length = G.witLen)
    (h32 : G.witLen < 2 ^ 32)
    {k p : Nat} {n' : BitVec 32} {rest : List Byte} (hrest : G.witB.drop (G.witLen - rest.length) = rest)
    (hpd : VG.Proof.Dsa.Generation.PDomain G.pLen p)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aPCfg G HO k n' p rest) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [g.gWindow, g.gPart, Geo.gUsed, .block (cmpF fG 1), .ite .eq g.checkPart g.gShort])
      (St G (aOut G HO k n' (winResult G.pLen p (Spec.Dsa.decodeBE (qBytes G k)) rest)) X) := by
  obtain hq0 : 0 < G.qLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  obtain hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hlq1 : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := hpd.width
  obtain hl384 : G.pLen ≤ 384 := by omega_arith
  obtain hrl : rest.length ≤ G.witLen := by
    have := congrArg List.length hrest; simp only [List.length_drop, hwl] at this; omega_arith
  generalize hqv : Spec.Dsa.decodeBE (qBytes G k) = qv at hqlo ⊢
  obtain qpos : 0 < qv := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  -- (p − 1) / q fits the exponent's words.
  obtain hev : (p - 1) / qv < 2 ^ (32 * g.e) := by
    have hp := hpd.upper
    refine (Nat.div_lt_iff_lt_mul qpos).mpr ?_
    calc p - 1 < 2 ^ (8 * G.pLen) := by omega_arith
      _ = 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * 2 ^ (8 * G.qLen - 1) := by rw [← Nat.pow_add]; congr 1; omega_arith
      _ ≤ 2 ^ (32 * g.e) * qv := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) he) hqlo
  obtain pl := padTail_length HO.md (n := G.qLen) (by omega_arith) hL
  generalize hw : G.witLen - rest.length = w at hrest
  generalize hHL : min (G.witLen - w) (128 * G.pLen) = HL
  let c₁ : Cfg := ((aPCfg G HO k n' p rest).setV fHs (G.wit + BitVec.ofNat 32 w)).setV fHsLen (BitVec.ofNat 32 HL)
  obtain hHL32 : HL < 2 ^ 32 := by omega_arith
  obtain hwHL : w + HL ≤ G.witLen := by omega_arith
  refine VP.seq (G := St G c₁ X) ((gWindow_vp (w := w) hp (by simp) (by simp [upd, fP, fUsed, ← hw])
    (by omega_arith)).mono (fun _ _ h => h) fun σ s h => by rw [hHL] at h; exact h) ?_
  refine VP.seq (gPart_vp (c := c₁) (pv := p) (ev := (p - 1) / qv) (qv := qv) (w := w) (HL := HL) certs ok hp hlq1
    hn hpm hpb hpe hpr hctx he4 he0 (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP])
    (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, hqv])
    (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1])
    (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1, aOne])
    (by simp [c₁, aH, aP, aE, aPm1, aOne]) (by simp [c₁, aTmp, aP, aE, aPm1, aOne])
    (by simp [c₁, aG, aP, aE, aPm1, aOne]) rfl hpd.odd
    (by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega_arith); omega_arith)
    hpd.upper hev (fun x hx => ?_) (by simp [c₁]) (by simp [c₁, upd, fHs, fHsLen]) (by simp [c₁]) (by simp [c₁])
    hwHL hwl hHL32 (by simp [c₁]; decide) (by simp [c₁]; decide) rfl) ?_
  · simp only [c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sG]; omega_arith
    · simp only [pl, sG]; omega_arith
    · simp only [hql, sQ, sG]; omega_arith
  -- The window's candidates are the spec's.
  obtain hcand : gCands G w HL 0 = windowCandidates G.pLen Spec.Dsa.generatorAttempts rest := by
    simp only [gCands, hsW, Nat.zero_mul, List.drop_zero, hrest, windowCandidates]
    rw [← hHL, show G.witLen - w = rest.length by omega_arith, take_window,
      show 128 * G.pLen = Spec.Dsa.generatorAttempts * G.pLen from rfl]
  unfold winResult
  rw [← hcand]
  rcases hgv : Spec.Dsa.generator p qv (gCands G w HL 0) with _ | gv
  · -- No g: a short window ran out.
    obtain hfin : gFin c₁ G w HL p qv = (c₁.setV fG 2).setV fH
        (G.wit + BitVec.ofNat 32 (w + gNum G w HL p qv 0 * G.pLen)) := by simp only [gFin, gRes, hgv]
    rw [hfin]
    refine VP.seq (gUsed_vp (x := w + gNum G w HL p qv 0 * G.pLen) (by simp) (by simp [upd])) ?_
    refine VP.seq (G := fun σ s => St G (((c₁.setV fG 2).setV fH
        (G.wit + BitVec.ofNat 32 (w + gNum G w HL p qv 0 * G.pLen))).setV fUsed
          (BitVec.ofNat 32 (w + gNum G w HL p qv 0 * G.pLen))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fG, fH, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine (gShort_vp hp (HL := HL) (by simp [c₁]) (by simp [c₁, upd, fHsLen, fG, fH, fUsed]) hHL32).mono
      (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    obtain hnum : gNum G w HL p qv 0 = (gCands G w HL 0).length := generatorCount_none hgv
    by_cases hs : HL < 128 * G.pLen
    · have hshort : ¬Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega_arith
      simp only [hs, hshort, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed, fC]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [c₁, pRest]
    · have hfull : Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega_arith
      obtain hlen : (gCands G w HL 0).length = 128 := by
        rw [hcand]
        simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range,
          List.length_take, Spec.Dsa.generatorAttempts]
        rw [Nat.min_eq_left (by omega_arith), Nat.mul_div_cancel _ (by omega_arith)]
      simp only [hs, hfull, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl
        · refine ⟨by simp, ?_⟩
          simp only [upd, ↓reduceIte, List.length_drop, hnum, hlen, Spec.Dsa.generatorAttempts]
          congr 1; omega_arith
        all_goals exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft,
          fSeed, fC]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [c₁, pRest]
  · -- g: the check.
    obtain hgb := VG.Proof.Dsa.Generation.generator_bounds (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hpd.lower) _ hgv
    obtain hpl8 : (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) := by rw [Nat.pow_mul]
    obtain hql8 : (256 : Nat) ^ G.qLen = 2 ^ (8 * G.qLen) := by rw [Nat.pow_mul]
    obtain qlt : qv < 2 ^ (8 * G.qLen) := by
      rw [← hqv, ← hql8, ← hql]; exact VG.Proof.Dsa.decodeBE_lt _
    obtain hpk : pkOf (Spec.Rsa.i2osp p G.pLen) (qBytes G k) (Spec.Rsa.i2osp gv G.pLen) =
        Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩ := by
      obtain hqb : qBytes G k = Spec.Rsa.i2osp qv G.qLen := by
        rw [← hqv, ← VG.Proof.Dsa.encodeBE_i2osp, ← hql, VG.Proof.Dsa.encodeBE_decodeBE]
      simp only [pkOf, Spec.Dsa.encodeParams, VG.Proof.Dsa.encodeBE_i2osp, hqb]
    obtain hok : Spec.Dsa.checkParametersBytes G.pLen G.qLen
        (pkOf (Spec.Rsa.i2osp p G.pLen) (qBytes G k) (Spec.Rsa.i2osp gv G.pLen)) =
        decide (Spec.Dsa.parametersValid ⟨p, qv, gv⟩) := by
      rw [hpk]
      exact VG.Proof.Dsa.Generation.check_encodedParams (by
          unfold Spec.Dsa.generationLengthsValid at hlq; unfold Spec.Dsa.lengthsValid; omega_using [hlq])
        (by rw [hpl8]; exact hpd.upper) (by rw [hql8]; exact qlt) (by rw [hpl8]; exact Nat.lt_trans hgb.2 hpd.upper)
    let xu := w + gNum G w HL p qv 0 * G.pLen
    let Dg : Cfg := ((({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 32 xu)).setV fUsed (BitVec.ofNat 32 xu)
    obtain hfin : gFin c₁ G w HL p qv = (({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV
        fH (G.wit + BitVec.ofNat 32 xu) := by simp only [gFin, gRes, hgv, xu]
    rw [hfin]
    refine VP.seq (G := St G Dg X) (gUsed_vp (x := xu) (by simp) (by simp [upd])) ?_
    refine VP.seq (G := fun σ s => St G Dg X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [Dg])).trans (by simp [Dg, upd, fG, fH, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    refine (checkPart_vp (c := Dg) (X := X) hp hq hck hlq (pB := Spec.Rsa.i2osp p G.pLen) (qB := qBytes G k)
      (gB := Spec.Rsa.i2osp gv G.pLen) (by simp [Dg, c₁, pRest]) (by simp [Dg, c₁, pRest]) (by simp [Dg])
      (VG.Proof.Rsa.i2osp_length _ _) hql (VG.Proof.Rsa.i2osp_length _ _) (fun x hx => ?_) (by simp [Dg, c₁]; decide)
      (by simp [Dg, c₁]; decide)).mono (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    · simp only [Dg, c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length, sG, sPacked]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sPacked]; omega_arith
      · simp only [pl, sPacked]; omega_arith
      · simp only [hql, sQ, sPacked]; omega_arith
    obtain hU : G.witLen - (rest.drop (G.pLen * gNum G w HL p qv 0)).length = xu := by
      simp only [List.length_drop, xu]; rw [Nat.mul_comm G.pLen]
      obtain h1 := VG.Proof.Dsa.Generation.generatorCount_le p qv (gCands G w HL 0)
      obtain h2 : (gCands G w HL 0).length * G.pLen ≤ rest.length := by
        rw [hcand]
        simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range]
        exact Nat.le_trans (Nat.div_mul_le_self _ _) (by simp only [List.length_take]; exact Nat.min_le_right _ _)
      obtain h3 := Nat.le_trans (Nat.mul_le_mul_right G.pLen h1) h2
      simp only [gNum] at h3 ⊢
      omega_arith
    rw [hok] at h
    by_cases hv : Spec.Dsa.parametersValid ⟨p, qv, gv⟩
    · simp only [hv, decide_true, ckCfg, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut, hU]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg, c₁], by simp [Dg, c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed,
            fC]⟩
      · change y ∈ [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩)] at hy
        rw [List.mem_singleton] at hy; subst hy; rw [← hpk]; simp
    · simp only [hv, decide_false, ckCfg, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut, hU]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg, c₁], by simp [Dg, c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed,
            fC]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [Dg, c₁, pRest]

/-- The stage after q passes, with the witnesses up to `r` read. -/
abbrev aQCfg (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) (u : Nat) (r : List Byte) : Cfg :=
  testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k) G.witLen (some (true, r))

/-- The candidates of the counters are the spec's. -/
theorem pCand_spec (HO : HashOk Gh) {k : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hk4 : 4 * Gh.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen) (hk : k + G.qLen ≤ G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen) (j : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j := by
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  obtain hc : G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  refine VG.Proof.Dsa.Arm.Gen.pCandidate_xBytes HO (fun i => ?_) hH hsl hlen (by omega_arith) hc _
  rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]

/-- The search for p, then g and the check, after q. -/
theorem attemptP_vp {g : Geo} {n : Nat} (HO : HashOk g.G) (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen) (gcerts : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters umaal) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e)
    (h32 : G.witLen < 2 ^ 32)
    {k u : Nat} {n' : BitVec 32} {r : List Byte} (hk : k + G.qLen ≤ G.seedsLen)
    (hr : G.witB.drop (G.witLen - r.length) = r)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aQCfg G HO k n' u r) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [g.pPart, .block (cmpF fP 0),
        .ite .eq (.block (stImm fStatus 2))
          (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fP 1),
            .ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [g.gWindow, g.gPart, Geo.gUsed, .block (cmpF fG 1),
              .ite .eq g.checkPart g.gShort])
              (.block [])])])
      (St G (aOut G HO k n' (primeRes G.pLen G.qLen (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r)) X) := by
  have hlq' : Spec.Dsa.generationLengthsValid G.pLen G.qLen := hlq
  obtain hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega_arith
  obtain pl := padTail_length HO.md (n := G.qLen) (by omega_arith) HO.hL
  refine VP.seq (pPart_vp (c := aBase G HO k n') (u0 := G.witLen - r.length) (d := aQCfg G HO k n' u r) HO okp certs hlq
    hp hq hk4 hsb hH hwl hsize (aBase_pnot G HO k n') hk (by simp) (by simp [upd, fSeed, fStatus, fSeedLeft])
    (by omega_arith) (pCand_spec HO hlq hk4 hsb hk hH hlen) (by simp [testCfg])
    (by simp [testCfg, upd]) (fun o ho => ⟨by simp [testCfg, ho], by
      change o ∈ [fStatus, fSeedLeft, fSeed, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp [testCfg, upd, fUsed, fRes, fStatus, fSeedLeft, fSeed, fC]⟩)
    (by simp [testCfg, qClaims]) (by simp [testCfg, qClaims])) ?_
  obtain hS0 : pSpec HO G k (G.witLen - r.length) 0 = Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r := by
    rw [pSpec, VG.Proof.Dsa.Generation.primeSearch_start, pU, hr]
  rw [hS0]
  unfold primeRes
  rcases hR : Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r
    with _ | ⟨_ | p, r'⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G ((pNone (aBase G HO k n') HO G).setV fP 0) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [pFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => (pNone (aBase G HO k n') HO G).setV fP 0) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fP, fStatus, fSeedLeft, fSeed, fC]⟩
  · -- No p: the next seed.
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k n') HO G).setV fUsed
        (BitVec.ofNat 32 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [pFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k n') HO G).setV fUsed
        (BitVec.ofNat 32 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by simp [upd, fUsed, fP, fStatus, fSeedLeft, fSeed, fC]⟩
  · -- p: g and the check.
    obtain hpd := VG.Proof.Dsa.Generation.primeSearch_domain hw hlen _ _ _ _ hR
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k n' p r') X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k n' p r') X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptG_vp HO gcerts ok hp hq hck hlq' hn hpm hpb hpe hpr hctx he4 he0 he HO.hL hwl h32 (rest := r') (by
        rw [← hwl]; exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.primeSearch_suffix _ _ _ hR).trans (hr ▸ List.drop_suffix _ _)))
        hpd hql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

/-- A seed: q, its test, then p, g and the check. -/
theorem attempt_vp {g : Geo} {n : Nat} (HO : HashOk g.G) (okq : PrimeOk (8 * G.qLen) g.qCode)
    (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen) (gcerts : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    (hsizeq : keyOff + 8 * keyWords (8 * G.qLen) ≤ wa G.pLen) (hb8 : 8 * G.qLen / 8 ≤ wa G.pLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters umaal) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e)
    (h32 : G.witLen < 2 ^ 32)
    {k u : Nat} {n' : BitVec 32} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) X) g.attempt
      (St G (aOut G HO k n' (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) := by
  obtain hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by have := hlen (seedAt G k); omega_arith
  obtain hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_arith
  obtain ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  obtain hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [hHq])
  obtain hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
  unfold Geo.attempt
  refine VP.seq (qPart_vp (c := (aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) HO okq hlq hp hq hk4 hH hwl hsb
    hsizeq hb8 hk hu (by simp) (by simp [upd, fUsed, fSeed, fStatus, fSeedLeft]) (by simp)
    (by simp [upd]) (by simp; decide) (by simp; decide) (by simp)) ?_
  rw [refillAttempt_eq]
  rcases hpp : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u)
    with _ | ⟨_ | _, r⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen none) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen none) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q is not prime: the next seed.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q: p, g and the check.
    obtain hr : G.witB.drop (G.witLen - r.length) = r := by
      rw [← hwl]; exact VG.Proof.Dsa.Generation.probablePrime_cursor hpp
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k n' u r) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k n' u r) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    rw [← hqv]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptP_vp HO okp certs gcerts ok hlq hp hq hk4 hsb hH hwl hsize hlen hck hn hpm hpb hpe hpr hctx he4 he0
        he h32 hk hr ql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: the controller

`sLoop_vp`: the seeds, one at a time from the cursor `fC`, with `fSeedLeft`
seeds left, until one gives a domain (`fStatus` := 1, p‖q‖g at `sPacked`),
`rand` runs out (2) or the seeds do (3), as `Spec.Dsa.parameterSearch` tries
them (`Proof/Dsa/Generation/RefillSearch.lean`): the stage it ends at is
`cFin`, and its result as the spec states it `cRes`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
open VG.Proof.Dsa.Generation (refillAttempt ranOutResult)

/-- What a geometry's code and the tape give the search. -/
structure GenOk (G : GP) (g : Geo) (HO : HashOk g.G) (n : Nat) : Prop where
  okq : PrimeOk (8 * G.qLen) g.qCode
  okp : PrimeOk (8 * G.pLen) g.pCode
  certs : PArithCerts G.pLen G.qLen
  gcerts : GStepCerts g
  pow : PowOk n g.e g.powCode
  hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  hp : g.pLen = G.pLen
  hq : g.qLen = G.qLen
  hk4 : 4 * g.G.k = G.qLen
  hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m
  hwl : G.witB.length = G.witLen
  hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen
  hsizeq : keyOff + 8 * keyWords (8 * G.qLen) ≤ wa G.pLen
  hb8 : 8 * G.qLen / 8 ≤ wa G.pLen
  hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen
  hck : ∃ umaal, g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters umaal
  hn : 8 * n = G.pLen
  hpm : g.powMod = modS n
  hpb : g.powBase = baseS n
  hpe : g.powExp = expS n
  hpr : g.powRes = resS n
  hctx : contextBytes n ≤ wa G.pLen
  he4 : 4 * g.e ≤ 8 * n
  he0 : 0 < g.e
  he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e
  h32 : G.witLen < 2 ^ 32
  hqL : G.qLen = Spec.Dsa.generationQLen G.pLen
  k0 : G.k0 ≤ Spec.Dsa.parameterSeeds

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

theorem GenOk.attempt_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {k u : Nat} {n' : BitVec 32}
    (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) X) g.attempt
      (St G (aOut G HO k n' (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) := by
  obtain ⟨_, hck⟩ := O.hck
  exact VG.Proof.Dsa.Arm.Gen.attempt_vp HO O.okq O.okp O.certs O.gcerts O.pow O.hlq O.hp O.hq O.hk4 O.hwl O.hH O.hwl
    O.hsize O.hsizeq O.hb8 O.hlen hck O.hn O.hpm O.hpb O.hpe O.hpr O.hctx O.he4 O.he0 O.he O.h32 hk hu

/-! ## The controller's pieces -/

/-- Whether a seed's octets are left after the cursor `c`. -/
theorem avail_vp {g : Geo} (hq : g.qLen = G.qLen) {d : Cfg} {c : Nat} (hC : fC ∈ d.LS)
    (hCv : d.V fC = BitVec.ofNat 32 c) (hc : c ≤ G.witLen) (h32 : G.witLen < 2 ^ 32) (hq16 : G.qLen < 2 ^ 16) :
    VP (St G d X) g.avail
      (fun σ s => St G d X σ s ∧ isa.eval .eq s = some (decide (G.witLen - c < G.qLen))) := by
  unfold Geo.avail
  rw [hq]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 G.witLen)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => h.1.fixedV (by simp [fixedWords]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 G.witLen) ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (by decide) (fun σ s h => (h.1.1.slotV hC).trans hCv)
      fun σ s t ⟨⟨h, x⟩, r0⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (G.witLen - c) ∧
      s.gpr .r1 = BitVec.ofNat 32 G.qLen)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .sub .r0 .r0 (.reg .r1), .movw .r1 (BitVec.ofNat 16 0)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => wp_dp (op2_reg _ _) fun s₁ u₁ => wp_movw fun t u => WP.block_nil
        ⟨⟨(h.of_rest (u₁.rest (ws := [.r0]) (by simp)) u₁.mem).of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
          ?_, by rw [u.gpr, setWidth_ofNat16 hq16]⟩) ?_
  · rw [u.other _ (by decide), u₁.gpr, dpVal, r0, r1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  exact less_vp (x := BitVec.ofNat 32 (G.witLen - c)) (y := BitVec.ofNat 32 G.qLen) (fun σ s h => h.2.1)
    (fun σ s h => h.2.2) fun σ s t ⟨⟨h, x⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by
      rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]⟩

/-- The seed at the cursor `c`: `fSeed` := `rand + c`, its witnesses from `c + q_len`. -/
theorem seedStart_vp {g : Geo} (hq : g.qLen = G.qLen) {d : Cfg} {c : Nat} (hC : fC ∈ d.LS)
    (hCv : d.V fC = BitVec.ofNat 32 c) (hq8 : G.qLen < 256) :
    VP (St G d X) g.seedStart
      (St G ((d.setV fSeed (G.seeds + BitVec.ofNat 32 c)).setV fUsed (BitVec.ofNat 32 (c + G.qLen))) X) := by
  unfold Geo.seedStart
  rw [hq]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = G.wit)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => h.1.fixedV (by simp [fixedWords]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = G.wit) ∧ s.gpr .r1 = BitVec.ofNat 32 c)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (by decide) (fun σ s h => (h.1.1.slotV hC).trans hCv)
      fun σ s t ⟨⟨h, x⟩, r0⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = G.seeds + BitVec.ofNat 32 c) ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .add .r0 .r0 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r0, r1]⟩,
          by rw [u.other _ (by decide), r1]⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fSeed (G.seeds + BitVec.ofNat 32 c)) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r0⟩, r1⟩ h' R => ⟨⟨r0 ▸ h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fSeed (G.seeds + BitVec.ofNat 32 c)) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (c + G.qLen))
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_dp (op2_imm (encodable_lt hq8)) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r1, BitVec.ofNat_add]⟩) ?_
  exact st_vp (c := fun _ => d.setV fSeed (G.seeds + BitVec.ofNat 32 c)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩

/-- A rejected seed: the cursor past it, one seed fewer left. -/
theorem rejected_vp {d : Cfg} {u j : Nat} (hU : fUsed ∈ d.LS) (hUv : d.V fUsed = BitVec.ofNat 32 u)
    (hL : fSeedLeft ∈ d.LS) (hLv : d.V fSeedLeft = BitVec.ofNat 32 (j + 1)) (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) Geo.rejected
      (St G ((d.setV fC (BitVec.ofNat 32 u)).setV fSeedLeft (BitVec.ofNat 32 j)) X) := by
  unfold Geo.rejected
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 u)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hU).trans hUv)
      fun σ s t ⟨h, x⟩ u' => ⟨⟨h.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, u'.gpr⟩) ?_
  refine VP.seq (G := St G (d.setV fC (BitVec.ofNat 32 u)) X)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r0⟩ h' _ => ⟨r0 ▸ h', x⟩) ?_
  obtain hL' : fSeedLeft ∈ (d.setV fC (BitVec.ofNat 32 u)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := fun σ s => St G (d.setV fC (BitVec.ofNat 32 u)) X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (j + 1))
    (ld_vp (c := fun _ => d.setV fC (BitVec.ofNat 32 u)) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hL').trans ((upd_ne (o := fC) d.V (BitVec.ofNat 32 u) (by decide)).trans hLv))
      fun σ s t ⟨h, x⟩ u' => ⟨⟨h.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, u'.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fC (BitVec.ofNat 32 u)) X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 j)
    (VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0])
      (.block [.dp .sub .r0 .r0 (.imm 1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r0⟩ => wp_dp (op2_imm (by decide)) fun t u' => WP.block_nil
        ⟨⟨h.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, ?_⟩) ?_
  · rw [u'.gpr, dpVal, r0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    have := hj
    omega_arith
  exact st_vp (c := fun _ => d.setV fC (BitVec.ofNat 32 u)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r0⟩ h' _ => ⟨r0 ▸ h', x⟩

/-! ## The controller's spec -/

/-- The seed at the cursor `c`, as the code runs it. -/
abbrev sR (G : GP) (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  refillAttempt G.pLen G.qLen (seedAt G c) (G.witB.drop (c + G.qLen))

/-- The controller's seeds left and cursor after `i` iterations. -/
def sPos (G : GP) : Nat → Nat × Nat
  | 0 => (G.k0, 0)
  | i + 1 => match sR G (sPos G i).2 with
    | some (none, rest) => ((sPos G i).1 - 1, G.witLen - rest.length)
    | _ => sPos G i

/-- The iterations, from the `i`-th at the cursor `c` with `j` seeds left. -/
def sCount (G : GP) : Nat → Nat → Nat → Nat
  | 0, _, i => i + 1
  | j + 1, c, i => if G.witLen - c < G.qLen then i + 1 else match sR G c with
    | some (none, rest) => sCount G j (G.witLen - rest.length) (i + 1)
    | _ => i + 1

theorem sCount_gt (G : GP) : ∀ j c i, i < sCount G j c i
  | 0, c, i => by simp [sCount]
  | j + 1, c, i => by
    have := sCount_gt G j
    simp only [sCount]; split
    · omega_arith
    · split
      · exact Nat.lt_of_succ_lt (this _ _)
      all_goals omega_arith

/-- How the controller ends. -/
inductive COut where
  | found (a : Spec.Dsa.Params) (u : Nat)
  | noSeeds (c : Nat)
  | ranOut (j c : Nat)

/-- The controller's end from seeds left `j` and the cursor `c`. -/
def cOutAt (G : GP) : Nat × Nat → COut
  | (0, c) => .noSeeds c
  | (j + 1, c) => if G.witLen - c < G.qLen then .ranOut (j + 1) c else match sR G c with
    | some (some a, rest) => .found a (G.witLen - rest.length)
    | _ => .ranOut (j + 1) c

/-- The stage it ends at. -/
def cFin (G : GP) : COut → Cfg
  | .found a u => ({ cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] } : Cfg).setV fUsed
      (BitVec.ofNat 32 u) |>.setV fStatus 1
  | .noSeeds c => (({} : Cfg).setV fC (BitVec.ofNat 32 c)).setV fStatus 3
  | .ranOut j c => ((({} : Cfg).setV fC (BitVec.ofNat 32 c)).setV fSeedLeft (BitVec.ofNat 32 j)).setV fStatus 2

/-- Its result, as the spec states it. -/
def cRes (G : GP) : COut → Spec.Dsa.ParameterSearchResult
  | .found a u => ⟨.accepted a, u, []⟩
  | .noSeeds c => ⟨.exhausted, c, []⟩
  | .ranOut j c => ranOutResult G.pLen j (G.witLen - c) c

/-- Its words' bounds. -/
def cOk (G : GP) : COut → Prop
  | .found _ u => u ≤ G.witLen
  | .noSeeds c => c ≤ G.witLen
  | .ranOut j c => c ≤ G.witLen ∧ j ≤ Spec.Dsa.parameterSeeds

/-- The whole search's result. -/
abbrev sW (G : GP) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch G.pLen G.k0 G.witB

/-- The controller's stage at the cursor `c` with `j` seeds left. -/
abbrev cBase (G : GP) (HO : HashOk Gh) (c j : Nat) : Cfg :=
  ((({ cl := [(G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 32 c)).setV fSeedLeft
    (BitVec.ofNat 32 j)).setV fStatus 0

/-- The search with `r` iterations left of `N`. -/
abbrev sInv (G : GP) (HO : HashOk Gh) (N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ sCount G (sPos G (N - r)).1 (sPos G (N - r)).2 (N - r) = N ∧
    (Spec.Dsa.parameterSearch G.pLen (sPos G (N - r)).1 (G.witB.drop (sPos G (N - r)).2)).consume
      (sPos G (N - r)).2 [] = sW G ∧
    (sPos G (N - r)).2 ≤ G.witLen ∧ (sPos G (N - r)).1 ≤ Spec.Dsa.parameterSeeds) ∧
    St G (cBase G HO (sPos G (N - r)).2 (sPos G (N - r)).1) X σ s

/-- The controller's end. -/
abbrev cOut (G : GP) (N : Nat) : COut := cOutAt G (sPos G (N - 1))

theorem sBody_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) {N : Nat} (r : Nat) :
    VP (sInv G HO N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fSeedLeft 0),
        .ite .eq (.block (stImm fStatus 3))
          (VG.Impl.Rsa.Arm.Keys.seqs [g.avail,
            .ite .eq (.block (stImm fStatus 2))
              (VG.Impl.Rsa.Arm.Keys.seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite .eq Geo.rejected (.block [])])]),
        .block (cmpF fStatus 0)])
      (fun σ s => isa.eval .eq s = some (decide (0 < r)) ∧
        (r = 0 → St G (cFin G (cOut G N)) X σ s ∧ cRes G (cOut G N) = sW G ∧ cOk G (cOut G N)) ∧
        (0 < r → sInv G HO N X r σ s)) := by
  refine VG.Proof.Dsa.Arm.Gen.VP.intro fun ⟨hr, hc, hW, hcw, hj⟩ => ?_
  obtain hq0 : 0 < G.qLen := by have := O.hlq; omega_arith
  obtain hq8 : G.qLen < 256 := by have := O.hlq; omega_arith
  obtain hpL : 0 < G.pLen := by have := O.hlq; omega_arith
  have h32 := O.h32
  have hwl := O.hwl
  have hqL := O.hqL
  generalize hii : N - (r + 1) = i at hc hW hcw hj
  generalize hp : sPos G i = jc at hc hW hcw hj
  obtain ⟨j, c⟩ := jc
  dsimp only at hc hW hcw hj
  obtain hNi : N - 1 = i + r := by omega_arith
  refine VP.seq (G := fun σ s => St G (cBase G HO c j) X σ s ∧
      isa.eval .eq s = some (BitVec.ofNat 32 j == BitVec.ofNat 32 0))
    (cmpF_vp (x := BitVec.ofNat 32 j) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fSeedLeft, fStatus]))
      fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, e⟩) ?_
  obtain jl : j < 2 ^ 32 := by simp only [Spec.Dsa.parameterSeeds] at hj; omega_arith
  rcases j with _ | j
  · -- No seeds left: `fStatus` := 3.
    obtain r0 : r = 0 := by simp only [sCount] at hc; omega_arith
    subst r0
    obtain hout : cOut G N = .noSeeds c := by simp only [cOut, hNi, Nat.add_zero, hp, cOutAt]
    refine VP.seq (G := St G ((cBase G HO c 0).setV fStatus (BitVec.ofNat 32 3)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => cBase G HO c 0) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)) ?_
    refine cmpF_vp (x := BitVec.ofNat 32 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
    · rw [hout]
      refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
        (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
      change o ∈ [fStatus, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
    · rw [hout, ← hW]; exact (VG.Proof.Dsa.Generation.search_zero _ _ _).symm
    · rw [hout]; exact hcw
  · have e0 : (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega_arith
    obtain notZ : ∀ {G₁ : State → State → Prop} {c' : Prog isa}, VP (fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval .eq s = some (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0)) ∧
        isa.eval .eq s = some true) c' G₁ :=
      VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    obtain avail := (avail_vp (X := X) O.hq (d := cBase G HO c (j + 1)) (by simp)
      (by simp [upd, fC, fSeedLeft, fStatus]) hcw h32 (by omega_arith)).mono
      (F' := fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval .eq s = some (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0)) ∧
        isa.eval .eq s = some false) (fun σ s h => h.1.1) fun _ _ h => h
    by_cases hshort : G.witLen - c < G.qLen
    · -- Too few octets for a seed: `fStatus` := 2.
      obtain r0 : r = 0 := by simp only [sCount, hshort, ↓reduceIte] at hc; omega_arith
      subst r0
      obtain hout : cOut G N = .ranOut (j + 1) c := by
        simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte]
      refine VP.seq (G := St G ((cBase G HO c (j + 1)).setV fStatus (BitVec.ofNat 32 2)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (stImm_vp (c := fun _ => cBase G HO c (j + 1)) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
            fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
      · rw [hout]
        refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
          (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
        change o ∈ [fStatus, fSeedLeft, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
      · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_short (by rw [hwl, ← hqL]; exact hshort), hwl]
      · rw [hout]; exact ⟨hcw, hj⟩
    · -- A seed.
      obtain hcq : c + G.qLen ≤ G.witLen := by omega_arith
      obtain attempt := O.attempt_vp (X := X) (k := c) (u := c + G.qLen) (n' := BitVec.ofNat 32 (j + 1)) hcq hcq
      obtain hmono : ∀ σ s, St G (((cBase G HO c (j + 1)).setV fSeed (G.seeds + BitVec.ofNat 32 c)).setV fUsed
          (BitVec.ofNat 32 (c + G.qLen))) X σ s →
          St G ((aBase G HO c (BitVec.ofNat 32 (j + 1))).setV fUsed (BitVec.ofNat 32 (c + G.qLen))) X σ s := by
        intro σ s h
        refine ⟨h.1.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
          (fun _ h' => absurd h' (by simp)), h.2⟩
        change o ∈ [fUsed, fStatus, fSeedLeft, fSeed, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp, by simp [upd, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
      obtain start := (seedStart_vp (X := X) O.hq (d := cBase G HO c (j + 1)) (c := c) (by simp)
        (by simp [upd, fC, fSeedLeft, fStatus]) hq8).mono (F' := fun σ s =>
          (St G (cBase G HO c (j + 1)) X σ s ∧ isa.eval .eq s = some (decide (G.witLen - c < G.qLen))) ∧
          isa.eval .eq s = some false) (fun σ s h => h.1.1) hmono
      obtain wrap : ∀ {G₁ : State → State → Prop}, VP (St G ((aBase G HO c (BitVec.ofNat 32 (j + 1))).setV fUsed
          (BitVec.ofNat 32 (c + G.qLen))) X) (VG.Impl.Rsa.Arm.Keys.seqs [g.attempt, .block (cmpF fStatus 0),
            .ite .eq Geo.rejected (.block [])]) G₁ →
          VP (fun σ s => St G (cBase G HO c (j + 1)) X σ s ∧
            isa.eval .eq s = some (BitVec.ofNat 32 (j + 1) == BitVec.ofNat 32 0))
            (.ite .eq (.block (stImm fStatus 3))
              (VG.Impl.Rsa.Arm.Keys.seqs [g.avail,
                .ite .eq (.block (stImm fStatus 2))
                  (VG.Impl.Rsa.Arm.Keys.seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0),
                    .ite .eq Geo.rejected (.block [])])])) G₁ := fun k =>
        VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z) (VP.seq start k)))
      obtain hRc : (G.witB.drop c).take (Spec.Dsa.generationQLen G.pLen) = seedAt G c := by
        show _ = (G.witB.drop c).take G.qLen; rw [hqL]
      obtain hcq' : c + Spec.Dsa.generationQLen G.pLen ≤ G.witB.length := by rw [hwl, ← hqL]; exact hcq
      obtain suffix : ∀ {x : Option Spec.Dsa.Params} {rest : List Byte}, sR G c = some (x, rest) →
          G.witB.drop (G.witLen - rest.length) = rest := fun {x rest} e => by
        rw [← hwl]
        exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.refillAttempt_suffix e).trans (List.drop_suffix _ _))
      change VP _ _ (St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) (sR G c)) X) at attempt
      rcases hR : sR G c with _ | ⟨_ | a, rest⟩ <;> rw [hR] at attempt
      · -- `rand` ran out inside the seed.
        obtain r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega_arith
        subst r0
        obtain hout : cOut G N = .ranOut (j + 1) c := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) none) X σ s ∧ isa.eval .eq s = some false)
          (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;>
            exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fC, fSeedLeft, fSeed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_attemptNone hpL hcq' (by rw [hRc, ← hqL]; exact hR),
            hwl]
        · rw [hout]; exact ⟨hcw, hj⟩
      · -- Rejected: the next seed.
        obtain hsuf := suffix hR
        obtain hcs : sCount G (j + 1) c i = sCount G j (G.witLen - rest.length) (i + 1) := by
          simp only [sCount, hshort, ↓reduceIte, hR]
        obtain hgt := sCount_gt G j (G.witLen - rest.length) (i + 1)
        obtain rpos : 0 < r := by omega_arith
        obtain hNr : N - r = i + 1 := by omega_arith
        obtain hp1 : sPos G (i + 1) = (j, G.witLen - rest.length) := by
          simp only [sPos, hp, hR, Nat.add_sub_cancel]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) (some (none, rest))) X σ s ∧
            isa.eval .eq s = some true)
          (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus]))
            fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            ((rejected_vp (u := G.witLen - rest.length) (j := j) (by simp [aOut]) (by simp [aOut, upd])
              (by simp [aOut]) (by simp [aOut, upd, fUsed, fStatus, fSeedLeft]) (by omega_arith)).mono
                (fun σ s h => h.1.1) fun _ _ h => h)
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus, fC, fSeedLeft]))
          fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_arith), fun _ => ?_⟩
        simp only [sInv, hNr, hp1]
        refine ⟨⟨by omega_arith, by rw [← hcs]; exact hc, ?_, Nat.sub_le _ _, by omega_arith⟩, ?_, x⟩
        · rw [← hW, VG.Proof.Dsa.Generation.search_rejected hpL hcq'
            (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm)) (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
            (fun _ h' => absurd h' (by simp))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;>
            exact ⟨by simp [aOut], by simp [aOut, upd, fStatus, fC, fSeedLeft, fUsed]⟩
      · -- Parameters: `fStatus` = 1.
        obtain hsuf := suffix hR
        obtain r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega_arith
        subst r0
        obtain hout : cOut G N = .found a (G.witLen - rest.length) := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 32 (j + 1)) (some (some a, rest))) X σ s ∧
            isa.eval .eq s = some false)
          (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨h, x⟩ R m e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine (h.of_rest R m).mono (fun o ho => ?_) (fun y hy => hy)
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fUsed] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fUsed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_accepted hpL hcq'
            (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm)) (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · rw [hout]; exact Nat.sub_le _ _

/-- The seeds, from the cursor 0 with `state[0]` seeds left. -/
theorem sLoop_vp {g : Geo} {HO : HashOk g.G} {n : Nat} (O : GenOk G g HO n) :
    VP (St G (cBase G HO 0 G.k0) X)
      (.loop (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fSeedLeft 0),
        .ite .eq (.block (stImm fStatus 3))
          (VG.Impl.Rsa.Arm.Keys.seqs [g.avail,
            .ite .eq (.block (stImm fStatus 2))
              (VG.Impl.Rsa.Arm.Keys.seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite .eq Geo.rejected (.block [])])]),
        .block (cmpF fStatus 0)]) .eq)
      (fun σ s => St G (cFin G (cOut G (sCount G G.k0 0 0))) X σ s ∧
        cRes G (cOut G (sCount G G.k0 0 0)) = sW G ∧ cOk G (cOut G (sCount G G.k0 0 0))) := by
  obtain hN := sCount_gt G G.k0 0 0
  generalize hNN : sCount G G.k0 0 0 = N at hN ⊢
  refine VP.mono (F := sInv G HO N X (N - 1 + 1)) ?_ (fun σ s h => ⟨⟨by omega_using [hN],
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; exact hNN,
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; simp [sPos, sW, Spec.Entropy.Result.consume],
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; simp [sPos], by rw [show N - (N - 1 + 1) = 0 by omega_using []]; exact O.k0⟩,
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; exact h⟩) fun _ _ h => h
  exact VP.loop (I := sInv G HO N X) (fun r => (sBody_vp O r).mono (fun _ _ h => h)
    fun σ s ⟨e, h0, hp⟩ => ⟨e, fun z => h0 z, hp⟩) _

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: before the seeds

`pre_vp`: `r7`–`r9` for the key working space (`ksRegs`), and the last 64 −
`qLen` bytes of a hash block after a `qLen`-byte message (`padInit`), which
every seed's hashes share: the search's first stage.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.WriteBytes
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_movw wp_dp wp_str wp_strb op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)

/-- A byte into bytes written before. -/
theorem writeBytes_set (m : Mem) (q : Addr) (xs : List Byte) {j : Nat} (hj : j < xs.length)
    (hl : xs.length < 2 ^ 64) (b : Byte) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 j) b = writeBytes m q (xs.set j b) := by
  funext x
  rw [writeW8_apply]
  simp only [writeBytes, List.length_set]
  by_cases hx : x = q + BitVec.ofNat 64 j
  · subst hx
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, hl])]
    simp [hj, List.getD_eq_getElem?_getD]
  · have hne : (x - q).toNat ≠ j := by
      intro h'
      apply hx
      have : x - q = BitVec.ofNat 64 j := BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h'])])
      rw [← BitVec.sub_add_cancel x q, this, BitVec.add_comm]
    simp only [hx, ite_false]
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
    · rfl

/-- Bytes within bytes written before. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) {d k : Nat} (h : d + k ≤ xs.length)
    (hl : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) (q + BitVec.ofNat 64 d) k = (xs.drop d).take k := by
  apply List.ext_getElem
  · simp [Spec.Rsa.bytesAt]; omega_using [h]
  · intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, writeBytes, List.getElem_take,
      List.getElem_drop]
    rw [BitVec.add_assoc, Offset.add_sub_cancel_left, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Spec.Rsa.bytesAt] at h1; omega_using [h, hl, h1])]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    simp [show d + i < xs.length by omega_using [h, h1], List.getD_eq_getElem?_getD]

/-- The 16 words from `r0` := `r3` (0): 64 zero bytes. -/
theorem zeros_ok {s : State} {a : Addr} (r3 : s.gpr .r3 = 0)
    (ha : ∀ i < 16, State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * i)) = a + BitVec.ofNat 64 (4 * i))
    (hw : ∀ i < 16, InRegions s.wr (a + BitVec.ofNat 64 (4 * i)) 4) :
    ∀ k ≤ 16, ∀ {rest : List Instr} {Q : State → Prop},
      (∀ t, Rest [] s t → t.mem = writeBytes s.mem a (List.replicate (4 * k) 0) → WP isa (.block rest) t Q) →
      WP isa (.block (((List.range k).map fun i => Instr.str .r3 .r0 (4 * i)) ++ rest)) s Q
  | 0, _, rest, Q, k => k s (Rest.refl _ _) (by simp [writeBytes_nil])
  | j + 1, hj, rest, Q, k => by
    rw [List.range_succ, List.map_append, List.append_assoc]
    refine zeros_ok r3 ha hw j (by omega_using [hj]) fun t R m => ?_
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine wp_str (a := a + BitVec.ofNat 64 (4 * j)) (by omega_using [hj]) (by rw [R.gpr .r0 (by simp), ha j (by omega_using [hj])])
      (by rw [R.wr]; exact hw j (by omega_using [hj])) fun t' u => k t' (R.trans (u.rest [])) ?_
    rw [u.mem, m, R.gpr _ (by simp), r3]
    show Mem.write (writeBytes s.mem a (List.replicate (4 * j) 0)) (a + BitVec.ofNat 64 (4 * j)) 4
      ((0 : BitVec 32).setWidth (8 * 4)) = _
    rw [write_eq_writeBytes]
    obtain z4 : ((List.range 4).map fun i => ((0 : BitVec 32).setWidth (8 * 4)).extractLsb' (8 * i) 8) =
        List.replicate 4 (0 : Byte) := by decide
    obtain ap := writeBytes_append s.mem a (List.replicate (4 * j) (0 : Byte)) (List.replicate 4 0) (by simp; omega_using [hj])
    rw [List.length_replicate] at ap
    rw [z4, ap, List.replicate_append_replicate, Nat.mul_succ]

section
variable {G : GP} {X : State → Prop}

/-- The 64 bytes `padInit` leaves at `sMsg`. -/
abbrev padList (n : Nat) : List Byte :=
  (((List.replicate 64 (0 : Byte)).set n 0x80).set 62 (BitVec.ofNat 8 (8 * n / 256))).set 63
    (BitVec.ofNat 8 (8 * n % 256))

theorem padList_tail {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n = 20 ∨ n = 32)
    (hlb : md.lenBytes n = [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * n / 256), BitVec.ofNat 8 (8 * n % 256)]) :
    ((padList n).drop n).take (64 - n) = padTail md n := by
  rw [padTail, hlb]; rcases hn with rfl | rfl <;> decide

/-- The search's first stage: `r7`–`r9` and the end of a hash block. -/
theorem pre_vp {V : Nat → BitVec 32} {LS : List Nat} {B N L : Nat} (md : MdStream.Md B N L) (hL : L = 8)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hlb : md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)]) :
    VP (fun σ s => GI G σ V LS s ∧ X σ) (.block (ksRegs G.pLen ++ padInit G.pLen G.qLen))
      (St G { V := V, LS := LS, cl := [(G.qLen, padTail md G.qLen)] } X) := by
  show VP _ (.block ([ld .r8 fScratch] ++ ([.movw .r12 (BitVec.ofNat 16 (sK G.pLen)), .dp .add .r8 .r8 (.reg .r12)] ++
    wRegs G.pLen ++ padInit G.pLen G.qLen))) _
  refine VP.block_append (G := fun σ s => (GI G σ V LS s ∧ X σ) ∧ s.gpr .r8 = G.scr)
    (VP.ld (G := G) (fun σ s h => h.1.sp) fun σ s ⟨gi, x⟩ => gi.ldV (o := fScratch) (by decide) (by decide)
      (gi.fixed (fScratch, G.scr) (by simp [fixedWords])) fun s' u => WP.block_nil
        ⟨⟨gi.of_rest (u.rest (ws := [.r8]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  obtain cert : Cert8 (.block ([.movw .r12 (BitVec.ofNat 16 (sK G.pLen)), .dp .add .r8 .r8 (.reg .r12)] ++
      wRegs G.pLen ++ padInit G.pLen G.qLen)) := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block ([.movw .r12 (BitVec.ofNat 16
        (sK 128)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs 128 ++ padInit 128 20)), by kernel_rfl⟩
    · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block ([.movw .r12 (BitVec.ofNat 16
        (sK 256)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs 256 ++ padInit 256 32)), by kernel_rfl⟩
    · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block ([.movw .r12 (BitVec.ofNat 16
        (sK 384)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs 384 ++ padInit 384 32)), by kernel_rfl⟩
  refine VP.taint [.r8] cert
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨⟨gi, x⟩, r8⟩ => ?_
  have big := gi.scrBig
  have fit := gi.scrFit
  obtain hn : G.qLen = 20 ∨ G.qLen = 32 := by omega_arith
  obtain hq32 : G.qLen ≤ 32 := by omega_arith
  obtain hl : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega_arith
  obtain sk := sK_lt hl
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain s64 : 64 ≤ sK G.pLen := by simp only [sK, sA]; omega_arith
  show WP isa (.block (.movw .r12 (BitVec.ofNat 16 (sK G.pLen)) :: .dp .add .r8 .r8 (.reg .r12) ::
    .mov .r9 (.imm (BitVec.ofNat 32 (G.pLen / 4))) :: (VG.Impl.Rsa.Arm.Keys.stride ++ (scr G.pLen .r0 sMsg ++
      (.mov .r3 (.imm 0) :: (((List.range 16).map fun i => Instr.str .r3 .r0 (4 * i)) ++
        [.mov .r1 (.imm 0x80), .strb .r1 .r0 G.qLen,
          .mov .r1 (.imm (BitVec.ofNat 32 ((8 * G.qLen) / 256))), .strb .r1 .r0 62,
          .mov .r1 (.imm (BitVec.ofNat 32 ((8 * G.qLen) % 256))), .strb .r1 .r0 63])))))) s _
  refine wp_movw fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  obtain kb : s₂.gpr .r8 = G.KB := by
    rw [u₂.gpr, dpVal, u₁.other _ (by decide), r8, u₁.gpr, setWidth_ofNat16 sk]
  refine wp_mov (op2_imm (encodable_lt (show G.pLen / 4 < 256 by omega_arith))) fun s₃ u₃ => ?_
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (w := G.w) (by simp only [GP.w]; omega_arith) u₃.gpr fun s₄ e7 R₄ M₄ => ?_
  obtain kb4 : s₄.gpr .r8 = G.KB := by rw [R₄.gpr _ (by decide), u₃.other _ (by decide), kb]
  refine scr_ok (d := .r0) kb4 rfl hl (by simp only [sMsg]; omega_arith) fun s₅ v₅ R₅ M₅ => ?_
  refine wp_mov (op2_imm (encodable_lt (show 0 < 256 by decide))) fun s₆ u₆ => ?_
  obtain a0 : ∀ i, i < 64 → State.addr (s₆.gpr .r0 + BitVec.ofNat 32 i) = State.addr G.scr + BitVec.ofNat 64 i :=
    fun i hi => by
      rw [u₆.other _ (by decide), v₅, show sMsg = 0 from rfl, BitVec.add_zero]
      exact gi.saddr (by omega_arith)
  obtain w6 : ∀ {o n : Nat}, o + n ≤ G.scrLen * 8 → InRegions s₆.wr (G.sa o) n := fun h => by
    rw [u₆.wr, R₅.wr, R₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact gi.inScr h
  refine zeros_ok (s := s₆) (a := State.addr G.scr) (by rw [u₆.gpr]) (fun i hi => a0 _ (by omega_arith))
    (fun i hi => w6 (o := 4 * i) (n := 4) (by omega_arith)) 16 (Nat.le_refl _) fun s₇ R₇ M₇ => ?_
  obtain a7 : ∀ i, i < 64 → State.addr (s₇.gpr .r0 + BitVec.ofNat 32 i) = State.addr G.scr + BitVec.ofNat 64 i :=
    fun i hi => by rw [R₇.gpr _ (by simp)]; exact a0 i hi
  refine wp_mov (op2_imm (encodable_lt (show 0x80 < 256 by decide))) fun s₈ u₈ => ?_
  refine wp_strb (a := State.addr G.scr + BitVec.ofNat 64 G.qLen) (by omega_arith)
    (by rw [u₈.other _ (by decide)]; exact a7 _ (by omega_arith))
    (by rw [u₈.wr, R₇.wr]; exact w6 (o := G.qLen) (n := 1) (by omega_arith)) fun s₉ u₉ => ?_
  refine wp_mov (op2_imm (encodable_lt (show 8 * G.qLen / 256 < 256 by omega_arith))) fun s₁₀ u₁₀ => ?_
  refine wp_strb (a := State.addr G.scr + BitVec.ofNat 64 62) (by omega_arith)
    (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide)]; exact a7 _ (by omega_arith))
    (by rw [u₁₀.wr, u₉.wr, u₈.wr, R₇.wr]; exact w6 (o := 62) (n := 1) (by omega_arith)) fun s₁₁ u₁₁ => ?_
  refine wp_mov (op2_imm (encodable_lt (show 8 * G.qLen % 256 < 256 by omega_arith))) fun s₁₂ u₁₂ => ?_
  refine wp_strb (a := State.addr G.scr + BitVec.ofNat 64 63) (by omega_arith)
    (by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide)]
        exact a7 _ (by omega_arith))
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, R₇.wr]; exact w6 (o := 63) (n := 1) (by omega_arith))
    fun t u₁₃ => WP.block_nil ?_
  obtain sw8 : ∀ x : Nat, (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)
  obtain hl64 : (List.replicate 64 (0 : Byte)).length < 2 ^ 64 := by simp
  obtain m6 : s₆.mem = s.mem := by rw [u₆.mem, M₅, M₄, u₃.mem, u₂.mem, u₁.mem]
  obtain mt : t.mem = writeBytes s.mem (State.addr G.scr) (padList G.qLen) := by
    rw [u₁₃.mem, u₁₂.gpr, u₁₂.mem, u₁₁.mem, u₁₀.gpr, u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, M₇, m6, sw8, sw8]
    rw [writeBytes_set _ _ _ (by simp; omega_arith) hl64, writeBytes_set _ _ _ (by simp) (by simp),
      writeBytes_set _ _ _ (by simp) (by simp)]
    rfl
  obtain R : Rest [.r12, .r8, .r9, .r7, .r0, .r3, .r1] s t :=
    ((((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))).trans
      ((R₄.mono (by simp)).trans ((R₅.mono (by simp)).trans (u₆.rest (by simp))))).trans
      ((R₇.mono (by simp)).trans ((u₈.rest (by simp)).trans ((u₉.rest _).trans ((u₁₀.rest (by simp)).trans
        ((u₁₁.rest _).trans ((u₁₂.rest (by simp)).trans (u₁₃.rest _)))))))
  obtain f : Frame [G.rScr, G.rBelow] s.mem t.mem := by
    rw [mt]
    exact (writeBytes_frame _ _ _ (R := G.rScr) (by
      show (_ - _ : Addr).toNat + _ ≤ _
      rw [BitVec.sub_self, BitVec.toNat_zero]; simp; omega_arith)).mono (by simp)
  obtain g7 : ∀ r, r ∉ [Reg.r0, .r1, .r3, .r12] → t.gpr r = s₄.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.gpr, u₁₂.other _ hr.2.1, u₁₁.gpr, u₁₀.other _ hr.2.1, u₉.gpr,
      u₈.other _ hr.2.1, R₇.gpr _ (by simp), u₆.other _ hr.2.2.1,
      R₅.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.2.2, hr.1⟩)]
  obtain pl := padTail_length md (n := G.qLen) (by omega_arith) hL
  refine ⟨⟨gi.of_scr R f, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun j hj => absurd hj (by simp),
    fun j hj => absurd hj (by simp), fun d hd => absurd hd (by simp), fun d hd => absurd hd (by simp)⟩, x⟩
  · rw [g7 _ (by decide), e7]
  · rw [g7 _ (by decide), kb4]
  · rw [g7 _ (by decide), R₄.gpr _ (by decide), u₃.gpr]
  · simp only [List.mem_singleton] at hy; subst hy
    show Spec.Rsa.bytesAt t.mem (State.addr G.scr + BitVec.ofNat 64 G.qLen) (padTail md G.qLen).length = _
    rw [mt, pl, bytesAt_writeBytes _ _ _ (by simp; omega_arith) (by simp), padList_tail md hn hlb]
  · simp only [List.mem_singleton] at hy; subst hy
    show G.qLen + (padTail md G.qLen).length ≤ _
    rw [pl]; omega_arith

end

end VG.Proof.Dsa.Arm.Gen
