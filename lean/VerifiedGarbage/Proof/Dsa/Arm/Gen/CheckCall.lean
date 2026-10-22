module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateContract
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Memory

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
  have hs : (s.sp - BitVec.ofNat 32 32).toNat = G.sp.toNat - 32 := by
    rw [h.gi.sp]; exact FrameStack.sub_toNat' (by omega)
  have := VG.Proof.Dsa.Arm.Key.storeWords_read (callPush.map s.gpr) s.mem (s.sp - BitVec.ofNat 32 32)
    (by rw [List.length_map]; show (s.sp - BitVec.ofNat 32 32).toNat + 4 * 8 ≤ 2 ^ 32; omega) i
    (by rw [List.length_map]; exact hi)
  simpa only [List.getElem_map, stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp, pushed, List.length_cons, List.length_nil] using this

theorem nPk_le (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) : nPk G ≤ 800 := by
  unfold Spec.Dsa.generationLengthsValid at hlq; simp only [nPk]; omega

/-- The check's arguments meet its precondition. -/
theorem SS.cEntry_pre (h : SS G σ c s) (regs : CArgs G s) (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    checkPre (cEntry G s) := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  have spHi := gi.spHi
  have hLv := h.lens
  have np := nPk_le hlq
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := regs
  have sp : s.sp = G.sp := gi.sp
  have esp : (cEntry G s).sp = G.sp - BitVec.ofNat 32 32 := by rw [cEntry_sp, sp]; rfl
  have espN : (cEntry G s).sp.toNat = G.sp.toNat - 32 := by rw [esp, FrameStack.sub_toNat' (by omega)]
  have e0 : (cEntry G s).gpr .r0 = G.scr + BitVec.ofNat 32 sPacked := by rw [cEntry_gpr (by decide), r0]
  have e1 : (cEntry G s).gpr .r1 = BitVec.ofNat 32 (nPk G) := by rw [cEntry_gpr (by decide), r1]
  have e2 : (cEntry G s).gpr .r2 = BitVec.ofNat 32 G.pLen := by rw [cEntry_gpr (by decide), r2]
  have e3 : (cEntry G s).gpr .r3 = BitVec.ofNat 32 G.qLen := by rw [cEntry_gpr (by decide), r3]
  have a0 : stackArg (cEntry G s) 0 = G.scr + BitVec.ofNat 32 sA := by rw [h.cEntry_arg (by decide)]; exact r4
  have a1 : stackArg (cEntry G s) 1 = BitVec.ofNat 32 (wa G.pLen / 8) := by
    rw [h.cEntry_arg (by decide)]; exact r5
  have wl := wa_toNat hLv
  have nl : (BitVec.ofNat 32 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpk : sPacked + nPk G ≤ sA := by simp only [sPacked, sA]; omega
  have hsA : sA + wa G.pLen ≤ sK G.pLen := by simp only [sK]; omega
  have aP : State.addr (G.scr + BitVec.ofNat 32 sPacked) = G.sa sPacked :=
    h.addr (n := nPk G) (by omega) (by simp only [nPk]; omega)
  have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) hsA (by simp only [wa]; omega)
  have argB : Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32), 8⟩ G.rBelow :=
    fun a ha => gi.pushSub a (by simp only [Region.Contains] at ha ⊢; omega)
  have spT : (G.sp - BitVec.ofNat 32 32).toNat = G.sp.toNat - 32 := by rw [← esp]; exact espN
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  unfold checkPre
  simp only [State.withRegions_rd, State.withRegions_wr, e0, e1, e2, e3, VG.Proof.Dsa.Arm.arg, a0, a1, esp]
  refine ⟨by omega, rfl, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aP, aS, nl, wl]; exact gi.sdisj (.inl hpk) (by omega) (by omega)
  · rw [aS, wl]; exact (gi.scr_below (by omega)).sub_right argB
  · rw [nl, h.toNat (by omega)]; omega
  · rw [wl, h.toNat (by omega)]; omega
  · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    unfold Spec.Dsa.generationLengthsValid at hlq; unfold Spec.Dsa.lengthsValid; omega
  · rw [nl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by simp only [wa]; omega)]
    unfold Spec.Dsa.scratchWords; simp only [wa]; omega

/-- The regions the check is given are the push's and `scratch`'s. -/
theorem SS.cCovers (h : SS G σ c s) (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    Covers (cRd G ++ cWr G) ((pushed callPush s).rd ++ (pushed callPush s).wr) ∧
      Covers (cWr G) (pushed callPush s).wr := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  have np := nPk_le hlq
  have hLv := h.lens
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  have wl := wa_toNat h.lens
  have nl : (BitVec.ofNat 32 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpk : sPacked + nPk G ≤ sA := by simp only [sPacked, sA]; omega
  have hsA : sA + wa G.pLen ≤ sK G.pLen := by simp only [sK]; omega
  have aP : State.addr (G.scr + BitVec.ofNat 32 sPacked) = G.sa sPacked :=
    h.addr (n := nPk G) (by omega) (by simp only [nPk]; omega)
  have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) hsA (by simp only [wa]; omega)
  have hpw : (pushed callPush s).wr = belowA G.sp 32 :: G.rFrame :: σ.wr := by
    rw [pushed_wr, gi.wr, gi.sp]; rfl
  have inScr : ∀ {o n : Nat}, o + n ≤ sK G.pLen → InRegions (pushed callPush s).wr (G.sa o) n := fun hon =>
    ⟨G.rScr, by rw [hpw, gi.pre.wr, gi.hG]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have hw : Covers (cWr G) (pushed callPush s).wr := Covers.one (by rw [aS, wl]; exact inScr hsA)
  refine ⟨Covers.append_left (Covers.right (Covers.pair (Covers.one ?_) (Covers.one ?_))) hw.right, hw⟩
  · rw [aP, nl]; exact inScr (by omega)
  · refine ⟨belowA G.sp 32, by rw [hpw]; simp, ?_⟩
    show (_ - _ : Addr).toNat + 8 ≤ 32
    rw [show (4 * callPush.length) = 32 from rfl, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The bytes the check reads: p‖q‖g at `sPacked`. -/
theorem SS.cEntry_params (h : SS G σ c s) (regs : CArgs G s) (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    checkParams (cEntry G s) = Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) := by
  have big := h.gi.scrBig
  have np := nPk_le hlq
  have hLv := h.lens
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  have nl : (BitVec.ofNat 32 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have aP : State.addr (G.scr + BitVec.ofNat 32 sPacked) = G.sa sPacked :=
    h.addr (n := nPk G) (by simp only [sK, sPacked, sA] at *; omega) (by simp only [nPk]; omega)
  show Spec.Rsa.bytesAt (pushed callPush s).mem (State.addr ((cEntry G s).gpr .r0)) ((cEntry G s).gpr .r1).toNat = _
  rw [cEntry_gpr (by decide), cEntry_gpr (by decide), regs.1, regs.2.1, aP, nl]
  refine List.map_congr_left fun k hk => ?_
  exact h.push_scr (o := sPacked) (n := nPk G) (by simp only [sK, sPacked, sA] at *; omega) (List.mem_range.mp hk)

/-- The check's call: its effects. -/
theorem SS.checkCall_ok (h : SS G σ c s) {name : String} (regs : CArgs G s)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], t.gpr r = s.gpr r) → t.sp = s.sp → t.rd = s.rd →
      t.wr = s.wr → Frame [G.rs sA (wa G.pLen), G.rU, G.rBelow] s.mem t.mem →
      t.gpr .r0 = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen
        (Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G)) then 1 else 0) → Q t) :
    WP isa (callWith name VG.Impl.Dsa.Arm.Generate.checkParameters) s Q := by
  have gi := h.gi
  have s176 := gi.sp176
  have pre := h.cEntry_pre regs hlq
  obtain ⟨hc, hw⟩ := h.cCovers hlq
  have sp : s.sp = G.sp := gi.sp
  have big := gi.scrBig
  unfold callWith
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega) (by decide) ?_
  refine FrameStack.WP.callF (k := checkArm) (fun s hs => by
      obtain ⟨t, s', e, ha, hp⟩ := VG.Proof.Dsa.Arm.check_correct hs; exact ⟨t, s', e, ha, hp⟩) pre hc hw
    (by rw [VG.Proof.Dsa.Arm.Key.check_armStack]; exact Nat.zero_le _)
    fun s₂ hrd hwr hsp hf hg hpost => ?_
  rw [VG.Proof.Dsa.Arm.Key.check_armStack] at hf
  have r0 := hpost
  dsimp only [checkArm] at r0
  rw [State.withRegions_gpr, BitVec.setWidth_append_eq_right] at r0
  have res : checkRes (cEntry G s) = Spec.Dsa.checkParametersBytes G.pLen G.qLen
      (Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G)) := by
    have hLv := h.lens
    have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
    unfold checkRes
    rw [h.cEntry_params regs hlq, cEntry_gpr (by decide), cEntry_gpr (by decide), regs.2.2.1, regs.2.2.2.1,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [res] at r0
  have pg : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → (popped .r4 (4 * callPush.length) s₂).gpr r = s.gpr r :=
    fun r h4 hp hl => by rw [popped_gpr h4, hg r hp hl, pushed_gpr]
  have mem : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], r ≠ .r4 ∧ r ∈ preserved ∧ r ≠ .lr := by decide
  refine k _ (fun r hr => pg r (mem r hr).1 (mem r hr).2.1 (mem r hr).2.2)
    (by rw [popped_sp, hsp, pushed_sp, BitVec.sub_add_cancel])
    (by rw [popped_rd, hrd, pushed_rd]) (by rw [popped_wr, hwr, pushed_wr, List.tail_cons]) ?_ ?_
  · have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
    have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen)
      (by simp only [sK] at big ⊢; omega) (by simp only [wa]; omega)
    rw [popped_mem]
    refine ((FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega)).sub
      fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨G.rBelow, by simp, by rw [sp]; exact gi.pushSub⟩
    · simp only [cWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨G.rs sA (wa G.pLen), List.mem_cons_self, ?_⟩
        rw [aS, wa_toNat h.lens]; exact fun _ h => h
      · exact ⟨G.rBelow, by simp, fun _ hc => absurd hc (by simp [Region.Contains])⟩
  · rw [popped_gpr (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [r0]; split <;> rfl

end

/-- The check's call in two runs at the same stage, with the same p‖q‖g. -/
theorem checkCall_ct {G : GP} {c : Cfg} {name : String} (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen)
    {pk : List Byte} :
    RelCT isa (fun s₁ s₂ => (∃ σ, SS G σ c s₁) ∧ CArgs G s₁ ∧ Spec.Rsa.bytesAt s₁.mem (G.sa sPacked) (nPk G) = pk ∧
        (∃ σ, SS G σ c s₂) ∧ CArgs G s₂ ∧ Spec.Rsa.bytesAt s₂.mem (G.sa sPacked) (nPk G) = pk)
      (callWith name VG.Impl.Dsa.Arm.Generate.checkParameters) fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun s₁ s₂ ⟨⟨_, h₁⟩, _, _, ⟨_, h₂⟩, _, _⟩ => by rw [h₁.gi.sp, h₂.gi.sp]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨⟨σ₁, h₁⟩, g₁, c₁, ⟨σ₂, h₂⟩, g₂, c₂⟩, p₁, p₂⟩ := hp
  have s₁ := h₁.gi.sp176
  have s₂ := h₂.gi.sp176
  rw [push_pushed (by decide) (by rw [h₁.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (by rw [h₂.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega), Option.some.injEq] at p₂
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
    rw [h₁.cEntry_arg (by omega), h₂.cEntry_arg (by omega)]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact g₁.2.2.2.2.1.trans g₂.2.2.2.2.1.symm
    · exact g₁.2.2.2.2.2.trans g₂.2.2.2.2.2.symm

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The check's call, at a stage that claims p‖q‖g at `sPacked`. -/
theorem checkCall_vp {name : String} {pk : List Byte} {cl' : Claims}
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) (hpk : (sPacked, pk) ∈ c.cl) (hpkl : pk.length = nPk G)
    (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS) (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa G.pLen) x) :
    VP (fun σ s => St G c X σ s ∧ CArgs G s) (callWith name VG.Impl.Dsa.Arm.Generate.checkParameters)
      (fun σ t => St G { c with cl := cl' } X σ t ∧
        t.gpr .r0 = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0)) := by
  have bytes : ∀ σ s, SS G σ c s → Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk := fun σ s h => by
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
