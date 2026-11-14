module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABI
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Rc2.PairMem

/-! ### `Dsa.X86.Generation.ABIEnv`, which only this module used -/

section

/-! # The precondition gives a valid environment -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The environment of a call, from its arguments: the seeds and the `h`
candidates are those of each seed's own environment (`Env.atSeed`,
`Env.window`). -/
def callEnv (s : State) : Env where
  pLen := pLenOf s
  qLen := Spec.Dsa.generationQLen (pLenOf s)
  base := (arg s 5).setWidth 64
  size := (arg s 6).toNat * 8
  out := (arg s 0).setWidth 64
  usedP := (arg s 2).setWidth 64
  stP := (arg s 7).setWidth 64
  k0 := (s.mem.readW ((arg s 7).setWidth 64) 64).toNat
  seedsOff := 0
  seedsLen := 0
  hsOff := 0
  hsLen := 0
  wit := (arg s 3).setWidth 64
  witLen := (arg s 4).toNat
  sp := s.gpr .esp - BitVec.ofNat 32 16
  table := (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64
  witT := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat

theorem disjoint_nat {a b : Addr} {n k : Nat}
    (_an : a.toNat + n ≤ 2 ^ 64) (_bk : b.toNat + k ≤ 2 ^ 64) (np : 0 < n) (kp : 0 < k)
    (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  have overlap : a.toNat < b.toNat + k ∧ b.toNat < a.toNat + n := by omega_using [bad]
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      omega_using [bad, order]
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]; change 0 + 1 ≤ k; omega_using [kp]
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]; change 0 + 1 ≤ n; omega_using [np]
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      omega_using [bad, order]

theorem CallFacts.tableRegion {s : State} (F : CallFacts s) :
    let t : Region := ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩
    t.base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s) :=
  F.tableFar _ (by rw [ProbablePrime.table_regions]; exact List.mem_cons_self)

theorem CallFacts.rd {s : State} (F : CallFacts s) :
    s.rd = [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, (callEnv s).tableRegion] := by
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, F.rdPrefix, F.rdTable, ProbablePrime.table_regions]
  rfl

theorem CallFacts.pLens {s : State} (F : CallFacts s) : pLenOf s = 128 ∨ pLenOf s = 256 ∨ pLenOf s = 384 := by
  have := F.pValid
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  omega_using [this]

theorem CallFacts.lengths {s : State} (F : CallFacts s) :
    Spec.Dsa.generationLengthsValid (pLenOf s) (Spec.Dsa.generationQLen (pLenOf s)) := by
  rcases F.pLens with h | h | h <;> simp [Spec.Dsa.generationLengthsValid, Spec.Dsa.generationQLen, h]

theorem CallFacts.reserved {s : State} (F : CallFacts s) : reservedRegion s = below (s.gpr .esp) 216 := by
  unfold reservedRegion below
  rw [Taint.sub_setWidth F.low]

theorem CallFacts.stackSub {s : State} (F : CallFacts s) : (callEnv s).stackRegion.Sub (reservedRegion s) := by
  rw [F.reserved]
  exact below_inner (by decide) F.low

theorem CallFacts.spNat {s : State} (F : CallFacts s) : (callEnv s).sp.toNat = (s.gpr .esp).toNat - 16 :=
  sub_toNat (by have := F.low; omega_using [this])

theorem CallFacts.reservedNat {s : State} (F : CallFacts s) :
    ((s.gpr .esp).setWidth 64 - 216#64).toNat = (s.gpr .esp).toNat - 216 := by
  change (reservedRegion s).base.toNat = _
  rw [F.reserved]
  change ((s.gpr .esp - BitVec.ofNat 32 216).setWidth 64).toNat = _
  rw [toNat_wide, sub_toNat F.low]

/-- `scratch` lies below the reserved stack or above the return address. -/
theorem CallFacts.scratchNat {s : State} (F : CallFacts s) :
    (arg s 5).toNat + (arg s 6).toNat * 8 ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 5).toNat := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have fit := F.scrFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) (by omega_using [room]) (by decide)
    F.stackScr.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) (by omega_using [room]) (by decide)
    F.retScr.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [room, b₁, b₂]

/-- `out` lies below the reserved stack or above the return address. -/
theorem CallFacts.outNat {s : State} (F : CallFacts s) :
    (arg s 0).toNat + (arg s 1).toNat ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 0).toNat := by
  have pos : 0 < (arg s 1).toNat := by
    rw [F.outLen]; rcases F.pLens with h | h | h <;> omega_using [h]
  have fit := F.outFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) pos (by decide)
    F.stackOut.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) pos (by decide)
    F.retOut.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [pos, b₁, b₂]

/-- `state` lies below the reserved stack or above the return address. -/
theorem CallFacts.stNat {s : State} (F : CallFacts s) :
    (arg s 7).toNat + 32 ≤ (s.gpr .esp).toNat - 216 ∨ (s.gpr .esp).toNat + 4 ≤ (arg s 7).toNat := by
  have fit := F.stFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) (by decide) (by decide)
    F.stackSt.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) (by decide) (by decide)
    F.retSt.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [b₁, b₂]

/-- `used` lies below the reserved stack or above the return address. -/
theorem CallFacts.usedNat {s : State} (F : CallFacts s) :
    (arg s 2).toNat + 8 ≤ (s.gpr .esp).toNat - 216 ∨ (s.gpr .esp).toNat + 4 ≤ (arg s 2).toNat := by
  have fit := F.usedFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) (by decide) (by decide)
    F.stackUsed.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) (by decide) (by decide)
    F.retUsed.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [b₁, b₂]

theorem CallFacts.outLenEq {s : State} (F : CallFacts s) : (callEnv s).outLen = (arg s 1).toNat := by
  simp only [Env.outLen, callEnv, F.outLen]

theorem CallFacts.outRegion {s : State} (F : CallFacts s) :
    (callEnv s).outRegion = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ := by
  simp only [Env.outRegion, F.outLenEq]; rfl

/-- A region of the arguments' memory, apart from the stack the calls use. -/
theorem CallFacts.far {s : State} (F : CallFacts s) {r : Region} (h : (reservedRegion s).Disjoint r) :
    r.Disjoint (callEnv s).stackRegion := h.symm.sub_right F.stackSub

theorem CallFacts.valid {s : State} (F : CallFacts s) : (callEnv s).Valid := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have T := F.tableRegion
  have scratchNat := F.scratchNat
  have spNat := F.spNat
  have low := F.low
  have ws : (callEnv s).scratchRegion = ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ := rfl
  have wW : (callEnv s).witRegion = ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ := rfl
  have uR : (callEnv s).usedRegion = ⟨(arg s 2).setWidth 64, 8⟩ := rfl
  have sR : (callEnv s).stRegion = ⟨(arg s 7).setWidth 64, 32⟩ := rfl
  have tW : ∀ r ∈ s.wr, (callEnv s).tableRegion.Disjoint r := T.2.1
  refine ⟨F.lengths, by change 512 * pLenOf s + 8192 ≤ (arg s 6).toNat * 8; omega_using [room],
    by change ((arg s 5).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.scrFit,
    by rw [F.outLenEq]; change ((arg s 0).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.outFit,
    by change ((arg s 3).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.randFit,
    by simp [callEnv], by simp [callEnv], by rw [spNat]; omega_using [low], ?_, by rw [ws, F.outRegion]; exact F.outScr,
    ⟨by rw [wW, ws]; exact F.randScr, by rw [wW, F.outRegion]; exact F.outRand.symm,
      by rw [wW]; exact F.far F.stackRand⟩,
    by rw [F.outRegion]; exact F.far F.stackOut,
    by rw [ws]; exact F.far F.stackScr, T.1, (toNat_wide _).symm ▸ (arg s 0).isLt,
    (toNat_wide _).symm ▸ (arg s 3).isLt, (arg s 4).isLt, ⟨T.2.1 _ ?_, ?_, T.2.2.2.sub_right F.stackSub⟩, ?_,
    by change ((arg s 2).setWidth 64).toNat + 8 ≤ _; rw [toNat_wide]; exact F.usedFit,
    by change ((arg s 7).setWidth 64).toNat + 32 ≤ _; rw [toNat_wide]; exact F.stFit, ?_, ?_, F.seeds⟩
  · change (callEnv s).sp.toNat ≤ ((arg s 5).setWidth 64).toNat ∨
      ((arg s 5).setWidth 64).toNat + (arg s 6).toNat * 8 + 200 ≤ (callEnv s).sp.toNat
    rw [spNat, toNat_wide]
    omega_using [room, scratchNat]
  · rw [F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [F.outRegion]; exact T.2.1 _ (by rw [F.wr]; exact List.mem_cons_self)
  · exact F.tableAligned _ (by rw [ProbablePrime.table_regions]; exact List.mem_cons_self)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [uR, ws]; exact F.usedScr
    · rw [uR, F.outRegion]; exact F.outUsed.symm
    · rw [uR]; exact F.far F.stackUsed
    · rw [uR, sR]; exact F.usedSt
    · rw [uR, wW]; exact F.usedRand
    · exact (tW _ (by rw [F.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [sR, ws]; exact F.scrSt.symm
    · rw [sR, F.outRegion]; exact F.outSt.symm
    · rw [sR]; exact F.far F.stackSt
    · rw [sR, wW]; exact F.randSt.symm
    · exact (tW _ (by rw [F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))).symm

end VG.Proof.Dsa.X86.Generation

end

end


/-! # The entry: the arguments into the state words -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)

/-- What the entry keeps of the state it starts from. -/
structure EInv (s t : State) : Prop where
  esp : t.gpr .esp = (callEnv s).sp
  rd : t.rd = s.rd
  wr : t.wr = below (s.gpr .esp) 16 :: s.wr
  syms : t.syms = s.syms
  fr : Frame [(callEnv s).scratchRegion, below (s.gpr .esp) 16] s.mem t.mem
  fe : Frame [(callEnv s).scratchRegion] (entered s).mem t.mem

theorem entered_inv {s : State} (F : CallFacts s) : EInv s (entered s) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega_using [this]
  refine ⟨by rw [entered, pushed_esp]; rfl, pushed_rd _ _, pushed_wr _ _, pushRegs_syms _ _, ?_, Frame.refl _ _⟩
  exact Frame.mono (pushed_frame (rs := savedRegisters) (s := s) (by decide) fit)
    fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem argOffset {s : State} (F : CallFacts s) {i : Nat} (hi : i < 8) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have bound := F.argsFit
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hi, bound]

theorem addrArg (s : State) (i : Nat) : addr (callEnv s).sp (20 + 4 * i) = argAddr s i := by
  change ((s.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) = _
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem argAccess {s t : State} (F : CallFacts s) (I : EInv s t) {i : Nat} (hi : i < 8) :
    InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
  have bound := F.argsFit
  refine ⟨⟨argAddr s 0, 32⟩, List.mem_append_right _ ?_, ?_⟩
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  · rw [argOffset F hi]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem argValue {s t : State} (F : CallFacts s) (I : EInv s t) {i : Nat} (hi : i < 8) :
    t.mem.readW (argAddr s i) 32 = arg s i := by
  have bound := F.argsFit
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega_using [this]
  have separate : (⟨argAddr s 0, 32⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 32⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by omega_using [bound])]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (⟨argAddr s 0, 32⟩ : Region).Contains (argAddr s i) 4 := by
    rw [argOffset F hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine I.fr.readW (r := ⟨argAddr s 0, 32⟩) (w := 32) contains ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact F.scrArgs.symm
  · exact separate

theorem EInv.store {s t t' : State} (F : CallFacts s) (I : EInv s t) {o : Nat} (ho : o + 4 ≤ 73728) {v : BitVec 32}
    (hm : t'.mem = t.mem.writeW (off (callEnv s).base o) v) (esp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd)
    (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : EInv s t' := by
  have v := F.valid
  have := v.size_ge
  have := v.scratchFit
  refine ⟨esp.trans I.esp, rd.trans I.rd, wr.trans I.wr, sy.trans I.syms, ?_, ?_⟩
  · rw [hm]
    exact Frame.writeW I.fr List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_using [ho]))
  · rw [hm]
    exact Frame.writeW I.fe List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_using [ho]))

/-- `copyArg`: an argument into a state word. -/
theorem copyArg_ok {s t : State} (F : CallFacts s) (I : EInv s t) (hs : Scr t (callEnv s).base (callEnv s).size)
    {i o : Nat} (hi : i < 8) (ho : o + 4 ≤ 73728) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', EInv s t' → Scr t' (callEnv s).base (callEnv s).size →
      t'.mem = t.mem.writeW (off (callEnv s).base o) (arg s i) → WP isa (.block is) t' Q) :
    WP isa (.block (copyArg i o ++ is)) t Q := by
  have := F.valid.size_ge
  simp only [copyArg, List.cons_append, List.nil_append]
  refine wp_ldm (B := (callEnv s).sp) I.esp (by rw [addrArg]; exact argAccess F I hi) fun t₁ u₁ => ?_
  have hs₁ := Scr.of_eq hs (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr
  refine st_ok hs₁ (d := o) (by omega_using [ho, this]) fun t₂ M₂ => k t₂ ?_ ?_ ?_
  · refine I.store F ho (v := arg s i) ?_ (by rw [M₂.gpr, u₁.other _ (by decide)]) (by rw [M₂.rd, u₁.rd])
      (by rw [M₂.wr, u₁.wr]) (by rw [M₂.syms, u₁.syms])
    rw [M₂.mem, u₁.mem, u₁.gpr, addrArg, argValue F I hi]
  · exact Scr.of_eq hs₁ (by rw [M₂.gpr]) (by rw [M₂.gpr]) M₂.wr
  · rw [M₂.mem, u₁.mem, u₁.gpr, addrArg, argValue F I hi]

theorem EInv.regs {s t t' : State} (I : EInv s t) (hm : t'.mem = t.mem) (esp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : EInv s t' :=
  ⟨esp.trans I.esp, rd.trans I.rd, wr.trans I.wr, sy.trans I.syms, by rw [hm]; exact I.fr, by rw [hm]; exact I.fe⟩

theorem readW_off_other (m : Mem) (b : Addr) {o o' : Nat} (v : BitVec 32) (h : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (h₁ : o + 4 ≤ 2 ^ 64) (h₂ : o' + 4 ≤ 2 ^ 64) :
    (m.writeW (off b o) v).readW (off b o') 32 = m.readW (off b o') 32 :=
  Mem.readW_writeW_sep (Offset.sep b (d := o') (n := 4) (e := o) (k := 4) (by omega_using [h]) h₂ h₁) (by decide)

/-- A state word's low half. -/
theorem readW_lowNat (m : Mem) (a : Addr) : m.readW a 32 = BitVec.ofNat 32 (m.readW a 64).toNat := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero]

/-- The address of `state`'s word `d`. -/
theorem stAddr {s : State} (F : CallFacts s) {d : Nat} (hd : d + 4 ≤ 32) :
    addr (arg s 7) d = (arg s 7).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := F.stFit; omega_using [hd, this])

/-- The low halves of `state`'s words, before anything wrote them. -/
theorem stWord {s t : State} (F : CallFacts s) (I : EInv s t) {d : Nat} (hd : d + 8 ≤ 32) :
    InRegions (t.rd ++ t.wr) (addr (arg s 7) d) 4 ∧
      t.mem.readW (addr (arg s 7) d) 32 = BitVec.ofNat 32 (s.mem.readW ((arg s 7).setWidth 64 + BitVec.ofNat 64 d) 64).toNat := by
  have fit := F.stFit
  rw [stAddr F (by omega_using [hd])]
  refine ⟨⟨⟨(arg s 7).setWidth 64, 32⟩, List.mem_append_right _ ?_, Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩, ?_⟩
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  · have sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
      rw [F.reserved]; exact below_sub (by decide) F.low
    rw [I.fr.readW (r := ⟨(arg s 7).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact F.scrSt.symm.sub_left (Offset.sub_base _ (by omega_using [hd]))
      · exact (F.stackSt.symm.sub_right sub).sub_left (Offset.sub_base _ (by omega_using [hd]))) (by decide), readW_lowNat]

/-- After the entry. -/
structure EPost (s t : State) : Prop where
  inv : EInv s t
  base : Base (callEnv s) t
  cur : t.mem.readW (off (callEnv s).base fC) 32 = BitVec.ofNat 32 0
  status : t.mem.readW (off (callEnv s).base fStatus) 32 = BitVec.ofNat 32 0

theorem narrow (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem entry_ok {s : State} (F : CallFacts s) : WP isa (.block entry) (entered s) (EPost s) := by
  have v := F.valid
  have sz := v.size_ge
  have I₀ := entered_inv F
  simp only [entry, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldm (B := (callEnv s).sp) I₀.esp (by rw [addrArg]; exact argAccess F I₀ (by decide)) fun t₀ u₀ => ?_
  have I₁ := I₀.regs u₀.mem (u₀.other _ (by decide)) u₀.rd u₀.wr u₀.syms
  have hs₀ : Scr t₀ (callEnv s).base (callEnv s).size := by
    refine ⟨?_, ?_, v.scratchFit, ?_⟩
    · rw [u₀.gpr, addrArg, argValue F I₀ (by decide)]; rfl
    · rw [I₁.wr, F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · have := v.stackScratch; have := v.low
      refine ⟨by rw [I₁.esp]; omega_using [this], ?_⟩
      rw [I₁.esp]; omega_arith
  refine copyArg_ok F I₁ hs₀ (i := 0) (o := fOut) (by decide) (by decide) fun t₁ I₂ hs₁ m₁ => ?_
  refine copyArg_ok F I₂ hs₁ (i := 2) (o := fUsedP) (by decide) (by decide) fun t₂ I₃ hs₂ m₂ => ?_
  refine copyArg_ok F I₃ hs₂ (i := 3) (o := fWit) (by decide) (by decide) fun t₃ I₄ hs₃ m₃ => ?_
  refine copyArg_ok F I₄ hs₃ (i := 4) (o := fWitLen) (by decide) (by decide) fun t₄ I₅ hs₄ m₄ => ?_
  refine copyArg_ok F I₅ hs₄ (i := 7) (o := fStP) (by decide) (by decide) fun t₅ I₆ hs₅ m₅ => ?_
  refine stImm_ok hs₅ (o := fC) (v := 0) (by simp only [fC, hdr]; omega_using [sz]) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ => ?_
  have hs₉ := Scr.of_eq hs₅ (g₉ _ (by decide)) (g₉ _ (by decide)) wr₉
  have I₁₀ := I₆.store F (o := fC) (by decide) m₉ (g₉ _ (by decide)) rd₉ wr₉ sy₉
  refine stImm_end hs₉ (o := fStatus) (v := 0) (by simp only [fStatus, hdr]; omega_using [sz])
    fun t₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ sy₁₀ => ?_
  have hs₁₀ := Scr.of_eq hs₉ (g₁₀ _ (by decide)) (g₁₀ _ (by decide)) wr₁₀
  have I := I₁₀.store F (o := fStatus) (by decide) m₁₀ (g₁₀ _ (by decide)) rd₁₀ wr₁₀ sy₁₀
  have M : t₁₀.mem = (((((((entered s).mem.writeW (off (callEnv s).base fOut) (arg s 0)).writeW
      (off (callEnv s).base fUsedP) (arg s 2)).writeW (off (callEnv s).base fWit) (arg s 3)).writeW
      (off (callEnv s).base fWitLen) (arg s 4)).writeW (off (callEnv s).base fStP) (arg s 7)).writeW
      (off (callEnv s).base fC) (BitVec.ofNat 32 0)).writeW (off (callEnv s).base fStatus) (BitVec.ofNat 32 0) := by
    rw [m₁₀, m₉, m₅, m₄, m₃, m₂, m₁, u₀.mem]
  have rd : (callEnv s).witRegion ∈ t₁₀.rd ∧ (callEnv s).tableRegion ∈ t₁₀.rd := by
    rw [I.rd, F.rd]; exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
  have far : ∀ R ∈ [(callEnv s).witRegion, (callEnv s).tableRegion],
      ∀ r ∈ [(callEnv s).scratchRegion, below (s.gpr .esp) 16], R.Disjoint r := by
    have sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
      rw [F.reserved]; exact below_sub (by decide) F.low
    intro R hR r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR hr
    rcases hr with rfl | rfl
    · rcases hR with rfl | rfl
      · exact v.witFar.1
      · exact v.tableFar.1
    · have T := F.tableRegion
      rcases hR with rfl | rfl
      · exact F.stackRand.symm.sub_right sub
      · exact T.2.2.2.sub_right sub
  have wit : Spec.Rsa.bytesAt t₁₀.mem (callEnv s).wit (callEnv s).witLen = (callEnv s).witT :=
    VG.Proof.RsaKeyGen.frame_bytesAt I.fr (far (callEnv s).witRegion (by simp))
      (Nat.le_of_lt (Nat.lt_trans (arg s 4).isLt (by decide)))
  have sy : (t₁₀.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = (callEnv s).table := by
    rw [I.syms]; rfl
  refine ⟨I, ⟨hs₁₀, I.esp, rd.1, rd.2, ?_, ?_, ?_, sy, ?_, wit, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [I.wr, F.wr, F.outRegion]; simp
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  · intro c hc i hi
    simp only [VG.Impl.RsaKeyGen.TrialTable32.consts, List.mem_singleton] at hc
    subst hc
    have len : i < 1024 := by simpa [VG.Impl.RsaKeyGen.TrialTable32.packed] using hi
    have fit := v.tableFit
    rw [I.syms, ← F.tableHeld _ (List.mem_singleton_self _) i hi]
    exact Frame.readW I.fr (r := (callEnv s).tableRegion)
      (Offset.contains_base _ (by change 8 * i + 64 / 8 ≤ 8192; omega_using [len]) (by omega_using [len]))
      (far _ (by simp)) (by decide)
  all_goals
    rw [M]
    simp (disch := decide) only [readW_off_other, Mem.readW_writeW_self32]
  all_goals first
    | exact (narrow _).symm
    | simp only [callEnv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    | rfl

end VG.Proof.Dsa.X86.Generation
