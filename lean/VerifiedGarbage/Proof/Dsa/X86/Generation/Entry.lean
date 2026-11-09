module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABIEnv
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Rc2.PairMem

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
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega
  refine ⟨by rw [entered, pushed_esp]; rfl, pushed_rd _ _, pushed_wr _ _, pushRegs_syms _ _, ?_, Frame.refl _ _⟩
  exact Frame.mono (pushed_frame (rs := savedRegisters) (s := s) (by decide) fit)
    fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem argOffset {s : State} (F : CallFacts s) {i : Nat} (hi : i < 8) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have bound := F.argsFit
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem addrArg (s : State) (i : Nat) : addr (callEnv s).sp (20 + 4 * i) = argAddr s i := by
  change ((s.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) = _
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem argAccess {s t : State} (F : CallFacts s) (I : EInv s t) {i : Nat} (hi : i < 8) :
    InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
  have bound := F.argsFit
  refine ⟨⟨argAddr s 0, 32⟩, List.mem_append_right _ ?_, ?_⟩
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  · rw [argOffset F hi]
    exact Offset.contains_base _ (by omega) (by omega)

theorem argValue {s t : State} (F : CallFacts s) (I : EInv s t) {i : Nat} (hi : i < 8) :
    t.mem.readW (argAddr s i) 32 = arg s i := by
  have bound := F.argsFit
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega
  have separate : (⟨argAddr s 0, 32⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 32⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by omega)]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (⟨argAddr s 0, 32⟩ : Region).Contains (argAddr s i) 4 := by
    rw [argOffset F hi]; exact Offset.contains_base _ (by omega) (by omega)
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
    exact Frame.writeW I.fr List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm]
    exact Frame.writeW I.fe List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

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
  refine st_ok hs₁ (d := o) (by omega) fun t₂ M₂ => k t₂ ?_ ?_ ?_
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
  Mem.readW_writeW_sep (Offset.sep b (d := o') (n := 4) (e := o) (k := 4) (by omega) h₂ h₁) (by decide)

/-- A state word's low half. -/
theorem readW_lowNat (m : Mem) (a : Addr) : m.readW a 32 = BitVec.ofNat 32 (m.readW a 64).toNat := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero]

/-- The address of `state`'s word `d`. -/
theorem stAddr {s : State} (F : CallFacts s) {d : Nat} (hd : d + 4 ≤ 32) :
    addr (arg s 7) d = (arg s 7).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := F.stFit; omega)

/-- The low halves of `state`'s words, before anything wrote them. -/
theorem stWord {s t : State} (F : CallFacts s) (I : EInv s t) {d : Nat} (hd : d + 8 ≤ 32) :
    InRegions (t.rd ++ t.wr) (addr (arg s 7) d) 4 ∧
      t.mem.readW (addr (arg s 7) d) 32 = BitVec.ofNat 32 (s.mem.readW ((arg s 7).setWidth 64 + BitVec.ofNat 64 d) 64).toNat := by
  have fit := F.stFit
  rw [stAddr F (by omega)]
  refine ⟨⟨⟨(arg s 7).setWidth 64, 32⟩, List.mem_append_right _ ?_, Offset.contains_base _ (by omega) (by omega)⟩, ?_⟩
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  · have sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
      rw [F.reserved]; exact below_sub (by decide) F.low
    rw [I.fr.readW (r := ⟨(arg s 7).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact F.scrSt.symm.sub_left (Offset.sub_base _ (by omega))
      · exact (F.stackSt.symm.sub_right sub).sub_left (Offset.sub_base _ (by omega))) (by decide), readW_lowNat]

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
      refine ⟨by rw [I₁.esp]; omega, ?_⟩
      rw [I₁.esp]; omega
  refine copyArg_ok F I₁ hs₀ (i := 0) (o := fOut) (by decide) (by decide) fun t₁ I₂ hs₁ m₁ => ?_
  refine copyArg_ok F I₂ hs₁ (i := 2) (o := fUsedP) (by decide) (by decide) fun t₂ I₃ hs₂ m₂ => ?_
  refine copyArg_ok F I₃ hs₂ (i := 3) (o := fWit) (by decide) (by decide) fun t₃ I₄ hs₃ m₃ => ?_
  refine copyArg_ok F I₄ hs₃ (i := 4) (o := fWitLen) (by decide) (by decide) fun t₄ I₅ hs₄ m₄ => ?_
  refine copyArg_ok F I₅ hs₄ (i := 7) (o := fStP) (by decide) (by decide) fun t₅ I₆ hs₅ m₅ => ?_
  refine stImm_ok hs₅ (o := fC) (v := 0) (by simp only [fC, hdr]; omega) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ => ?_
  have hs₉ := Scr.of_eq hs₅ (g₉ _ (by decide)) (g₉ _ (by decide)) wr₉
  have I₁₀ := I₆.store F (o := fC) (by decide) m₉ (g₉ _ (by decide)) rd₉ wr₉ sy₉
  refine stImm_end hs₉ (o := fStatus) (v := 0) (by simp only [fStatus, hdr]; omega)
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
      (Offset.contains_base _ (by change 8 * i + 64 / 8 ≤ 8192; omega) (by omega))
      (far _ (by simp)) (by decide)
  all_goals
    rw [M]
    simp (disch := decide) only [readW_off_other, Mem.readW_writeW_self32]
  all_goals first
    | exact (narrow _).symm
    | simp only [callEnv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    | rfl

end VG.Proof.Dsa.X86.Generation
