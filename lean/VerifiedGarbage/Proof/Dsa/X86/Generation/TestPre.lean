module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Spec.Dsa.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env

/-! # A probable-prime test's call meets the test's contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The registers a test's call pushes, last argument first. -/
abbrev testRegs : List Reg := [.ebp, .ebx, .edx, .ecx, .eax]

/-- The test's contract, as `Generic/MillerRabin/X86/DsaProbablePrime.lean`
registers it. -/
abbrev ppContract (bits : Nat) : Contract isa :=
  Spec.Dsa.ProbablePrime.contract (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
    (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 112

/-- The regions the test is given: the witnesses left and the table, and the
working space, `used` and the arguments. -/
def randAddr (E : Env) (used : Nat) : Addr :=
  if E.witLen - used = 0 then E.wit else E.wit + BitVec.ofNat 64 used

def testRd (E : Env) (used : Nat) : List Region :=
  [⟨randAddr E used, E.witLen - used⟩, E.tableRegion]

def testWr (E : Env) (s : State) : List Region :=
  [⟨off E.base sPP, 8 * ppWords⟩, ⟨off E.base fUsedOut, 8⟩, ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩]

/-- The state the test starts in. -/
abbrev testEntry (E : Env) (used : Nat) (s : State) : State :=
  (pushed testRegs s).callEntry.withRegions (testRd E used) (testWr E s)

theorem packed_len : VG.Impl.RsaKeyGen.TrialTable32.packed.length = 1024 := by
  simp [VG.Impl.RsaKeyGen.TrialTable32.packed]

/-- A part of a region, by its start and length. -/
theorem sub_of_contains {R : Region} {a : Addr} {n : Nat} (h : R.Contains a n) : Region.Sub ⟨a, n⟩ R :=
  fun _ hx => h.byte (by simp only [Region.Contains] at hx; omega)

theorem randPtr_toNat {E : Env} (v : E.Valid) {used : Nat} (hu : used ≤ E.witLen) :
    (randPtr (E.wit.setWidth 32) E.witLen used).toNat = (randAddr E used).toNat := by
  have witLt := v.ptrs.2.2.2
  have wf := v.witFit
  have w32 : (E.wit.setWidth 32).toNat = E.wit.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt witLt]
  by_cases h0 : E.witLen - used = 0
  · simp only [randPtr, randAddr, h0, ↓reduceIte, w32]
  · have e1 : (E.wit.setWidth 32 + BitVec.ofNat 32 used).toNat = E.wit.toNat + used := by
      rw [BitVec.toNat_add, w32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have e2 : (E.wit + BitVec.ofNat 64 used).toNat = E.wit.toNat + used := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    simp only [randPtr, randAddr, h0, ↓reduceIte, e1, e2]

theorem randPtr_wide {E : Env} (v : E.Valid) {used : Nat} (hu : used ≤ E.witLen) :
    (randPtr (E.wit.setWidth 32) E.witLen used).setWidth 64 = randAddr E used :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth, randPtr_toNat v hu, Nat.mod_eq_of_lt (by
    have := (randPtr (E.wit.setWidth 32) E.witLen used).isLt; rw [randPtr_toNat v hu] at this; omega)])

theorem randAddr_fit {E : Env} (v : E.Valid) {used : Nat} (hu : used ≤ E.witLen) :
    (randAddr E used).toNat + (E.witLen - used) ≤ 2 ^ 32 := by
  have wf := v.witFit
  by_cases h0 : E.witLen - used = 0
  · simp only [randAddr, h0, ↓reduceIte]; omega
  · have e2 : (E.wit + BitVec.ofNat 64 used).toNat = E.wit.toNat + used := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    simp only [randAddr, h0, ↓reduceIte, e2]; omega

theorem randAddr_sub {E : Env} {used : Nat} (hu : used ≤ E.witLen) :
    Region.Sub ⟨randAddr E used, E.witLen - used⟩ E.witRegion := by
  by_cases h0 : E.witLen - used = 0
  · intro x hx; simp only [Region.Contains, h0] at hx; omega
  · simp only [randAddr, h0, ↓reduceIte]
    exact Offset.sub_base E.wit (by omega)

/-- The witnesses left, in memory that holds the tape. -/
theorem rand_bytes {E : Env} {used : Nat} {m : Mem}
    (hm : Spec.Rsa.bytesAt m E.wit E.witLen = E.witT) :
    Spec.Rsa.bytesAt m (randAddr E used) (E.witLen - used) = E.witT.drop used := by
  rw [← hm]
  by_cases h0 : E.witLen - used = 0
  · simp only [randAddr, h0, ↓reduceIte, Spec.Rsa.bytesAt, List.range_zero, List.map_nil]
    exact (List.drop_eq_nil_of_le (by simp; omega)).symm
  · simp only [randAddr, h0, ↓reduceIte, Spec.Rsa.bytesAt]
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [VG.Offset.add_add]

/-- The test's arguments, from the registers pushed. -/
theorem testEntry_arg {E : Env} {used : Nat} {s : State} (fit : 24 ≤ (s.gpr .esp).toNat) :
    arg (testEntry E used s) 0 = s.gpr .eax ∧ arg (testEntry E used s) 1 = s.gpr .ecx ∧
      arg (testEntry E used s) 2 = s.gpr .edx ∧ arg (testEntry E used s) 3 = s.gpr .ebx ∧
      arg (testEntry E used s) 4 = s.gpr .ebp := by
  have fit' : 4 * testRegs.length + 4 ≤ (s.gpr .esp).toNat := by simpa using fit
  have hrs : Reg.esp ∉ testRegs := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [testEntry, arg_withRegions, callEntry_arg fit' hrs (by decide)]; rfl)

theorem testEntry_mem {E : Env} {used : Nat} {s : State} (fit : 24 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 24] s.mem (testEntry E used s).mem :=
  callEntry_frame (rs := testRegs) (by simpa using fit) (by decide)

/-- A test's candidate keeps its value through writes to the stack. -/
theorem cand_frame {E : Env} (v : E.Valid) {bits : Nat}
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords) {k : Nat} (hk : k ≤ 160)
    {m m' : Mem} (F : Frame [below E.sp k] m m') :
    Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m' (off E.base sPP) =
      Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m (off E.base sPP) := by
  have sz := v.size_ge
  have low := v.low
  have lay' : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).candidate + bits / 8 ≤ ppWords * 8 := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega
  unfold Spec.Dsa.ProbablePrime.candidateAt
  refine congrArg Spec.Dsa.decodeBE ?_
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  have subWS : Region.Sub ⟨off E.base sPP, ppWords * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPP, ppWords]; omega)
  have sub : Region.Sub ⟨off E.base sPP + BitVec.ofNat 64 (VG.Impl.Dsa.X86.ProbablePrime.layout bits).candidate,
      bits / 8⟩ ⟨off E.base sPP, ppWords * 8⟩ := Offset.sub_base _ (by simpa using lay')
  have lb : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).bits = bits := rfl
  rw [lb] at hi
  refine Frame.bytes F (R := ⟨_, bits / 8⟩) ?_ (by
      show bits / 8 ≤ 2 ^ 64; simp only [VG.Impl.Dsa.X86.ProbablePrime.layout, ppWords] at lay; omega)
    (by simpa using hi)
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact ((v.scratchStack.sub_left subWS).sub_left sub).sub_right (below_sub hk (by omega))

theorem test_pre {bits : Nat} {E : Env} (v : E.Valid) {s₀ s : State} (B : Base E s₀) {used : Nat}
    (A : TestArgs E.base (E.wit.setWidth 32) E.witLen used s₀ s) (hu : used ≤ E.witLen)
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords)
    (odd : Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      (off E.base sPP) % 2 = 1)
    (len : Spec.Dsa.bitLength (Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
      s.mem (off E.base sPP)) = bits) :
    (ppContract bits).pre (testEntry E used s) := by
  have sp := B.sp
  have spU : s.gpr .esp = E.sp := by rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), sp]
  have low := v.low
  have spLt := E.sp.isLt
  have nw := v.scratchFit
  have room := v.room
  have wf := v.witFit
  have tf := v.tableFit
  have fit : 4 * testRegs.length + 4 ≤ (s.gpr .esp).toNat := by rw [spU]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ testRegs := by decide
  have nat24 : (s.gpr .esp - 24#32).toNat = E.sp.toNat - 24 := by rw [spU]; exact sub_toNat (by omega)
  have nat20 : ((s.gpr .esp - 20#32).setWidth 64).toNat = E.sp.toNat - 20 := by
    rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have uesp : (testEntry E used s).gpr .esp = s.gpr .esp - 24#32 := by
    change (pushed testRegs s).callEntry.gpr .esp = _
    exact callEntry_esp' testRegs s
  have uarg0 : argAddr (testEntry E used s) 0 = (s.gpr .esp - 20#32).setWidth 64 := by
    rw [testEntry, argAddr_withRegions]; exact callEntry_argAddr0 testRegs s
  have ua : ∀ i (hi : i < 5), arg (testEntry E used s) i = arg (pushed testRegs s).callEntry i := fun i _ => by
    rw [testEntry, arg_withRegions]
  have a0 : arg (testEntry E used s) 0 = s₀.gpr .edi + BitVec.ofNat 32 sPP := by
    rw [ua 0 (by decide), callEntry_arg fit hrs (by decide)]; exact A.eax
  have a1 : arg (testEntry E used s) 1 = BitVec.ofNat 32 ppWords := by
    rw [ua 1 (by decide), callEntry_arg fit hrs (by decide)]; exact A.ecx
  have a2 : arg (testEntry E used s) 2 = randPtr (E.wit.setWidth 32) E.witLen used := by
    rw [ua 2 (by decide), callEntry_arg fit hrs (by decide)]; exact A.edx
  have a3 : arg (testEntry E used s) 3 = BitVec.ofNat 32 (E.witLen - used) := by
    rw [ua 3 (by decide), callEntry_arg fit hrs (by decide)]; exact A.ebx
  have a4 : arg (testEntry E used s) 4 = s₀.gpr .edi + BitVec.ofNat 32 fUsedOut := by
    rw [ua 4 (by decide), callEntry_arg fit hrs (by decide)]; exact A.ebp
  have urd : (testEntry E used s).rd = testRd E used := rfl
  have uwr : (testEntry E used s).wr = testWr E s := rfl
  have usy : (testEntry E used s).syms = s.syms := rfl
  have umem : Frame [below (s.gpr .esp) (4 * testRegs.length + 4)] s.mem (testEntry E used s).mem :=
    callEntry_frame fit hrs
  generalize eu : testEntry E used s = u at *
  sig_pre [ppContract, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  have hs := B.scr
  have sz := v.size_ge
  have witLt := v.ptrs.2.2.2
  have lenLt := v.lens.2.2
  have wsW := Scr.wide hs (d := sPP) (by simp only [sPP]; omega)
  have uoW := Scr.wide hs (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega)
  have wsN := Scr.toNat_add hs (d := sPP) (by simp only [sPP]; omega)
  have uoN := Scr.toNat_add hs (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega)
  have randW := randPtr_wide v (used := used) hu
  have randN := randPtr_toNat v (used := used) hu
  have randFit := randAddr_fit v (used := used) hu
  have randSub := randAddr_sub (E := E) (used := used) hu
  have lenN : (BitVec.ofNat 32 (E.witLen - used)).toNat = E.witLen - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ppN : (BitVec.ofNat 32 ppWords).toNat = ppWords := by decide
  have callee : (s.gpr .esp - 24#32).setWidth 64 - 112#64 = (s.gpr .esp - 136#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [nat24]; omega : 112 ≤ (s.gpr .esp - 24#32).toNat), BitVec.sub_sub]; rfl
  have sy₀ : s.syms = s₀.syms := A.syms
  have m₀ : s.mem = s₀.mem := A.mem
  simp only [a0, a1, a2, a3, a4, uesp, uarg0, urd, uwr, usy, testRd, testWr, wsW, uoW, randW, randN, lenN,
    ppN, wsN, uoN, callee, Abi.constRegions_cons, Abi.constRegions_nil, packed_len, List.length_cons,
    List.length_nil, List.drop, List.take, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]
  have symT : (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = E.table := by rw [sy₀]; exact B.syms
  have subWS : Region.Sub ⟨off E.base sPP, ppWords * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPP, ppWords]; omega)
  have subUO : Region.Sub ⟨off E.base fUsedOut, 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [fUsedOut, hdr]; omega)
  have subArgs : Region.Sub ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega)
  have subRet : Region.Sub ⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 24) (by decide) (by omega) (by decide))
  have subCal : Region.Sub ⟨(s.gpr .esp - 136#32).setWidth 64, 112⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 136) (by decide) (by omega) (by decide))
  have subPush : Region.Sub (below (s.gpr .esp) (4 * testRegs.length + 4)) E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega)
  have ss := v.scratchStack
  have wf := v.tapesFar E.witRegion (by simp)
  have ws := wf.1; have wk := wf.2.2
  have ts := v.tableFar.1; have tk := v.tableFar.2.2
  have nat136 : ((s.gpr .esp - 136#32).setWidth 64).toNat = E.sp.toNat - 136 := by
    rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have nat24' : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
    rw [BitVec.toNat_setWidth, nat24]; exact Nat.mod_eq_of_lt (by omega)
  have retArgs : Region.Disjoint ⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat24', nat20]; omega) (by simp only [nat20]; omega)
  have calArgs : Region.Disjoint ⟨(s.gpr .esp - 136#32).setWidth 64, 112⟩ ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat136, nat20]; omega) (by simp only [nat20]; omega)
  have wsUO : Region.Disjoint ⟨off E.base sPP, ppWords * 8⟩ ⟨off E.base fUsedOut, 8⟩ :=
    Offset.disjoint E.base (by simp only [sPP, ppWords, fUsedOut, hdr]; omega) (by simp only [sPP, ppWords]; omega)
      (by simp only [fUsedOut, hdr]; omega)
  have candEq : ∀ m : Mem, Frame [below (s.gpr .esp) (4 * testRegs.length + 4)] s.mem m →
      Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m (off E.base sPP) =
        Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP) :=
    fun m F => cand_frame v lay (k := 24) (by decide) (by simpa [spU] using F)
  refine ⟨by omega, by omega, by rw [symT]; rfl, ?_, ?_, trivial, by rw [Nat.mul_comm 8 ppWords],
    (ws.symm.sub_left subWS).sub_right randSub, wsUO, (ss.sub_left subWS).sub_right subArgs,
    (ws.sub_left randSub).sub_right subUO, (wk.sub_left randSub).sub_right subArgs,
    (ss.sub_left subUO).sub_right subArgs,
    (ss.symm.sub_left subRet).sub_right subWS, (wk.symm.sub_left subRet).sub_right randSub,
    (ss.symm.sub_left subRet).sub_right subUO, retArgs,
    (ss.symm.sub_left subCal).sub_right subWS, (wk.symm.sub_left subCal).sub_right randSub,
    (ss.symm.sub_left subCal).sub_right subUO, calArgs,
    by simp only [sPP, ppWords]; omega, randFit, by simp only [fUsedOut, hdr]; omega,
    by simpa [VG.Impl.Dsa.X86.ProbablePrime.layout] using lay, by rw [candEq _ umem]; exact odd,
    by rw [candEq _ umem]; exact len⟩
  · intro c hc i hi
    have h := B.held c hc i hi
    simp only [List.mem_singleton] at hc
    subst hc
    simp only at h ⊢
    rw [symT]
    rw [← sy₀, symT] at h
    rw [← h, ← m₀]
    have len : i < 1024 := by simpa [packed_len] using hi
    refine Frame.readW umem (r := E.tableRegion) (Offset.contains_base E.table (by omega) (by omega)) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact tk.sub_right subPush
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    rw [symT]
    refine ⟨by omega, ?_, tk.sub_right subRet, tk.sub_right subCal⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ts.sub_right (by rw [Nat.mul_comm]; exact subWS)
    · exact ts.sub_right subUO
    · exact tk.sub_right subArgs

end VG.Proof.Dsa.X86.Generation
