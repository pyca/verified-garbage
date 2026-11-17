module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestPre
import VerifiedGarbage.Proof.Framework.X86.CallReturn
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! ### `Dsa.X86.Generation.TestCall`, which this module and modules that import it used -/

section

/-! # A probable-prime test: its status, and the witnesses it read -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- The witness cursor after a test's result. -/
def nextUsed (witLen used : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => used
  | some (_, rest) => witLen - rest.length

/-- After a test of the candidate `c` from `s`: its status in `fRes`, the
witness cursor in `fUsed`, and only the test's working space, those words
and the stack changed. -/
structure TestPost (E : Env) (bits used c : Nat) (s t : State) : Prop where
  base : Base E t
  res : t.mem.readW (off E.base fRes) 32 =
    BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime c (E.witT.drop used)))
  used : t.mem.readW (off E.base fUsed) 32 =
    BitVec.ofNat 32 (nextUsed E.witLen used (Spec.Dsa.probablePrime c (E.witT.drop used)))
  chg : E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
    (fRes, 4), (fUsed, 4), (fUsedOut, 8)] s.mem t.mem
  esi : t.gpr .esi = s.gpr .esi
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem ret32 (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt
  omega_arith

/-- The low word of a 64-bit word in memory. -/
theorem readW_low (m : Mem) (a : Addr) : m.readW a 32 = (m.readW a 64).setWidth 32 := by
  simp only [Mem.readW]
  rw [VG.Proof.Bignum.read_prefix m a (n := 8) (k := 4) (by decide)]
  simp

/-- What the call changes: the test's own ranges of its working space, the
word for `used`, and the stack. -/
theorem call_chg {E : Env} (v : E.Valid) {bits : Nat} {t w u : State} (hsp : t.gpr .esp = E.sp)
    (Fm : Frame [below E.sp 24] t.mem w.mem)
    {k : Nat} (hk : k ≤ 200) (Fu : Frame (testWr E t ++ [below (t.gpr .esp) k]) t.mem u.mem)
    {m₂ : Mem} (M : Frame [below E.sp 20] m₂ u.mem)
    (K : Proof.Dsa.ModPow.Keeps (off E.base sPP) ppWords
      [(0, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits))] w.mem m₂) :
    E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fUsedOut, 8)] t.mem u.mem := by
  have sz := v.size_ge
  have low := v.low
  have nw := v.scratchFit
  intro x hx
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨hPP, hUO, hS⟩ := hx
  obtain hS' : ∀ k ≤ 200, ¬ (below E.sp k).Contains x 1 := fun k hk h => hS (below_sub hk (by omega_arith) x h)
  by_cases hw : (⟨off E.base sPP, 8 * ppWords⟩ : Region).Contains x 1
  · -- In the working space but not its scratch: the test kept it.
    obtain hi : (x - off E.base sPP).toNat < 8 * ppWords := by simp only [Region.Contains] at hw; omega_arith
    obtain hx : x = off E.base sPP + BitVec.ofNat 64 (x - off E.base sPP).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    obtain k := K (x - off E.base sPP).toNat hi (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      by_contra h
      apply hPP
      simp only [Region.Contains]
      omega_arith)
    rw [← hx] at k
    rw [M x (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hS' 20 (by decide)), k]
    exact Fm x (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hS' 24 (by decide))
  · refine Fu x ?_
    intro r hr
    simp only [testWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hw
    · exact hUO
    · rw [hsp]; exact hS' 20 (by decide)
    · rw [hsp]; exact hS' _ hk

/-- What a test's call leaves, from the state `s` its arguments were loaded
in: the status of the candidate `c` in `eax`, the octets read in `fUsedOut`,
and only the test's working space and the stack changed. -/
structure TestRet (E : Env) (bits used c : Nat) (s u : State) : Prop where
  eax : u.gpr .eax = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime c (E.witT.drop used)))
  edi : u.gpr .edi = s.gpr .edi
  esp : u.gpr .esp = E.sp
  esi : u.gpr .esi = s.gpr .esi
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  chg : E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
    (fUsedOut, 8)] s.mem u.mem
  usedOut : ∀ b rest, Spec.Dsa.probablePrime c (E.witT.drop used) = some (b, rest) →
    u.mem.readW (off E.base fUsedOut) 32 = BitVec.ofNat 32 (E.witLen - used - rest.length)

/-- The call's precondition, after the arguments are loaded. -/
theorem testCallPre {bits : Nat} {E : Env} (v : E.Valid) {s t : State} (B : Base E s) {used : Nat}
    (A : TestArgs E.base (E.wit.setWidth 32) E.witLen used s t) (hu : used ≤ E.witLen)
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords)
    (odd : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      (off E.base sPP) % 2 = 1)
    (len : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
      s.mem (off E.base sPP)) = bits) :
    CallPre (ppContract bits) testRegs (testRd E used) (testWr E t) t := by
  have sz := v.size_ge
  obtain spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have low := v.low
  obtain hsT : Scr t E.base E.size := Scr.of_eq B.scr (A.other _ (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by rw [spT, B.sp]) A.wr
  refine ⟨test_pre v B A hu lay (by rw [A.mem]; exact odd) (by rw [A.mem]; exact len), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [testRd, testWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · by_cases h0 : E.witLen - used = 0
      · exact ⟨E.witRegion, List.mem_append_left _ (A.rd ▸ B.tapes), 0, by simp [randAddr, h0, Env.witRegion],
          by simp [h0]⟩
      · exact ⟨E.witRegion, List.mem_append_left _ (A.rd ▸ B.tapes), used, by simp [randAddr, h0, Env.witRegion],
          by simp only [Env.witRegion]; omega_arith⟩
    · exact ⟨E.tableRegion, List.mem_append_left _ (A.rd ▸ B.table), 0, by simp, by simp⟩
    · exact ⟨E.scratchRegion, List.mem_append_right _ (.tail _ (A.wr ▸ hsT.wr)), sPP, rfl,
        by simp only [Env.scratchRegion, sPP, ppWords]; omega_arith⟩
    · exact ⟨E.scratchRegion, List.mem_append_right _ (.tail _ (A.wr ▸ hsT.wr)), fUsedOut, rfl,
        by simp only [Env.scratchRegion, fUsedOut, hdr]; omega_arith⟩
    · exact ⟨below (t.gpr .esp) (4 * testRegs.length), List.mem_append_right _ (.head _), 0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [testWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨E.scratchRegion, .tail _ hsT.wr, sPP, rfl, by simp only [Env.scratchRegion, sPP, ppWords]; omega_arith⟩
    · exact ⟨E.scratchRegion, .tail _ hsT.wr, fUsedOut, rfl,
        by simp only [Env.scratchRegion, fUsedOut, hdr]; omega_arith⟩
    · exact ⟨below (t.gpr .esp) (4 * testRegs.length), .head _, 0, by simp, by simp⟩

/-- What the callee sees: its arguments, the candidate and the witnesses. -/
theorem testEntry_facts {bits : Nat} {E : Env} (v : E.Valid) {s t : State} (B : Base E s) {used : Nat}
    (A : TestArgs E.base (E.wit.setWidth 32) E.witLen used s t) (hu : used ≤ E.witLen)
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords) :
    (testEntry E used t).gpr .esp = E.sp - BitVec.ofNat 32 24 ∧ (testEntry E used t).syms = s.syms ∧
      (arg (testEntry E used t) 0).setWidth 64 = off E.base sPP ∧
      arg (testEntry E used t) 1 = BitVec.ofNat 32 ppWords ∧
      (arg (testEntry E used t) 2).setWidth 64 = randAddr E used ∧
      (arg (testEntry E used t) 3).toNat = E.witLen - used ∧
      (arg (testEntry E used t) 4).setWidth 64 = off E.base fUsedOut ∧
      arg (testEntry E used t) 0 = s.gpr .edi + BitVec.ofNat 32 sPP ∧
      arg (testEntry E used t) 2 = randPtr (E.wit.setWidth 32) E.witLen used ∧
      arg (testEntry E used t) 3 = BitVec.ofNat 32 (E.witLen - used) ∧
      arg (testEntry E used t) 4 = s.gpr .edi + BitVec.ofNat 32 fUsedOut ∧
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) (testEntry E used t).mem
        (off E.base sPP) =
        Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP) ∧
      Spec.Rsa.bytesAt (testEntry E used t).mem (randAddr E used) (E.witLen - used) = E.witT.drop used := by
  have sz := v.size_ge
  obtain spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have low := v.low
  obtain fitT : 24 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_arith
  obtain ⟨e0, e1, e2, e3, e4⟩ := testEntry_arg (E := E) (used := used) fitT
  obtain Fm := testEntry_mem (E := E) (used := used) fitT
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.ebp] at e4
  obtain wsW := Scr.wide B.scr (d := sPP) (by simp only [sPP]; omega_arith)
  obtain uoW := Scr.wide B.scr (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  have lenLt := v.witLen32
  rw [spT] at Fm
  obtain cw := cand_frame v lay (k := 24) (by decide) Fm
  rw [A.mem] at cw
  obtain wk := (v.tapesFar E.witRegion (by simp)).2.2
  have wf := v.witFit
  refine ⟨?_, ?_, by rw [e0, wsW], e1, by rw [e2, randPtr_wide v hu], ?_, by rw [e4, uoW], e0, e2, e3, e4, cw, ?_⟩
  · simp only [testEntry, State.withRegions_gpr]
    rw [callEntry_esp', spT]; rfl
  · show ((pushed testRegs t).callEntry).syms = s.syms
    rw [← A.syms]
    exact pushRegs_syms _ _
  · rw [e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [← rand_bytes (m := t.mem) (by rw [A.mem]; exact B.wit)]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine Frame.bytes Fm (R := ⟨randAddr E used, E.witLen - used⟩) ?_ (by show E.witLen - used ≤ 2 ^ 64; omega_arith) hi
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (wk.sub_left (randAddr_sub hu)).sub_right (below_sub (by decide) (by omega_arith))

/-- The test's call. -/
theorem testCall_ok {bits : Nat} {name : String} {callee : Prog isa}
    (verified : Verified target callee (ppContract bits)) (noSp : NoSp callee) (stack : stackUse callee ≤ 152)
    {E : Env} (v : E.Valid) {s t : State} (B : Base E s) {used : Nat}
    (A : TestArgs E.base (E.wit.setWidth 32) E.witLen used s t) (hu : used ≤ E.witLen)
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords)
    (odd : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      (off E.base sPP) % 2 = 1)
    (len : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
      s.mem (off E.base sPP)) = bits) :
    WP isa (.frame (.push testRegs) (.call name callee) (.pop .ecx 5)) t (TestRet E bits used
      (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP)) s) := by
  have sz := v.size_ge
  obtain spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have low := v.low
  obtain cp := testCallPre v B A hu lay odd len
  obtain fitT : 24 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_arith
  obtain ⟨e0, e1, e2, e3, e4⟩ := testEntry_arg (E := E) (used := used) fitT
  obtain Fm := testEntry_mem (E := E) (used := used) fitT
  simp only [testEntry] at e0 e1 e2 e3 e4 Fm
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.ebp] at e4
  refine WP.of_syms (WP.callWithReturn verified.1 noSp (by decide) (by decide)
    (by rw [spT]; simp only [List.length_cons, List.length_nil]; omega_arith) cp fun u rdu wru csu Fu post usy => ?_)
  obtain ⟨s₂, m₂, ax₂, post⟩ := post
  generalize ew : (pushed testRegs t).callEntry.withRegions (testRd E used) (testWr E t) = w at e0 e1 e2 e3 e4 Fm post
  sig_post [ppContract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow] at post
  simp only [e0, e1, e2, e3, e4, ret32] at post
  obtain wsW := Scr.wide B.scr (d := sPP) (by simp only [sPP]; omega_arith)
  obtain uoW := Scr.wide B.scr (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  have lenLt := v.witLen32
  obtain lenN : (BitVec.ofNat 32 (E.witLen - used)).toNat = E.witLen - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain ppN : (BitVec.ofNat 32 ppWords).toNat = ppWords := by decide
  rw [spT] at Fm
  obtain cw := cand_frame v lay (k := 24) (by decide) Fm
  rw [A.mem] at cw
  obtain wk := (v.tapesFar E.witRegion (by simp)).2.2
  have wf := v.witFit
  obtain rw' : Spec.Rsa.bytesAt w.mem (randAddr E used) (E.witLen - used) = E.witT.drop used := by
    rw [← rand_bytes (m := t.mem) (by rw [A.mem]; exact B.wit)]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine Frame.bytes Fm (R := ⟨randAddr E used, E.witLen - used⟩) ?_ (by show E.witLen - used ≤ 2 ^ 64; omega_arith) hi
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (wk.sub_left (randAddr_sub hu)).sub_right (below_sub (by decide) (by omega_arith))
  simp only [wsW, uoW, randPtr_wide v hu, lenN, ppN, cw, rw'] at post
  obtain ⟨P1, P2, P3⟩ := post
  obtain m₂ : Frame [below E.sp 20] s₂.mem u.mem := by rw [spT] at m₂; exact m₂
  obtain tdi : t.gpr .edi = s.gpr .edi := A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize hres : Spec.Dsa.probablePrime (Proof.Dsa.ProbablePrime.candidateAt
    (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP)) (E.witT.drop used) = res at P1 P3 ⊢
  obtain stLt : Proof.Dsa.ProbablePrime.status res < 2 ^ 32 := by
    unfold Proof.Dsa.ProbablePrime.status; split <;> decide
  refine ⟨?_, (csu .edi (by decide)).trans tdi, (csu .esp (by decide)).trans spT,
    (csu .esi (by decide)).trans (A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)),
    rdu.trans A.rd, wru.trans A.wr, usy.trans A.syms, ?_, ?_⟩
  · rw [hres, ← ax₂]; exact BitVec.eq_of_toNat_eq (by rw [P1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt stLt])
  · rw [← A.mem]
    exact call_chg v spT Fm (by simp only [List.length_cons, List.length_nil]; omega_arith) Fu m₂ P2
  · intro b rest hr
    obtain hr' : res = some (b, rest) := hres.symm.trans hr
    obtain wl : E.witT.length = E.witLen := by rw [← B.wit]; simp [Spec.Rsa.bytesAt]
    obtain restLe : rest.length ≤ E.witLen - used := by
      have := (VG.Proof.Dsa.Generation.probablePrime_suffix hr).length_le
      simp only [List.length_drop, wl] at this; omega_arith
    rw [m₂.readW (r := ⟨off E.base fUsedOut, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (v.scratchStack.sub_left (Offset.sub_base _ (by simp only [fUsedOut, hdr]; omega_arith))).sub_right
        (below_sub (by decide) v.low)) (by decide), readW_low]
    obtain h := P3 b rest hr'
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
      BitVec.add_zero, List.cons.injEq, and_true] at h
    rw [h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith

theorem test_ok {bits : Nat} {name : String} {callee : Prog isa}
    (verified : Verified target callee (ppContract bits)) (noSp : NoSp callee) (stack : stackUse callee ≤ 152)
    {E : Env} (v : E.Valid) {s : State} (B : Base E s) {used : Nat}
    (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen)
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords)
    (odd : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      (off E.base sPP) % 2 = 1)
    (len : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
      s.mem (off E.base sPP)) = bits) :
    WP isa (test name callee) s (TestPost E bits used
      (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP)) s) := by
  have sz := v.size_ge
  unfold test
  simp only [seqs]
  refine testArgs_ok B.scr (by simp only [sPP]; omega_arith) B.witW B.witLenW hU hu v.witLen32 fun t A =>
    WP.seq (WP.mono (testCall_ok verified noSp stack v B A hu lay odd len) fun u R => ?_)
  obtain hsU : Scr u E.base E.size := Scr.of_eq B.scr R.edi (R.esp.trans B.sp.symm) R.wr
  generalize hres : Spec.Dsa.probablePrime (Proof.Dsa.ProbablePrime.candidateAt
    (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP)) (E.witT.drop used) = res
  obtain uax : u.gpr .eax = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := by rw [R.eax, hres]
  obtain Apt : E.Apart [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fRes, 4), (fUsed, 4), (fUsedOut, 8)] := by
    have lay' := lay
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay'
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;>
      simp only [sPP, ppWords, fRes, fUsed, fUsedOut, fOut, fWitLen, hdr] at lay' ⊢ <;> omega_arith
  obtain CH' : E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fRes, 4), (fUsed, 4), (fUsedOut, 8)] s.mem u.mem :=
    R.chg.mono fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
      rcases ho with h | h <;> simp only [h, true_or, or_true]
  obtain usedU : u.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v R.chg (by simp only [fUsed, hdr]; omega_arith) (fun o ho => by
      have lay' := lay
      simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;>
        simp only [sPP, ppWords, fUsed, fUsedOut, hdr] at lay' ⊢ <;> omega_arith), hU]
  refine WP.seq (st_ok hsU (by simp only [fRes, hdr]; omega_arith) fun x₁ M₁ => wp_cmpi fun x₂ F₂ _ z₂ => WP.block_nil ?_)
  obtain m₂' : x₂.mem = u.mem.writeW (off E.base fRes) (u.gpr .eax) := by rw [F₂.mem, M₁.mem]
  obtain g₂ : x₂.gpr = u.gpr := by rw [F₂.gpr, M₁.gpr]
  obtain hsX : Scr x₂ E.base E.size := Scr.of_eq hsU (by rw [g₂]) (by rw [g₂]) (by rw [F₂.wr, M₁.wr])
  obtain resX : x₂.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := by
    rw [m₂', Mem.readW_writeW_self32, uax]
  obtain usedX : x₂.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [m₂', word_store_other v _ (by simp only [fUsed, hdr]; omega_arith) (by simp only [fRes, hdr]; omega_arith)
      (by simp only [fUsed, fRes, hdr]; omega_arith), usedU]
  obtain CHX : E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fRes, 4), (fUsed, 4), (fUsedOut, 8)] s.mem x₂.mem := by
    rw [m₂']; exact CH'.store (d := fRes) (n := 4) (.tail _ (.head _)) (by decide) _
  obtain post : ∀ y : State, y.gpr .edi = s.gpr .edi → y.gpr .esp = E.sp → y.gpr .esi = s.gpr .esi →
      y.rd = s.rd → y.wr = s.wr → y.syms = s.syms →
      E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
        (fRes, 4), (fUsed, 4), (fUsedOut, 8)] s.mem y.mem →
      y.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) →
      y.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (nextUsed E.witLen used res) →
      TestPost E bits used (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
        (off E.base sPP)) s y := by
    intro y yd ysp ysi yrd ywr ysy yc yr yu
    refine ⟨B.keep v yc Apt yd (ysp.trans B.sp.symm) yrd ywr ysy, ?_, ?_, yc, ysi, yrd, ywr, ysy⟩
    · rw [yr, hres]
    · rw [yu, hres]
  obtain xrd : x₂.rd = s.rd := by rw [F₂.rd, M₁.rd, R.rd]
  obtain xwr : x₂.wr = s.wr := by rw [F₂.wr, M₁.wr, R.wr]
  obtain xsy : x₂.syms = s.syms := by rw [F₂.syms, M₁.syms, R.syms]
  cases res with
  | none =>
    refine WP.ite true (by change x₂.zf = _; rw [z₂, M₁.gpr, uax]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact post x₂ (by rw [g₂, R.edi]) (by rw [g₂, R.esp]) (by rw [g₂, R.esi]) xrd xwr xsy CHX resX usedX
  | some p =>
    obtain ⟨b, rest⟩ := p
    refine WP.ite false (by
        change x₂.zf = _; rw [z₂, M₁.gpr, uax]; cases b <;> simp [Proof.Dsa.ProbablePrime.status])
      (fun h => by cases h) (fun _ => ?_)
    obtain wl : E.witT.length = E.witLen := by rw [← B.wit]; simp [Spec.Rsa.bytesAt]
    obtain restLe : rest.length ≤ E.witLen - used := by
      have := (VG.Proof.Dsa.Generation.probablePrime_suffix hres).length_le
      simp only [List.length_drop, wl] at this; omega_arith
    obtain uo : x₂.mem.readW (off E.base fUsedOut) 32 = BitVec.ofNat 32 (E.witLen - used - rest.length) := by
      rw [m₂', word_store_other v _ (by simp only [fUsedOut, hdr]; omega_arith) (by simp only [fRes, hdr]; omega_arith)
        (by simp only [fUsedOut, fRes, hdr]; omega_arith), R.usedOut b rest hres]
    refine ld_ok hsX (by simp only [fUsedOut, hdr]; omega_arith) fun x₃ u₃ => addm_ok (Scr.of_eq hsX
      (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.wr) (by simp only [fUsed, hdr]; omega_arith) fun x₄ u₄ =>
        st_ok (Scr.of_eq hsX (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
          (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr]))
          (by simp only [fUsed, hdr]; omega_arith) fun x₅ M₅ => WP.block_nil ?_
    obtain val : x₅.mem = x₂.mem.writeW (off E.base fUsed)
        (BitVec.ofNat 32 (E.witLen - used - rest.length) + BitVec.ofNat 32 used) := by
      rw [M₅.mem, u₄.gpr, u₃.gpr, u₄.mem, u₃.mem, uo, usedX]
    obtain sum : BitVec.ofNat 32 (E.witLen - used - rest.length) + BitVec.ofNat 32 used =
        BitVec.ofNat 32 (E.witLen - rest.length) := by
      rw [← BitVec.ofNat_add]; congr 1; omega_arith
    rw [sum] at val
    obtain g₅ : ∀ r, r ≠ .eax → x₅.gpr r = u.gpr r := fun r h => by
      rw [M₅.gpr, u₄.other r h, u₃.other r h, g₂]
    refine post x₅ (by rw [g₅ _ (by decide), R.edi]) (by rw [g₅ _ (by decide), R.esp])
      (by rw [g₅ _ (by decide), R.esi]) (by rw [M₅.rd, u₄.rd, u₃.rd, xrd]) (by rw [M₅.wr, u₄.wr, u₃.wr, xwr])
      (by rw [M₅.syms, u₄.syms, u₃.syms, xsy]) ?_ ?_ ?_
    · rw [val]; exact CHX.store (d := fUsed) (n := 4) (.tail _ (.tail _ (.head _))) (by decide) _
    · rw [val, word_store_other v _ (by simp only [fRes, hdr]; omega_arith) (by simp only [fUsed, hdr]; omega_arith)
        (by simp only [fUsed, fRes, hdr]; omega_arith), resX]
    · rw [val, Mem.readW_writeW_self32]; rfl

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.Copy`, which this module and modules that import it used -/

section

/-! # Copies of bytes into `scratch` -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Bignum.X86 (byteAddr)

/-- Equal reads are equal bytes. -/
theorem bytesAt_of_read {m m' : Mem} {a b : Addr} {n : Nat} (h : m'.read b n = m.read a n) :
    Spec.Rsa.bytesAt m' b n = Spec.Rsa.bytesAt m a n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [← Mem.extractLsb'_read m' b hi, ← Mem.extractLsb'_read m a hi, h]

/-- `n` bytes from `scratch + src` to `scratch + dst`. -/
theorem copyS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src n : Nat}
    (hn : 0 < n) (hd : dst + n ≤ size) (hsrc : src + n ≤ size) (apart : dst + n ≤ src ∨ src + n ≤ dst) :
    WP isa (copyS dst src n) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base dst) n = Spec.Rsa.bytesAt s.mem (off base src) n ∧
      Frame [⟨off base dst, n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold copyS copyTo
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => scr_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ _ => wp_movi fun s₃ u₃ =>
    WP.block_nil ?_
  have edi₂ : s₂.gpr .edi = s.gpr .edi := by rw [g₂ _ (by decide), g₁ _ (by decide)]
  have srcW := Scr.wide hs (d := src) (by omega_using [hn, hsrc])
  have dstW := Scr.wide hs (d := dst) (by omega_using [hn, hd])
  have srcN := Scr.toNat_add hs (d := src) (by omega_using [hn, hsrc])
  have dstN := Scr.toNat_add hs (d := dst) (by omega_using [hn, hd])
  refine WP.mono (VG.Proof.Bignum.X86.copyBuffers_ok (src := s.gpr .edi + BitVec.ofNat 32 src)
    (dst := s.gpr .edi + BitVec.ofNat 32 dst) hn (by omega_using [hd, hsrc, apart, nw]) (by rw [srcN]; omega_using [hsrc, nw]) (by rw [dstN]; omega_using [hd, nw])
    ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨R, _, _, F, K⟩ => ?_
  · simp only [byteAddr, srcW, u₃.rd, u₃.wr, rd₂, wr₂, rd₁, wr₁]; exact hs.read (by omega_using [hsrc])
  · simp only [byteAddr, dstW, u₃.wr, wr₂, wr₁]; exact hs.write (by omega_using [hd])
  · simp only [byteAddr, srcW, dstW]; exact Offset.disjoint base (by omega_using [apart]) (by omega_using [hsrc, nw]) (by omega_using [hd, nw])
  · rw [u₃.other _ (by decide), g₂ _ (by decide), e₁]
  · rw [u₃.other _ (by decide), e₂, g₁ _ (by decide)]
  · rw [u₃.gpr]
  simp only [byteAddr, srcW, dstW, u₃.mem, m₂, m₁] at R F
  refine ⟨bytesAt_of_read R, F, ?_⟩
  refine ⟨fun r hr => ?_, by rw [K.2.1, u₃.rd, rd₂, rd₁], by rw [K.2.2, u₃.wr, wr₂, wr₁]⟩
  rw [K.1 r hr, u₃.other r (by simp_all), g₂ r (by simp_all), g₁ r (by simp_all)]

/-- `n` bytes from the address in the word at `scratch + w` (a range of a
readable region apart from `scratch`) to `scratch + dst`. -/
theorem copyIn_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w dst n : Nat} {S : BitVec 32}
    (hw : w + 4 ≤ size) (hS : s.mem.readW (off base w) 32 = S) {R : Region} (hR : R ∈ s.rd)
    (hRs : R.Disjoint ⟨base, size⟩) (hRl : R.len ≤ 2 ^ 32) {o : Nat} (hSo : S.setWidth 64 = R.base + BitVec.ofNat 64 o)
    (ho : o + n ≤ R.len) (hSn : S.toNat + n ≤ 2 ^ 32)
    (hn : 0 < n) (hd : dst + n ≤ size) :
    WP isa (copyTo [.mov .esi (.mem (sc w))] dst n) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base dst) n = Spec.Rsa.bytesAt s.mem (R.base + BitVec.ofNat 64 o) n ∧
      Frame [⟨off base dst, n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold copyTo
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append]
  refine ld_ok hs hw fun s₁ u₁ => scr_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ _ => wp_movi fun s₃ u₃ => WP.block_nil ?_
  have dstW := Scr.wide hs (d := dst) (by omega_using [hn, hd])
  have dstN := Scr.toNat_add hs (d := dst) (by omega_using [hn, hd])
  have sub : Region.Sub ⟨S.setWidth 64, n⟩ R := by rw [hSo]; exact Offset.sub_base _ ho
  refine WP.mono (VG.Proof.Bignum.X86.copyBuffers_ok (src := S)
    (dst := s.gpr .edi + BitVec.ofNat 32 dst) hn (by omega_using [hd, sl]) hSn (by rw [dstN]; omega_using [hd, nw])
    ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨Rd, _, _, F, K⟩ => ?_
  · simp only [byteAddr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
    rw [hSo]
    exact ⟨R, List.mem_append_left _ hR, Offset.contains_base _ ho (by omega_using [hRl, ho])⟩
  · simp only [byteAddr, dstW, u₃.wr, wr₂, u₁.wr]; exact hs.write (by omega_using [hd])
  · simp only [byteAddr, dstW]
    exact (hRs.sub_left sub).sub_right (Offset.sub_base base hd)
  · rw [u₃.other _ (by decide), g₂ _ (by decide), u₁.gpr, hS]
  · rw [u₃.other _ (by decide), e₂, u₁.other _ (by decide)]
  · rw [u₃.gpr]
  simp only [byteAddr, dstW, u₃.mem, m₂, u₁.mem] at Rd F
  refine ⟨?_, F, ?_⟩
  · rw [bytesAt_of_read Rd, hSo]
  · refine ⟨fun r hr => ?_, by rw [K.2.1, u₃.rd, rd₂, u₁.rd], by rw [K.2.2, u₃.wr, wr₂, u₁.wr]⟩
    rw [K.1 r hr, u₃.other r (by simp_all), g₂ r (by simp_all), u₁.other r (by simp_all)]

end VG.Proof.Dsa.X86.Generation

end

end

/-! # q from a seed: hashed, shaped, and tested -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Seed `k` of the tape. -/
def chunk (E : Env) (k : Nat) : List Byte := (E.seedT.drop (k * E.qLen)).take E.qLen

/-- The seed into the block after the hash value. -/
theorem seedIn_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {s : State}
    (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32) :
    WP isa g.seedIn s fun t =>
      Spec.Rsa.bytesAt t.mem (off E.base (sState + g.H.N)) g.qLen = chunk E k ∧
      Frame [⟨off E.base (sState + g.H.N), g.qLen⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have sf := v.seedsFit
  obtain q0 : 0 < g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  obtain q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  obtain kq : k * E.qLen + E.qLen ≤ E.seedsLen := by rw [Nat.add_mul] at hk; omega_arith
  obtain sl : E.seeds.toNat < 2 ^ 32 := by omega_arith
  have sN := v.seedsNat
  have si := v.seedsIn
  obtain seedW : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).setWidth 64 =
      E.seeds + BitVec.ofNat 64 (k * E.qLen) := by
    apply BitVec.eq_of_toNat_eq
    obtain e : (E.seeds + BitVec.ofNat 64 (k * E.qLen)).toNat = E.seeds.toNat + k * E.qLen := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * E.qLen) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
    simp only [BitVec.toNat_setWidth, e]
    rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain seedN : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).toNat = E.seeds.toNat + k * E.qLen := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * E.qLen) (by omega_arith),
      Nat.mod_eq_of_lt (a := E.seeds.toNat + k * E.qLen) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  unfold Geo.seedIn
  obtain seedW' : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).setWidth 64 =
      E.wit + BitVec.ofNat 64 (E.seedsOff + k * E.qLen) := by
    rw [seedW, Env.seeds, VG.Offset.add_add]
  have wl := v.witFit
  refine WP.mono (copyIn_ok B.scr (w := fSeed) (by simp only [fSeed, hdr]; omega_arith) hS (R := E.witRegion)
    B.tapes v.witFar.1 (by simp only [Env.witRegion]; omega_arith) (o := E.seedsOff + k * E.qLen) seedW'
    (by simp only [Env.witRegion]; omega_arith) (by rw [seedN]; omega_arith) q0
    (by simp only [sState]; omega_arith)) fun t ⟨R, F, K⟩ => ?_
  refine ⟨?_, F, K⟩
  rw [R, ← hq]
  change Spec.Rsa.bytesAt s.mem (E.wit + _) E.qLen = _
  rw [B.part (by omega_arith)]
  simp only [chunk, Env.seedT, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega_arith

theorem HashOk.hash_length {H : VG.Impl.Pbkdf2.Md.X86.Hash} {iv : List (BitVec 32)} (F : HashOk H iv)
    (m : List Byte) : (F.ok.hH.SH.H.hash m).length = H.N := by
  rw [F.ok.link.hash, List.length_take, VG.Proof.MdStream.Md.hash, F.ok.md.digest_length, F.DN, Nat.min_self]

/-- The ranges a seed's q changes before its test. -/
def qPre (g : Geo) : List (Nat × Nat) :=
  [(sState, 128), (sHScr, 560), (sPk + g.pLen, g.qLen),
    (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size)]

/-- The ranges a seed's q changes. -/
def qRanges (g : Geo) : List (Nat × Nat) := qPre g ++ [(fRes, 4), (fUsed, 4), (fUsedOut, 8)]

/-- After q of seed `k`: q in p||q||g, the test's status and the witness
cursor, and only `qRanges` and the stack changed. -/
structure QPost (E : Env) (g : Geo) (k used : Nat) (s t : State) : Prop where
  base : Base E t
  q : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen) =
    Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)
  res : t.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
    (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (E.witT.drop used)))
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (nextUsed E.witLen used
    (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (E.witT.drop used)))
  chg : E.Chg (qRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The two ORs of q's shaping, as `qShape_memory` states them. -/
theorem shape_mem (m : Mem) (op : Addr) {n : Nat} (hn : 2 ≤ n) (hn' : n < 2 ^ 64) :
    let m₁ := m.writeW op (m op ||| BitVec.ofNat 8 0x80)
    m₁.writeW (op + BitVec.ofNat 64 (n - 1)) (m₁ (op + BitVec.ofNat 64 (n - 1)) ||| BitVec.ofNat 8 1) =
      (m.writeW op (m op ||| (128#8))).writeW (op + BitVec.ofNat 64 (n - 1))
        (m (op + BitVec.ofNat 64 (n - 1)) ||| (1#8)) := by
  intro m₁
  obtain ne : op + BitVec.ofNat 64 (n - 1) ≠ op := by
    simpa using Offset.add_ofNat_ne op (by omega_arith : n - 1 < 2 ^ 64) (by decide : 0 < 2 ^ 64) (by omega_arith)
  simp only [m₁, VG.WriteBytes.writeW8_apply, ne, ↓reduceIte]

/-- Within q of a seed: what every step keeps. -/
structure QAt (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (qPre g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem qPre_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (qPre g) := by
  have sz := v.size_ge
  obtain p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  obtain q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  intro o ho
  simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  obtain szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [sState, sHScr, sPk, sPP, fOut, fWitLen, hdr] <;> omega_arith

theorem qin {g : Geo} {E : Env} {d n : Nat} (o : Nat × Nat) (ho : o ∈ qPre g) (h₁ : o.1 ≤ d)
    (h₂ : d + n ≤ o.1 + o.2) :
    ∃ r' ∈ ((qPre g).map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion],
      Region.Sub ⟨off E.base d, n⟩ r' := Env.in_range ho h₁ h₂

theorem stk_sub {E : Env} (v : E.Valid) {t : State} (B : Base E t) :
    Region.Sub (VG.Proof.Pbkdf2.Stream.X86.stk t) E.stackRegion := by
  have low := v.low
  simp only [VG.Proof.Pbkdf2.Stream.X86.stk, B.sp, Env.stackRegion]; exact below_sub (by decide) (by omega_arith)

/-- A step within q keeps what every step keeps. -/
theorem QAt.step {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t u : State} (Q : QAt E g s t)
    (C : E.Chg (qPre g) t.mem u.mem) (edi : u.gpr .edi = t.gpr .edi) (sp : u.gpr .esp = t.gpr .esp)
    (rd : u.rd = t.rd) (wr : u.wr = t.wr) (sy : u.syms = t.syms) : QAt E g s u :=
  ⟨Q.base.keep v C (qPre_apart G v) edi sp rd wr sy, Q.chg.trans C, rd.trans Q.rd, wr.trans Q.wr, sy.trans Q.syms⟩

/-- The seed in the block. -/
theorem q1_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32) :
    WP isa g.seedIn s fun t => QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sState + g.H.N)) g.qLen = chunk E k := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have hN := G.N
  obtain q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  refine VG.X86.WP.mono_syms (seedIn_ok G v hq B hk hS) fun t₁ ⟨S₁, F₁, K₁⟩ sy₁ => ⟨?_, S₁⟩
  exact QAt.step G v ⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩ (Env.Chg.of_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact qin (sState, 128) (by simp [qPre]) (by omega_arith) (by omega_arith))
    (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁

/-- The seed's hash, into p||q||g. -/
theorem q2_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₁ : State} (Q₁ : QAt E g s t₁) {k : Nat}
    (S₁ : Spec.Rsa.bytesAt t₁.mem (off E.base (sState + g.H.N)) g.qLen = chunk E k) :
    WP isa (hash g.H g.iv g.qLen (sPk + g.pLen)) t₁ fun t => QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N = Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  obtain p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  have hN := G.N
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  have B₁ := Q₁.base
  have low := v.low
  rw [← hN]
  refine VG.X86.WP.mono_syms (hash_ok G.hash B₁.scr (dst := sPk + g.pLen)
    (by simp only [sHScr]; omega_arith) (by simp only [sHScr]; omega_arith) (by simp only [sPk]; omega_arith)
    (by simp only [sState, sPk]; omega_arith) (by simp only [sHScr, sPk]; omega_arith) (by rw [B₁.sp]; omega_arith)
    (v.scratchStack.symm.sub_left (stk_sub v B₁))) fun t₂ ⟨H₂, F₂, G₂, rd₂, wr₂⟩ sy₂ => ⟨?_, ?_⟩
  · refine Q₁.step G v (Env.Chg.of_frame F₂ fun r hr => ?_)
      (G₂ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (G₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)) rd₂ wr₂ sy₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact qin (sState, 128) (by simp [qPre]) (by omega_arith) (by omega_arith)
    · exact qin (sHScr, 560) (by simp [qPre]) (by omega_arith) (by omega_arith)
    · exact qin (sPk + g.pLen, g.qLen) (by simp [qPre]) (by omega_arith) (by omega_arith)
    · exact Env.in_stack (stk_sub v B₁)
  · have bsEq : ∀ m p n, Spec.Sha256.bytesAt m p n = Spec.Rsa.bytesAt m p n := fun _ _ _ => rfl
    rw [← hN] at S₁
    simp only [bsEq] at H₂
    rw [S₁, G.seedHash, hN] at H₂
    rw [hN]
    exact H₂

/-- q's top and low bits. -/
theorem q3_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₂ : State} (Q₂ : QAt E g s t₂) {k : Nat}
    (H₂ : Spec.Rsa.bytesAt t₂.mem (off E.base (sPk + g.pLen)) g.H.N = Spec.Dsa.seedHash (8 * g.qLen) (chunk E k)) :
    WP isa (.block (orByte (sPk + g.pLen) 0x80 ++ orByte (sPk + g.pLen + g.qLen - 1) 1)) t₂ fun t => QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Dsa.seedHash (8 * g.qLen) (chunk E k)) 7 := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  obtain p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  obtain q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  have hN := G.N
  have B₂ := Q₂.base
  rw [show orByte (sPk + g.pLen + g.qLen - 1) 1 = orByte (sPk + g.pLen + g.H.N - 1) 1 ++ [] by
    rw [hN, List.append_nil]]
  refine orByte_ok B₂.scr (by simp only [sPk]; omega_arith) (by decide) fun t₃' g₃' rd₃' wr₃' sy₃' m₃' =>
    orByte_ok (Scr.of_eq B₂.scr (g₃' _ (by decide)) (g₃' _ (by decide)) wr₃') (by simp only [sPk]; omega_arith)
      (by decide) fun t₃ g₃ rd₃ wr₃ sy₃ m₃ => WP.block_nil ?_
  rw [m₃'] at m₃
  have nw := v.scratchFit
  obtain aEq : off E.base (sPk + g.pLen + g.H.N - 1) = off E.base (sPk + g.pLen) + BitVec.ofNat 64 (g.H.N - 1) := by
    simp only [off, VG.Offset.add_add]; congr 2; omega_arith
  rw [aEq, shape_mem t₂.mem _ (by omega_arith) (by omega_arith)] at m₃
  set D := Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) with hD
  obtain Dl : D.length = g.H.N := by rw [hD, ← G.seedHash]; exact G.hash.hash_length _
  obtain qPk : (sPk + g.pLen, g.qLen) ∈ qPre g := by simp [qPre]
  refine ⟨Q₂.step G v ?_ (by rw [g₃ _ (by decide), g₃' _ (by decide)]) (by rw [g₃ _ (by decide), g₃' _ (by decide)])
    (by rw [rd₃, rd₃']) (by rw [wr₃, wr₃']) (by rw [sy₃, sy₃']), ?_⟩
  · rw [m₃]
    obtain h1 := (Env.Chg.refl (E := E) (qPre g) t₂.mem).byte qPk (i := 0) (by omega_arith) (by omega_arith)
      (t₂.mem (off E.base (sPk + g.pLen)) ||| 128#8)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h1
    exact h1.byte qPk (i := g.H.N - 1) (by omega_arith) (by omega_arith) _
  · rw [m₃, ← Dl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega_arith) (by omega_arith) fun i hi => ?_
    have := congrArg (fun l => l.getD i 0) H₂
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show i < g.H.N by omega_arith), Option.map_some, Option.getD_some] at this
    rw [this, List.getD_eq_getElem?_getD]

/-- q into the test's working space. -/
theorem q4_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₃ : State} (Q₃ : QAt E g s t₃) {k : Nat}
    (shaped : Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.H.N =
      VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Dsa.seedHash (8 * g.qLen) (chunk E k)) 7) :
    WP isa (copyS (sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).candidate) (sPk + g.pLen) g.qLen) t₃
      fun t => QAt E g s t ∧
        Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)) t.mem
          (off E.base sPP) = Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) ∧
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen) =
          Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  obtain p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  obtain q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  have hN := G.N
  have B₃ := Q₃.base
  have nw := v.scratchFit
  set D := Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) with hD
  obtain Dl : D.length = g.H.N := by rw [hD, ← G.seedHash]; exact G.hash.hash_length _
  obtain candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).candidate + g.qLen ≤
      (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout]; omega_arith
  obtain candLay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  refine VG.X86.WP.mono_syms (copyS_ok B₃.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).candidate) (src := sPk + g.pLen) (n := g.qLen)
    (by omega_arith) (by simp only [sPP]; omega_arith) (by simp only [sPk]; omega_arith)
    (by simp only [sPP, sPk]; omega_arith)) fun t₄ ⟨R₄, F₄, K₄⟩ sy₄ => ⟨?_, ?_, ?_⟩
  · exact Q₃.step G v (Env.Chg.of_frame F₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact qin (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size) (by simp [qPre]) (by omega_arith)
        (by omega_arith))
      (K₄.1 _ (by decide)) (K₄.1 _ (by decide)) K₄.2.1 K₄.2.2 sy₄
  · have qval : Spec.Dsa.decodeBE (VG.Proof.Ffdh.ParameterCandidate.shapedOctets D 7) =
        Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) :=
      VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hD, Dl, hN])
    unfold Proof.Dsa.ProbablePrime.candidateAt
    obtain b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).bits / 8 = g.qLen := by
      show 8 * g.qLen / 8 = g.qLen; omega_arith
    rw [b8, VG.Offset.add_add, R₄, ← hN, shaped, qval, hN]
  · have qval : Spec.Dsa.decodeBE (VG.Proof.Ffdh.ParameterCandidate.shapedOctets D 7) =
        Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) :=
      VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hD, Dl, hN])
    rw [frame_bytes F₄ (by simp only [sPP, sPk]; omega_arith) (by simp only [sPP]; omega_arith) (by simp only [sPk]; omega_arith),
      ← hN, shaped, qval, hN]

theorem qPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k used : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen) :
    WP isa g.qPart s (QPost E g k used s) := by
  have sz := v.size_ge
  obtain q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  obtain q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  obtain p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  unfold Geo.qPart
  simp only [seqs]
  refine WP.seq (WP.mono (q1_ok G v hq B hk hS) fun t₁ h₁ => ?_)
  obtain ⟨Q₁, S₁⟩ := h₁
  refine WP.seq (WP.mono (q2_ok G v Q₁ S₁) fun t₂ h₂ => ?_)
  obtain ⟨Q₂, H₂⟩ := h₂
  refine WP.seq (WP.mono (q3_ok G v Q₂ H₂) fun t₃ h₃ => ?_)
  obtain ⟨Q₃, shaped⟩ := h₃
  refine WP.seq (WP.mono (q4_ok G v Q₃ shaped) fun t₄ h₄ => ?_)
  obtain ⟨Q₄, cval, qval⟩ := h₄
  obtain lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  obtain candLay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  obtain Ap := qPre_apart G v
  obtain qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega) (chunk E k)
  obtain hU₄ : t₄.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v Q₄.chg (by simp only [fUsed, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sState, sHScr, sPk, sPP, fUsed, hdr] <;> omega⟩), hU]
  refine VG.X86.WP.mono_syms (test_ok G.qv G.qNoSp G.qStack v Q₄.base hU₄ hu lay (by rw [cval]; exact qsh.1)
    (by rw [cval]; exact VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega) _)) fun t₅ P sy₅ => ?_
  rw [cval] at P
  obtain szq : VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width (8 * g.qLen)) ≤
      (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout]; omega
  refine ⟨P.base, ?_, P.res, P.used, ?_, P.rd.trans Q₄.rd, P.wr.trans Q₄.wr, P.syms.trans Q₄.syms⟩
  · rw [Env.Chg.scratch v P.chg (by simp only [sPk]; omega) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;>
        simp only [sPP, sPk, fRes, fUsed, fUsedOut, hdr] at szq candLay ⊢ <;> omega)]
    exact qval
  · refine (Q₄.chg.mono fun o ho => List.mem_append_left _ ho).trans (Env.Chg.of_frame P.chg fun r hr => ?_)
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Env.in_range (o := (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size))
        (by simp [qPre]) (by omega) (by omega)
    · exact Env.in_range (o := (fRes, 4)) (by simp) (by omega) (by omega)
    · exact Env.in_range (o := (fUsed, 4)) (by simp) (by omega) (by omega)
    · exact Env.in_range (o := (fUsedOut, 8)) (by simp) (by omega) (by omega)
    · exact Env.in_stack (fun _ h => h)

end VG.Proof.Dsa.X86.Generation
