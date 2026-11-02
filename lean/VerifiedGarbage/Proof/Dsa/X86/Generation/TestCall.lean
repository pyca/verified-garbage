module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestPre
import VerifiedGarbage.Proof.Framework.X86.CallReturn
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.X86.Wp

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
    (K : Proof.Dsa.ModPow.Keeps (off E.base sPP) ppWords
      [(0, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits))] w.mem u.mem) :
    E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fUsedOut, 8)] t.mem u.mem := by
  have sz := v.size_ge
  have low := v.low
  have nw := v.scratchFit
  intro x hx
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨hPP, hUO, hS⟩ := hx
  have hS' : ∀ k ≤ 200, ¬ (below E.sp k).Contains x 1 := fun k hk h => hS (below_sub hk (by omega_arith) x h)
  by_cases hw : (⟨off E.base sPP, 8 * ppWords⟩ : Region).Contains x 1
  · -- In the working space but not its scratch: the test kept it.
    have hi : (x - off E.base sPP).toNat < 8 * ppWords := by simp only [Region.Contains] at hw; omega_arith
    have hx : x = off E.base sPP + BitVec.ofNat 64 (x - off E.base sPP).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have k := K (x - off E.base sPP).toNat hi (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      by_contra h
      apply hPP
      simp only [Region.Contains]
      omega_arith)
    rw [← hx] at k
    rw [k]
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
  have spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have low := v.low
  have hsT : Scr t E.base E.size := Scr.of_eq B.scr (A.other _ (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by rw [spT, B.sp]) A.wr
  refine ⟨test_pre v B A hu lay (by rw [A.mem]; exact odd) (by rw [A.mem]; exact len), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [testRd, testWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · by_cases h0 : E.witLen - used = 0
      · exact ⟨E.witRegion, List.mem_append_left _ (A.rd ▸ B.tapes.2.2), 0, by simp [randAddr, h0, Env.witRegion],
          by simp [h0]⟩
      · exact ⟨E.witRegion, List.mem_append_left _ (A.rd ▸ B.tapes.2.2), used, by simp [randAddr, h0, Env.witRegion],
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
  have spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have low := v.low
  have fitT : 24 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_arith
  obtain ⟨e0, e1, e2, e3, e4⟩ := testEntry_arg (E := E) (used := used) fitT
  have Fm := testEntry_mem (E := E) (used := used) fitT
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.ebp] at e4
  have wsW := Scr.wide B.scr (d := sPP) (by simp only [sPP]; omega_arith)
  have uoW := Scr.wide B.scr (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  have lenLt := v.lens.2.2
  rw [spT] at Fm
  have cw := cand_frame v lay (k := 24) (by decide) Fm
  rw [A.mem] at cw
  have wk := (v.tapesFar E.witRegion (by simp)).2.2
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
  have spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have low := v.low
  have cp := testCallPre v B A hu lay odd len
  have fitT : 24 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_arith
  obtain ⟨e0, e1, e2, e3, e4⟩ := testEntry_arg (E := E) (used := used) fitT
  have Fm := testEntry_mem (E := E) (used := used) fitT
  simp only [testEntry] at e0 e1 e2 e3 e4 Fm
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.ebp] at e4
  refine WP.of_syms (WP.callWithReturn verified.1 noSp (by decide) (by decide)
    (by rw [spT]; simp only [List.length_cons, List.length_nil]; omega_arith) cp fun u rdu wru csu Fu post usy => ?_)
  obtain ⟨s₂, m₂, ax₂, post⟩ := post
  generalize ew : (pushed testRegs t).callEntry.withRegions (testRd E used) (testWr E t) = w at e0 e1 e2 e3 e4 Fm post
  sig_post [ppContract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow] at post
  simp only [e0, e1, e2, e3, e4, ret32] at post
  have wsW := Scr.wide B.scr (d := sPP) (by simp only [sPP]; omega_arith)
  have uoW := Scr.wide B.scr (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  have lenLt := v.lens.2.2
  have lenN : (BitVec.ofNat 32 (E.witLen - used)).toNat = E.witLen - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have ppN : (BitVec.ofNat 32 ppWords).toNat = ppWords := by decide
  rw [spT] at Fm
  have cw := cand_frame v lay (k := 24) (by decide) Fm
  rw [A.mem] at cw
  have wk := (v.tapesFar E.witRegion (by simp)).2.2
  have wf := v.witFit
  have rw' : Spec.Rsa.bytesAt w.mem (randAddr E used) (E.witLen - used) = E.witT.drop used := by
    rw [← rand_bytes (m := t.mem) (by rw [A.mem]; exact B.wit)]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine Frame.bytes Fm (R := ⟨randAddr E used, E.witLen - used⟩) ?_ (by show E.witLen - used ≤ 2 ^ 64; omega_arith) hi
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (wk.sub_left (randAddr_sub hu)).sub_right (below_sub (by decide) (by omega_arith))
  simp only [wsW, uoW, randPtr_wide v hu, lenN, ppN, cw, rw'] at post
  obtain ⟨P1, P2, P3⟩ := post
  rw [m₂] at P2 P3
  have tdi : t.gpr .edi = s.gpr .edi := A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize hres : Spec.Dsa.probablePrime (Proof.Dsa.ProbablePrime.candidateAt
    (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP)) (E.witT.drop used) = res at P1 P3 ⊢
  have stLt : Proof.Dsa.ProbablePrime.status res < 2 ^ 32 := by
    unfold Proof.Dsa.ProbablePrime.status; split <;> decide
  refine ⟨?_, (csu .edi (by decide)).trans tdi, (csu .esp (by decide)).trans spT,
    (csu .esi (by decide)).trans (A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)),
    rdu.trans A.rd, wru.trans A.wr, usy.trans A.syms, ?_, ?_⟩
  · rw [hres, ← ax₂]; exact BitVec.eq_of_toNat_eq (by rw [P1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt stLt])
  · rw [← A.mem]
    exact call_chg v spT Fm (by simp only [List.length_cons, List.length_nil]; omega_arith) Fu P2
  · intro b rest hr
    have hr' : res = some (b, rest) := hres.symm.trans hr
    have wl : E.witT.length = E.witLen := by rw [← B.wit]; simp [Spec.Rsa.bytesAt]
    have restLe : rest.length ≤ E.witLen - used := by
      have := (VG.Proof.Dsa.Generation.probablePrime_suffix hr).length_le
      simp only [List.length_drop, wl] at this; omega_arith
    rw [readW_low]
    have h := P3 b rest hr'
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
  refine testArgs_ok B.scr (by simp only [sPP]; omega_arith) B.witW B.witLenW hU hu v.lens.2.2 fun t A =>
    WP.seq (WP.mono (testCall_ok verified noSp stack v B A hu lay odd len) fun u R => ?_)
  have hsU : Scr u E.base E.size := Scr.of_eq B.scr R.edi (R.esp.trans B.sp.symm) R.wr
  generalize hres : Spec.Dsa.probablePrime (Proof.Dsa.ProbablePrime.candidateAt
    (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP)) (E.witT.drop used) = res
  have uax : u.gpr .eax = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := by rw [R.eax, hres]
  have Apt : E.Apart [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fRes, 4), (fUsed, 4), (fUsedOut, 8)] := by
    have lay' := lay
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay'
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;>
      simp only [sPP, ppWords, fRes, fUsed, fUsedOut, fOut, fWitLen, hdr] at lay' ⊢ <;> omega_arith
  have CH' : E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fRes, 4), (fUsed, 4), (fUsedOut, 8)] s.mem u.mem :=
    R.chg.mono fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
      rcases ho with h | h <;> simp only [h, true_or, or_true]
  have usedU : u.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v R.chg (by simp only [fUsed, hdr]; omega_arith) (fun o ho => by
      have lay' := lay
      simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;>
        simp only [sPP, ppWords, fUsed, fUsedOut, hdr] at lay' ⊢ <;> omega_arith), hU]
  refine WP.seq (st_ok hsU (by simp only [fRes, hdr]; omega_arith) fun x₁ M₁ => wp_cmpi fun x₂ F₂ _ z₂ => WP.block_nil ?_)
  have m₂' : x₂.mem = u.mem.writeW (off E.base fRes) (u.gpr .eax) := by rw [F₂.mem, M₁.mem]
  have g₂ : x₂.gpr = u.gpr := by rw [F₂.gpr, M₁.gpr]
  have hsX : Scr x₂ E.base E.size := Scr.of_eq hsU (by rw [g₂]) (by rw [g₂]) (by rw [F₂.wr, M₁.wr])
  have resX : x₂.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := by
    rw [m₂', Mem.readW_writeW_self32, uax]
  have usedX : x₂.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [m₂', word_store_other v _ (by simp only [fUsed, hdr]; omega_arith) (by simp only [fRes, hdr]; omega_arith)
      (by simp only [fUsed, fRes, hdr]; omega_arith), usedU]
  have CHX : E.Chg [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width bits)),
      (fRes, 4), (fUsed, 4), (fUsedOut, 8)] s.mem x₂.mem := by
    rw [m₂']; exact CH'.store (d := fRes) (n := 4) (.tail _ (.head _)) (by decide) _
  have post : ∀ y : State, y.gpr .edi = s.gpr .edi → y.gpr .esp = E.sp → y.gpr .esi = s.gpr .esi →
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
  have xrd : x₂.rd = s.rd := by rw [F₂.rd, M₁.rd, R.rd]
  have xwr : x₂.wr = s.wr := by rw [F₂.wr, M₁.wr, R.wr]
  have xsy : x₂.syms = s.syms := by rw [F₂.syms, M₁.syms, R.syms]
  cases res with
  | none =>
    refine WP.ite true (by change x₂.zf = _; rw [z₂, M₁.gpr, uax]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact post x₂ (by rw [g₂, R.edi]) (by rw [g₂, R.esp]) (by rw [g₂, R.esi]) xrd xwr xsy CHX resX usedX
  | some p =>
    obtain ⟨b, rest⟩ := p
    refine WP.ite false (by
        change x₂.zf = _; rw [z₂, M₁.gpr, uax]; cases b <;> simp [Proof.Dsa.ProbablePrime.status])
      (fun h => by cases h) (fun _ => ?_)
    have wl : E.witT.length = E.witLen := by rw [← B.wit]; simp [Spec.Rsa.bytesAt]
    have restLe : rest.length ≤ E.witLen - used := by
      have := (VG.Proof.Dsa.Generation.probablePrime_suffix hres).length_le
      simp only [List.length_drop, wl] at this; omega_arith
    have uo : x₂.mem.readW (off E.base fUsedOut) 32 = BitVec.ofNat 32 (E.witLen - used - rest.length) := by
      rw [m₂', word_store_other v _ (by simp only [fUsedOut, hdr]; omega_arith) (by simp only [fRes, hdr]; omega_arith)
        (by simp only [fUsedOut, fRes, hdr]; omega_arith), R.usedOut b rest hres]
    refine ld_ok hsX (by simp only [fUsedOut, hdr]; omega_arith) fun x₃ u₃ => addm_ok (Scr.of_eq hsX
      (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.wr) (by simp only [fUsed, hdr]; omega_arith) fun x₄ u₄ =>
        st_ok (Scr.of_eq hsX (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
          (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr]))
          (by simp only [fUsed, hdr]; omega_arith) fun x₅ M₅ => WP.block_nil ?_
    have val : x₅.mem = x₂.mem.writeW (off E.base fUsed)
        (BitVec.ofNat 32 (E.witLen - used - rest.length) + BitVec.ofNat 32 used) := by
      rw [M₅.mem, u₄.gpr, u₃.gpr, u₄.mem, u₃.mem, uo, usedX]
    have sum : BitVec.ofNat 32 (E.witLen - used - rest.length) + BitVec.ofNat 32 used =
        BitVec.ofNat 32 (E.witLen - rest.length) := by
      rw [← BitVec.ofNat_add]; congr 1; omega_arith
    rw [sum] at val
    have g₅ : ∀ r, r ≠ .eax → x₅.gpr r = u.gpr r := fun r h => by
      rw [M₅.gpr, u₄.other r h, u₃.other r h, g₂]
    refine post x₅ (by rw [g₅ _ (by decide), R.edi]) (by rw [g₅ _ (by decide), R.esp])
      (by rw [g₅ _ (by decide), R.esi]) (by rw [M₅.rd, u₄.rd, u₃.rd, xrd]) (by rw [M₅.wr, u₄.wr, u₃.wr, xwr])
      (by rw [M₅.syms, u₄.syms, u₃.syms, xsy]) ?_ ?_ ?_
    · rw [val]; exact CHX.store (d := fUsed) (n := 4) (.tail _ (.tail _ (.head _))) (by decide) _
    · rw [val, word_store_other v _ (by simp only [fRes, hdr]; omega_arith) (by simp only [fUsed, hdr]; omega_arith)
        (by simp only [fUsed, fRes, hdr]; omega_arith), resX]
    · rw [val, Mem.readW_writeW_self32]; rfl

end VG.Proof.Dsa.X86.Generation
