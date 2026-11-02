module

public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
import VerifiedGarbage.Proof.Framework.RelCTAssoc
/-! # A probable-prime test's call meets the test's contract -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Generation/TestArgs.lean`, which only this module imported.
section

/-! # The arguments of a probable-prime test

The working space at `sPP`, its 64-bit words, the witnesses left (from
`fUsed` on) and the word `fUsedOut` for the octets the test reads. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- The witnesses left: from `used` on, or the start of the tape once none
is left (so that the pointer stays within the tape). -/
def randPtr (W : BitVec 32) (witLen used : Nat) : BitVec 32 :=
  if witLen - used = 0 then W else W + BitVec.ofNat 32 used

/-- The registers a test's call pushes: `ws`, `ws_len`, `rand`, `rand_len`
and `used`, from the state words. -/
structure TestArgs (base : Addr) (W : BitVec 32) (witLen used : Nat) (s t : State) : Prop where
  eax : t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sPP
  ecx : t.gpr .ecx = BitVec.ofNat 32 ppWords
  edx : t.gpr .edx = randPtr W witLen used
  ebx : t.gpr .ebx = BitVec.ofNat 32 (witLen - used)
  ebp : t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 fUsedOut
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- After the test's first block: the cursor's pointer and the octets left,
and whether none are. -/
structure TestHead (base : Addr) (W : BitVec 32) (witLen used : Nat) (s t : State) : Prop where
  zf : t.zf = some (decide (witLen - used = 0))
  edx : t.gpr .edx = W + BitVec.ofNat 32 used
  ebx : t.gpr .ebx = BitVec.ofNat 32 (witLen - used)
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem testHead_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W)
    (hWL : s.mem.readW (off base fWitLen) 32 = BitVec.ofNat 32 witLen)
    (hU : s.mem.readW (off base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ witLen)
    (hwl : witLen < 2 ^ 32) :
    WP isa (.block [.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
        .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)]) s (TestHead base W witLen used s) := by
  have szs : fWitLen + 4 ≤ size ∧ fUsed + 4 ≤ size ∧ fWit + 4 ≤ size := by
    simp only [fWitLen, fUsed, fWit, hdr, sPP] at hsz ⊢; omega
  refine ld_ok hs (by omega) fun s₁ u₁ => ld_ok (Scr.of_eq hs (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.wr) (by omega) fun s₂ u₂ => wp_add fun s₃ u₃ _ => ?_
  have edi₃ : s₃.gpr .edi = s.gpr .edi := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine ld_ok (Scr.of_eq hs edi₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr])) (by omega) fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_
  have c₂ : s₂.gpr .ecx = BitVec.ofNat 32 used := by rw [u₂.other _ (by decide), u₁.gpr, hU]
  have d₂ : s₂.gpr .edx = W := by rw [u₂.gpr, u₁.mem, hW]
  have b₅ : s₅.gpr .ebx = BitVec.ofNat 32 (witLen - used) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), c₂, u₃.mem, u₂.mem, u₁.mem, hWL,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hu]
  refine ⟨?_, ?_, b₅, ?_, ?_, ?_, ?_, ?_⟩
  · rw [z₅, ← u₅.gpr, b₅, ofNat_beq_zero (by omega)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, d₂, c₂]
  · intro r a b c d e
    rw [u₅.other r b, u₄.other r b, u₃.other r d, u₂.other r d, u₁.other r c]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The cursor's pointer, the start of the tape if none are left, and the
other arguments. -/
theorem testMid_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W) {t : State}
    (H : TestHead base W witLen used s t) :
    WP isa (.seq (.ite .e (.block [.mov .edx (.mem (sc fWit))]) (.block []))
      (.block (scr .eax sPP ++ ([.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] : List Instr) ++ scr .ebp fUsedOut))) t
      (TestArgs base W witLen used s) := by
  have szs : fWit + 4 ≤ size := by simp only [fWit, hdr, sPP] at hsz ⊢; omega
  have edi₅ : t.gpr .edi = s.gpr .edi := H.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp₅ : t.gpr .esp = s.gpr .esp := H.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs₅ : Scr t base size := Scr.of_eq hs edi₅ sp₅ H.wr
  have tail : ∀ x : State, x.gpr .edi = s.gpr .edi → x.gpr .edx = randPtr W witLen used →
      x.gpr .ebx = BitVec.ofNat 32 (witLen - used) →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → x.gpr r = s.gpr r) →
      x.mem = s.mem → x.rd = s.rd → x.wr = s.wr → x.syms = s.syms →
      WP isa (.block (scr .eax sPP ++ ([.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] : List Instr) ++ scr .ebp fUsedOut)) x
        (TestArgs base W witLen used s) := by
    intro x xd xdx xbx xo xm xrd xwr xsy
    simp only [List.append_assoc]
    refine scr_ok fun s₆ e₆ g₆ m₆ rd₆ wr₆ sy₆ => wp_movi fun s₇ u₇ => scr_ok fun s₈ e₈ g₈ m₈ rd₈ wr₈ sy₈ => ?_
    refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g₈ _ (by decide), u₇.other _ (by decide), e₆, xd]
    · rw [g₈ _ (by decide), u₇.gpr]
    · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), xdx]
    · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), xbx]
    · rw [e₈, u₇.other _ (by decide), g₆ _ (by decide), xd]
    · intro r a b c d e
      rw [g₈ r e, u₇.other r c, g₆ r a, xo r a b c d e]
    · rw [m₈, u₇.mem, m₆, xm]
    · rw [rd₈, u₇.rd, rd₆, xrd]
    · rw [wr₈, u₇.wr, wr₆, xwr]
    · rw [sy₈, u₇.syms, sy₆, xsy]
  refine WP.seq (WP.ite (decide (witLen - used = 0)) H.zf (fun hz => ld_ok hs₅ (by omega) fun s₆ u₆ =>
    WP.block_nil (tail s₆ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)) (fun hz => WP.block_nil (tail t edi₅ ?_ H.ebx H.other H.mem H.rd
      H.wr H.syms)))
  · rw [u₆.other _ (by decide), edi₅]
  · have h0 : witLen - used = 0 := by simpa using hz
    rw [u₆.gpr, H.mem, hW]; simp only [randPtr, h0, ↓reduceIte]
  · rw [u₆.other _ (by decide), H.ebx]
  · intro r a b c d e; rw [u₆.other r d, H.other r a b c d e]
  · rw [u₆.mem, H.mem]
  · rw [u₆.rd, H.rd]
  · rw [u₆.wr, H.wr]
  · rw [u₆.syms, H.syms]
  · have h0 : ¬ witLen - used = 0 := by simpa using hz
    rw [H.edx]; simp only [randPtr, h0, ↓reduceIte]

theorem testArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W)
    (hWL : s.mem.readW (off base fWitLen) 32 = BitVec.ofNat 32 witLen)
    (hU : s.mem.readW (off base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ witLen)
    (hwl : witLen < 2 ^ 32) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, TestArgs base W witLen used s t → WP isa rest t Q) :
    WP isa (.seq (.block [.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
        .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)])
      (.seq (.ite .e (.block [.mov .edx (.mem (sc fWit))]) (.block []))
        (.seq (.block (scr .eax sPP ++ ([.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] : List Instr) ++ scr .ebp fUsedOut)) rest))) s
      Q :=
  WP.seq (WP.mono (testHead_ok hs hsz hW hWL hU hu hwl) fun _ H =>
    WP.assoc (WP.seq (WP.mono (testMid_ok hs hsz hW H) k)))

end VG.Proof.Dsa.X86.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The registers a test's call pushes, last argument first. -/
abbrev testRegs : List Reg := [.ebp, .ebx, .edx, .ecx, .eax]

/-- The test's contract, as `Generic/MillerRabin/X86/DsaProbablePrime.lean`
registers it. -/
abbrev ppContract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
    (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 152

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
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords) {k : Nat} (hk : k ≤ 200)
    {m m' : Mem} (F : Frame [below E.sp k] m m') :
    Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m' (off E.base sPP) =
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m (off E.base sPP) := by
  have sz := v.size_ge
  have low := v.low
  have lay' : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).candidate + bits / 8 ≤ ppWords * 8 := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega
  unfold Proof.Dsa.ProbablePrime.candidateAt
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
    (odd : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      (off E.base sPP) % 2 = 1)
    (len : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
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
  have fit : 4 * testRegs.length + 4 ≤ (s.gpr .esp).toNat := by rw [spU]; simp only [List.length_cons, List.length_nil]; omega_arith
  have hrs : Reg.esp ∉ testRegs := by decide
  have nat24 : (s.gpr .esp - 24#32).toNat = E.sp.toNat - 24 := by rw [spU]; exact sub_toNat (by omega_arith)
  have nat20 : ((s.gpr .esp - 20#32).setWidth 64).toNat = E.sp.toNat - 20 := by
    rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
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
  sig_pre [ppContract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  have hs := B.scr
  have sz := v.size_ge
  have witLt := v.ptrs.2.2.2
  have lenLt := v.lens.2.2
  have wsW := Scr.wide hs (d := sPP) (by simp only [sPP]; omega_arith)
  have uoW := Scr.wide hs (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  have wsN := Scr.toNat_add hs (d := sPP) (by simp only [sPP]; omega_arith)
  have uoN := Scr.toNat_add hs (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  have randW := randPtr_wide v (used := used) hu
  have randN := randPtr_toNat v (used := used) hu
  have randFit := randAddr_fit v (used := used) hu
  have randSub := randAddr_sub (E := E) (used := used) hu
  have lenN : (BitVec.ofNat 32 (E.witLen - used)).toNat = E.witLen - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have ppN : (BitVec.ofNat 32 ppWords).toNat = ppWords := by decide
  have callee : (s.gpr .esp - 24#32).setWidth 64 - 152#64 = (s.gpr .esp - 176#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [nat24]; omega_arith : 152 ≤ (s.gpr .esp - 24#32).toNat), BitVec.sub_sub]; rfl
  have sy₀ : s.syms = s₀.syms := A.syms
  have m₀ : s.mem = s₀.mem := A.mem
  simp only [a0, a1, a2, a3, a4, uesp, uarg0, urd, uwr, usy, testRd, testWr, wsW, uoW, randW, randN, lenN,
    ppN, wsN, uoN, callee, Abi.constRegions_cons, Abi.constRegions_nil, packed_len, List.length_cons,
    List.length_nil, List.drop, List.take, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]
  have symT : (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = E.table := by rw [sy₀]; exact B.syms
  have subWS : Region.Sub ⟨off E.base sPP, ppWords * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPP, ppWords]; omega_arith)
  have subUO : Region.Sub ⟨off E.base fUsedOut, 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [fUsedOut, hdr]; omega_arith)
  have subArgs : Region.Sub ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega_arith)
  have subRet : Region.Sub ⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 24) (by decide) (by omega_arith) (by decide))
  have subCal : Region.Sub ⟨(s.gpr .esp - 176#32).setWidth 64, 152⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 176) (by decide) (by omega_arith) (by decide))
  have subPush : Region.Sub (below (s.gpr .esp) (4 * testRegs.length + 4)) E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega_arith)
  have ss := v.scratchStack
  have wf := v.tapesFar E.witRegion (by simp)
  have ws := wf.1; have wk := wf.2.2
  have ts := v.tableFar.1; have tk := v.tableFar.2.2
  have nat136 : ((s.gpr .esp - 176#32).setWidth 64).toNat = E.sp.toNat - 176 := by
    rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
  have nat24' : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
    rw [BitVec.toNat_setWidth, nat24]; exact Nat.mod_eq_of_lt (by omega_arith)
  have retArgs : Region.Disjoint ⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat24', nat20]; omega_arith) (by simp only [nat20]; omega_arith)
  have calArgs : Region.Disjoint ⟨(s.gpr .esp - 176#32).setWidth 64, 152⟩ ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat136, nat20]; omega_arith) (by simp only [nat20]; omega_arith)
  have wsUO : Region.Disjoint ⟨off E.base sPP, ppWords * 8⟩ ⟨off E.base fUsedOut, 8⟩ :=
    Offset.disjoint E.base (by simp only [sPP, ppWords, fUsedOut, hdr]; omega_arith) (by simp only [sPP, ppWords]; omega_arith)
      (by simp only [fUsedOut, hdr]; omega_arith)
  have candEq : ∀ m : Mem, Frame [below (s.gpr .esp) (4 * testRegs.length + 4)] s.mem m →
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m (off E.base sPP) =
        Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP) :=
    fun m F => cand_frame v lay (k := 24) (by decide) (by simpa [spU] using F)
  refine ⟨by omega_arith, by omega_arith, by rw [symT]; rfl, ?_, ?_, fun t ht => by
    simp only [List.mem_singleton] at ht; subst ht; dsimp only; rw [symT]; exact v.tableAligned, trivial, by rw [Nat.mul_comm 8 ppWords],
    (ws.symm.sub_left subWS).sub_right randSub, wsUO, (ss.sub_left subWS).sub_right subArgs,
    (ws.sub_left randSub).sub_right subUO, (wk.sub_left randSub).sub_right subArgs,
    (ss.sub_left subUO).sub_right subArgs,
    (ss.symm.sub_left subRet).sub_right subWS, (wk.symm.sub_left subRet).sub_right randSub,
    (ss.symm.sub_left subRet).sub_right subUO, retArgs,
    (ss.symm.sub_left subCal).sub_right subWS, (wk.symm.sub_left subCal).sub_right randSub,
    (ss.symm.sub_left subCal).sub_right subUO, calArgs,
    by simp only [sPP, ppWords]; omega_arith, randFit, by simp only [fUsedOut, hdr]; omega_arith,
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
    refine Frame.readW umem (r := E.tableRegion) (Offset.contains_base E.table (by omega_arith) (by omega_arith)) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact tk.sub_right subPush
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    rw [symT]
    refine ⟨by omega_arith, ?_, tk.sub_right subRet, tk.sub_right subCal⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ts.sub_right (by rw [Nat.mul_comm]; exact subWS)
    · exact ts.sub_right subUO
    · exact tk.sub_right subArgs

end VG.Proof.Dsa.X86.Generation
