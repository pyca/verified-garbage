module

public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSum
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Rsa.KeyArrays
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! ### `Dsa.PPC64LE.Gen.Bytes`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.Frame`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.Base`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: the public parameters

`mkG s`: the public parameters of a call of `vg_dsa_parameter_search` from
`s`: its arguments, the state's first two words (the seeds left and the
modulus's width) and the tape's bytes, which the contract makes public, and
the address of the table of small primes the probable-prime tests read
(`kT`), which the contract's calling convention adds to the readable regions.
`CIn s`: the contract's precondition (`cin_of_pre`), for the functions we
call using at most `STK` bytes below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- The public parameters of a call. -/
structure GP where
  sp : Addr
  out : Addr
  outLen : Nat
  usedP : Addr
  /-- `rand`, which holds the seeds, the witnesses and the `h` candidates. -/
  wit : Addr
  witLen : Nat
  scr : Addr
  scrLen : Nat
  stP : Addr
  /-- The seeds left, `state[0]`. -/
  k0 : Nat
  pLen : Nat
  qLen : Nat
  witB : List Byte
  tab : Addr

/-- The modulus's width, `state[1]`. -/
abbrev pLenOf (s : State) : Nat := (s.mem.readW (s.gpr .r10 + 8) 64).toNat

def mkG (s : State) : GP where
  sp := s.sp
  out := s.gpr .r3
  outLen := (s.gpr .r4).toNat
  usedP := s.gpr .r5
  wit := s.gpr .r6
  witLen := (s.gpr .r7).toNat
  scr := s.gpr .r8
  scrLen := (s.gpr .r9).toNat
  stP := s.gpr .r10
  k0 := (s.mem.readW (s.gpr .r10) 64).toNat
  pLen := pLenOf s
  qLen := Spec.Dsa.generationQLen (pLenOf s)
  witB := Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
  tab := s.syms Impl.RsaKeyGen.TrialTable32.symbol

/-- The table of small primes the probable-prime tests read. -/
abbrev kT : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

namespace GP
variable (G : GP)

/-- The seeds are read from `rand`. -/
abbrev seeds : Addr := G.wit
abbrev seedsLen : Nat := G.witLen
abbrev seedsB : List Byte := G.witB

abbrev rScr : Region := ⟨G.scr, G.scrLen * 8⟩
abbrev rOut : Region := ⟨G.out, G.outLen⟩
abbrev rUsed : Region := ⟨G.usedP, 8⟩
abbrev rWit : Region := ⟨G.wit, G.witLen⟩
abbrev rSeeds : Region := G.rWit
abbrev rSt : Region := ⟨G.stP, 32⟩
abbrev rTab : Region := ⟨G.tab, 8192⟩

end GP

/-- The stack below the stack pointer the functions we call use. -/
abbrev rBelow (σ : State) (STK : Nat) : Region := ⟨σ.sp - BitVec.ofNat 64 STK, STK⟩

/-- The precondition under `abi`, for `STK` bytes of stack. -/
structure CIn0 (STK : Nat) (s : State) : Prop where
  spLo : STK ≤ s.sp.toNat
  rd : s.rd = [(mkG s).rWit]
  wr : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt]
  oU : (mkG s).rOut.Disjoint (mkG s).rUsed
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oS : (mkG s).rOut.Disjoint (mkG s).rSt
  uW : (mkG s).rUsed.Disjoint (mkG s).rWit
  uC : (mkG s).rUsed.Disjoint (mkG s).rScr
  uS : (mkG s).rUsed.Disjoint (mkG s).rSt
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  wS : (mkG s).rWit.Disjoint (mkG s).rSt
  cS : (mkG s).rScr.Disjoint (mkG s).rSt
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bU : (rBelow s STK).Disjoint (mkG s).rUsed
  bW : (rBelow s STK).Disjoint (mkG s).rWit
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bS : (rBelow s STK).Disjoint (mkG s).rSt
  nO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  nU : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  nW : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  nC : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  nS : (s.gpr .r10).toNat + 32 ≤ 2 ^ 64
  valid : Spec.Dsa.generationPLenValid (pLenOf s)
  outLen : (s.gpr .r4).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  scrLen : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (s.gpr .r9).toNat
  seeds : (s.mem.readW (s.gpr .r10) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (s.gpr .r10 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (s.gpr .r7).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)

theorem cin0_of_pre {n : Nat} (s : State) (h : (Spec.Dsa.parameterSearchContract abi (n + 1)).pre s) :
    CIn0 (n + 1) s := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackBelow] at h
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackBelow] at h
  sig_split h
  constructor
  all_goals try dsimp only [mkG, GP.rOut, GP.rUsed, GP.rWit, GP.rScr, GP.rSt, pLenOf]
  all_goals with_reducible assumption

/-- The contract's precondition, for `STK` bytes of stack. -/
structure CIn (STK : Nat) (s : State) : Prop where
  spLo : STK ≤ s.sp.toNat
  rd : s.rd = [(mkG s).rWit, (mkG s).rTab]
  wr : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt]
  oU : (mkG s).rOut.Disjoint (mkG s).rUsed
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oS : (mkG s).rOut.Disjoint (mkG s).rSt
  uW : (mkG s).rUsed.Disjoint (mkG s).rWit
  uC : (mkG s).rUsed.Disjoint (mkG s).rScr
  uS : (mkG s).rUsed.Disjoint (mkG s).rSt
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  wS : (mkG s).rWit.Disjoint (mkG s).rSt
  cS : (mkG s).rScr.Disjoint (mkG s).rSt
  bO : (rBelow s STK).Disjoint (mkG s).rOut
  bU : (rBelow s STK).Disjoint (mkG s).rUsed
  bW : (rBelow s STK).Disjoint (mkG s).rWit
  bC : (rBelow s STK).Disjoint (mkG s).rScr
  bS : (rBelow s STK).Disjoint (mkG s).rSt
  nO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  nU : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  nW : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  nC : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  nS : (s.gpr .r10).toNat + 32 ≤ 2 ^ 64
  valid : Spec.Dsa.generationPLenValid (pLenOf s)
  outLen : (s.gpr .r4).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  scrLen : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (s.gpr .r9).toNat
  seeds : (s.mem.readW (s.gpr .r10) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (s.gpr .r10 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (s.gpr .r7).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)
  held : Abi.constsHeld s.mem (fun name => s.syms name) kT
  tFit : (mkG s).tab.toNat + 8192 ≤ 2 ^ 64
  tO : (mkG s).rTab.Disjoint (mkG s).rOut
  tU : (mkG s).rTab.Disjoint (mkG s).rUsed
  tC : (mkG s).rTab.Disjoint (mkG s).rScr
  tS : (mkG s).rTab.Disjoint (mkG s).rSt
  tB : (mkG s).rTab.Disjoint (rBelow s STK)
  tAl : (mkG s).tab.toNat % 64 = 0

/-- The table's regions under `abi.withConsts kT`. -/
theorem constRegs_kT (s : State) : constRegs kT s = [(mkG s).rTab] := by
  simp only [constRegs, kT, Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.TrialTable32.packed_length]
  rfl

theorem cin_of_pre {n : Nat} (s : State)
    (h : (Spec.Dsa.parameterSearchContract (abi.withConsts kT) (n + 1)).pre s) : CIn (n + 1) s := by
  obtain ⟨h₀, hk⟩ := (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := []) (sig := Spec.Dsa.parameterSearchSig)).mp h
  have c := cin0_of_pre (stripConsts kT s) h₀
  obtain ⟨hd, held, ht, hal⟩ := hk
  have e : constRegs [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] s = _ :=
    constRegs_kT s
  rw [e] at ht hd hal
  obtain ⟨tFit, tW, tR⟩ := ht _ (List.mem_cons_self (l := []))
  have hrd : s.rd = (stripConsts kT s).rd ++
      s.rd.drop (s.rd.length - [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)].length) :=
    (List.take_append_drop _ _).symm
  rw [hd, c.rd] at hrd
  have hw : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt] := c.wr
  exact ⟨c.spLo, hrd, hw, c.oU, c.oW, c.oC, c.oS, c.uW, c.uC, c.uS, c.wC, c.wS, c.cS, c.bO, c.bU, c.bW, c.bC, c.bS, c.nO, c.nU, c.nW, c.nC, c.nS, c.valid, c.outLen, c.scrLen, c.seeds, c.budget, c.randLen, held, tFit,
    tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp), tW _ (by rw [hw]; simp),
    tR _ (by simp [abi, stackBelow]), hal _ (List.mem_cons_self (l := []))⟩

theorem CIn.lens {STK : Nat} {s : State} (h : CIn STK s) :
    ((mkG s).pLen = 128 ∧ (mkG s).qLen = 20) ∨ ((mkG s).pLen = 256 ∧ (mkG s).qLen = 32) ∨
      ((mkG s).pLen = 384 ∧ (mkG s).qLen = 32) := by
  have := h.valid
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  simp only [mkG, Spec.Dsa.generationQLen]
  rcases this with (e | e) | e <;> simp [e]

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: a state of the search

`GI G STK σ V LS s`: a state of the search for the call from `σ` (with the
parameters `G`, and `STK` bytes of stack for the functions we call): `r28`
holds `scratch`, whose header holds our caller's registers, our return
address, the fixed words (`fixedWords`) and the words of `LS` holding `V`;
the regions are the call's, and memory changed only in `scratch` and the
stack below the stack pointer. Loads of header words (`GI.ldV`), stores into
its variable words (`GI.stF`), and steps that keep a search state: those that
change registers alone (`GI.of_keep`) or memory in `scratch` past the header
(`GI.of_scr`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- The header's end: the state, then the saved registers. -/
def hEnd : Nat := fSave + 8 * 19

/-- The header word at `o`. -/
abbrev fw (m : Mem) (G : GP) (o : Nat) : BitVec 64 := m.readW (G.scr + BitVec.ofNat 64 o) 64

/-- The fixed header words: `out`, `rand`, `used` and `state`. -/
def fixedWords (G : GP) : List (Nat × BitVec 64) :=
  [(fOut, G.out), (fWit, G.wit), (fWitLen, BitVec.ofNat 64 G.witLen), (fUsedP, G.usedP), (fStP, G.stP)]

/-- A variable header word: before the saved registers, apart from the return
address and the fixed words. -/
abbrev VarOk (G : GP) (o : Nat) : Prop := o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fLR ∧ ∀ p ∈ fixedWords G, o ≠ p.1

/-- `V` with the word at `o` := `v`. -/
def upd (V : Nat → BitVec 64) (o : Nat) (v : BitVec 64) : Nat → BitVec 64 := fun o' => if o' = o then v else V o'

@[simp] theorem upd_self (V : Nat → BitVec 64) (o : Nat) (v : BitVec 64) : upd V o v o = v := by simp [upd]
theorem upd_ne (V : Nat → BitVec 64) {o o' : Nat} (v : BitVec 64) (h : o' ≠ o) : upd V o v o' = V o' := by
  simp [upd, h]

/-- A state of the search. -/
structure GI (G : GP) (STK : Nat) (σ : State) (V : Nat → BitVec 64) (LS : List Nat) (s : State) : Prop where
  pre : CIn STK σ
  hG : mkG σ = G
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  r28 : s.gpr .r28 = G.scr
  saved : ∀ i < 19, fw s.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .r14)
  lr : fw s.mem G fLR = σ.lr
  fixed : ∀ p ∈ fixedWords G, fw s.mem G p.1 = p.2
  slots : ∀ o ∈ LS, fw s.mem G o = V o
  ls : ∀ o ∈ LS, VarOk G o
  frame : Frame [G.rScr, rBelow σ STK] σ.mem s.mem

/-- A run keeps the stack pointer. -/
theorem WP.sp_eq {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s fun t => t.sp = s.sp → Q t) :
    WP isa c s Q := by
  obtain ⟨tr, s', he, hq⟩ := h; exact ⟨tr, s', he, hq (Exec.sp he)⟩

/-- `std t, off(n)`, with the stack pointer and the link register kept. -/
theorem wp_std' {s : State} {is : List Instr} {Q : State → Prop} {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → s'.sp = s.sp → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.scrFit (h : GI G STK σ V LS s) : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by
  have := h.pre.nC; rw [← h.hG]; exact this

theorem GI.lens (h : GI G STK σ V LS s) :
    (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32) := by
  rw [← h.hG]; exact h.pre.lens

/-- `scratch`'s size. -/
theorem GI.scrBig (h : GI G STK σ V LS s) : 8 * (64 * G.pLen + 1024) ≤ G.scrLen * 8 := by
  have := h.pre.scrLen
  have e1 : pLenOf σ = G.pLen := by rw [← h.hG]; rfl
  have e2 : (σ.gpr .r9).toNat = G.scrLen := by rw [← h.hG]; rfl
  rw [e1, e2] at this
  simp only [Spec.Dsa.generationScratchWords] at this
  omega_using [this]

/-- Byte `o` of `scratch`. -/
abbrev GP.sa (G : GP) (o : Nat) : Addr := G.scr + BitVec.ofNat 64 o
/-- The `n` bytes at byte `o` of `scratch`. -/
abbrev GP.rs (G : GP) (o n : Nat) : Region := ⟨G.sa o, n⟩

/-- A range of `scratch` is writable. -/
theorem sw (G : GP) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) : Region.Sub (G.rs o n) G.rScr :=
  Offset.sub_base _ ho

theorem GI.inScr (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n := by decide) :
    InRegions s.wr (G.sa o) n := by
  have := h.scrFit
  refine ⟨G.rScr, ?_, Offset.contains_base _ ho (by omega_using [ho, hn, this])⟩
  rw [h.wr, h.pre.wr, h.hG]; simp

theorem GI.inRdWr (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n := by decide) :
    InRegions (s.rd ++ s.wr) (G.sa o) n := by
  obtain ⟨r, hr, hc⟩ := h.inScr ho hn
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Ranges of `scratch` apart by their offsets are disjoint. -/
theorem GI.sdisj (h : GI G STK σ V LS s) {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o)
    (h1 : o + n ≤ G.scrLen * 8) (h2 : o' + n' ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint (G.rs o' n') := by
  have := h.scrFit
  exact Offset.disjoint _ hs (by omega_using [h1, this]) (by omega_using [h2, this])

/-- `scratch` is apart from the stack below the stack pointer. -/
theorem GI.scr_below (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint (rBelow σ STK) := by
  have := h.pre.bC; rw [h.hG] at this
  exact this.symm.sub_left (sw G ho)

theorem GI.hEnd_le (h : GI G STK σ V LS s) : hEnd ≤ G.scrLen * 8 := by
  have := h.scrBig; simp only [hEnd, fSave]; omega_using [this]

/-- A header word's value. -/
theorem GI.fixedV (h : GI G STK σ V LS s) {o : Nat} {v : BitVec 64} (hp : (o, v) ∈ fixedWords G) :
    fw s.mem G o = v := h.fixed (o, v) hp

theorem GI.slotV (h : GI G STK σ V LS s) {o : Nat} (ho : o ∈ LS) : fw s.mem G o = V o := h.slots o ho

/-- A state of the search through a step that changes registers other than
`r28` alone. -/
theorem GI.of_keep {t : State} {ws : List Reg} (h : GI G STK σ V LS s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h28 : .r28 ∉ ws := by decide) : GI G STK σ V LS t :=
  ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h28).trans h.r28,
    by rw [m]; exact h.saved, by rw [m]; exact h.lr, by rw [m]; exact h.fixed, by rw [m]; exact h.slots,
    h.ls, by rw [m]; exact h.frame⟩

theorem GI.of_upd {t : State} {r : Reg} {v : BitVec 64} (h : GI G STK σ V LS s) (u : Upd s t r v)
    (sp : t.sp = s.sp) (h28 : r ≠ .r28) : GI G STK σ V LS t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem sp
    (by simpa using h28.symm)

/-- A header word keeps its value through writes outside the header. -/
theorem fw_frame {G : GP} {m m' : Mem} {rs : List Region} (f : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, (G.rs o 8).Disjoint r) : fw m' G o = fw m G o :=
  f.readW (r := G.rs o 8) (Region.contains_self _ _) hd (by decide)

theorem fixed_ok (G : GP) : ∀ p ∈ fixedWords G, p.1 + 8 ≤ fSave ∧ p.1 % 8 = 0 := by
  intro p hp
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

/-- A state of the search through a step that writes `scratch` past the
header and the stack below the stack pointer. -/
theorem GI.of_scr {t : State} {ws : List Reg} (h : GI G STK σ V LS s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {o n : Nat} (ho : hEnd ≤ o) (hon : o + n ≤ G.scrLen * 8)
    (f : Frame [G.rs o n, rBelow σ STK] s.mem t.mem) (h28 : .r28 ∉ ws := by decide) : GI G STK σ V LS t := by
  have big := h.hEnd_le
  have hd : ∀ p, p + 8 ≤ hEnd → ∀ r ∈ [G.rs o n, rBelow σ STK], (G.rs p 8).Disjoint r := fun p hp r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.sdisj (.inl (by omega_using [ho, hp])) (by omega_using [big, hp]) hon
    · exact h.scr_below (by omega_using [big, hp])
  refine ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h28).trans h.r28,
    fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, h.ls, h.frame.trans (f.sub fun x hx => ?_)⟩
  · rw [fw_frame f (hd _ (by simp only [hEnd]; omega_using [hi]))]; exact h.saved i hi
  · rw [fw_frame f (hd _ (by decide))]; exact h.lr
  · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega_using [this]))]; exact h.fixed p hp
  · rw [fw_frame f (hd _ (by have := (h.ls p hp).1; simp only [hEnd]; omega_using [this]))]; exact h.slots p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨G.rScr, List.mem_cons_self, sw G hon⟩
    · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩

/-- `std r, o(r28)` of a variable header word. -/
theorem GI.stF (h : GI G STK σ V LS s) {o : Nat} (hv : VarOk G o) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, GI G STK σ (upd V o (s.gpr r)) (o :: LS) t → Mupd s t (s.mem.writeW (G.sa o) (s.gpr r)) →
      t.lr = s.lr → WP isa (.block rest) t Q) :
    WP isa (.block (st r o :: rest)) s Q := by
  obtain ⟨oS, o8, oLR, ofix⟩ := hv
  have big := h.hEnd_le
  have fit := h.scrFit
  refine wp_std' (by decide) ⟨by simp only [fSave] at oS; omega_using [oS], by omega_using [o8]⟩ (by rw [h.r28])
    (h.inScr (by simp only [hEnd] at big; omega_using [oS, big])) fun t m tsp tlr => k t ?_ m tlr
  have mt : t.mem = s.mem.writeW (G.sa o) (s.gpr r) := m.mem
  have sep : ∀ {p : Nat}, p % 8 = 0 → p ≠ o → p + 8 ≤ hEnd → fw t.mem G p = fw s.mem G p := fun hp hne hpE => by
    show t.mem.readW _ 64 = s.mem.readW _ 64
    rw [mt]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [o8, hp, hne]) (by simp only [hEnd] at *; omega_using [big, fit, hpE])
      (by simp only [hEnd, fSave] at *; omega_using [oS])) (by decide)
  refine ⟨h.pre, h.hG, by rw [tsp, h.sp], by rw [m.rd, h.rd], by rw [m.wr, h.wr],
    by rw [m.gpr, h.r28], fun i hi => ?_, ?_, fun p hp => ?_, fun o' ho' => ?_, fun o' ho' => ?_, ?_⟩
  · rw [sep (by simp only [fSave]; omega_using []) (by simp only [fSave] at *; omega_using [oS]) (by simp only [hEnd]; omega_using [hi])]
    exact h.saved i hi
  · rw [sep (by decide) (Ne.symm oLR) (by decide)]; exact h.lr
  · obtain ⟨b1, b2⟩ := fixed_ok G p hp
    exact (sep b2 (fun e => ofix p hp e.symm) (by simp only [hEnd]; omega_using [b1])).trans (h.fixed p hp)
  · by_cases he : o' = o
    · subst he; show t.mem.readW _ 64 = _; rw [mt, Mem.readW_writeW_self64, upd_self]
    · have ho'' := (List.mem_cons.mp ho').resolve_left he
      obtain ⟨l1, l2, _, _⟩ := h.ls o' ho''
      rw [sep l2 he (by simp only [hEnd]; omega_using [l1]), upd_ne _ _ he]; exact h.slots o' ho''
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ⟨oS, o8, oLR, ofix⟩
    · exact h.ls o' ho'
  · rw [mt]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by simp only [hEnd] at big; omega_using [oS, big])
      (by simp only [fSave] at oS; omega_using [oS]))

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.Pieces`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.St`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on PPC64LE: a state of the search with its data

`SS G STK σ c s`: a state of the search (`GI`), with the bytes the claims
`c.cl` of `scratch` hold (past the header, apart from the key working
space), and the arrays and header words of the key working space (at
`kB p_len`) that `c` lists. The key working space's registers are not kept:
the power, in the P space, uses them; each phase of arithmetic sets them
(`ksRegs`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Rsa.KeyWorkspace
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Mont (w32 val32 val32_congr)

/-- Claims on `scratch`: the bytes at an offset. -/
abbrev Claims := List (Nat × List Byte)

/-- The key working space's bytes. -/
def kz (pLen : Nat) : Nat := hdr + nArrs * S (pLen / 4)

namespace GP
variable (G : GP)

/-- The key working space. -/
abbrev KB : Addr := G.sa (kB G.pLen)
abbrev w : Nat := G.pLen / 4
abbrev rK : Region := ⟨G.KB, kz G.pLen⟩

end GP

/-- The claims hold. -/
def SB (G : GP) (m : Mem) (cl : Claims) : Prop :=
  ∀ x ∈ cl, Spec.Rsa.bytesAt m (G.sa x.1) x.2.length = x.2

/-- What a stage keeps: header words, claims, arrays and key header words. -/
structure Cfg where
  V : Nat → BitVec 64 := fun _ => 0
  LS : List Nat := []
  cl : Claims := []
  A : Nat → Nat := fun _ => 0
  live : List Nat := []
  KV : Nat → Nat := fun _ => 0
  kls : List Nat := []

/-- A key header word a stage keeps. -/
abbrev KlsOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ d % 4 = 0

/-- A claim's place: past the header, apart from the key working space,
within `scratch`. -/
abbrev ClOk (G : GP) (x : Nat × List Byte) : Prop :=
  hEnd ≤ x.1 ∧ (x.1 + x.2.length ≤ kB G.pLen ∨ wB G.pLen ≤ x.1) ∧ x.1 + x.2.length ≤ G.scrLen * 8

structure SS (G : GP) (STK : Nat) (σ : State) (c : Cfg) (s : State) : Prop where
  gi : GI G STK σ c.V c.LS s
  sb : SB G s.mem c.cl
  clOk : ∀ x ∈ c.cl, ClOk G x
  arrs : Arrs s.mem G.KB G.w c.A c.live
  liveOk : ∀ j ∈ c.live, j < nArrs
  ksl : ∀ d ∈ c.kls, slot s.mem G.KB d = c.KV d
  kslOk : ∀ d ∈ c.kls, KlsOk d

/-! ## Sizes -/

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.lens3 (h : GI G STK σ V LS s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by
  rcases h.lens with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> simp [e]

/-- `scratch` holds the working space of the functions we call and everything
below it. -/
theorem GI.wBig (h : GI G STK σ V LS s) : wB G.pLen + 8 * wWords G.pLen ≤ G.scrLen * 8 := by
  have := h.scrBig
  rcases h.lens3 with e | e | e <;> rw [e] at this ⊢
  · have : wB 128 + 8 * wWords 128 ≤ 8 * (64 * 128 + 1024) := by decide
    omega_arith
  · have : wB 256 + 8 * wWords 256 ≤ 8 * (64 * 256 + 1024) := by decide
    omega_arith
  · have : wB 384 + 8 * wWords 384 ≤ 8 * (64 * 384 + 1024) := by decide
    omega_arith

theorem GI.kBig (h : GI G STK σ V LS s) : kB G.pLen + kz G.pLen ≤ wB G.pLen := by
  rcases h.lens3 with e | e | e <;> rw [e] <;> decide

theorem GI.kSub (h : GI G STK σ V LS s) : Region.Sub G.rK G.rScr :=
  sw G (by have := h.wBig; have := h.kBig; omega_arith)

/-- The key working space is apart from the ranges of `scratch` apart from it. -/
theorem GI.kdisj (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ kB G.pLen ∨ wB G.pLen ≤ o)
    (hon : o + n ≤ G.scrLen * 8) : G.rK.Disjoint (G.rs o n) := by
  have := h.wBig; have := h.kBig
  exact h.sdisj (by omega_using [ho, this]) (by omega_arith) hon

end

/-! ## Claims -/

theorem SB.frame {G : GP} {m m' : Mem} {cl : Claims} {rs : List Region} (h : SB G m cl) (f : Frame rs m m')
    (hd : ∀ x ∈ cl, ∀ r ∈ rs, (G.rs x.1 x.2.length).Disjoint r) (hl : ∀ x ∈ cl, x.2.length ≤ 2 ^ 64) :
    SB G m' cl := fun x hx => by
  rw [VG.Proof.Dsa.Generation.frame_bytesAt f (hd x hx) (hl x hx)]; exact h x hx

theorem SB.sub {G : GP} {m : Mem} {cl cl' : Claims} (h : SB G m cl) (hs : ∀ x ∈ cl', x ∈ cl) : SB G m cl' :=
  fun x hx => h x (hs x hx)

theorem SB.cons {G : GP} {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {bs : List Byte}
    (e : Spec.Rsa.bytesAt m (G.sa o) bs.length = bs) : SB G m ((o, bs) :: cl) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact e
  · exact h x hx

/-- A claim apart from the range `[o, o + n)`. -/
abbrev Apart (o n : Nat) (x : Nat × List Byte) : Prop := x.1 + x.2.length ≤ o ∨ o + n ≤ x.1

/-! ## The key working space through other steps -/

theorem w32_frame {B : Addr} {Z : Nat} {m m' : Mem} {rs : List Region} (f : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨B, Z⟩ : Region).Disjoint r) (hZ : Z ≤ 2 ^ 64) {d : Nat} (h : d + 4 ≤ Z) :
    w32 m' B d = w32 m B d := by
  simp only [w32]
  rw [f.readW (r := ⟨B, Z⟩) (Offset.contains_base _ h (by omega_using [hZ, h])) hd (by decide)]

theorem kz_eq {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : kz L ≤ 2 ^ 64 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- The arrays fit the key working space. -/
theorem arrs_fit {L j : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) (hj : j < nArrs) :
    arr (L / 4) j + 4 * (L / 4 + 2) ≤ kz L := by
  have := arr_end (w := L / 4) hj
  simp only [arr, S, hdr, nArrs, kz] at *
  rcases hL with rfl | rfl | rfl <;> omega_using [hj]

theorem num_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < nArrs) : num m' B (L / 4) j = num m B (L / 4) j := by
  have := arrs_fit hL hj
  exact val32_congr fun i hi => w32_frame f hd (kz_eq hL) (by omega_using [this, hi])

theorem slot_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {d : Nat} (hdk : KlsOk d) : slot m' B d = slot m B d :=
  w32_frame f hd (kz_eq hL) (by obtain ⟨h1, _⟩ := hdk; simp only [kz, hdr] at h1 ⊢; omega_using [h1])

/-! ## Steps that keep a state of the search -/

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s t : State}

theorem SS.lens (h : SS G STK σ c s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := h.gi.lens3

/-- Registers other than `r28` alone change. -/
theorem SS.of_keep {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h28 : .r28 ∉ ws := by decide) : SS G STK σ c t :=
  ⟨h.gi.of_keep r m sp h28, m ▸ h.sb, h.clOk, m ▸ h.arrs, h.liveOk, m ▸ h.ksl, h.kslOk⟩

theorem SS.of_upd {r : Reg} {v : BitVec 64} (h : SS G STK σ c s) (u : Upd s t r v)
    (sp : t.sp = s.sp) (h28 : r ≠ .r28) : SS G STK σ c t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem sp
    (by simpa using h28.symm)

/-- Fewer header words, claims, arrays or key header words. -/
theorem SS.mono (h : SS G STK σ c s) {c' : Cfg} (hV : ∀ o ∈ c'.LS, o ∈ c.LS ∧ c.V o = c'.V o)
    (hcl : ∀ x ∈ c'.cl, x ∈ c.cl) (hA : ∀ j ∈ c'.live, j ∈ c.live ∧ c.A j = c'.A j)
    (hK : ∀ d ∈ c'.kls, d ∈ c.kls ∧ c.KV d = c'.KV d) : SS G STK σ c' s := by
  obtain ⟨gi, sb, clOk, arrs, liveOk, ksl, kslOk⟩ := h
  refine ⟨⟨gi.pre, gi.hG, gi.sp, gi.rd, gi.wr, gi.r28, gi.saved, gi.lr, gi.fixed, fun o ho => ?_,
    fun o ho => gi.ls o (hV o ho).1, gi.frame⟩, sb.sub hcl, fun x hx => clOk x (hcl x hx), fun j hj => ?_,
    fun j hj => liveOk j (hA j hj).1, fun d hd => ?_, fun d hd => kslOk d (hK d hd).1⟩
  · rw [← (hV o ho).2]; exact gi.slots o (hV o ho).1
  · rw [← (hA j hj).2]; exact arrs j (hA j hj).1
  · rw [← (hK d hd).2]; exact ksl d (hK d hd).1

/-- The ranges `(o, n)` of `scratch`. -/
abbrev GP.rss (G : GP) (os : List (Nat × Nat)) : List Region := os.map fun p => G.rs p.1 p.2

/-- A step that writes the ranges `os` of `scratch`, past the header and
apart from the key working space, and the stack below the stack pointer: the
claims `cl'`, each kept and apart from the ranges, or holding. -/
theorem SS.of_scrs {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {os : List (Nat × Nat)} (hon : ∀ p ∈ os, ClOk G (p.1, List.replicate p.2 0))
    (f : Frame (G.rss os ++ [rBelow σ STK]) s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', (x ∈ c.cl ∧ ∀ p ∈ os, Apart p.1 p.2 x) ∨
      (Spec.Rsa.bytesAt t.mem (G.sa x.1) x.2.length = x.2 ∧ ClOk G x))
    (h28 : .r28 ∉ ws := by decide) : SS G STK σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hon' : ∀ p ∈ os, hEnd ≤ p.1 ∧ (p.1 + p.2 ≤ kB G.pLen ∨ wB G.pLen ≤ p.1) ∧ p.1 + p.2 ≤ G.scrLen * 8 :=
    fun p hp => by have := hon p hp; simp only [ClOk, List.length_replicate] at this; exact this
  have mem : ∀ r' ∈ G.rss os ++ [rBelow σ STK], (∃ p ∈ os, r' = G.rs p.1 p.2) ∨ r' = rBelow σ STK :=
    fun r' hr' => by
      simp only [GP.rss, List.mem_append, List.mem_map, List.mem_singleton] at hr'
      rcases hr' with ⟨p, hp, rfl⟩ | rfl
      · exact .inl ⟨p, hp, rfl⟩
      · exact .inr rfl
  have kd : ∀ r' ∈ G.rss os ++ [rBelow σ STK], (⟨G.KB, kz G.pLen⟩ : Region).Disjoint r' := fun r' hr' => by
    rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
    · obtain ⟨_, a, b⟩ := hon' p hp; exact gi.kdisj a b
    · exact gi.scr_below (by omega_using [big, kb])
  -- The header: a step past it.
  have gi' : GI G STK σ c.V c.LS t := by
    have hd : ∀ q, q + 8 ≤ hEnd → ∀ r' ∈ G.rss os ++ [rBelow σ STK], (G.rs q 8).Disjoint r' := fun q hq r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega_using [hq, a])) (by omega_using [hE, hq]) b
      · exact gi.scr_below (by omega_using [hE, hq])
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h28).trans gi.r28,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega_using [hi]))]; exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide))]; exact gi.lr
    · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega_using [this]))]; exact gi.fixed p hp
    · rw [fw_frame f (hd _ (by have := (gi.ls p hp).1; simp only [hEnd]; omega_using [this]))]; exact gi.slots p hp
    · rcases mem x hx with ⟨p, hp, rfl⟩ | rfl
      · exact ⟨G.rScr, List.mem_cons_self, sw G (hon' p hp).2.2⟩
      · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩
  refine ⟨gi', fun x hx => ?_, fun x hx => ?_, fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · rcases hcl x hx with ⟨hm, ha⟩ | ⟨e, _⟩
    · obtain ⟨_, _, xb⟩ := h.clOk x hm
      rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
        rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
        · exact gi.sdisj (ha p hp) xb (hon' p hp).2.2
        · exact gi.scr_below xb) (by omega_using [fit, xb])]
      exact h.sb x hm
    · exact e
  · rcases hcl x hx with ⟨hm, _⟩ | ⟨_, b⟩
    · exact h.clOk x hm
    · exact b
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- The volatile registers, which a call may change. -/
abbrev volatile : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem keep_of_preserved {s t : State} (g : ∀ r ∈ preserved, t.gpr r = s.gpr r) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : Keep volatile s t :=
  ⟨fun r hr => g r (by revert hr; cases r <;> decide), rd, wr⟩

/-- A step that writes the ranges `os` of `scratch` (past the header, apart
from the key working space), the header words `hw` (variable, not among
`LS`) and the stack below the stack pointer: the claims `cl'`, each kept and
apart from the ranges, or holding. -/
theorem SS.of_hdrScrs {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {os : List (Nat × Nat)} (hon : ∀ p ∈ os, ClOk G (p.1, List.replicate p.2 0)) {hw : List Nat}
    (hhw : ∀ o ∈ hw, VarOk G o ∧ ∀ o' ∈ c.LS, o + 8 ≤ o' ∨ o' + 8 ≤ o)
    (f : Frame (G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK]) s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ p ∈ os, Apart p.1 p.2 x)
    (h28 : .r28 ∉ ws := by decide) : SS G STK σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hon' : ∀ p ∈ os, hEnd ≤ p.1 ∧ (p.1 + p.2 ≤ kB G.pLen ∨ wB G.pLen ≤ p.1) ∧ p.1 + p.2 ≤ G.scrLen * 8 :=
    fun p hp => by have := hon p hp; simp only [ClOk, List.length_replicate] at this; exact this
  have hw' : ∀ o ∈ hw, o + 8 ≤ fSave := fun o ho => (hhw o ho).1.1
  have mem : ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK],
      (∃ p ∈ os, r' = G.rs p.1 p.2) ∨ (∃ o ∈ hw, r' = G.rs o 8) ∨ r' = rBelow σ STK := fun r' hr' => by
    simp only [GP.rss, List.mem_append, List.mem_map, List.mem_singleton] at hr'
    rcases hr' with (⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩) | rfl
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr (.inl ⟨o, ho, rfl⟩)
    · exact .inr (.inr rfl)
  have kd : ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK],
      (⟨G.KB, kz G.pLen⟩ : Region).Disjoint r' := fun r' hr' => by
    rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
    · obtain ⟨_, a, b⟩ := hon' p hp; exact gi.kdisj a b
    · have := hw' o ho
      exact gi.kdisj (.inl (by simp only [kB, pB, fSave] at this ⊢; omega_using [this])) (by simp only [hEnd] at hE; omega_using [hE, this])
    · exact gi.scr_below (by omega_using [big, kb])
  -- The header word at `q`, apart from those written.
  have hd : ∀ q, q + 8 ≤ hEnd → (∀ o ∈ hw, o + 8 ≤ q ∨ q + 8 ≤ o) →
      ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK], (G.rs q 8).Disjoint r' :=
    fun q hq hq' r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega_using [hq, a])) (by omega_using [hE, hq]) b
      · have := hw' o ho
        exact gi.sdisj (hq' o ho).symm (by omega_using [hE, hq]) (by simp only [hEnd] at hE; omega_using [hE, this])
      · exact gi.scr_below (by omega_using [hE, hq])
  have fixedFar : ∀ p ∈ fixedWords G, ∀ o ∈ hw, o + 8 ≤ p.1 ∨ p.1 + 8 ≤ o := fun p hp o ho => by
    obtain ⟨_, a8, _, af⟩ := (hhw o ho).1
    obtain ⟨b, b8⟩ := fixed_ok G p hp
    have := af p hp; omega_using [a8, b8, this]
  have gi' : GI G STK σ c.V c.LS t := by
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h28).trans gi.r28,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega_using [hi]) fun o ho => by have := hw' o ho; simp only [fSave] at *; omega_using [this])]
      exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide) fun o ho => by
        obtain ⟨_, a8, aL, _⟩ := (hhw o ho).1; simp only [fLR] at aL ⊢; omega_using [a8, aL])]
      exact gi.lr
    · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega_using [this]) (fixedFar p hp))]
      exact gi.fixed p hp
    · rw [fw_frame f (hd _ (by have := (gi.ls p hp).1; simp only [hEnd]; omega_using [this]) fun o ho => (hhw o ho).2 p hp)]
      exact gi.slots p hp
    · rcases mem x hx with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · exact ⟨G.rScr, List.mem_cons_self, sw G (hon' p hp).2.2⟩
      · exact ⟨G.rScr, List.mem_cons_self, sw G (by have := hw' o ho; simp only [hEnd] at hE; omega_using [hE, this])⟩
      · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩
  refine ⟨gi', fun x hx => ?_, fun x hx => h.clOk x (hcl x hx).1, fun j hj => ?_, h.liveOk, fun d hd' => ?_,
    h.kslOk⟩
  · obtain ⟨hm, ha⟩ := hcl x hx
    obtain ⟨xE, _, xb⟩ := h.clOk x hm
    rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · exact gi.sdisj (ha p hp) xb (hon' p hp).2.2
      · have := hw' o ho
        exact gi.sdisj (.inr (by simp only [hEnd] at xE; omega_using [xE, this])) xb (by simp only [hEnd] at hE; omega_using [hE, this])
      · exact gi.scr_below xb) (by omega_using [fit, xb])]
    exact h.sb x hm
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd')]; exact h.ksl d hd'

/-- `c` with the header word `o` := `v`. -/
abbrev Cfg.setV (c : Cfg) (o : Nat) (v : BitVec 64) : Cfg := { c with V := upd c.V o v, LS := o :: c.LS }

/-- `std r, o(r28)` of a variable header word keeps the claims, arrays and key
header words. -/
theorem SS.stF (h : SS G STK σ c s) {o : Nat} (hv : VarOk G o) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, SS G STK σ (c.setV o (s.gpr r)) t → Mupd s t (s.mem.writeW (G.sa o) (s.gpr r)) → t.lr = s.lr →
      WP isa (.block rest) t Q) :
    WP isa (.block (st r o :: rest)) s Q := by
  refine h.gi.stF hv fun t gi m lr => k t ?_ m lr
  have gi₀ := h.gi
  have big := gi₀.wBig
  have kb := gi₀.kBig
  have hE := gi₀.hEnd_le
  obtain ⟨oS, _, _, _⟩ := hv
  have f : Frame [G.rs o 8] s.mem t.mem := by
    rw [m.mem]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hd : (G.rs o 8).Disjoint (⟨G.KB, kz G.pLen⟩ : Region) :=
    (gi₀.kdisj (o := o) (n := 8) (.inl (by simp only [kB, fSave] at oS ⊢; omega_using [oS]))
      (by simp only [hEnd] at hE; omega_using [hE, oS])).symm
  refine ⟨gi, h.sb.frame f (fun x hx r' hr' => ?_) (fun x hx => ?_), h.clOk, fun j hj => ?_, h.liveOk,
    fun d hd' => ?_, h.kslOk⟩
  · simp only [List.mem_singleton] at hr'; subst hr'
    obtain ⟨a, _, b⟩ := h.clOk x hx
    exact gi₀.sdisj (.inr (by simp only [hEnd] at a; omega_using [oS, a])) b (by simp only [hEnd] at hE; omega_using [hE, oS])
  · have := (h.clOk x hx).2.2; have := gi₀.scrFit; omega_arith
  · rw [num_frame h.lens f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.liveOk j hj)]
    exact h.arrs j hj
  · rw [slot_frame h.lens f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.kslOk d hd')]
    exact h.ksl d hd'

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.VP`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: pieces proven correct and constant time at once

As on ARMv7 (`Proof/Rsa/Arm/RvVP.lean`): `VP F c G`: from any state at the
stage `F σ` of a run from `σ`, `c` ends at the stage `G σ` (`wp`), and two
runs, each at the stage `F` of its own run, leak the same trace and end at
the stages `G` (`ct`). The stages carry the public parameters both runs
share, so that a piece checked by the taint analysis needs only that the
registers it takes as public are determined by them (`VP.taint`), and pieces
compose by `seq`, `ite` and `loop` (whose number of iterations is public).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE

/-- Two runs, each at the stage `F` of its own run from `σ`. -/
def Two (F : State → State → Prop) (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, F σ₁ s₁ ∧ F σ₂ s₂

/-- The stage `F` of a run from `σ`, whose states name the statics `σ` names. -/
def Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

structure VP (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop where
  wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)
  ct : RelCT isa (Two (Sy F)) c (Two (Sy G))

namespace VP

variable {F G H : State → State → Prop}

/-- The stage after a piece names the statics of the run's start. -/
theorem wps {c : Prog isa} (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) {σ s : State}
    (hs : F σ s) (hy : s.syms = σ.syms) : WP isa c s (Sy G σ) :=
  WP.mono_syms (wp σ s hs hy) fun _ ht ty => ⟨ht, ty.trans hy⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct' {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => Sy F σ₁ s₁ ∧ Sy F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) : VP F c G := by
  refine ⟨wp, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂
  have r := ((ct σ₁ σ₂).wp (F₁ := Sy G σ₁) (F₂ := Sy G σ₂) fun s t h =>
    ⟨wps wp h.1.1 h.1.2, wps wp h.2.1 h.2.2⟩) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, r.2.2.1, r.2.2.2⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => F σ₁ s₁ ∧ F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  of_ct' (fun σ₁ σ₂ => (ct σ₁ σ₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    fun σ s hs _ => wp σ s hs

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem taint {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs rs) c hc).isSome = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hc) wp

/-- `taint`, with the Montgomery kernel's summary in place of its code
(`Proof/Bignum/PPC64LE/MontSum.lean`). -/
theorem taintR {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.checkR VG.PPC64LE.taint VG.Proof.Bignum.PPC64LE.montSums (Taint.ofRegs rs) c
      hc).isSome = true ∧ VG.Taint.fillR VG.Proof.Bignum.PPC64LE.montSums c hc = c)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc, hf⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taintR VG.Proof.Bignum.PPC64LE.montSums_ok (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hf hc) wp

theorem mono {F' G' : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hF : ∀ σ s, F' σ s → F σ s) (hG : ∀ σ s, G σ s → G' σ s) : VP F' c G' :=
  ⟨fun σ s hs hy => WP.mono (h.wp σ s (hF σ s hs) hy) (hG σ),
    h.ct.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hF _ _ h₁.1, h₁.2⟩, ⟨hF _ _ h₂.1, h₂.2⟩⟩)
      fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hG _ _ h₁.1, h₁.2⟩, ⟨hG _ _ h₂.1, h₂.2⟩⟩⟩

theorem seq {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VP G c₂ H) : VP F (.seq c₁ c₂) H :=
  ⟨fun σ _ hs hy => WP.seq (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2), RelCT.seq h₁.ct h₂.ct⟩

theorem assoc {a b c : Prog isa} (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs hy => WP.assoc (h.wp σ s hs hy), RelCT.assoc h.ct⟩

theorem block_append {l₁ l₂ : List Instr} (h₁ : VP F (.block l₁) G) (h₂ : VP G (.block l₂) H) :
    VP F (.block (l₁ ++ l₂)) H :=
  ⟨fun σ _ hs hy => WP.block_append (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2),
    RelCT.block_append (RelCT.seq h₁.ct h₂.ct)⟩

theorem block_nil (h : ∀ σ s, F σ s → G σ s) : VP F (.block []) G :=
  ⟨fun σ s hs _ => WP.block_nil (h σ s hs),
    RelCT.block_nil fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨h _ _ h₁.1, h₁.2⟩, ⟨h _ _ h₂.1, h₂.2⟩⟩⟩

/-- A branch on a condition both runs agree on. -/
theorem ite {c : Cond} {t e : Prog isa}
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VP (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VP (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VP F (.ite c t e) G := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, isa.eval c s = some b := by cases c <;> exact ⟨_, rfl⟩
    exact WP.ite b hb (fun h => ht.wp σ s ⟨hs, by rw [hb, h]⟩ hy) (fun h => he.wp σ s ⟨hs, by rw [hb, h]⟩ hy)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁.1 h₂.1) ?_ ?_
    · exact ht.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h
    · exact he.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h

/-- A loop whose iterations left, `n + 1` at the stage `I (n + 1)`, both
runs share: each iteration goes on iff `n > 0`. -/
theorem loop {I : Nat → State → State → Prop} {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (hb : ∀ n, VP (I (n + 1)) body fun σ s =>
      isa.eval c s = some (decide (0 < n)) ∧ (n = 0 → Q σ s) ∧ (0 < n → I n σ s))
    (n : Nat) : VP (I (n + 1)) (.loop body c) Q := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · refine WP.loop (M := isa) (Q := Q σ) (fun m u => Sy (I (m + 1)) σ u) (fun m u hu => ?_) n s ⟨hs, hy⟩
    refine WP.mono (wps (hb m).wp hu.1 hu.2) fun u' ⟨⟨he, hq, hi⟩, uy⟩ => ?_
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · exact .inl ⟨by rw [he, h0]; rfl, hq h0⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [hp]⟩
      exact .inr ⟨by rw [he]; simp, k, by omega_using [], hi hp, uy⟩
  · refine RelCT.loop (M := isa) (fun m => Two (Sy (I (m + 1)))) (fun m => ?_) n
    refine (hb m).ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨σ₁, σ₂, ⟨⟨e₁, q₁, i₁⟩, y₁⟩, ⟨⟨e₂, q₂, i₂⟩, y₂⟩⟩ =>
      ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ?_⟩
    · have h0 : m = 0 := by rw [e₁] at hf; simpa using hf
      exact ⟨σ₁, σ₂, ⟨q₁ h0, y₁⟩, ⟨q₂ h0, y₂⟩⟩
    · have hp : 0 < m := by rw [e₁] at ht; simpa using ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [hp]⟩
      exact ⟨k, by omega_using [], σ₁, σ₂, ⟨i₁ hp, y₁⟩, ⟨i₂ hp, y₂⟩⟩

/-- A piece no state reaches. -/
theorem of_false {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁.1 (h σ _)⟩

end VP

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: header words in pieces

`WP.wr`: an instruction that writes one register, with the stack pointer and
the link register kept. The taint analysis does not follow the header's
words, which the search keeps its state in: a load of one (`ld`) and a store
into one (`st`) leak only addresses from `r28`, which holds `scratch` in both
runs of the search, so they are analysed with `r28` public (`ld_vp`,
`st_vp`, `stImm_vp`, `cmpF_vp`), and the code between them with the registers
the loads set public (`VP.taint`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- An instruction that writes `v` to `d`. -/
theorem WP.wr {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 64}
    (h : exec i s = some (s.write d v))
    (k : ∀ s', Upd s s' d v → s'.sp = s.sp → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ (Upd.write _ _ _) rfl rfl)

section
variable {G : GP} {STK : Nat}

/-- The stage's states hold `scratch` in `r28` and have the call's stack pointer. -/
abbrev Pub (G : GP) (F : State → State → Prop) : Prop :=
  ∀ σ s, F σ s → s.gpr .r28 = G.scr ∧ s.sp = G.sp

theorem SS.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G F := fun σ s h => ⟨(hF σ s h).gi.r28, by rw [(hF σ s h).gi.sp, ← (hF σ s h).gi.hG]; rfl⟩

/-- A piece analysed with `r28` and `rs` public. -/
theorem VP.pub {F Q : State → State → Prop} {c : Prog isa} (hp : Pub G F) (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs (.r28 :: rs)) c hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (Q σ)) : VP F c Q :=
  VP.taint (.r28 :: rs) cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [(hp _ _ h₁).2, (hp _ _ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [(hp _ _ h₁).1, (hp _ _ h₂).1]
      · exact regs _ _ _ _ h₁ h₂ r hr) wp

end

/-- `ld t, o(r28)` of a header word whose value `v` is known, keeping a stage. -/
theorem SS.ldK {G : GP} {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {o : Nat} (ho : o + 8 ≤ hEnd)
    (h8 : o % 8 = 0) {v : BitVec 64} (hv : fw s.mem G o = v) {t : Reg} (ht : t ≠ .r28) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G STK σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (ld t o :: rest)) s Q := by
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write t v) ?_ (k _ (h.of_upd (Upd.write _ _ _) rfl ht) (Upd.write _ _ _))
  rw [show ld t o = .load .d t .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega_using [ho],
    by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])), h.gi.r28, ← hv]

/-! ## Header words as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A load of a header word whose value both runs know. -/
theorem ld_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} (hr : r ≠ .r28) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Upd s t r x → Q σ t) : VP P (.block [ld r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [ld r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write r x) ?_ (WP.block_nil (k σ s _ hs (h.of_upd (Upd.write _ _ _) rfl hr)
    (Upd.write _ _ _)))
  rw [show ld r o = .load .d r .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega_using [ho],
    by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])), h.gi.r28, ← hx σ s hs]

/-- A store into a variable word of the header. -/
theorem st_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} {o : Nat} (hv : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (s.gpr r)) t → Keep [] s t → Q σ t) :
    VP P (.block [st r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [st r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).stF hv fun t h m _ => WP.block_nil (k σ s t hs h ⟨fun r _ => by rw [m.gpr], m.rd, m.wr⟩)

/-- `stImm o v`: the header word `o` := `v`. -/
theorem stImm_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (hv : v < 2 ^ 15) (ho : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (BitVec.ofNat 64 v)) t → Keep [.r3] s t → Q σ t) :
    VP P (.block (stImm o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (stImm o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  refine WP.wr (d := .r3) (exec_li hv) fun s₁ u₁ sp₁ _ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := (hF σ s hs).of_upd u₁ sp₁ (by decide)
  refine h₁.stF ho fun t h m _ => WP.block_nil (k σ s t hs (by rw [u₁.gpr] at h; exact h) ?_)
  exact ⟨fun r hr => by rw [m.gpr, u₁.other _ (by simpa using hr)], by rw [m.rd, u₁.rd], by rw [m.wr, u₁.wr]⟩

theorem sub_beq_zero (x y : BitVec 64) : (x - y == 0) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; exact BitVec.zero_add y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-- `cmpF o v`: `r0 = 0` iff the header word `o`, which both runs know, is `v`. -/
theorem cmpF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v ≤ 2 ^ 15) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3] s t →
      isa.eval (.zero .d .r0) t = some (x == BitVec.ofNat 64 v) → Q σ t) : VP P (.block (cmpF o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (cmpF o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write .r3 x) ?_ ?_
  · rw [show ld .r3 o = .load .d .r3 .r28 o from rfl, exec_load_d (by decide)
      ⟨by simp only [hEnd, fSave] at ho; omega_using [ho], by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])),
      h.gi.r28, ← hx σ s hs]
  refine WP.wr (exec_subi (by decide) hv) fun t u sp _ => WP.block_nil ?_
  have u₀ : Upd s (s.write .r3 x) .r3 x := Upd.write _ _ _
  refine k σ s t hs ((h.of_upd u₀ rfl (by decide)).of_upd u sp (by decide)) ?_ ?_
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u.other _ hr.1, u₀.other _ hr.2], by rw [u.rd, u₀.rd], by rw [u.wr, u₀.wr]⟩
  · rw [eval_zero, u.gpr, u₀.gpr, sub_beq_zero]

/-- `ltR`: `r0 = 0` iff `r3 < r4`, through the carry. -/
theorem ltR_ok {s : State} {rest : List Instr} {Q : State → Prop} {x y : BitVec 64} (h3 : s.gpr .r3 = x)
    (h4 : s.gpr .r4 = y)
    (k : ∀ t, Keep [.r0] s t → t.mem = s.mem → t.sp = s.sp → t.lr = s.lr →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < y.toNat)) → WP isa (.block rest) t Q) :
    WP isa (.block (ltR ++ rest)) s Q := by
  refine WP.cons exec_subc (WP.cons (exec_li (by decide)) (WP.cons exec_addze (k _ ?_ rfl rfl rfl ?_)))
  · refine ⟨fun r hr => ?_, rfl, rfl⟩
    have : r ≠ .r0 := by simpa using hr
    simp [State.writeCarry, State.write, this]
  · rw [eval_zero]
    simp only [State.writeCarry, State.write, ite_true, h3, h4]
    have hx := x.isLt
    have hy := y.isLt
    by_cases hl : x.toNat < y.toNat
    · simp [show ¬(2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1) by omega_using [hl], hl]
    · simp [show 2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1 by omega_using [hl], hl]

/-- `ld r3, o(r28); li r4, v; ltR`: `r0 = 0` iff the header word `o`, which
both runs know, is below `v`. -/
theorem ltF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v < 2 ^ 15) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3, .r4] s t →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < v)) → Q σ t) :
    VP P (.block ([ld .r3 o, .li .r4 v] ++ ltR)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o, .li .r4 v] ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_
  have h := hF σ s hs
  refine h.ldK ho h8 (hx σ s hs) (by decide) fun s₁ h₁ u₁ => ?_
  refine WP.wr (d := .r4) (exec_li hv) fun s₂ u₂ sp₂ _ => ?_
  have h₂ := h₁.of_upd u₂ sp₂ (by decide)
  refine ltR_ok (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr fun t K m sp _ e => WP.block_nil ?_
  refine k σ s t hs (h₂.of_keep K m sp) ⟨fun r hr => ?_, by rw [K.2.1, u₂.rd, u₁.rd], by rw [K.2.2, u₂.wr, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K.gpr (by simpa using hr.1), u₂.other _ hr.2.2, u₁.other _ hr.2.1]
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv])]

/-- An instruction that writes one register other than `r28` keeps a stage. -/
theorem SS.wrK {σ s : State} {c : Cfg} (h : SS G STK σ c s) {i : Instr} {d : Reg} {v : BitVec 64}
    (he : exec i s = some (s.write d v)) (hd : d ≠ .r28 := by decide) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', SS G STK σ c s' → Upd s s' d v → WP isa (.block rest) s' Q) : WP isa (.block (i :: rest)) s Q :=
  WP.wr he fun s' u sp _ => k s' (h.of_upd u sp hd) u

/-- `shl`: `r := v · 2^sh`. -/
theorem shl_ok {σ s : State} {c : Cfg} (h : SS G STK σ c s) {r : Reg} (hr : r ≠ .r28) {v sh : Nat}
    (hv : v < 2 ^ 15) (hsh : sh < 64) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', SS G STK σ c s' → Keep [r] s s' → s'.gpr r = BitVec.ofNat 64 (v * 2 ^ sh) → s'.mem = s.mem →
      WP isa (.block rest) s' Q) : WP isa (.block (shl r v sh ++ rest)) s Q := by
  refine h.wrK (exec_li hv) hr fun s₁ h₁ u₁ => h₁.wrK (exec_lsl hsh) hr fun s₂ h₂ u₂ => k s₂ h₂
    ⟨fun r' hr' => by rw [u₂.other _ (by simpa using hr'), u₁.other _ (by simpa using hr')],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩ ?_ (by rw [u₂.mem, u₁.mem])
  rw [u₂.gpr, u₁.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega_using [hv])]

/-- `ld r3, o(r28); shl r4 v sh; ltR`: `r0 = 0` iff the header word `o` is
below `v · 2^sh`. -/
theorem ltShl_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v sh : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v < 2 ^ 15) (hsh : sh < 64)
    (hb : v * 2 ^ sh < 2 ^ 64) {x : BitVec 64} (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3, .r4] s t →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < v * 2 ^ sh)) → Q σ t) :
    VP P (.block ([ld .r3 o] ++ shl .r4 v sh ++ ltR)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o] ++ shl .r4 v sh ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_
  have h := hF σ s hs
  rw [List.append_assoc]
  refine h.ldK ho h8 (hx σ s hs) (by decide) fun s₁ h₁ u₁ => ?_
  refine shl_ok h₁ (r := .r4) (by decide) hv hsh fun s₂ h₂ K₂ e₂ m₂ => ?_
  refine ltR_ok (by rw [K₂.gpr (by decide), u₁.gpr]) e₂ fun t K m sp _ e => WP.block_nil ?_
  refine k σ s t hs (h₂.of_keep K m sp) ⟨fun r hr => ?_, by rw [K.2.1, K₂.2.1, u₁.rd], by rw [K.2.2, K₂.2.2, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K.gpr (by simpa using hr.1), K₂.gpr (by simpa using hr.2.2), u₁.other _ hr.2.1]
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: byte loops

`loop_nz`: a `do … while (r ≠ 0)` loop that runs its body `N` times.
`copyLoop_ok`: `copyBody`'s loop copies `n` bytes from `r3` to `r4`, which
are apart. `zeroLoop_ok`: `zeroN`'s loop zeroes `n` bytes from `r3`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A `do … while (r ≠ 0)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `r` zero exactly when it is the last. -/
theorem loop_nz {body : Prog isa} {r : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr r != 0) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.nonzero .d r)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d r) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.nonzero .d r) s' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero]; simpa using hz
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, h], rfl, hs'⟩

/-- The count after `subi r, r, 1` from `N - i`. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  rw [show N - i = (N - (i + 1)) + 1 by omega_using [hi], BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The count is nonzero exactly when it is not the last iteration. -/
theorem count_nz {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 (N - (i + 1)) != 0) = decide (i + 1 ≠ N) := by
  by_cases h : i + 1 = N
  · subst h; simp
  · have h1 : (BitVec.ofNat 64 (N - (i + 1))).toNat = N - (i + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hN])
    have : BitVec.ofNat 64 (N - (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega_using [hi, h, this]
    rw [bne_iff_ne.mpr this]; simp [h]

theorem ptr_succ1 (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Copies -/

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = S + BitVec.ofNat 64 k
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 k
  r5 : s.gpr .r5 = BitVec.ofNat 64 (len - k)
  keep : Keep [.r3, .r4, .r5, .r6] s₀ s
  sp : s.sp = s₀.sp
  frame : Frame [⟨D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (D + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)

theorem copy_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : ∀ k < len, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 k) 1)
    (cw : ∀ k < len, InRegions s₀.wr (D + BitVec.ofNat 64 k) 1)
    {k : Nat} (hk : k < len) {s : State} (h : CopyInv S D len s₀ k s) :
    WP isa (.block VG.Impl.MlKem.PPC64LE.copyBody) s fun s' =>
      CopyInv S D len s₀ (k + 1) s' ∧ (s'.gpr .r5 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hlen, hk])
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hlen, hk])
  refine WP.sp_eq ?_
  simp only [VG.Impl.MlKem.PPC64LE.copyBody]
  refine wp_lbz (by decide) (by decide) (by rw [h.r3, BitVec.add_zero]) (by rw [h.keep.2.1, h.keep.2.2]; exact cr k hk)
    fun s₁ u₁ => ?_
  refine wp_stb (by decide) (by decide) (by rw [u₁.other _ (by decide), h.r4, BitVec.add_zero])
    (by rw [u₁.wr, h.keep.2.2]; exact cw k hk) fun s₂ m₂ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₃ u₃ sp₃ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₄ u₄ sp₄ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun s₅ u₅ sp₅ _ => WP.block_nil fun sp => ⟨⟨?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide), h.r3, ptr_succ1]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r4, ptr_succ1]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r5,
      count_sub hk]
  · refine ⟨fun r hr => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.keep.2.1],
      by rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.keep.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, m₂.gpr, u₁.other _ hr.2.2.2,
      h.keep.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [sp, h.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · intro t ht
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, write1_apply, u₁.gpr, setWidth8_64]
    by_cases e : t = k
    · subst e
      rw [ite_eq_left (by simp)]
      exact h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    · have hne : ¬ ((D + BitVec.ofNat 64 t - (D + BitVec.ofNat 64 k)).toNat < 1) := by
        intro hlt
        have e0 : D + BitVec.ofNat 64 t - (D + BitVec.ofNat 64 k) = 0 :=
          BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
        apply Offset.add_ofNat_ne D (a := t) (b := k) (by omega_using [hlen, hk, ht]) (by omega_using [hlen, hk]) e
        rw [← BitVec.sub_add_cancel (D + BitVec.ofNat 64 t) (D + BitVec.ofNat 64 k), e0]; simp
      rw [ite_eq_right hne]; exact h.bytes t (by omega_using [ht, e])
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r5,
      count_sub hk]
    exact count_nz hk hlen

/-- `len > 0` bytes copied from `S` to `D`, with the pointers and the count in
`r3`–`r5`. -/
theorem copyLoop_ok {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64) (hl0 : 0 < len)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : ∀ k < len, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 k) 1)
    (cw : ∀ k < len, InRegions s₀.wr (D + BitVec.ofNat 64 k) 1)
    (h3 : s₀.gpr .r3 = S) (h4 : s₀.gpr .r4 = D) (h5 : s₀.gpr .r5 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)) s₀ fun s =>
      Keep [.r3, .r4, .r5, .r6] s₀ s ∧ s.sp = s₀.sp ∧ Frame [⟨D, len⟩] s₀.mem s.mem ∧
      Spec.Rsa.bytesAt s.mem D len = Spec.Rsa.bytesAt s₀.mem S len :=
  loop_nz (CopyInv S D len s₀) hl0 (fun k hk s h => copy_step hlen hd cr cw hk h)
    (fun s h => ⟨h.keep, h.sp, h.frame, by
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun t ht => h.bytes t (List.mem_range.mp ht)⟩)
    ⟨by rw [h3]; simp, by rw [h4]; simp, by rw [h5]; simp, Keep.refl _ _, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

/-! ## Copies as pieces -/

theorem GP.sa_add (G : GP) (o i : Nat) : G.sa o + BitVec.ofNat 64 i = G.sa (o + i) := by
  simp only [GP.sa, BitVec.add_assoc, ← BitVec.ofNat_add]

open GP (sa_add) in

section
variable {G : GP} {STK : Nat}

/-- A copy between two ranges of `scratch` past the header, apart from the key
working space and from each other: the claims `cl'` apart from the
destination kept, the destination's bytes those of the source. -/
theorem copyS_vp {F Q : State → State → Prop} {c : State → Cfg} {dst src n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15)
    (hs15 : src < 2 ^ 15) (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hso : ∀ σ s, F σ s → src + n ≤ G.scrLen * 8)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.r3, .r4, .r5, .r6] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (G.sa src) n → Q σ t) :
    VP F (copyS dst src n) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (copyS 512 576 8), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  have sS := hso σ s hs
  refine WP.sp_eq ?_
  simp only [copyS, copyN, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine WP.wr (exec_addi (by decide) hs15) fun s₁ u₁ _ _ => ?_
  refine WP.wr (exec_addi (by decide) hd15) fun s₂ u₂ _ _ => ?_
  refine WP.wr (exec_li hn15) fun s₃ u₃ _ _ => WP.block_nil ?_
  have r28 : s.gpr .r28 = G.scr := gi.r28
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copyLoop_ok (S := G.sa src) (D := G.sa dst) (by omega_using [hn15]) hn
    (gi.sdisj hsep.symm (by omega_using [sS]) (by omega_using [dS]))
    (fun i hi => by rw [rd₃, wr₃, sa_add]; exact gi.inRdWr (o := src + i) (n := 1) (by omega_using [sS, hi]))
    (fun i hi => by rw [wr₃, sa_add]; exact gi.inScr (o := dst + i) (n := 1) (by omega_using [dS, hi]))
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, r28])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r28]) (by rw [u₃.gpr]))
    fun t ⟨kp, sp', f, b⟩ sp => ?_
  have K : Keep [.r3, .r4, .r5, .r6] s t := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, rd₃], by rw [kp.2.2, wr₃]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), u₃.other _ hr.2.2.1, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  refine k σ s t hs ?_ K (by rw [b, m₃])
  refine h.of_scrs (os := [(dst, n)]) K sp (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
    (by rw [← m₃]; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
  exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩

/-- A copy of `n` bytes from the pointer `P` in the header word `o` (to a
region apart from `scratch` and the stack below the stack pointer, readable)
to a range of `scratch` past the header, apart from the key working space:
the claims `cl'` apart from the destination kept, the destination's bytes
those at `P`. -/
theorem copyIn_vp {F Q : State → State → Prop} {c : State → Cfg} {o dst n : Nat} {P : Addr}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15)
    (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G o = P)
    (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hPr : ∀ σ s, F σ s → InRegions (s.rd ++ s.wr) P n ∧ P.toNat + n ≤ 2 ^ 64 ∧
      (⟨P, n⟩ : Region).Disjoint G.rScr)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.r3, .r4, .r5, .r6] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem P n → Q σ t) :
    VP F (copyN [ld .r3 o] [scr .r4 dst] n) Q := by
  let M : State → State → Prop := fun σ t => ∃ s, F σ s ∧ SS G STK σ (c σ) t ∧ Keep [.r3, .r4, .r5] s t ∧
    t.sp = s.sp ∧ t.mem = s.mem ∧ t.gpr .r3 = P ∧ t.gpr .r4 = G.sa dst ∧ t.gpr .r5 = BitVec.ofNat 64 n
  refine VP.seq (G := M) (VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o] ++ [scr .r4 dst] ++ [.li .r5 n])), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_) (VP.pub (G := G) (fun σ t ⟨_, _, h, _⟩ => ⟨h.gi.r28, by
      rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.r3, .r4, .r5] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3, .r4, .r5]) (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, _, _, _, _, a3, a4, a5⟩ ⟨_, _, _, _, _, _, b3, b4, b5⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a3, b3]
      · rw [a4, b4]
      · rw [a5, b5]) fun σ t ⟨s, hs, h, K₁, sp₁, m₁, t3, t4, t5⟩ => ?_)
  · have h := hF σ s hs
    have hE := h.gi.hEnd_le
    simp only [List.cons_append, List.nil_append]
    refine WP.cons (s' := s.write .r3 P) ?_ ?_
    · rw [show ld .r3 o = .load .d .r3 .r28 o from rfl, exec_load_d (by decide)
        ⟨by simp only [hEnd, fSave] at ho; omega_using [ho], by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])),
        h.gi.r28, ← hP σ s hs]
    have u₁ : Upd s (s.write .r3 P) .r3 P := Upd.write _ _ _
    refine WP.wr (exec_addi (by decide) hd15) fun s₂ u₂ sp₂ _ => ?_
    refine WP.wr (exec_li hn15) fun s₃ u₃ sp₃ _ => WP.block_nil ⟨s, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((h.of_upd u₁ rfl (by decide)).of_upd u₂ sp₂ (by decide)).of_upd u₃ sp₃ (by decide)
    · refine ⟨fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
    · rw [sp₃, sp₂]; rfl
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.gi.r28]
    · rw [u₃.gpr]
  have h₀ := hF σ s hs
  have gi := h₀.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  obtain ⟨Pr, Pf, Pd⟩ := hPr σ s hs
  have dsub : Region.Sub (G.rs dst n) G.rScr := sw G dS
  refine WP.sp_eq (WP.mono (copyLoop_ok (S := P) (D := G.sa dst) (by omega_using [hn15]) hn (Pd.sub_right dsub)
    (fun i hi => ?_) (fun i hi => by rw [K₁.2.2, sa_add]; exact gi.inScr (o := dst + i) (n := 1) (by omega_using [dS, hi]))
    t3 t4 t5) fun u ⟨kp, sp', f, b⟩ sp => ?_)
  · rw [K₁.2.1, K₁.2.2]
    obtain ⟨r, hr, hc⟩ := Pr
    have hb : (P + BitVec.ofNat 64 i - P).toNat < n := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn15, hi])]; exact hi
    exact ⟨r, hr, hc.byte hb⟩
  have K : Keep [.r3, .r4, .r5, .r6] s u := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, K₁.2.1], by rw [kp.2.2, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), K₁.1 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  refine k σ s u hs ?_ K (by rw [b, m₁])
  refine h₀.of_scrs (os := [(dst, n)]) K (sp.trans sp₁) (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
    (by rw [← m₁]; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
  exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.PrimeCall`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: calling the probable-prime test

`PrimeOk L code`: a verified probable-prime test of layout `L`, which uses at
most 176 bytes of stack. The witnesses from `u` on (`GP.randP`, `GP.rRand`)
are unchanged since the call's entry (`GI.randBytes`). A call's changes to
the working space are only in the test's ranges (`frame_of_keeps`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A verified test of layout `L`, which reads the table of small primes,
with the stack it uses. -/
structure PrimeOk (L : Impl.Dsa.ProbablePrime.Layout) (code : Prog isa) : Prop where
  verified : Verified target code (Proof.Dsa.ProbablePrime.contract L (abi.withConsts kT) 176)
  stack : sdepth code ≤ 176

/-- A region's writes and a working space's kept bytes: what changed is the
working space's ranges `rs` and the other regions. -/
theorem frame_of_keeps {B : Addr} {wsLen : Nat} {rs : List (Nat × Nat)} {rest : List Region} {m m' : Mem}
    (hB : B.toNat + 8 * wsLen ≤ 2 ^ 64) (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 8 * wsLen)
    (f : Frame (⟨B, wsLen * 8⟩ :: rest) m m') (hk : Proof.Dsa.ModPow.Keeps B wsLen rs m m') :
    Frame (rs.map (fun r => ⟨B + BitVec.ofNat 64 r.1, r.2⟩) ++ rest) m m' := by
  intro x hx
  by_cases hin : (⟨B, wsLen * 8⟩ : Region).Contains x 1
  · simp only [Region.Contains] at hin
    obtain hi : (x - B).toNat < 8 * wsLen := by omega
    obtain ex : x = B + BitVec.ofNat 64 (x - B).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.sub_add_cancel x B).symm
    rw [ex]
    refine hk _ hi fun r hr => ?_
    obtain hr' := hx _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    obtain hb := hrs r hr
    by_contra hc
    simp only [not_or, Nat.not_lt, Nat.not_le] at hc
    apply hr'
    obtain e : x - (B + BitVec.ofNat 64 r.1) = BitVec.ofNat 64 ((x - B).toNat - r.1) := by
      apply BitVec.eq_of_toNat_eq
      rw [← BitVec.sub_sub,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show (x - (B + BitVec.ofNat 64 r.1)).toNat + 1 ≤ r.2
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact f x fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hin
      · exact hx r (List.mem_append_right _ hr)

/-! ## The witnesses -/

/-- Where the witnesses from `u` on start: `witnesses` itself when none is left. -/
abbrev GP.randP (G : GP) (u : Nat) : Addr := if u = G.witLen then G.wit else G.wit + BitVec.ofNat 64 u

/-- The witnesses from `u` on. -/
abbrev GP.rRand (G : GP) (u : Nat) : Region := ⟨G.randP u, G.witLen - u⟩

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.witFit (h : GI G STK σ V LS s) : G.wit.toNat + G.witLen ≤ 2 ^ 64 := by
  have := h.pre.nW; rw [← h.hG]; exact this

theorem GI.randSub (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : Region.Sub (G.rRand u) G.rWit := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · show Region.Sub ⟨_, _⟩ _
    rw [GP.randP, ite_eq_right (by omega_using [hl])]; exact Offset.sub_base _ (by omega_using [hu])
  · intro a ha; simp only [Region.Contains, show G.witLen - u = 0 by omega_using [hl]] at ha; omega

theorem GI.randFit (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.randP u).toNat + (G.witLen - u) ≤ 2 ^ 64 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega_using [hl]), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega_using [this, hl]),
      Nat.mod_eq_of_lt (by omega_using [this, hl])]
    omega_using [hu, this]
  · have := (G.randP u).isLt; omega_using [hl]

/-- The witnesses are apart from what the search changes. -/
theorem GI.wit_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rWit.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.wC
  · rw [← h.hG]; exact h.pre.bW.symm

/-- The witnesses from `u` on, in memory. -/
theorem GI.randBytes (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt s.mem (G.randP u) (G.witLen - u) = G.witB.drop u := by
  have fit := h.witFit
  obtain hw : Spec.Rsa.bytesAt s.mem G.wit G.witLen = G.witB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.wit_apart (by omega_using [fit]), ← h.hG]; rfl
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · obtain ⟨d, hd⟩ : ∃ d, G.witLen = u + d := ⟨G.witLen - u, by omega_using [hu]⟩
    rw [GP.randP, ite_eq_right (by omega_using [hl]), show G.witLen - u = d by omega_using [hd], ← hw, hd,
      VG.Proof.Dsa.Generation.bytesAt_append, List.drop_left' (by simp [Spec.Rsa.bytesAt])]
  · rw [show G.witLen - u = 0 by omega_using [hl], List.drop_of_length_le (by
      rw [← hw]; simp [Spec.Rsa.bytesAt]; omega_using [hl])]
    rfl

end

/-! ## The test's contract, as facts -/

/-- The test's contract under `abi`, without the table. -/
abbrev primeK0 (L : Impl.Dsa.ProbablePrime.Layout) : Contract isa := Proof.Dsa.ProbablePrime.contract L abi 176

/-- The test's contract. -/
abbrev primeK (L : Impl.Dsa.ProbablePrime.Layout) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract L (abi.withConsts kT) 176

/-- The candidate at `ws`. -/
abbrev candOf (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt L s.mem (s.gpr .r3)

/-- The precondition, as facts. -/
structure PIn (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Prop where
  spLo : 176 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩]
  wr : s.wr = [⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩, ⟨s.gpr .r7, 8⟩]
  wR : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩ ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  wU : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩ ⟨s.gpr .r7, 8⟩
  rU : Region.Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ ⟨s.gpr .r7, 8⟩
  bW : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩
  bR : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  bU : Region.Disjoint ⟨s.sp - 176#64, 176⟩ ⟨s.gpr .r7, 8⟩
  fw : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  fu : (s.gpr .r7).toNat + 8 ≤ 2 ^ 64
  size : L.size ≤ 8 * (s.gpr .r4).toNat
  odd : candOf L s % 2 = 1
  bl : Spec.Dsa.bitLength (candOf L s) = L.bits

theorem pre_of_pin {L : Impl.Dsa.ProbablePrime.Layout} {s : State} (h : PIn L s) : (primeK0 L).pre s := by
  sig_pre [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  exact ⟨h.spLo, h.rd, h.wr, h.wR, h.wU, h.rU, h.bW, h.bR, h.bU, h.fw, h.fr, h.fu, h.size, h.odd, h.bl⟩

/-- The test's result. -/
abbrev resOf (L : Impl.Dsa.ProbablePrime.Layout) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (candOf L s) (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)

/-- The postcondition, as facts. -/
def PPost (L : Impl.Dsa.ProbablePrime.Layout) (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (resOf L s) ∧
    Proof.Dsa.ModPow.Keeps (s.gpr .r3) (s.gpr .r4).toNat L.scratch s.mem t.mem ∧
    ∀ b rest, resOf L s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (s.gpr .r7) 1 = [BitVec.ofNat 64 ((s.gpr .r6).toNat - rest.length)]

theorem ppost_of_post {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (h : (primeK L).post s t) : PPost L s t := by
  replace h : (primeK0 L).post s t := post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol,
    Impl.RsaKeyGen.TrialTable32.packed)) (cs := []) |>.mp h
  sig_post [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  exact h

/-- Two calls with the same public arguments, candidate and tape. -/
theorem pub_of {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (sp : s.sp = t.sp)
    (p3 : s.gpr .r3 = t.gpr .r3) (p4 : s.gpr .r4 = t.gpr .r4) (p5 : s.gpr .r5 = t.gpr .r5)
    (p6 : s.gpr .r6 = t.gpr .r6) (p7 : s.gpr .r7 = t.gpr .r7) (hc : candOf L s = candOf L t)
    (hr : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .r5) (t.gpr .r6).toNat) :
    (primeK0 L).pub s t := by
  sig_pub [primeK0, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  exact ⟨sp, by simp only [candOf] at hc; rw [hc, hr], p3, p4, p5, p6, p7⟩

/-! ## The call -/

/-- The test's arguments, in `r3`–`r7`. -/
abbrev TArgs (G : GP) (u : Nat) (s : State) : Prop :=
  s.gpr .r3 = G.sa (wB G.pLen) ∧ s.gpr .r4 = BitVec.ofNat 64 (wWords G.pLen) ∧ s.gpr .r5 = G.randP u ∧
    s.gpr .r6 = BitVec.ofNat 64 (G.witLen - u) ∧ s.gpr .r7 = G.sa fUsedOut

/-- The regions the test is given. -/
abbrev tRd (G : GP) (u : Nat) : List Region := [⟨G.randP u, (BitVec.ofNat 64 (G.witLen - u)).toNat⟩]
abbrev tWr (G : GP) : List Region :=
  [⟨G.sa (wB G.pLen), (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8⟩, ⟨G.sa fUsedOut, 8⟩]

/-- The test's entry, without the table. -/
abbrev tEntry (G : GP) (u : Nat) (s : State) : State := s.callEntry.withRegions (tRd G u) (tWr G)

/-- The regions the test reads, the table among them. -/
abbrev tRdK (G : GP) (u : Nat) : List Region := tRd G u ++ [G.rTab]

/-- The test's entry. -/
abbrev tEntryK (G : GP) (u : Nat) (s : State) : State := s.callEntry.withRegions (tRdK G u) (tWr G)

section
variable {G : GP} {σ s : State} {c : Cfg}

theorem GI.witLt {V : Nat → BitVec 64} {LS : List Nat} (h : GI G 176 σ V LS s) : G.witLen < 2 ^ 64 := by
  rw [← h.hG]; exact (σ.gpr .r7).isLt

theorem wWords_lt {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : wWords L < 2 ^ 15 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- The test's arguments meet its precondition. -/
theorem SS.tEntry_pin (h : SS G 176 σ c s) {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat} (regs : TArgs G u s)
    (hu : u ≤ G.witLen) (hsize : L.size ≤ 8 * wWords G.pLen) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits) :
    PIn L (tEntry G u s) := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have wl := gi.witLt
  have lens := gi.lens3
  obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain wWp : 0 < wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain ⟨r3, r4, r5, r6, r7⟩ := regs
  obtain e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  obtain e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
  obtain g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntry G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega_using [big]
  obtain hwW : (G.rs (wB G.pLen) (wWords G.pLen * 8)).Disjoint G.rWit := by
    have := gi.pre.wC; rw [gi.hG] at this; exact this.symm.sub_left (sw G W8)
  obtain hRand := gi.randSub hu
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
  obtain hbS : (rBelow σ 176).Disjoint G.rScr := by have := gi.pre.bC; rw [gi.hG] at this; exact this
  obtain hbW : (rBelow σ 176).Disjoint G.rWit := by have := gi.pre.bW; rw [gi.hG] at this; exact this
  obtain sp : (tEntry G u s).sp = σ.sp := by rw [State.withRegions_sp, State.callEntry_sp, gi.sp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact gi.pre.spLo
  · rw [State.withRegions_rd, g _ (by simp), g _ (by simp), r5, r6]
  · rw [State.withRegions_wr, g .r3 (by simp), g .r4 (by simp), g .r7 (by simp), r3, r4, r7]
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), g _ (by simp), r3, r4, r5, r6, e4, e6]
    exact hwW.sub_right hRand
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), r3, r4, r7, e4]
    exact gi.sdisj (.inr (by simp only [fUsedOut, wB, kB, pB]; omega_using [])) W8 hfU
  · rw [g _ (by simp), g _ (by simp), g _ (by simp), r5, r6, r7, e6]
    have := gi.pre.wC; rw [gi.hG] at this
    exact (this.sub_left hRand).sub_right (sw G hfU)
  · rw [sp, g _ (by simp), g _ (by simp), r3, r4, e4]; exact hbS.sub_right (sw G W8)
  · rw [sp, g _ (by simp), g _ (by simp), r5, r6, e6]; exact hbW.sub_right hRand
  · rw [sp, g _ (by simp), r7]; exact hbS.sub_right (sw G hfU)
  · rw [g _ (by simp), g _ (by simp), r3, r4, e4]
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega_using [wBl]),
      Nat.mod_eq_of_lt (by omega_using [big, fit, wWp])]
    omega_using [big, fit]
  · rw [g _ (by simp), g _ (by simp), r5, r6, e6]; exact gi.randFit hu
  · rw [g _ (by simp), r7]
    show (G.scr + BitVec.ofNat 64 fUsedOut).toNat + 8 ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by simp only [fUsedOut]; omega_using []),
      Nat.mod_eq_of_lt (by omega_using [fit, hfU])]
    omega_using [fit, hfU]
  · rw [g _ (by simp), r4, e4]; exact hsize
  · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [g _ (by simp), r3, hcb]; exact hodd
  · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [g _ (by simp), r3, hcb]; exact hbl

/-- The test's regions are the search's. -/
theorem SS.tCovers (h : SS G 176 σ c s) {u : Nat} (hu : u ≤ G.witLen) :
    Covers (tRdK G u) s.rd ∧ Covers (tWr G) s.wr := by
  have gi := h.gi
  have big := gi.wBig
  have wl := gi.witLt
  have lens := gi.lens3
  obtain e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  obtain e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
  refine ⟨Covers.append_left ?_ (Covers.of_mem fun r hr => ?_), ?_⟩
  · rw [gi.rd, gi.pre.rd, gi.hG]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rcases Nat.lt_or_ge u G.witLen with hl | hl
    · refine ⟨G.rWit, by simp, u, ?_, ?_⟩
      · show G.randP u = G.wit + BitVec.ofNat 64 u
        rw [GP.randP, ite_eq_right (by omega_using [hl])]
      · show u + (BitVec.ofNat 64 (G.witLen - u)).toNat ≤ G.witLen
        rw [e6]; omega_using [hu]
    · refine ⟨G.rWit, by simp, 0, ?_, ?_⟩
      · show G.randP u = G.wit + BitVec.ofNat 64 0
        rw [GP.randP, ite_eq_left (by omega_using [hu, hl])]; simp
      · show 0 + (BitVec.ofNat 64 (G.witLen - u)).toNat ≤ G.witLen
        rw [e6]; omega_using []
  · simp only [List.mem_singleton] at hr; subst hr
    rw [gi.rd, gi.pre.rd, gi.hG]; simp
  · rw [gi.wr, gi.pre.wr, gi.hG]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨G.rScr, by simp, wB G.pLen, rfl, by show wB G.pLen + (BitVec.ofNat 64 (wWords G.pLen)).toNat * 8 ≤ G.scrLen * 8; rw [e4]; omega_using [big]⟩
    · exact ⟨G.rScr, by simp, fUsedOut, rfl, hfU⟩

/-- The table, at the test's entry, under `abi.withConsts`. -/
theorem SS.tConsts (h : SS G 176 σ c s) (hy : s.syms = σ.syms) (u : Nat) : ConstsOk kT 176 (tEntryK G u s) := by
  have gi := h.gi
  have fit := gi.scrFit
  obtain tf : G.tab.toNat + 8192 ≤ 2 ^ 64 := by have := gi.pre.tFit; rw [gi.hG] at this; exact this
  obtain et : (mkG (tEntryK G u s)).rTab = G.rTab := by
    show (⟨s.syms Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩ : Region) = ⟨G.tab, 8192⟩
    rw [hy, ← gi.hG]; rfl
  obtain hC : G.rTab.Disjoint G.rScr := by have := gi.pre.tC; rw [gi.hG] at this; exact this
  obtain hB : G.rTab.Disjoint (rBelow σ 176) := by have := gi.pre.tB; rw [gi.hG] at this; exact this
  have big := gi.wBig
  have kb := gi.kBig
  have lens := gi.lens3
  obtain e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [constRegs_kT, et]; rfl
  · intro k hk i hi
    simp only [kT, Impl.RsaKeyGen.TrialTable32.consts, List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    obtain held := gi.pre.held _ List.mem_cons_self i hi
    dsimp only at hi held
    obtain hi' : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at hi; exact hi
    dsimp only
    rw [show (tEntryK G u s).mem = s.mem from rfl, show (tEntryK G u s).syms = s.syms from rfl]
    obtain eg : σ.syms Impl.RsaKeyGen.TrialTable32.symbol = G.tab := by rw [← gi.hG]; rfl
    rw [← held, hy, eg]
    refine gi.frame.readW (r := G.rTab) (Offset.contains_base _ (show 8 * i + 64 / 8 ≤ 8192 by omega_using [hi']) (by omega_using [hi'])) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hC
    · exact hB
  · intro t ht
    rw [constRegs_kT, et, List.mem_singleton] at ht
    subst ht
    refine ⟨tf, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [tEntryK, State.withRegions_wr, tWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e4]; exact hC.sub_right (sw G (by omega_using [big]))
      · exact hC.sub_right (sw G hfU)
    · have : abi.reserved 176 (tEntryK G u s) = [rBelow σ 176] := by
        show stackBelow s.sp 176 = _
        rw [gi.sp]; rfl
      rw [this, List.mem_singleton] at hr
      subst hr; exact hB
  · intro t ht
    rw [constRegs_kT, et, List.mem_singleton] at ht
    subst ht
    have := gi.pre.tAl; rw [gi.hG] at this; exact this

/-- The test's arguments meet its precondition. -/
theorem SS.tPre (h : SS G 176 σ c s) (hy : s.syms = σ.syms) {L : Impl.Dsa.ProbablePrime.Layout} {u : Nat}
    (regs : TArgs G u s) (hu : u ≤ G.witLen) (hsize : L.size ≤ 8 * wWords G.pLen) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits) :
    (primeK L).pre (tEntryK G u s) :=
  (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)) (cs := [])).mpr
    ⟨pre_of_pin (h.tEntry_pin regs hu hsize hcb hodd hbl), h.tConsts hy u⟩

/-- Two calls with the same public arguments, candidate and tape, and the
same table. -/
theorem pubK_of {L : Impl.Dsa.ProbablePrime.Layout} {s t : State} (h : (primeK0 L).pub (stripConsts kT s) (stripConsts kT t))
    (hy : s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol) :
    (primeK L).pub s t := by
  refine (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ⟨(pub_stripConsts (K := kT)).mp h, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  subst hk; exact hy

theorem pubK_tEntry {L : Impl.Dsa.ProbablePrime.Layout} {G : GP} {u : Nat} {s t : State}
    (h : (primeK0 L).pub (tEntry G u s) (tEntry G u t))
    (hy : s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol) :
    (primeK L).pub (tEntryK G u s) (tEntryK G u t) :=
  pubK_of h hy

/-- The test's result on the candidate `cb` with the witnesses from `u` on. -/
abbrev tRes (G : GP) (cb : List Byte) (u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u)

/-- The call of a test: its status in `r3`'s low half, the witnesses it read
at `fUsedOut` when the tape sufficed, and memory changed only in the test's
ranges of its working space, the count's word and the stack. -/
theorem SS.primeCall_ok {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String}
    (ok : PrimeOk L code) (h : SS G 176 σ c s) (hy : s.syms = σ.syms) {u : Nat} (regs : TArgs G u s)
    (hu : u ≤ G.witLen) (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ preserved, t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      Frame (L.scratch.map (fun r => G.rs (wB G.pLen + r.1) r.2) ++ [G.rs fUsedOut 8, rBelow σ 176]) s.mem t.mem →
      ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (tRes G cb u) →
      (∀ b rest, tRes G cb u = some (b, rest) →
        Spec.Rsa.wordsAt t.mem (G.sa fUsedOut) 1 = [BitVec.ofNat 64 (G.witLen - u - rest.length)]) → Q t) :
    WP isa (.call name code) s Q := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have wl := gi.witLt
  have lens := gi.lens3
  obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain pin := h.tPre hy regs hu hsize hcb hodd hbl
  obtain ⟨r3, r4, r5, r6, r7⟩ := regs
  obtain e4 : (BitVec.ofNat 64 (wWords G.pLen)).toNat = wWords G.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wWords_lt lens; omega_using [this])]
  obtain e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
  obtain W8 : wB G.pLen + wWords G.pLen * 8 ≤ G.scrLen * 8 := by omega_using [big]
  obtain hfU : fUsedOut + 8 ≤ G.scrLen * 8 := by simp only [fUsedOut]; have := gi.hEnd_le; simp only [hEnd] at this; omega_using [this]
  obtain wWp : 0 < wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain hBfit : (G.sa (wB G.pLen)).toNat + 8 * wWords G.pLen ≤ 2 ^ 64 := by
    show (G.scr + BitVec.ofNat 64 (wB G.pLen)).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wB G.pLen) (by omega_using [wBl]),
      Nat.mod_eq_of_lt (by omega_using [big, fit, wWp])]
    omega_using [big, fit]
  obtain ⟨hcovR, hcovW⟩ := h.tCovers hu
  refine WP.callAny ok.verified.1 pin (Covers.append hcovR hcovW)
    hcovW (fun t rd wr sp f g post => ?_) (by have := ok.stack; omega_using [this])
  obtain pp := ppost_of_post post
  obtain ⟨st, keeps, used⟩ := pp
  obtain eg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntryK G u s).gpr r = s.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain hres : resOf L (tEntryK G u s) = tRes G cb u := by
    simp only [resOf, candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
    rw [eg .r3 (by simp), eg .r5 (by simp), eg .r6 (by simp), r3, hcb, r5, r6, e6, gi.randBytes hu]
  refine k t g rd wr sp ?_ ?_ ?_
  · rw [State.withRegions_mem, State.callEntry_mem, State.withRegions_mem, eg .r3 (by simp), eg .r4 (by simp),
      r3, r4, e4] at keeps
    obtain f' := frame_of_keeps (B := G.sa (wB G.pLen)) (wsLen := wWords G.pLen) (rs := L.scratch)
      (rest := [⟨G.sa fUsedOut, 8⟩, below s.sp (sdepth code)])
      hBfit hL (by rw [← e4]; exact f) keeps
    refine f'.sub fun x hx => ?_
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨r, hr, rfl⟩ | rfl | rfl
    · exact ⟨G.rs (wB G.pLen + r.1) r.2, List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩), by
        rw [GP.sa_add]; exact fun _ h => h⟩
    · exact ⟨G.rs fUsedOut 8, by simp, fun _ h => h⟩
    · refine ⟨rBelow σ 176, by simp, ?_⟩
      have := ok.stack
      rw [gi.sp]
      exact Offset.sub_below _ (by omega_using [this]) (by omega_using [this])
  · rw [State.withRegions_gpr] at st; rw [← hres]; exact st
  · intro b rest e
    have := used b rest (by rw [hres]; exact e)
    rw [State.withRegions_mem, eg .r7 (by simp), eg .r6 (by simp), r7, r6, e6] at this
    rw [this, Nat.sub_sub]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: a probable-prime test (`test_vp`)

`test pLen c src n name code` copies the candidate to byte `c` of the
working space of the functions we call and tests it with the witnesses from
`fUsed` on: `fRes` := its status, and `fUsed` := the witnesses it read when
the tape sufficed (`testCfg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A stage: a state of the search with the contents `c`, and `X` of the run. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G 176 σ c s ∧ X σ

/-- The stage after a test, from its result `res`. -/
def testCfg (c : Cfg) (cl : Claims) (witLen : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }.setV fRes 0
  | some (b, rest) => ({ c with cl := cl }.setV fRes (BitVec.ofNat 64 (if b then 1 else 2))).setV fUsed
      (BitVec.ofNat 64 (witLen - rest.length))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem varOk_of {o : Nat} (h : o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fLR ∧ o ∉ [fOut, fWit, fWitLen, fUsedP, fStP]) :
    VarOk G o := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p hp e => h.2.2.2 ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [e]

theorem varOk_fRes : VarOk G fRes := varOk_of (by decide)
theorem varOk_fUsed : VarOk G fUsed := varOk_of (by decide)
theorem varOk_fUsedOut : VarOk G fUsedOut := varOk_of (by decide)

/-! ## The arguments -/

/-- `r3`–`r7`, the test's arguments, from the header. -/
theorem targs_vp {u : Nat} (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) (.seq (.block [scr .r3 (wB G.pLen), .li .r4 (wWords G.pLen), ld .r9 fUsed, ld .r5 fWit,
        ld .r6 fWitLen, .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut])
        (.ite (.zero .d .r6) (.block [ld .r5 fWit]) (.block [])))
      (fun σ s => St G c X σ s ∧ TArgs G u s) := by
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.sa (wB G.pLen) ∧
    s.gpr .r4 = BitVec.ofNat 64 (wWords G.pLen) ∧ s.gpr .r5 = G.wit + BitVec.ofNat 64 u ∧
    s.gpr .r6 = BitVec.ofNat 64 (G.witLen - u) ∧ s.gpr .r7 = G.sa fUsedOut
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [scr .r3 (wB 128), .li .r4 (wWords 128),
      ld .r9 fUsed, ld .r5 fWit, ld .r6 fWitLen, .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · have gi := h.gi
    have lens := gi.lens3
    have wl := gi.witLt
    obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
    refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) wBl) fun s₁ u₁ sp₁ _ => ?_
    obtain h₁ := h.of_upd u₁ sp₁ (by decide)
    refine WP.wr (exec_li (wWords_lt lens)) fun s₂ u₂ sp₂ _ => ?_
    obtain h₂ := h₁.of_upd u₂ sp₂ (by decide)
    refine h₂.ldK (o := fUsed) (by decide) (by decide) ((h₂.gi.slotV hU).trans hUv) (by decide) fun s₃ h₃ u₃ => ?_
    refine h₃.ldK (o := fWit) (by decide) (by decide) (h₃.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
      fun s₄ h₄ u₄ => ?_
    refine h₄.ldK (o := fWitLen) (by decide) (by decide)
      (h₄.gi.fixedV (v := BitVec.ofNat 64 G.witLen) (by simp [fixedWords])) (by decide)
      fun s₅ h₅ u₅ => ?_
    refine WP.wr exec_add fun s₆ u₆ sp₆ _ => ?_
    obtain h₆ := h₅.of_upd u₆ sp₆ (by decide)
    refine WP.wr exec_sub fun s₇ u₇ sp₇ _ => ?_
    obtain h₇ := h₆.of_upd u₇ sp₇ (by decide)
    refine WP.wr (exec_addi (by decide) (by decide)) fun s₈ u₈ sp₈ _ => WP.block_nil fun _ => ?_
    obtain h₈ := h₇.of_upd u₈ sp₈ (by decide)
    refine ⟨⟨h₈, x⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, gi.r28]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [u₈.other .r5 (by decide), u₇.other .r5 (by decide), u₆.gpr, u₅.other .r5 (by decide),
        u₅.other .r9 (by decide), u₄.gpr, u₄.other .r9 (by decide), u₃.gpr]
    · rw [u₈.other .r6 (by decide), u₇.gpr, u₆.other .r6 (by decide), u₆.other .r9 (by decide), u₅.gpr,
        u₅.other .r9 (by decide), u₄.other .r9 (by decide), u₃.gpr, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu, wl])
        (by omega_using [hu])]
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gi.r28]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2.2.1, h₂.2.2.2.2.1]) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [ld .r5 fWit]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, r3, r4, r5, r6, r7⟩, e⟩ => ?_
    have wl := h.gi.witLt
    rw [eval_zero, r6, ofNat_beq_zero (by omega_using [wl])] at e
    obtain hu' : u = G.witLen := by simp at e; omega_using [hu, e]
    refine WP.sp_eq (h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.wit) (by simp [fixedWords]))
      (by decide) fun t ht ut => WP.block_nil fun sp => ⟨⟨ht, x⟩, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [ut.other _ (by decide), r3]
    · rw [ut.other _ (by decide), r4]
    · rw [ut.gpr, GP.randP, ite_eq_left hu']
    · rw [ut.other _ (by decide), r6]
    · rw [ut.other _ (by decide), r7]
  · refine VP.block_nil fun σ s ⟨⟨hx, r3, r4, r5, r6, r7⟩, e⟩ => ⟨hx, r3, r4, ?_, r6, r7⟩
    have wl := hx.1.gi.witLt
    rw [eval_zero, r6, ofNat_beq_zero (by omega_using [wl])] at e
    obtain hu' : u ≠ G.witLen := by simp at e; omega_using [e]
    rw [r5, GP.randP, ite_eq_right hu']

/-! ## The call -/

/-- After the call: the count's word known when the tape sufficed. -/
def callCfg (c : Cfg) (cl : Claims) (witLen u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }
  | some (_, rest) => { c with cl := cl }.setV fUsedOut (BitVec.ofNat 64 (witLen - u - rest.length))

/-- One more known header word. -/
theorem GI.addSlot {STK : Nat} {σ t : State} {V : Nat → BitVec 64} {LS : List Nat} (h : GI G STK σ V LS t) {o : Nat}
    (ho : VarOk G o) {v : BitVec 64} (hv : fw t.mem G o = v) : GI G STK σ (upd V o v) (o :: LS) t := by
  refine ⟨h.pre, h.hG, h.sp, h.rd, h.wr, h.r28, h.saved, h.lr, h.fixed, fun o' ho' => ?_, fun o' ho' => ?_, h.frame⟩
  · by_cases e : o' = o
    · subst e; rw [upd_self]; exact hv
    · rw [upd_ne _ _ e]; exact h.slots o' (List.mem_of_ne_of_mem e ho')
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ho
    · exact h.ls o' ho'

/-- The call of the test on the candidate `cb` at byte `L.candidate` of the
working space, with the witnesses from `u` on. -/
theorem primeCall_vp {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hu : u ≤ G.witLen)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcb : (wB G.pLen + L.candidate, cb) ∈ c.cl) (hcbl : cb.length = L.bits / 8)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (fun σ s => St G c X σ s ∧ TArgs G u s) (.call name code)
      (fun σ t => St G (callCfg c cl' G.witLen u (tRes G cb u)) X σ t ∧
        ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status (tRes G cb u)) := by
  obtain bytes : ∀ σ s, SS G 176 σ c s →
      Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb := fun σ s h => by
    have := h.sb _ hcb; rw [hcbl, ← GP.sa_add] at this; exact this
  refine VP.of_ct' (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ hy => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (tRdK G u) (tWr G)
      fun s₁ s₂ ⟨⟨⟨⟨h₁, _⟩, g₁⟩, y₁⟩, ⟨⟨⟨h₂, _⟩, g₂⟩, y₂⟩⟩ => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    obtain p₁ := h₁.tPre y₁ g₁ hu hsize (bytes _ _ h₁) hodd hbl
    obtain p₂ := h₂.tPre y₂ g₂ hu hsize (bytes _ _ h₂) hodd hbl
    obtain ⟨cr₁, cw₁⟩ := h₁.tCovers hu
    obtain ⟨cr₂, cw₂⟩ := h₂.tCovers hu
    obtain eg : ∀ {s : State}, ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntry G u s).gpr r = s.gpr r := fun r hr => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    obtain et : ∀ {σ s : State} {c : Cfg}, SS G 176 σ c s → s.syms = σ.syms →
        s.syms Impl.RsaKeyGen.TrialTable32.symbol = G.tab := fun h y => by rw [y, ← h.gi.hG]; rfl
    obtain ⟨a3, a4, a5, a6, a7⟩ := g₁
    obtain ⟨b3, b4, b5, b6, b7⟩ := g₂
    refine ⟨p₁, p₂, pubK_tEntry (pub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ((et h₁ y₁).trans (et h₂ y₂).symm),
      Covers.append cr₁ cw₁, cw₁, Covers.append cr₂ cw₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      obtain e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [eg _ (by simp), eg _ (by simp), a3, b3]
    · rw [eg _ (by simp), eg _ (by simp), a4, b4]
    · rw [eg _ (by simp), eg _ (by simp), a5, b5]
    · rw [eg _ (by simp), eg _ (by simp), a6, b6]
    · rw [eg _ (by simp), eg _ (by simp), a7, b7]
    · simp only [candOf, Proof.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
      rw [eg _ (by simp), eg _ (by simp), a3, b3, bytes _ _ h₁, bytes _ _ h₂]
    · have wl := h₁.gi.witLt
      obtain e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [eg _ (by simp), eg _ (by simp), eg _ (by simp), eg _ (by simp), a5, a6, b5, b6, e6, h₁.gi.randBytes hu,
        h₂.gi.randBytes hu]
  have hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut := hU
  refine h.primeCall_ok (name := name) ok hy regs hu hsize hL (bytes _ _ h) hodd hbl
    fun t g rd wr sp f st used => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  obtain h' : SS G 176 σ { c with cl := cl' } t := by
    refine h.of_hdrScrs (keep_of_preserved g rd wr) sp (os := L.scratch.map fun r => (wB G.pLen + r.1, r.2))
      (fun p hp => ?_) (hw := [fUsedOut]) (fun o ho => ?_) (by
        refine f.sub fun x hx => ?_
        rcases List.mem_append.mp hx with h1 | h2
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
          exact ⟨G.rs (wB G.pLen + q.1) q.2, List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.mpr ⟨(wB G.pLen + q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)), fun _ h => h⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with rfl | rfl
          · exact ⟨G.rs fUsedOut 8, List.mem_append_left _ (List.mem_append_right _ (by simp)), fun _ h => h⟩
          · exact ⟨rBelow σ 176, List.mem_append_right _ (by simp), fun _ h => h⟩) fun y hy => ⟨(hcl y hy).1, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hL q hq
      refine ⟨by simp only [hEnd, wB, kB, pB, fSave] at hE ⊢; omega_using [], .inr (by omega_using []), by simp; omega_using [big, this]⟩
    · simp only [List.mem_singleton] at ho; subst ho; exact ⟨varOk_fUsedOut, hU'⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hcl y hy).2 q hq
  unfold callCfg
  split
  · exact h'
  · rename_i b rest e
    refine ⟨h'.gi.addSlot varOk_fUsedOut ?_, h'.sb, h'.clOk, h'.arrs, h'.liveOk, h'.ksl, h'.kslOk⟩
    have := used b rest e
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      List.cons.injEq, and_true] at this
    exact this

/-! ## The result -/

theorem status_lt (res : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status res < 3 := by
  unfold Proof.Dsa.ProbablePrime.status; split <;> decide

/-- The test's result, zero-extended, into `fRes`. -/
theorem testRes_vp {c' : Cfg} {res : Option (Bool × Spec.RsaKeyGen.Rand)} :
    VP (fun σ t => St G c' X σ t ∧ ((t.gpr .r3).setWidth 32).toNat = Proof.Dsa.ProbablePrime.status res)
      (.block [.lsr .w .r3 .r3 0, st .r3 fRes])
      (fun σ t => St G (c'.setV fRes (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
        t.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res)) := by
  refine VP.pub (SS.pub (c := fun _ => c') fun σ s h => h.1.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.lsr .w .r3 .r3 0, st .r3 fRes]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  obtain hv : ((s.gpr .r3).setWidth 32 >>> 0).setWidth 64 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ushiftRight_zero, BitVec.toNat_setWidth, r3, BitVec.toNat_ofNat]
  refine WP.wr (exec_lsr_w (by decide)) fun s₁ u₁ sp₁ _ => ?_
  obtain h₁ := h.of_upd u₁ sp₁ (by decide)
  refine h₁.stF varOk_fRes fun t ht m _ => WP.block_nil ⟨⟨?_, x⟩, ?_⟩
  · rw [u₁.gpr, hv] at ht; exact ht
  · rw [m.gpr, u₁.gpr, hv]

/-- `fUsed` := the witnesses read, unless the tape ran out. -/
theorem testTail_vp {cl' : Claims} {u cand : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU88 : fUsedOut ∉ c.LS) (hwl : G.witB.length = G.witLen) (hu : u ≤ G.witLen) :
    VP (fun σ t => St G ((callCfg c cl' G.witLen u (Spec.Dsa.probablePrime cand (G.witB.drop u))).setV fRes
        (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.witB.drop u))))) X σ t ∧
        t.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.witB.drop u))))
      (.ite (.zero .d .r3) (.block []) (.block [ld .r4 fUsedOut, ld .r5 fUsed, .add .r5 .r5 .r4, st .r5 fUsed]))
      (St G (testCfg c cl' G.witLen (Spec.Dsa.probablePrime cand (G.witB.drop u))) X) := by
  generalize hres : Spec.Dsa.probablePrime cand (G.witB.drop u) = res
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, r3⟩, z⟩ => ?_
    rw [eval_zero, r3, ofNat_beq_zero (by have := status_lt res; omega_using [this])] at z
    rcases res with _ | ⟨b, rest⟩
    · exact ⟨h, x⟩
    · cases b <;> simp [Proof.Dsa.ProbablePrime.status] at z
  rcases res with _ | ⟨b, rest⟩
  · exact VP.of_false fun σ s ⟨⟨_, r3⟩, z⟩ => by
      rw [eval_zero, r3] at z; simp [Proof.Dsa.ProbablePrime.status] at z
  -- The tape sufficed: `fUsed` := `u` and the count.
  obtain rl : rest.length ≤ G.witLen - u := by
    have := (VG.Proof.Dsa.Generation.probablePrime_suffix hres).length_le
    rw [List.length_drop, hwl] at this; exact this
  let x : BitVec 64 := BitVec.ofNat 64 (G.witLen - u - rest.length)
  let st0 : BitVec 64 := BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (some (b, rest)))
  let c6 : Cfg := ({ c with cl := cl' }.setV fUsedOut x).setV fRes st0
  obtain v88 : c6.V fUsedOut = x := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsedOut = x; rw [upd_ne _ _ (by decide), upd_self]
  obtain vU : c6.V fUsed = BitVec.ofNat 64 u := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsed = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hUv]
  refine VP.pub (SS.pub (c := fun _ => c6) fun σ s h => h.1.1.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [ld .r4 fUsedOut, ld .r5 fUsed, .add .r5 .r5 .r4, st .r5 fUsed]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, xx⟩, _⟩, _⟩ => ?_
  change SS G 176 σ c6 s at h
  refine WP.sp_eq (h.ldK (o := fUsedOut) (by decide) (by decide) ((h.gi.slotV (by simp [c6])).trans v88)
    (by decide) fun s₁ h₁ u₁ => ?_)
  refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.gi.slotV (by simp [c6, hU])).trans vU) (by decide)
    fun s₂ h₂ u₂ => ?_
  refine WP.wr exec_add fun s₃ u₃ sp₃ _ => ?_
  obtain h₃ := h₂.of_upd u₃ sp₃ (by decide)
  refine h₃.stF varOk_fUsed fun t ht _ _ => WP.block_nil fun _ => ⟨?_, xx⟩
  obtain v5 : s₃.gpr .r5 = BitVec.ofNat 64 (G.witLen - rest.length) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    show BitVec.ofNat 64 u + BitVec.ofNat 64 (G.witLen - u - rest.length) = _
    rw [← BitVec.ofNat_add, show u + (G.witLen - u - rest.length) = G.witLen - rest.length by omega_using [hu, rl]]
  rw [v5] at ht
  refine ht.mono (fun o ho => ?_) (fun x hx => hx) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  simp only [testCfg, c6, Cfg.setV, List.mem_cons] at ho ⊢
  rcases ho with rfl | rfl | ho
  · exact ⟨by simp, by simp [upd]⟩
  · refine ⟨by simp, ?_⟩
    simp only [upd, show fRes ≠ fUsed by decide, ite_false, ite_true]
    cases b <;> rfl
  · refine ⟨by simp [ho], ?_⟩
    obtain n88 : o ≠ fUsedOut := fun e => hU88 (e ▸ ho)
    obtain e : st0 = BitVec.ofNat 64 (if b then 1 else 2) := by cases b <;> rfl
    simp only [upd, n88, ite_false, e]

/-! ## The test -/

/-- The stage after copying the candidate `cb` from `src` to byte `cand` of
the working space of the functions we call. -/
abbrev candCfg (G : GP) (c : Cfg) (cand : Nat) (cb : List Byte) : Cfg :=
  { c with cl := (wB G.pLen + cand, cb) :: c.cl.filter fun x => decide (Apart (wB G.pLen + cand) cb.length x) }

/-- The test of the candidate at `src` (`cb`), copied to the test's working
space, with the tape from `fUsed`: its result in `fRes` and the witnesses it
read in `fUsed`. -/
theorem test_vp {L : Impl.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u src : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 64 u) (hwl : G.witB.length = G.witLen)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : L.candidate + L.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + L.candidate < 2 ^ 15)
    (hsrc : (src, cb) ∈ c.cl) (hsrcK : src + cb.length ≤ kB G.pLen) (hcbl : cb.length = L.bits / 8) (hn0 : 0 < cb.length) (hn15 : cb.length < 2 ^ 15)
    (hs15 : src < 2 ^ 15) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ (candCfg G c L.candidate cb).cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (St G c X) (test G.pLen L.candidate src cb.length name code)
      (St G (testCfg c cl' G.witLen (tRes G cb u)) X) := by
  obtain hc0 : ∀ σ s, St G c X σ s → wB G.pLen + L.candidate + cb.length ≤ G.scrLen * 8 := fun σ s ⟨h, _⟩ => by
    have := h.gi.wBig; omega_using [hcand, hcbl, this]
  refine VP.seq (G := St G (candCfg G c L.candidate cb) X)
    (copyS_vp (c := fun _ => c) (fun σ s h => h.1) hn0 hn15 hcand15 hs15
      (fun σ s h => ⟨by have := h.1.gi.kBig; simp only [hEnd, wB, kB, pB, fSave] at this ⊢; omega_using [], by
        simp only [List.length_replicate]; exact .inr (by omega_using []), by simp only [List.length_replicate]; exact hc0 σ s h⟩)
      (fun σ s h => by have := (h.1.clOk _ hsrc).2.2; exact this)
      (.inr (by have := (show kB G.pLen ≤ wB G.pLen by simp only [wB]; omega_using []); omega_using [hsrcK, this]))
      fun σ s t ⟨h, x⟩ h' _ b => ⟨?_, x⟩) ?_
  · refine ⟨h'.gi, h'.sb.cons (by rw [b]; have := h.sb _ hsrc; rw [this]), fun y hy => ?_, h'.arrs, h'.liveOk,
      h'.ksl, h'.kslOk⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨by have := h.gi.kBig; simp only [hEnd, wB, kB, pB, fSave] at this ⊢; omega_using [], .inr (by omega_using []),
        hc0 σ s ⟨h, x⟩⟩
    · exact h'.clOk y hy
  refine VP.assoc (VP.seq (targs_vp (c := candCfg G c L.candidate cb) hu hU hUv)
    (VP.seq (primeCall_vp (c := candCfg G c L.candidate cb) (cl' := cl') (name := name) ok hu hsize hL
      List.mem_cons_self hcbl hodd hbl hU' hcl)
      (VP.seq testRes_vp (testTail_vp (c := candCfg G c L.candidate cb) hU hUv hU88 hwl hu))))

end

end VG.Proof.Dsa.PPC64LE.Gen
