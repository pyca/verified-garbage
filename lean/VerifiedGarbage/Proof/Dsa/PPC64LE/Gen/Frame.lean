module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
