module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Body
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Draw
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Result
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # `vg_ffdh_parameter_candidate_sieved` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The contract, with RSA's table of primes as the constants. -/
abbrev contract : Contract isa :=
  Proof.Ffdh.sievedParameterCandidateContract (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) stack

/-- The table's region. -/
abbrev tableR (s : State) : Region := ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩

abbrev outR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev usedR (s : State) : Region := ⟨argumentPointer s 2, 8⟩
abbrev randR (s : State) : Region := ⟨argumentPointer s 5, (arg s 6).toNat⟩
abbrev wsR (s : State) : Region := ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
abbrev argsR (s : State) : Region := ⟨argAddr s 0, 36⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev belowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩

/-- What the contract gives `vg_ffdh_parameter_candidate_sieved(out, out_len, used, bits, generator,
rand, rand_len, scratch, scratch_len)`. -/
structure CandABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  held : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)],
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint (retR s) ∧ t.Disjoint (belowR s)
  rdPrefix : s.rd.take (s.rd.length - 1) = [randR s]
  wr : s.wr = [outR s, usedR s, wsR s, argsR s]
  outUsed : (outR s).Disjoint (usedR s)
  outRand : (outR s).Disjoint (randR s)
  outWs : (outR s).Disjoint (wsR s)
  outArgs : (outR s).Disjoint (argsR s)
  usedRand : (usedR s).Disjoint (randR s)
  usedWs : (usedR s).Disjoint (wsR s)
  usedArgs : (usedR s).Disjoint (argsR s)
  randWs : (randR s).Disjoint (wsR s)
  randArgs : (randR s).Disjoint (argsR s)
  wsArgs : (wsR s).Disjoint (argsR s)
  retOut : (retR s).Disjoint (outR s)
  retUsed : (retR s).Disjoint (usedR s)
  retRand : (retR s).Disjoint (randR s)
  retWs : (retR s).Disjoint (wsR s)
  retArgs : (retR s).Disjoint (argsR s)
  belowOut : (belowR s).Disjoint (outR s)
  belowUsed : (belowR s).Disjoint (usedR s)
  belowRand : (belowR s).Disjoint (randR s)
  belowWs : (belowR s).Disjoint (wsR s)
  belowArgs : (belowR s).Disjoint (argsR s)
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  randBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  wsBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  bitsLow : 512 ≤ (arg s 3).toNat
  bitsHigh : (arg s 3).toNat ≤ 8192
  outLen : (arg s 1).toNat = ((arg s 3).toNat + 7) / 8
  gen : (arg s 4).toNat = 2 ∨ (arg s 4).toNat = 5
  scratchLength : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s 8).toNat

theorem candABI_of {s : State} (h : contract.pre s) : CandABI s := by
  sig_pre [contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argSlots,
    argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem wrapABI {s : State} (A : CandABI s) : WrapABI Impl.Ffdh.X86.Candidate.args 9 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h),
    (fun _ h => by cases h), by decide⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by
    rw [A.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  wsIn := by
    show (⟨argumentPointer s 7, (arg s 8).toNat * 8⟩ : Region) ∈ _
    rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  scratchArgs := A.wsArgs
  retScratch := A.retWs
  belowScratch := A.belowWs
  scratchBound := A.wsBound
  lower := by have := A.bitsLow; have := A.outLen; show 64 ≤ (arg s 1).toNat; omega
  upper := by have := A.bitsHigh; have := A.outLen; show (arg s 1).toNat ≤ 1024; omega
  scratchLength := A.scratchLength

/-- The 40 bytes below the frame, and the frame, below the caller's stack pointer. -/
theorem frame_subs {s : State} (A : CandABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) :
    Region.Sub (below sp 96) (belowR s) ∧ Region.Sub ⟨sp.setWidth 64, 76⟩ (belowR s) := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  refine ⟨?_, ?_⟩
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  · rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)

/-- What the body may read: the tape, the arguments and the table; and write: `out` and `used`. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 5) (arg s 6).toNat ∧
    InRegions wr (argumentPointer s 0) (arg s 1).toNat ∧ InRegions wr (argumentPointer s 2) 8 ∧
    InRegions (rd ++ wr) (argAddr s 0) 36 ∧ InRegions (rd ++ wr) (tableR s).base 8192

theorem table_eq (s : State) : Abi.constRegions (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] = [tableR s] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem rd_of {s : State} (A : CandABI s) : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
  have rd : s.rd = [randR s, tableR s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, A.rdPrefix, A.rdTable, table_eq]; rfl
  have wr := A.wr
  refine ⟨⟨randR s, by rw [rd]; simp, Region.contains_self _ _⟩, ⟨outR s, by rw [wr]; simp, Region.contains_self _ _⟩,
    ⟨usedR s, by rw [wr]; simp, Region.contains_self _ _⟩, ⟨argsR s, by rw [wr]; simp, Region.contains_self _ _⟩,
    ⟨tableR s, by rw [rd]; simp, Region.contains_self _ _⟩⟩

/-- The tape at entry. -/
abbrev entryRand (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat

/-- What the contract asks of the status, `out` and `used`. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  r.toNat = Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate (arg s 3).toNat (arg s 4).toNat
      (entryRand s)) ∧
    Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 1).toNat =
      (match Spec.Ffdh.sievedParameterCandidate (arg s 3).toNat (arg s 4).toNat (entryRand s) with
        | some (some p, _) => Spec.Rsa.i2osp p (arg s 1).toNat
        | _ => List.replicate (arg s 1).toNat 0) ∧
    Spec.Rsa.wordsAt m (argumentPointer s 2) 1 =
      [BitVec.ofNat 64 (match Spec.Ffdh.sievedParameterCandidate (arg s 3).toNat (arg s 4).toNat (entryRand s) with
        | some (_, rest) => (arg s 6).toNat - rest.length
        | none => 0)]

theorem ofn (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem held_word {m : Mem} {f : String → Addr} {tables : List (String × List (BitVec 64))}
    {name : String} {words : List (BitVec 64)} (H : Abi.constsHeld m f tables)
    (member : (name, words) ∈ tables) {i : Nat} (bound : i < words.length) :
    m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words[i] := by
  rw [H (name, words) member i bound, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]

/-- What the body needs of the frame's state `f`, for the tape `T`, `used` at `up` and RSA's table at
`Tb`. -/
structure Facts (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (T : List Byte) (up Tb : BitVec 32) (bits g : Nat) (f : State) : Prop where
  esp : f.gpr .esp = sp
  G : TapeGeo Ex args base bytes sp T.length
  hT : Spec.Rsa.bytesAt f.mem (byteAddr (args 2)) T.length = T
  Ox : OutAt args base bytes len 0 sp f.wr
  U : UsedAt base bytes up sp ⟨byteAddr (args 0), len⟩ f.wr
  h3 : args 3 = BitVec.ofNat 32 len
  rb : readSrc f (.mem (argAt 19 3)) = some (BitVec.ofNat 32 bits)
  rg : readSrc f (.mem (argAt 19 4)) = some (BitVec.ofNat 32 g)
  ru : readSrc f (.mem (argAt 19 2)) = some up
  dws : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨f.ea (argAt 19 j), 4⟩ ⟨base, bytes⟩
  d40 : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨f.ea (argAt 19 j), 4⟩ (below sp 96)
  TT : Table Tb sp f
  TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩

/-- The frame's state, with what the body needs. -/
theorem frame_facts {s : State} (A : CandABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
      (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) (syf : f.syms = s.syms) :
    Facts (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
      (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryRand s) (arg s 2)
      (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) (arg s 3).toNat (arg s 4).toNat f := by
  obtain ⟨sub40, subF⟩ := frame_subs A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have top := A.stackBound
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  have frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ (belowR s) := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have ex := I.extra
  have Tlen : (entryRand s).length = (arg s 6).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  -- What keeps its bytes from entry to the frame's state.
  have keep : ∀ {r : Region}, r.Disjoint (wsR s) → r.Disjoint (belowR s) → r.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt f.mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := fun hw hb hn =>
    frame_bytes Ft (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hw
      · exact hb.sub_right frameSub) hn
  have G : TapeGeo (Rd s) (synth Impl.Ffdh.X86.Candidate.args (arg s)) (wsBase Impl.Ffdh.X86.Candidate.args s)
      (wsSize Impl.Ffdh.X86.Candidate.args s) (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryRand s).length := by
    rw [Tlen]
    exact ⟨(ofn _).symm, (arg s 6).isLt, A.randBound, fun _ _ h => h.1, A.randWs,
      (A.belowRand.sub_left sub40).symm⟩
  have hT : Spec.Rsa.bytesAt f.mem (byteAddr (synth Impl.Ffdh.X86.Candidate.args (arg s) 2)) (entryRand s).length =
      entryRand s := by
    rw [Tlen]; exact keep A.randWs A.belowRand.symm (by show (arg s 6).toNat ≤ 2 ^ 64; have := (arg s 6).isLt; omega_arith)
  have Ox : OutAt (synth Impl.Ffdh.X86.Candidate.args (arg s)) (wsBase Impl.Ffdh.X86.Candidate.args s)
      (wsSize Impl.Ffdh.X86.Candidate.args s) (pLenOf Impl.Ffdh.X86.Candidate.args s) 0 (s.gpr .esp - BitVec.ofNat 32 argsFrame) f.wr :=
    ⟨A.outBound, ex.2.1, A.outWs.symm, (A.belowOut.sub_left subF), (A.belowOut.sub_left sub40).symm⟩
  have U : UsedAt (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s) (arg s 2)
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) ⟨byteAddr (synth Impl.Ffdh.X86.Candidate.args (arg s) 0),
        pLenOf Impl.Ffdh.X86.Candidate.args s⟩ f.wr :=
    ⟨A.usedBound, ex.2.2.1, A.usedWs.symm, A.belowUsed.sub_left subF, (A.belowUsed.sub_left sub40).symm, A.outUsed⟩
  -- The function's arguments, above the frame.
  have ea : ∀ j, j < 9 → f.ea (argAt 19 j) = argAddr s j := by
    intro j hj
    simp only [State.ea, argAt, at_, espf, argAddr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, argsFrame]
    omega_arith
  have aa : ∀ j, j < 9 → argAddr s j = argAddr s 0 + BitVec.ofNat 64 (4 * j) := by
    intro j hj
    rw [show argAddr s j = addr (s.gpr .esp) (4 + 4 * j) from rfl, show argAddr s 0 = addr (s.gpr .esp) (4 + 4 * 0) from rfl,
      addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_add]
  have sub : ∀ j, j < 9 → Region.Sub ⟨argAddr s j, 4⟩ (argsR s) := fun j hj => by
    rw [aa j hj]; exact Offset.sub_base _ (by omega_arith)
  have rd : ∀ j, j < 9 → readSrc f (.mem (argAt 19 j)) = some (arg s j) := by
    intro j hj
    have ir : InRegions (f.rd ++ f.wr) (argAddr s j) 4 := by
      rw [aa j hj]; exact VG.CallLay.inRegions_sub ex.2.2.2.1 (by omega_arith) (by decide)
    simp only [readSrc, State.load32, ea j hj]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ir)]
    exact congrArg some (Ft.readW (r := ⟨argAddr s j, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact A.wsArgs.symm.sub_left (sub j hj)
      · exact (A.belowArgs.symm.sub_left (sub j hj)).sub_right frameSub) (by decide))
  have dws : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨f.ea (argAt 19 j), 4⟩
      ⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩ := fun j hj => by
    have : j < 9 := by simp at hj; omega_arith
    rw [ea j this]; exact A.wsArgs.symm.sub_left (sub j this)
  have d40 : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨f.ea (argAt 19 j), 4⟩ (below (s.gpr .esp - BitVec.ofNat 32 argsFrame) 96) := fun j hj => by
    have : j < 9 := by simp at hj; omega_arith
    rw [ea j this]; exact (A.belowArgs.symm.sub_left (sub j this)).sub_right sub40
  -- RSA's table.
  have tf := A.tableFar (tableR s) (by rw [table_eq]; exact List.mem_singleton_self _)
  have tw : wsR s ∈ s.wr := by rw [A.wr]; simp
  have T32 := (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).isLt
  have tb : ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64).toNat =
      (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]
  have tfit : (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).toNat + 8192 ≤ 2 ^ 32 := by
    have : ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64).toNat + 8192 ≤ 2 ^ 32 := tf.1
    omega_arith
  have TT : Table (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) (s.gpr .esp - BitVec.ofNat 32 argsFrame) f := by
    refine ⟨by rw [syf], fun i hi d hd => ?_, fun i hi => ?_, tfit, tf.2.2.2.sub_right sub40⟩
    · have hd4 : d ≤ 4 := by simp at hd; omega_arith
      have e : addr (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol + BitVec.ofNat 32 (8 * i)) d =
          (tableR s).base + BitVec.ofNat 64 (8 * i + d) := by
        apply BitVec.eq_of_toNat_eq
        simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega_arith
      rw [e]; exact VG.CallLay.inRegions_sub ex.2.2.2.2 (by omega_arith) (by decide)
    · rw [Ft.readW (r := tableR s) (Offset.contains_base _ (by omega_arith : 8 * i + 8 ≤ 8192) (by omega_arith)) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact tf.2.1 _ tw
        · exact tf.2.2.2.sub_right frameSub) (by decide)]
      have bound : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
        rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact hi
      exact (held_word A.held List.mem_cons_self bound).trans (VG.Proof.RsaKeyGen.TrialTable32.packed_entry hi)
  have TA : Region.Disjoint ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩
      ⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩ := tf.2.1 _ tw
  refine ⟨espf, G, hT, Ox, U, (ofn _).symm, by rw [ofn]; exact rd 3 (by decide), by rw [ofn]; exact rd 4 (by decide),
    rd 2 (by decide), dws, d40, TT, TA⟩

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CandABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
      (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) (syf : f.syms = s.syms) :
    WP isa Impl.Ffdh.X86.Candidate.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([outR s, usedR s] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.Candidate.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.Candidate.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  have F := frame_facts A f I espf Ft syf
  have Tlen : (entryRand s).length = (arg s 6).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  rw [← espf] at F
  have ef := F.esp
  have hst : ∀ x : Option (Option Nat × Spec.RsaKeyGen.Rand), Proof.Ffdh.candidateStatus x < 2 ^ 32 := by
    intro x
    have : Proof.Ffdh.candidateStatus x ≤ 2 := by unfold Proof.Ffdh.candidateStatus; split <;> omega
    omega
  refine WP.mono (body_ok I F.G F.hT F.Ox F.U F.h3 F.rb F.rg F.ru F.dws F.d40
    A.outLen A.bitsLow A.bitsHigh A.gen F.TT F.TA) fun t R => ⟨⟨?_, ?_, ?_⟩, R.frame, R.keeps⟩
  · rw [R.eax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hst _)]
  · refine R.bytes.trans ?_
    generalize Spec.Ffdh.sievedParameterCandidate (arg s 3).toNat (arg s 4).toNat (entryRand s) = r
    rcases r with _ | ⟨_ | p, r⟩ <;> rfl
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
      BitVec.add_zero]
    refine congrArg (· :: []) (R.used.trans ?_)
    generalize Spec.Ffdh.sievedParameterCandidate (arg s 3).toNat (arg s 4).toNat (entryRand s) = r
    rcases r with _ | ⟨x, r⟩
    · rfl
    · simp only [candUsed, Tlen]

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.Candidate.args)) Impl.Ffdh.X86.Candidate.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

theorem operation_ok {s : State} (A : CandABI s) :
    WP isa Impl.Ffdh.X86.Candidate.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u :=
  wrap_syms_ok (wrapABI A) (NoSp.of_all frameBody_all) (rd_of A) (Out := [outR s, usedR s])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.retOut
      · exact A.retUsed)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.outWs.symm
      · exact A.usedWs.symm)
    (P := fun m e => spec s m e) fun f I espf Ft syf => frame_ok A f I espf Ft syf

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Candidate.code s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (candABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argSlots,
    argVal, argBytes, Abi.withConsts]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Ffdh.X86.Cand
