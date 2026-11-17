module

public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall

/-! ### `RsaOaep.X86_64.PcTab`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.X86_64.PcCtx`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩

/-- All nine stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- The precondition of the original function, and the cache. -/
structure PPre (H : Spec.Mgf1.Hash) (s : State) : Prop extends EPre H s where
  sp3 : (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 80
  pre : InRegions s.rd (stackArg s 8) ((stackArg s 9).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 9).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem stackArgs_twelve (s : State) :
    (List.range 12).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
      stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11] := rfl

/-- MGF1's table. -/
def tabE (s : State) : Region := ⟨stackArg s 11, 88⟩

/-- All ten stack arguments. -/
def argsT (s : State) : Region := ⟨stackArgAddr s 0, 96⟩

/-- The functions of the tables `ts`. -/
def tabFnsE (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

/-- The contract, with the tables `ts` for both hash functions. -/
abbrev encC (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.encryptMdTablesContract (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", ts), ("mgf1", ts)])
    encStack

/-- The table of the label's hash function. -/
def tabLE (s : State) : Region := ⟨stackArg s 10, 88⟩

/-- `PPre`, with the tables: the label's hash function's (the stack argument
10) and MGF1's (11). -/
structure PPreT (H : Spec.Mgf1.Hash) (s : State) : Prop extends PPre H s where
  sp4 : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  argsT' : InRegions s.rd (stackArgAddr s 0) 96
  tab : InRegions s.rd (stackArg s 11) 88
  argsTOut : (argsT s).Disjoint (outR s)
  argsTScr : (argsT s).Disjoint (scrR s)
  argsTStack : (argsT s).Disjoint (stkR s)
  tabOut : (tabE s).Disjoint (outR s)
  tabScr : (tabE s).Disjoint (scrR s)
  tabStack : (tabE s).Disjoint (stkR s)
  tabWrap : (stackArg s 11).toNat + 88 ≤ 2 ^ 64
  tabL : InRegions s.rd (stackArg s 10) 88
  tabLOut : (tabLE s).Disjoint (outR s)
  tabLScr : (tabLE s).Disjoint (scrR s)
  tabLStack : (tabLE s).Disjoint (stkR s)
  tabLWrap : (stackArg s 10).toNat + 88 ≤ 2 ^ 64

/-- The tables: each one of `ts`. -/
theorem tabs_of {ts : List FnTable} {s : State} (h : (encC ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 10) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 11) (FnTable.words isa s T)) ∧
      (tabFnsE ts).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    encStack, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
  obtain ⟨-, -, t1, t2, fnd, -⟩ := h
  exact ⟨t1, t2, fnd.sublist (List.sublist_append_left _ _)⟩

/-- The precondition, for the hash function `H` that the table `hash` names. -/
theorem preT_of {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (encC ts).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 10) = some H) : PPreT H s := by
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    encStack, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp3 _ _ _ hrd hwr dOn dOe dOl dOm dOsd dOs dOq dOtL dOt dOa dns des dls dms
    dsds dsq dstL dst dsa dRo dRn dRe dRl dRm dRsd dRs _ _ _ dRa dKo dKn dKe dKl dKm dKsd
    dKs dKq dKtL dKt dKa wO wN wE wL wM wSd wS wQ wTL wT k12 hsi L1 L2 hsl pl
  obtain ⟨k1, k2⟩ := k12
  have hl := h H hH
  rw [hl] at hrd dOsd dsds dRsd dKsd wSd
  have ha : Region.Sub ⟨stackArgAddr s 0, 64⟩ ⟨stackArgAddr s 0, 96⟩ := Region.sub_prefix (by decide)
  have hb : Region.Sub ⟨stackArgAddr s 0, 80⟩ ⟨stackArgAddr s 0, 96⟩ := Region.sub_prefix (by decide)
  have hA : InRegions s.rd (stackArgAddr s 0) 96 := ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  refine ⟨⟨⟨sp1, by omega_using [sp3], ?_, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOa.sub_right ha, dns, des, dls, dms, dsds,
    dsa.sub_right ha, dRo, dRn, dRe, dRl, dRm, dRsd, dRs, dRa.sub_right ha, dKo, dKn, dKe, dKl, dKm, dKsd, dKs,
    dKa.sub_right ha, wO, wN, wE, wL, wM, wSd, wS, k1, k2, hsi, L1, L2,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hsl; omega_using [hsl]⟩,
    by omega_using [sp3], ?_, ?_, (dOa.sub_right hb).symm, (dsa.sub_right hb).symm, (dKa.sub_right hb).symm, dOq.symm,
    dsq.symm, dKq.symm, wQ, pl⟩, sp3, hA, ⟨_, by rw [hrd]; simp [Sig.tableRegion], Region.contains_self _ _⟩,
    dOa.symm, dsa.symm, dKa.symm, dOt.symm, dst.symm, dKt.symm, wT,
    ⟨_, by rw [hrd]; simp [Sig.tableRegion], Region.contains_self _ _⟩, dOtL.symm, dstL.symm, dKtL.symm, wTL⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [rdL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 96⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨⟨stackArgAddr s 0, 96⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaOaep.X86_64.Pc

end

end

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: MGF1's table

From a state in the frame (`EnvE`) naming the entry state's addresses of
statics, the table that the stack argument 9 points to as MGF1 needs it
(`Table.Tab`), as for decryption (`DecTab.lean`): the table and the stack
arguments are apart from everything the code writes (`etab`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.RsaOaep.X86_64.Table (Tab TabOK TabMem)

/-- A word of a region apart from what the code writes, in memory it may
leave. -/
theorem FrE.readW' {s : State} {m : Mem} (h : FrE s m) {r : Region} {a : Addr}
    (hc : r.Contains a 8) (hk : r.Disjoint (stkR s)) (ho : r.Disjoint (outR s)) (hs : r.Disjoint (scrR s)) :
    m.readW a 64 = s.mem.readW a 64 :=
  Frame.readW h hc (fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hk
    · exact ho
    · exact hs) (by decide)

/-- The table at the stack argument `j`, from the entry state's. -/
theorem etabJ {H : Spec.Mgf1.Hash} {s t : State} (hp : PPreT H s) (he : EnvE s t) (hsy : t.syms = s.syms)
    {G : Stream} {f : Fns} {j : Nat} (hj : j < 12) (hT : InRegions s.rd (stackArg s j) 88)
    (wT : (stackArg s j).toNat + 88 ≤ 2 ^ 64) (dK : (⟨stackArg s j, 88⟩ : Region).Disjoint (stkR s))
    (dO : (⟨stackArg s j, 88⟩ : Region).Disjoint (outR s)) (dS : (⟨stackArg s j, 88⟩ : Region).Disjoint (scrR s))
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s j) s.mem)
    (hD : s.mem.readW (off (stackArg s j) 48) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s j) (frameBytes + 8 + 8 * j) t := by
  have hsp := hp.sp4
  have cT : ∀ d, d + 8 ≤ 88 → (⟨stackArg s j, 88⟩ : Region).Contains (off (stackArg s j) d) 8 := fun d hd =>
    Offset.contains_base _ hd (by have := wT; omega_using [hd])
  have cA : (argsT s).Contains (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  have rT : ∀ d, d + 8 ≤ 88 → InRegions (t.rd ++ t.wr) (off (stackArg s j) d) 8 := fun d hd => by
    rw [he.rd]; exact Covers.left (Covers.one hT) _ _ ⟨_, List.mem_singleton_self _, cT d hd⟩
  have rA : InRegions (t.rd ++ t.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [he.rd]; exact Covers.left (Covers.one hp.argsT') _ _ ⟨_, List.mem_singleton_self _, cA⟩
  refine ⟨by rw [hsy]; exact ok, fun i hi => rT _ (by omega_using [hi]), rT 48 (by omega_using []), rA, fun m hf => ?_⟩
  have hF : FrE s m := FrE.step he.fr he.wr hf
  have rt : ∀ d, d + 8 ≤ 88 → m.readW (off (stackArg s j) d) 64 = s.mem.readW (off (stackArg s j) d) 64 :=
    fun d hd => FrE.readW' hF (cT d hd) dK dO dS
  rw [hsy]
  refine ⟨⟨(rt _ (by omega_using [])).trans hm.1, (rt _ (by omega_using [])).trans hm.2.1, (rt _ (by omega_using [])).trans hm.2.2⟩,
    (rt 48 (by omega_using [])).trans hD, ?_⟩
  rw [FrE.readW' hF cA hp.argsTStack hp.argsTOut hp.argsTScr, argAddr]
  rfl

/-- MGF1's table, from the entry state's. -/
theorem etab {H : Spec.Mgf1.Hash} {s t : State} (hp : PPreT H s) (he : EnvE s t) (hsy : t.syms = s.syms)
    {G : Stream} {f : Fns} (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 11) s.mem)
    (hD : s.mem.readW (off (stackArg s 11) 48) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 11) (frameBytes + 8 + 8 * 11) t :=
  etabJ hp he hsy (by decide) hp.tab hp.tabWrap hp.tabStack hp.tabOut hp.tabScr ok hm hD

/-- The table of the label's hash function, from the entry state's. -/
theorem etabL {H : Spec.Mgf1.Hash} {s t : State} (hp : PPreT H s) (he : EnvE s t) (hsy : t.syms = s.syms)
    {G : Stream} {f : Fns} (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 10) s.mem)
    (hD : s.mem.readW (off (stackArg s 10) 48) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t :=
  etabJ hp he hsy (by decide) hp.tabL hp.tabLWrap hp.tabLStack hp.tabLOut hp.tabLScr ok hm hD

end VG.Proof.RsaOaep.X86_64.Pc

end

end

/-! ### `RsaOaep.X86_64.PcCorrect`, which only this module used -/

section

/-! ### `RsaOaep.X86_64.PcCall`, which only this module used -/

section

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: the call

The original arguments of the public operation, then `pre` and `pre_len`
from the stack arguments 7 and 8 (`pubArgs_ok`); the precondition of
`vg_rsa_public_precomputed_checked` (`call_pre`), and what the call leaves
(`call_ok`): `out` holds RSAEP of `EM` if `pre` holds the values for `n`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

variable {H : Spec.Mgf1.Hash}

/-! ## The arguments -/

theorem arg_in {s t : State} (hp : PPre H s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 10) :
    InRegions (t.rd ++ t.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [argAddr, hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [stackArgAddr_j s j]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem arg_keep {s : State} (hp : PPre H s) {m : Mem} (hf : FrE s m) {j : Nat} (hj : j < 10) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.argsStack
    · exact hp.argsOut
    · exact hp.argsScr

/-- `pre` and `pre_len` in place of `n` and `n_len`. -/
theorem load_pre {s t : State} (hp : PPre H s) (hsp : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hf : FrE s t.mem) :
    WP isa (.block [.mov .rdx (.mem (arg 8)), .mov .rcx (.mem (arg 9))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧ u.gpr .rdx = stackArg s 8 ∧ u.gpr .rcx = stackArg s 9 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  have i8 := arg_in hp hrd (show 8 < 10 by decide)
  have i9 := arg_in hp hrd (show 9 < 10 by decide)
  have r8 := arg_keep hp hf (show 8 < 10 by decide)
  have r9 := arg_keep hp hf (show 9 < 10 by decide)
  xrun [arg, ea_sp, hsp, i8, i9, r8, r9]

/-! ## The call -/

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, `EM` and its
stack arguments. -/
def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (stackArg s 6) oEm, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

theorem call_pre {s t : State} (hp : PPre H s) (hsp : t.gpr .rsp = fb s)
    (hw0 : t.mem.readW (off (fb s) (8 * 0)) 64 = off (stackArg s 6) oEm) (hw1 : t.mem.readW (off (fb s) (8 * 1)) 64 = s.gpr .rcx)
    (hw2 : t.mem.readW (off (fb s) (8 * 2)) 64 = off (stackArg s 6) oRsa)
    (hw3 : t.mem.readW (off (fb s) (8 * 3)) 64 = stackArg s 7 - 1024)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 8)
    (hcx : t.gpr .rcx = stackArg s 9) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  have hF := fb_toNat hp.toEPre
  have hsp1 := hp.sp1; have hsp2 := hp.sp2
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = t.mem.readW (off (fb s) (8 * i)) 64 :=
    fun i hi => stackArg_entry hsp (by unfold encStack frameBytes at *; omega_using [hF, hsp1]) _ _ (by unfold frameBytes at *; omega_using [hF, hi])
  have hA : stackArgAddr (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = fb s := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
    rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp, hA,
    hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hw0, hw1, hw2, hw3]
  have hsi' := hp.hsi
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have ⟨r1, r2⟩ := rsa_toNat hp.toEPre
  have e8 : fb s - 8 = fb s - BitVec.ofNat 64 8 := rfl
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) = outR s := by simp [outR, hsi']
  have sF : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := Offset.sub_below (s.gpr .rsp) (a := frameBytes) (n := 32) (b := encStack) (m := encStack)
      (by decide) (by decide)
    exact this
  have sR : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := by
    rw [e8]
    exact fun x h => ret_sub s x (Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide)
      (by decide) x h)
  have dRF : Region.Disjoint ⟨fb s - 8, 8⟩ ⟨fb s, 32⟩ := by
    rw [e8]; exact (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega_using [])).symm
  have dEmR : Region.Disjoint ⟨off (stackArg s 6) oEm, (s.gpr .rcx).toNat⟩ (rsaR s) := by
    simp only [rsaR]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega_using [hk2])) (by unfold oEm; omega_using []) (by unfold oRsa; omega_using [wS])
  have em := em_sub hp.toEPre
  have rs := rsa_sub hp.toEPre
  have dSo : (scrR s).Disjoint (outR s) := hp.d_out_scr.symm
  have dSk : (scrR s).Disjoint (stkR s) := hp.d_stk_scr.symm
  have hf8 : (fb s - 8).toNat = (fb s).toNat - 8 := by
    rw [e8, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega_using [hF, hsp1]
  have dOF : (outR s).Disjoint ⟨fb s, 32⟩ := hp.d_stk_out.symm.sub_right sF
  refine ⟨by rw [hf8]; unfold frameBytes at *; omega_using [hF], rfl, rfl,
    by rw [hout]; exact hp.preOut.symm, by rw [hout]; exact hp.d_out_e, by rw [hout]; exact dSo.symm.sub_right em,
    by rw [hout]; exact dSo.symm.sub_right rs, by rw [hout]; exact dOF,
    hp.preScr.sub_right rs, hp.d_e_scr.sub_right rs, dEmR, (dSk.sub_right sF).sub_left rs,
    by rw [hout]; exact (hp.d_stk_out).sub_left sR, hp.preStack.symm.sub_left sR, hp.d_stk_e.sub_left sR,
    (dSk.symm.sub_left sR).sub_right em, (dSk.symm.sub_left sR).sub_right rs, dRF,
    by rw [← hsi']; exact hp.wO, hp.preWrap, hp.wE,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega_using [hsl, wS],
    by rw [r1, r2]; unfold oRsa; omega_using [hsl, wS],
    ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1, hp.L2, by rw [r1]; unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega_using [hsl]⟩

theorem call_covers {s t : State} (hp : PPre H s) (hrd : t.rd = s.rd) (hwr : t.wr = [frR s, outR s, scrR s]) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  obtain ⟨c, cw⟩ := pub_covers hp.toEPre hrd hwr
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) cw.right, cw⟩
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hrd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [pubRd])).trans c
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [pubRd])).trans c
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [pubRd])).trans c

/-- `pre`, unchanged where the function writes. -/
theorem pre_words {s : State} {m : Mem} (hp : PPre H s) (hf : FrE s m) :
    Spec.Rsa.wordsAt m (stackArg s 8) (stackArg s 9).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega_using [this])
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega_arith)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.preStack
    · exact hp.preOut
    · exact hp.preScr

/-- Whether `pre` holds the values for `n`. -/
def Consistent (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat)

/-- The call of `vg_rsa_public_precomputed_checked`: `out` holds RSAEP of
`EM`, or zeros, if `pre` holds the values for `n`. -/
theorem call_ok (v : PublicImpl) {s t : State} (hp : PPre H s) (L : Lay t (fb s) (stackArg s 6)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hrd : t.rd = s.rd)
    (hwr : t.wr = [frR s, outR s, scrR s]) (hf : FrE s t.mem)
    (hw0 : W 0 = off (stackArg s 6) oEm) (hw1 : W 1 = s.gpr .rcx) (hw2 : W 2 = off (stackArg s 6) oRsa)
    (hw3 : W 3 = stackArg s 7 - 1024)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 8)
    (hcx : t.gpr .rcx = stackArg s 9) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call v.name v.code) t fun t' =>
      (Consistent s → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          ((List.range (s.gpr .rcx).toNat).map fun i => V (oEm + i)))) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧ FrE s t'.mem := by
  have hk2 := hp.k2; have hsl := hp.hsl
  obtain ⟨hc, hw⟩ := call_covers hp hrd hwr
  have rd : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = W i := fun i hi => R.rd i rfl (by unfold nW frameBytes; omega_using [hi])
  have hpre := call_pre hp L.rsp ((rd 0 (by decide)).trans hw0) ((rd 1 (by decide)).trans hw1)
      ((rd 2 (by decide)).trans hw2) ((rd 3 (by decide)).trans hw3) hdi hsi hdx hcx h8 h9
  refine WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := callRd s)
    (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_
  intro s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, L.rsp] at hfr
  have hE : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (stackArg s 6) oEm := by
    have hF := fb_toNat hp.toEPre
    rw [stackArg_entry L.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega_using [hF, this]) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega_using [hF])]
    exact (rd 0 (by decide)).trans hw0
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, L.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    hf.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  have hem : Spec.Rsa.bytesAt t.callEntry.mem (off (stackArg s 6) oEm) (s.gpr .rcx).toNat =
      (List.range (s.gpr .rcx).toNat).map fun i => V (oEm + i) := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [off_plus, ← R.scr _ (by unfold oEm oRsa; omega_using [hk2, hi'])]
    have := Frame.bytes hfe (R := ⟨off (stackArg s 6) (oEm + i), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (L.dRS.sub_right (Offset.sub_base _ (by unfold oEm oRsa; omega_using [hk2, hi']))).symm)
      (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
    simp only [BitVec.add_zero] at this
    exact this
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hE, hm₂,
    hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE, FrE.bytes hfE hp.d_stk_e hp.d_out_e hp.d_e_scr.symm (by have := hp.wE; omega_using []), hem]
    at hpost
  refine ⟨fun hq => hpost _ (by simp [Spec.Rsa.bytesAt]) hq, hrd', hwr', hcs, hmx, FrE.step hf (ws := t.wr) hwr ?_⟩
  refine hfr.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨outR s, List.mem_append_left _ (by rw [hwr]; simp), by simp only [outR, hp.hsi]; exact fun _ h => h⟩
    · exact ⟨scrR s, List.mem_append_left _ (by rw [hwr]; simp), rsa_sub hp.toEPre⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨below (fb s) 16, List.mem_append_right _ (List.mem_singleton_self _),
      Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩

end VG.Proof.RsaOaep.X86_64.Pc

end

end


/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: correctness

`EM` built and masked as `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` does
(`encMask_ok`), then the call with `pre` (`encMain_ok`), after the
prologue and the checks (`encBodyWith_ok`): memory safety and the registers
the ABI keeps whatever `pre` holds, and, if `pre` holds the values for `n`,
`encK`'s postcondition (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.HashTable.X86_64 (tables fnsOf Coh tabOK_of held_tableOf hashAt_tableOf fnsGood_of)

/-- `encK`'s postcondition, if `pre` holds the values for `n`. -/
def post (H G : Spec.Mgf1.Hash) (s u : State) : Prop := Consistent s → (encK H G).post s u

/-- `post` for the hash functions the tables name. -/
def postT (s u : State) : Prop :=
  ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 10) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 11) = some G → post H G s u

/-- What the function's caller sees of the registers and the stack, from a
state in the frame. -/
theorem encEnd_abi {H : Spec.Mgf1.Hash} {s s₂ : State} (hp : EPre H s) (he : EnvE s s₂) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧ abiPreserved s (freed frameBytes s₂) := by
  refine ⟨he.rsp, by rw [he.wr, EPre.wr hp], fun r hr => ?_, ?_, he.mx⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show s₂.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else s₂.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact he.cs r hr hr'
  · have hsp2 := hp.sp2
    refine Frame.readW he.fr (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := Offset.disjoint_below (s.gpr .rsp) (n := encStack) (d := 0) (k := 8) (by unfold encStack; omega_using [])
      simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · exact hp.d_ret_out
    · exact hp.d_ret_scr

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH hG mH mG in
theorem encMain_ok (v : PublicImpl) {f : Fns} (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd)
    (hgf : Table.FnsGood f.fin) {s t : State} (hp : PPreT mH.G s) (he : EnvE s t) (hsy : t.syms = s.syms)
    (okL : Table.TabOK Hl.stream f s.syms) (hmL : Table.TabMem Hl.stream s.syms (stackArg s 10) s.mem)
    (hDmL : s.mem.readW (off (stackArg s 10) 48) 64 = BitVec.ofNat 64 Hl.D)
    (ok : Table.TabOK Gm.stream f s.syms) (hm : Table.TabMem Gm.stream s.syms (stackArg s 11) s.mem)
    (hDm : s.mem.readW (off (stackArg s 11) 48) 64 = BitVec.ofNat 64 Gm.D)
    (L : Lay t (fb s) (stackArg s 6)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W)
    (hk : 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa (Impl.RsaOaep.X86_64.Precomputed.encMain Hl.stream f v.name v.code) t fun t' => EnvE s t' ∧
      (Consistent s → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (emOf mG.G Hl.D (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
            (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
            (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)))) := by
  unfold Impl.RsaOaep.X86_64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  refine encMask_ok hH hG mH mG hgi hgu hgf hp.toEPre he hsy (fun t he' sy => etab hp he' sy ok hm hDm)
    (fun t he' sy => etabL hp he' sy okL hmL hDmL) L R hW hk fun t9 V9 W9 he9 L9 R9 W9e hlist => ?_
  refine WP.seq ?_
  rw [Impl.RsaOaep.X86_64.Precomputed.pubArgs, WP.block_append_iff]
  refine WP.mono (wp_good pubArgs_good (pubArgs_ok L9 R9 W9e))
    fun t10 ⟨⟨L10, k10, R10, hdi, hsi, _, _, h8, h9⟩, sp10, mx10, f10⟩ => ?_
  have he10 : EnvE s t10 := he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10
  refine WP.mono (wp_good (block_good _ rfl) (load_pre hp.toPPre he10.rsp he10.rd he10.fr))
    fun t11 ⟨⟨k11, hm11, hdx, hcx⟩, sp11, mx11, f11⟩ => ?_
  have he11 : EnvE s t11 := he10.step k11.2.1 k11.2.2 sp11 (keep_cs3 k11 (by decide)) mx11 f11
  have L11 : Lay t11 (fb s) (stackArg s 6) := L10.congr (k11.gpr (by decide)) k11.2.2 (by rw [hm11])
  refine WP.mono (call_ok v hp.toPPre L11 (hm11 ▸ R10) he11.rd he11.wr he11.fr (by simp [upd]) (by simp [upd])
    (by simp [upd]) (by simp [upd]) ((k11.gpr (by decide)).trans hdi) ((k11.gpr (by decide)).trans hsi) hdx hcx
    ((k11.gpr (by decide)).trans h8) ((k11.gpr (by decide)).trans h9))
    fun t12 ⟨hout, rd12, wr12, cs12, mx12, f12⟩ => ?_
  refine ⟨⟨(cs12 .rsp (by decide)).trans he11.rsp, rd12.trans he11.rd, wr12.trans he11.wr,
    fun r hr h => (cs12 r hr).trans (he11.cs r hr h), mx12.trans he11.mx, f12⟩, fun hq => ?_⟩
  have := hout hq
  rw [hlist] at this
  exact this

/-- The code after the checks, for a digest length, which is all it uses of
the streaming functions' shape. -/
theorem encMain_D {G G' : Impl.Pbkdf2.Md.X86_64.Stream} (h : G.D = G'.D) (f : Fns) (n : String) (c : Prog isa) :
    Impl.RsaOaep.X86_64.Precomputed.encMain G f n c = Impl.RsaOaep.X86_64.Precomputed.encMain G' f n c := by
  simp only [Impl.RsaOaep.X86_64.Precomputed.encMain, encEm, copySeed, copyLh, dbArgs, seedArgs, h]

variable {vs : List MdHash} (hc : Coh vs)

include hc in
theorem code_correct (v : PublicImpl) (s : State) (h : (encC (tables vs)).pre s) :
    ∃ t s', Exec isa (Impl.RsaOaep.X86_64.Precomputed.encrypt (fnsOf vs) v.name v.code) s t s' ∧
      abiPreserved s s' ∧ postT s s' := by
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, ⟨T, hT, hheld⟩, hd⟩ := tabs_of h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hmL, hidxL, hDmL⟩ := held_tableOf hheld₁
  obtain ⟨hm, hidx, hDm⟩ := held_tableOf hheld
  have okL := tabOK_of hc hd hw₁
  have ok := tabOK_of hc hd hw
  obtain ⟨hgi, hgu, hgf⟩ := fnsGood_of vs
  have hHa : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 10) = some w₁.mgf.G := hashAt_tableOf hidxL
  have hGa : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 11) = some w.mgf.G := hashAt_tableOf hidx
  have hp : PPreT w₁.mgf.G s := preT_of h hHa
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlen : w₁.mgf.G.len = w₁.H.D := w₁.mgf.len
  have hnl : (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length = (s.gpr .rcx).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hml : (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat).length = (stackArg s 3).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hsl : (Spec.Rsa.bytesAt s.mem (stackArg s 4) w₁.mgf.G.len).length = w₁.mgf.G.len := by
    simp [Spec.Rsa.bytesAt]
  suffices hw : WP isa (Impl.RsaOaep.X86_64.Precomputed.encrypt (fnsOf vs) v.name v.code) s
      fun s' => abiPreserved s s' ∧ post w₁.mgf.G w.mgf.G s s' by
    obtain ⟨t, s', he, hq, hpo⟩ := hw
    refine ⟨t, s', he, hq, fun H G hH' hG' => ?_⟩
    rw [hHa] at hH'
    rw [hGa] at hG'
    obtain rfl := Option.some.inj hH'
    obtain rfl := Option.some.inj hG'
    exact hpo
  refine wp_alloc (by have := hp.sp1; unfold encStack at this; unfold frameBytes; omega_using [this]) ?_
  refine encBodyWith_ok w₁.ok w₁.mgf hp.toEPre (fun t he sy => etabL hp he sy okL hmL hDmL)
    (fun t' he' hw' hb => ?_) fun t he hsy L R hk => ?_
  · obtain ⟨h1, h2, h3, h4⟩ := encEnd_ok hp.toEPre he' hw'
    refine ⟨h1, h2, h3, fun _ => ?_⟩
    show Spec.Rsa.written _ _ _ _ _
    rw [encrypt_none (by rw [hnl, hlen, hml]; omega_using [hb])]; exact h4
  · dsimp only
    rw [encMain_D (G := ofLen w₁.H.D) (G' := w₁.H.stream) rfl]
    refine WP.mono (encMain_ok w₁.ok w.ok w₁.mgf w.mgf v hgi hgu hgf hp he hsy okL hmL hDmL ok hm hDm L R
        ArgsW_35 hk)
      fun t' ⟨he', hw'⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := encEnd_abi hp.toEPre he'
    refine ⟨h1, h2, h3, fun hq => ?_⟩
    show Spec.Rsa.written _ _ _ _ _
    have hw'' := hw' hq
    rw [encrypt_some (by rw [hsl]) (by rw [hnl, hlen, hml]; omega_using [hk]), hnl, hml, hlen]
    rw [hlen] at hw''
    exact hw''

end VG.Proof.RsaOaep.X86_64.Pc

end

end


/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition (with the tables `ts` of
MGF1's hash function), `postT`, and `encK`'s public data with `pre` and its
words and the table; it implies the shared contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (ts : List FnTable)

/-- The shared contract's precondition, `postT`, and `encK`'s public data
with `pre` and its words, the tables' addresses, the tables' functions'
addresses, and which tables they are. -/
def contract : Contract isa where
  pre := (encC ts).pre
  post := postT
  pub a s := encPub a s ∧ stackArg a 8 = stackArg s 8 ∧ stackArg a 9 = stackArg s 9 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 8) (stackArg a 9).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat ∧ stackArg a 10 = stackArg s 10 ∧
    stackArg a 11 = stackArg s 11 ∧ (∀ f ∈ tabFnsE ts, a.syms f = s.syms f) ∧
    (∀ T ∈ ts, (Abi.tableHeld 64 a.mem (stackArg a 10) (FnTable.words isa a T) ↔
      Abi.tableHeld 64 s.mem (stackArg s 10) (FnTable.words isa s T))) ∧
    ∀ T ∈ ts, (Abi.tableHeld 64 a.mem (stackArg a 11) (FnTable.words isa a T) ↔
      Abi.tableHeld 64 s.mem (stackArg s 11) (FnTable.words isa s T))

theorem implies (hsat : ∃ s, (encC ts).pre s) : (contract ts).Implies (encC ts) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.RsaOaep.seedLenMdOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Abi.withTables, Sig.wordIndex, abi, argRegs, contract, postT, post, Consistent, encK, encStack, stackArgs_twelve,
      List.append_eq, tabFnsE]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.RsaOaep.seedLenMdOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Abi.withTables, Sig.wordIndex, abi, argRegs, contract, postT, post, Consistent, encK, encStack,
      List.append_eq, tabFnsE, List.range, List.range.loop] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_eight, a0, a1, a2, a3, a4, a5, a6, a7], hn, he⟩, a8, a9, hq', a10, a11,
      fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htab _ _ rfl rfl T hT,
      fun T hT => htab' _ _ rfl rfl T hT⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaOaep.X86_64.Pc
