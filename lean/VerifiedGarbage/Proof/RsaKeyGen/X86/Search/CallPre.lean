module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Args
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Args
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
meta import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

-- separate module: the callee's precondition, whose facts build in parallel with the rest of the search

/-! # The candidate's precondition (i686)

With its eleven arguments in the frame (`ArgsAt`), `vg_rsa_keygen_candidate`'s
contract holds on its entry, narrowed to `e`, `p`, the rest of the tape and
RSA's table, which it reads, and to `out`, `used`, the working space and its
frame of arguments, which it writes (`call_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86

/-- An implementation of `vg_rsa_keygen_candidate`, as the search calls it:
its name, its code, its proof and the stack it uses. -/
structure Cand where
  name : String
  code : Prog isa
  verified : Verified target code VG.Proof.RsaKeyGen.X86.Candidate.contract
  noSp : NoSp code
  stack : stackUse code ≤ 152

/-- The candidate, as the search calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

/-- RSA's table. -/
abbrev tR (o : State) : Region := ⟨(o.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩

/-- The table's region, as the constants name it. -/
abbrev tableRs (o : State) : List Region :=
  Abi.constRegions (fun name => (o.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts

theorem tableRs_eq (o : State) : tableRs o = [tR o] := by
  rw [tableRs, VG.Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

/-- The rest of the tape. -/
abbrev winR (o : State) (used : Nat) : Region :=
  ⟨(arg o 7 + BitVec.ofNat 32 used).setWidth 64, (arg o 8).toNat - used⟩

/-- What the callee may read and write. -/
abbrev callRd (o : State) (used : Nat) : List Region := eR o :: pR o :: winR o used :: tableRs o
abbrev callWr (o : State) : List Region := [oR o, uR o, bR o, frR o]

theorem ce_arg {p : SearchPublic} {o t : State} {used : Nat} (h : SearchInput p o)
    (he : t.gpr .esp = p.S2) (ha : ArgsAt o used 11 t.mem) (rd wr : List Region) {j : Nat} (hj : j < 11) :
    arg (t.callEntry.withRegions rd wr) j = callArg o used j := by
  have A := h.abi
  have h1 : 216 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 60 := by
    rw [he, SearchPublic.S2, h.sp_eq]; exact VG.X86.sub_toNat (by omega)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    SearchPublic.S2, h.sp_eq, addr_sub A (by decide) (by omega)]

/-- Constants held, through writes apart from them. -/
theorem held_frame {m m' : Mem} {f : String → BitVec 64} {cs : List (String × List (BitVec 64))}
    (h : Abi.constsHeld m f cs) {rs : List Region} (hf : Frame rs m m') (hb : ∀ c ∈ cs, 8 * c.2.length ≤ 2 ^ 64)
    (hd : ∀ t ∈ Abi.constRegions f cs, ∀ r ∈ rs, t.Disjoint r) : Abi.constsHeld m' f cs := by
  intro c hc i hi
  have := hb c hc
  rw [hf.readW (r := ⟨f c.1, 8 * c.2.length⟩) (Offset.contains_base _ (by omega) (by omega))
    (hd _ (List.mem_map_of_mem hc)) (by decide)]
  exact h c hc i hi

theorem win_base {o : State} (A : SearchABI o) {used : Nat} (hu : used < (arg o 8).toNat) :
    (arg o 7 + BitVec.ofNat 32 used).setWidth 64 = (arg o 7).setWidth 64 + BitVec.ofNat 64 used := by
  have := A.rBound
  exact VG.Proof.MlKem.X86.ea_off (by omega)

theorem win_sub {o : State} (A : SearchABI o) {used : Nat} (hu : used < (arg o 8).toNat) :
    Region.Sub (winR o used) (rR o) := by
  rw [winR, win_base A hu]; exact Offset.sub_base _ (by omega)

theorem win_toNat {o : State} (A : SearchABI o) {used : Nat} (hu : used < (arg o 8).toNat) :
    (arg o 7 + BitVec.ofNat 32 used).toNat = (arg o 7).toNat + used := by
  have := A.rBound
  have := (arg o 8).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The callee's stack pointer on its entry. -/
theorem esp_sub4 {p : SearchPublic} {o t : State} (h : SearchInput p o) (he : t.gpr .esp = p.S2) :
    t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 64 := by
  rw [he, SearchPublic.S2, h.sp_eq, BitVec.sub_sub]; rfl

theorem ret_addr {p : SearchPublic} {o t : State} (h : SearchInput p o) (he : t.gpr .esp = p.S2) :
    (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 152 := by
  rw [esp_sub4 h he]
  have e := addr_sub h.abi (k := 64) (d := 0) (by decide) (by decide)
  simpa only [addr, BitVec.add_zero] using e

/-- The table, apart from every region the run may write. -/
theorem table_far {o : State} (A : SearchABI o) :
    (tR o).base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ o.wr, (tR o).Disjoint r) ∧ (tR o).Disjoint (retR o) ∧
      (tR o).Disjoint (lowR o) := by
  exact A.tableFar (tR o) (by
    simp only [tableRegions, Abi.constRegions_cons, Abi.constRegions_nil,
      VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _)

theorem call_pre {p : SearchPublic} {o t : State} {used : Nat} (h : SearchInput p o)
    (hu : used + p.len ≤ p.randLen) (he : t.gpr .esp = p.S2) (ha : ArgsAt o used 11 t.mem)
    (hsy : t.syms = o.syms) (hm : Frame (changes o) o.mem t.mem) :
    VG.Proof.RsaKeyGen.X86.Candidate.contract.pre (t.callEntry.withRegions (callRd o used) (callWr o)) := by
  have A := h.abi
  have h1 : 216 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hpl : p.len = (arg o 1).toNat := by rw [← h.2]; rfl
  have hpr : p.randLen = (arg o 8).toNat := by rw [← h.2]; rfl
  have hv := h.len_valid
  have hu' : used < (arg o 8).toNat := by omega
  have hs4 := esp_sub4 h he
  have hs4n : (o.gpr .esp - BitVec.ofNat 32 64).toNat = (o.gpr .esp).toNat - 64 := VG.X86.sub_toNat (by omega)
  have ha0 : argAddr (t.callEntry.withRegions (callRd o used) (callWr o)) 0 = low o + BitVec.ofNat 64 156 := by
    rw [argAddr_withRegions, argAddr_callEntry, show 4 * 0 = 0 from rfl, BitVec.add_zero, he, SearchPublic.S2,
      h.sp_eq]
    have e := addr_sub A (k := 60) (d := 0) (by decide) (by decide)
    simpa only [addr, BitVec.add_zero] using e
  have hret : (o.gpr .esp - BitVec.ofNat 32 64).setWidth 64 = low o + BitVec.ofNat 64 152 := by
    rw [← hs4]; exact ret_addr h he
  have hlen : (arg o 8 - BitVec.ofNat 32 used).toNat = (arg o 8).toNat - used := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by have := (arg o 8).isLt; omega)]
    have := (arg o 8).isLt; omega
  have hT : Abi.constRegions (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] = [tR o] := by
    rw [hsy, Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
  have TF := table_far A
  have W := win_sub A hu'
  have Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  have Rs : Region.Sub ⟨low o + BitVec.ofNat 64 152, 4⟩ (lowR o) := low_sub (by decide)
  have Bs : Region.Sub ⟨low o, 152⟩ (lowR o) := Region.sub_prefix (by decide)
  have oIn : oR o ∈ o.wr := by rw [A.wr]; simp
  have uIn : uR o ∈ o.wr := by rw [A.wr]; simp
  have bIn : bR o ∈ o.wr := by rw [A.wr]; simp
  -- The callee's regions, apart.
  have dOU : (oR o).Disjoint (uR o) := A.ou
  have dOE : (oR o).Disjoint (eR o) := A.oe
  have dOP : (oR o).Disjoint (pR o) := A.op
  have dOW : (oR o).Disjoint (winR o used) := A.or_.sub_right W
  have dOB : (oR o).Disjoint (bR o) := A.ob
  have dOF : (oR o).Disjoint (frR o) := A.lowO.symm.sub_right Fs
  have dUE : (uR o).Disjoint (eR o) := A.ue
  have dUP : (uR o).Disjoint (pR o) := A.up
  have dUW : (uR o).Disjoint (winR o used) := A.ur.sub_right W
  have dUB : (uR o).Disjoint (bR o) := A.ub
  have dUF : (uR o).Disjoint (frR o) := A.lowU.symm.sub_right Fs
  have dEB : (eR o).Disjoint (bR o) := A.eb
  have dEF : (eR o).Disjoint (frR o) := A.lowE.symm.sub_right Fs
  have dPB : (pR o).Disjoint (bR o) := A.pb
  have dPF : (pR o).Disjoint (frR o) := A.lowP.symm.sub_right Fs
  have dWB : (winR o used).Disjoint (bR o) := A.rb.sub_left W
  have dWF : (winR o used).Disjoint (frR o) := (A.lowRand.symm.sub_left W).sub_right Fs
  have dBF : (bR o).Disjoint (frR o) := A.lowB.symm.sub_right Fs
  have rO : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (oR o) := A.lowO.sub_left Rs
  have rU : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (uR o) := A.lowU.sub_left Rs
  have rE : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (eR o) := A.lowE.sub_left Rs
  have rP : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (pR o) := A.lowP.sub_left Rs
  have rW : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (winR o used) := (A.lowRand.sub_left Rs).sub_right W
  have rB : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (bR o) := A.lowB.sub_left Rs
  have rF : Region.Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ (frR o) :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have bO : Region.Disjoint ⟨low o, 152⟩ (oR o) := A.lowO.sub_left Bs
  have bU : Region.Disjoint ⟨low o, 152⟩ (uR o) := A.lowU.sub_left Bs
  have bE : Region.Disjoint ⟨low o, 152⟩ (eR o) := A.lowE.sub_left Bs
  have bP : Region.Disjoint ⟨low o, 152⟩ (pR o) := A.lowP.sub_left Bs
  have bW : Region.Disjoint ⟨low o, 152⟩ (winR o used) := (A.lowRand.sub_left Bs).sub_right W
  have bB : Region.Disjoint ⟨low o, 152⟩ (bR o) := A.lowB.sub_left Bs
  have bF : Region.Disjoint ⟨low o, 152⟩ (frR o) := Offset.base_disjoint _ (by omega) (by omega)
  have oB := A.oBound
  have uB := A.uBound
  have eB := A.eBound
  have pB := A.pBound
  have wB : (arg o 7 + BitVec.ofNat 32 used).toNat + ((arg o 8).toNat - used) ≤ 2 ^ 32 := by
    rw [win_toNat A hu']; have := A.rBound; omega
  have sB := A.bBound
  have lV := A.lenValid
  have eL := A.eLow
  have eH := A.eHigh
  have pL := A.pLen
  have sL := A.scratchLength
  have st : 152 ≤ (o.gpr .esp - BitVec.ofNat 32 64).toNat := by rw [hs4n]; omega
  have st' : (o.gpr .esp - BitVec.ofNat 32 64).toNat + 4 + 44 ≤ 2 ^ 32 := by rw [hs4n]; omega
  have held : Abi.constsHeld (t.mem.writeW (low o + BitVec.ofNat 64 152) (t.unknowns 0))
      (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] := by
    have H := A.held
    rw [hsy]
    have hb : ∀ c ∈ [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)],
        8 * c.2.length ≤ 2 ^ 64 := by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc
      rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
    refine held_frame (held_frame H hm hb fun r hr => ?_) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) hb fun r hr => ?_
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr
      intro q hq
      simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact TF.2.1 _ oIn
      · exact TF.2.1 _ uIn
      · exact TF.2.1 _ bIn
      · exact TF.2.1 _ (by rw [A.wr]; simp)
      · rw [← h.low_eq]; exact TF.2.2.2
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact TF.2.2.2.sub_right Rs
  sig_pre [VG.Proof.RsaKeyGen.X86.Candidate.contract, Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length, stackBelow]
  simp only [ce_arg h he ha _ _ (show 0 < 11 by decide), ce_arg h he ha _ _ (show 1 < 11 by decide),
    ce_arg h he ha _ _ (show 2 < 11 by decide), ce_arg h he ha _ _ (show 3 < 11 by decide),
    ce_arg h he ha _ _ (show 4 < 11 by decide), ce_arg h he ha _ _ (show 5 < 11 by decide),
    ce_arg h he ha _ _ (show 6 < 11 by decide), ce_arg h he ha _ _ (show 7 < 11 by decide),
    ce_arg h he ha _ _ (show 8 < 11 by decide), ce_arg h he ha _ _ (show 9 < 11 by decide),
    ce_arg h he ha _ _ (show 10 < 11 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, hs4, ha0, hret,
    hlen, hT, BitVec.add_sub_cancel]
  have hrd : callRd o used = [eR o, pR o, winR o used, tR o] := by rw [callRd, tableRs_eq]
  have tW : ∀ r ∈ o.wr, (tR o).Disjoint r := TF.2.1
  have tL : (tR o).Disjoint (lowR o) := TF.2.2.2
  have tO : (tR o).Disjoint (oR o) := tW _ oIn
  have tU : (tR o).Disjoint (uR o) := tW _ uIn
  have tB : (tR o).Disjoint (bR o) := tW _ bIn
  have tF : (tR o).Disjoint (frR o) := tL.sub_right Fs
  have tRet : (tR o).Disjoint ⟨low o + BitVec.ofNat 64 152, 4⟩ := tL.sub_right Rs
  have tBel : (tR o).Disjoint ⟨low o, 152⟩ := tL.sub_right Bs
  have tBd := TF.1
  have tAl : (tR o).base.toNat % 64 = 0 := A.tableAligned (tR o) (by
    simp only [tableRegions, Abi.constRegions_cons, Abi.constRegions_nil,
      VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _)
  sig_and_intros
  all_goals first
    | exact True.intro
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | (rw [hrd]; rfl)
    | (intro r hr; simp only [List.mem_singleton] at hr; subst hr
       exact ⟨tBd, tO, tU, tB, tF, tRet, tBel⟩)
    | (intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact tAl)

end VG.Proof.RsaKeyGen.X86.Search
