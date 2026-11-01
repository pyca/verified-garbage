module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Frame
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Top
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # The attempt's precondition (x86)

With its nine arguments in the frame (`ArgsAt`),
`vg_ffdh_parameter_candidate_sieved`'s contract holds on its entry, narrowed
to the rest of the tape and RSA's table, which it reads, and to the output,
the state's word for its `used`, the working space and its frame of
arguments, which it writes (`call_pre`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The table's region, as the constants name it. -/
abbrev tableRs (o : State) : List Region :=
  Abi.constRegions (fun name => (o.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts

/-- The rest of the tape. -/
abbrev winR (o : State) (used : Nat) : Region :=
  ⟨(arg o 5 + BitVec.ofNat 32 used).setWidth 64, (arg o 6).toNat - used⟩

/-- The state's word the candidate writes its `used` to. -/
abbrev cuR (o : State) : Region := ⟨(arg o 9 + BitVec.ofNat 32 candOff).setWidth 64, 8⟩

/-- What the callee may read and write. -/
abbrev callRd (o : State) (used : Nat) : List Region := winR o used :: tableRs o
abbrev callWr (o : State) : List Region := [oR o, cuR o, bR o, frR o]

theorem tableRs_eq (o : State) : tableRs o = [tR o] := by
  rw [tableRs, VG.Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

/-- The callee's arguments, on its entry. -/
theorem ce_arg {o t : State} {used : Nat} (A : PSearchABI o)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 9 t.mem)
    (rd wr : List Region) {j : Nat} (hj : j < 9) :
    arg (t.callEntry.withRegions rd wr) j = callArg o used j := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 36 := by
    rw [he]; exact VG.X86.sub_toNat (by unfold argsBytes; omega)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    addr_sub A (by decide) (by unfold argsBytes; omega)]
  rfl

/-- Constants held, through writes apart from them. -/
theorem held_frame {m m' : Mem} {f : String → BitVec 64} {cs : List (String × List (BitVec 64))}
    (h : Abi.constsHeld m f cs) {rs : List Region} (hf : Frame rs m m') (hb : ∀ c ∈ cs, 8 * c.2.length ≤ 2 ^ 64)
    (hd : ∀ t ∈ Abi.constRegions f cs, ∀ r ∈ rs, t.Disjoint r) : Abi.constsHeld m' f cs := by
  intro c hc i hi
  have := hb c hc
  rw [hf.readW (r := ⟨f c.1, 8 * c.2.length⟩) (Offset.contains_base _ (by omega) (by omega))
    (hd _ (List.mem_map_of_mem hc)) (by decide)]
  exact h c hc i hi

/-- The rest of the tape, at its offset in the tape. -/
theorem win_base {o : State} (A : PSearchABI o) {used : Nat} (hu : used < (arg o 6).toNat) :
    (arg o 5 + BitVec.ofNat 32 used).setWidth 64 = argumentPointer o 5 + BitVec.ofNat 64 used := by
  have := A.rBound
  exact addr_eq (by omega)

theorem win_toNat {o : State} (A : PSearchABI o) {used : Nat} (hu : used < (arg o 6).toNat) :
    (arg o 5 + BitVec.ofNat 32 used).toNat = (arg o 5).toNat + used := by
  have := A.rBound
  have := (arg o 6).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem win_sub {o : State} (A : PSearchABI o) {used : Nat} (hu : used < (arg o 6).toNat) :
    Region.Sub (winR o used) (rR o) := by
  rw [winR, win_base A hu]; exact Offset.sub_base _ (by omega)

theorem cu_base {o : State} (A : PSearchABI o) :
    (arg o 9 + BitVec.ofNat 32 candOff).setWidth 64 = argumentPointer o 9 + BitVec.ofNat 64 80 :=
  Spill.addr_eq_of A.sBound (d := 80) (by decide)

theorem cu_sub {o : State} (A : PSearchABI o) : Region.Sub (cuR o) (sR o) := by
  rw [cuR, cu_base A]; exact Offset.sub_base _ (by decide)

/-- The callee's stack pointer on its entry. -/
theorem esp_sub4 {o t : State} (A : PSearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 40 := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  rw [he]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, argsBytes]
  have := (o.gpr .esp).isLt
  show (2 ^ 32 - 4 % 2 ^ 32 + (2 ^ 32 - 36 % 2 ^ 32 + (o.gpr .esp).toNat) % 2 ^ 32) % 2 ^ 32 = _
  omega

/-- The table, apart from every region the run may write. -/
theorem table_far {o : State} (A : PSearchABI o) :
    (tR o).base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ frameR o, (tR o).Disjoint r) ∧ (tR o).Disjoint (retR o) := by
  have F := A.tableFar (tR o) (by
    rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _)
  refine ⟨F.1, fun r hr => ?_, F.2.2.1⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact F.2.1 r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact F.2.2.2

theorem call_pre {o t : State} {used : Nat} (A : PSearchABI o) (hu : used < (arg o 6).toNat)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 9 t.mem)
    (hsy : t.syms = o.syms) (hm : Frame (frameR o) o.mem t.mem) :
    Cand.contract.pre (t.callEntry.withRegions (callRd o used) (callWr o)) := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hs4 := esp_sub4 A he
  have hs4n : (o.gpr .esp - BitVec.ofNat 32 40).toNat = (o.gpr .esp).toNat - 40 := VG.X86.sub_toNat (by omega)
  have ha0 : argAddr (t.callEntry.withRegions (callRd o used) (callWr o)) 0 = low o + BitVec.ofNat 64 176 := by
    rw [argAddr_withRegions, argAddr_callEntry, show 4 * 0 = 0 from rfl, BitVec.add_zero, he,
      sw_sub A (by decide)]; rfl
  have hret : (o.gpr .esp - BitVec.ofNat 32 40).setWidth 64 = low o + BitVec.ofNat 64 172 := sw_sub A (by decide)
  have hlen : (BitVec.ofNat 32 ((arg o 6).toNat - used)).toNat = (arg o 6).toNat - used := by
    have := (arg o 6).isLt; rw [BitVec.toNat_ofNat]; omega
  have hT : Abi.constRegions (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] = [tR o] := by
    rw [hsy, Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
  have TF := table_far A
  have W := win_sub A hu
  have Cu := cu_sub A
  have Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  have Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  have Bs : Region.Sub ⟨low o, 172⟩ (lowR o) := Region.sub_prefix (by decide)
  have oIn := oR_mem A
  have bIn := bR_mem A
  have sIn := sR_mem A
  -- The callee's regions, apart.
  have dOC : (oR o).Disjoint (cuR o) := A.os.sub_right Cu
  have dOW : (oR o).Disjoint (winR o used) := A.or_.sub_right W
  have dOB : (oR o).Disjoint (bR o) := A.ob
  have dOF : (oR o).Disjoint (frR o) := A.lowO.symm.sub_right Fs
  have dCW : (cuR o).Disjoint (winR o used) := (A.rs.symm.sub_left Cu).sub_right W
  have dCB : (cuR o).Disjoint (bR o) := A.bs.symm.sub_left Cu
  have dCF : (cuR o).Disjoint (frR o) := (A.lowS.symm.sub_left Cu).sub_right Fs
  have dWB : (winR o used).Disjoint (bR o) := A.rb.sub_left W
  have dWF : (winR o used).Disjoint (frR o) := (A.lowRand.symm.sub_left W).sub_right Fs
  have dBF : (bR o).Disjoint (frR o) := A.lowB.symm.sub_right Fs
  have rO : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (oR o) := A.lowO.sub_left Rs
  have rC : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (cuR o) := (A.lowS.sub_left Rs).sub_right Cu
  have rW : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (winR o used) := (A.lowRand.sub_left Rs).sub_right W
  have rB : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (bR o) := A.lowB.sub_left Rs
  have rF : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (frR o) :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have bO : Region.Disjoint ⟨low o, 172⟩ (oR o) := A.lowO.sub_left Bs
  have bC : Region.Disjoint ⟨low o, 172⟩ (cuR o) := (A.lowS.sub_left Bs).sub_right Cu
  have bW : Region.Disjoint ⟨low o, 172⟩ (winR o used) := (A.lowRand.sub_left Bs).sub_right W
  have bB : Region.Disjoint ⟨low o, 172⟩ (bR o) := A.lowB.sub_left Bs
  have bF : Region.Disjoint ⟨low o, 172⟩ (frR o) := Offset.base_disjoint _ (by omega) (by omega)
  have oB := A.oBound
  have cB : (arg o 9 + BitVec.ofNat 32 candOff).toNat + 8 ≤ 2 ^ 32 := by
    have := A.sBound
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show candOff = 80 from rfl]
    rw [Nat.mod_eq_of_lt (a := 80) (by decide), Nat.mod_eq_of_lt (by omega)]; omega
  have wB : (arg o 5 + BitVec.ofNat 32 used).toNat + ((arg o 6).toNat - used) ≤ 2 ^ 32 := by
    rw [win_toNat A hu]; have := A.rBound; omega
  have sB := A.bBound
  have bL := A.bitsLow
  have bH := A.bitsHigh
  have oL := A.outLen
  have gG := A.gen
  have sL := A.scratchLength
  have st : Proof.Ffdh.X86.stack ≤ (o.gpr .esp - BitVec.ofNat 32 40).toNat := by
    rw [hs4n]; show 172 ≤ _; omega
  have st' : (o.gpr .esp - BitVec.ofNat 32 40).toNat + 4 + 36 ≤ 2 ^ 32 := by rw [hs4n]; omega
  have held : Abi.constsHeld (t.mem.writeW (low o + BitVec.ofNat 64 172) (t.unknowns 0))
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
      simp only [List.mem_singleton] at hr; subst hr; exact TF.2.1
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact (TF.2.1 _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right Rs
  sig_pre [Cand.contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length, stackBelow]
  simp only [ce_arg A he ha _ _ (show 0 < 9 by decide), ce_arg A he ha _ _ (show 1 < 9 by decide),
    ce_arg A he ha _ _ (show 2 < 9 by decide), ce_arg A he ha _ _ (show 3 < 9 by decide),
    ce_arg A he ha _ _ (show 4 < 9 by decide), ce_arg A he ha _ _ (show 5 < 9 by decide),
    ce_arg A he ha _ _ (show 6 < 9 by decide), ce_arg A he ha _ _ (show 7 < 9 by decide),
    ce_arg A he ha _ _ (show 8 < 9 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, hs4, ha0, hret,
    hlen, hT, BitVec.add_sub_cancel]
  have hrd : callRd o used = [winR o used, tR o] := by rw [callRd, tableRs_eq]
  have tW : ∀ r ∈ o.wr, (tR o).Disjoint r := fun r hr => TF.2.1 r (List.mem_append_left _ hr)
  have tL : (tR o).Disjoint (lowR o) := TF.2.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
  have tO : (tR o).Disjoint (oR o) := tW _ oIn
  have tC : (tR o).Disjoint (cuR o) := (tW _ sIn).sub_right Cu
  have tB : (tR o).Disjoint (bR o) := tW _ bIn
  have tF : (tR o).Disjoint (frR o) := tL.sub_right Fs
  have tRet : (tR o).Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ := tL.sub_right Rs
  have tBel : (tR o).Disjoint ⟨low o, 172⟩ := tL.sub_right Bs
  have tBd := TF.1
  have tAl : (tR o).base.toNat % 64 = 0 := A.tableAligned (tR o) (by
    rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _)
  sig_and_intros
  all_goals first
    | exact True.intro
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | (rw [hrd]; rfl)
    | (intro r hr; simp only [List.mem_singleton] at hr; subst hr
       exact ⟨tBd, tO, tC, tB, tF, tRet, tBel⟩)
    | (intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact tAl)


end VG.Proof.Ffdh.X86.PSearch
