module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Body
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Rsa.Octets
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! ### `Ffdh.X86_64.ParameterCandidate.Finish`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.ClearOutput`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: clear an unsuccessful candidate -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64

theorem clearOutput_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut oOut oLen) s fun t =>
      CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = List.replicate p.k 0 ∧
      (∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j)) ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86_64.zeroOut_ok h.base.scr hdi h.base.header_room
    (by decide : oOut < 32) (by decide : oLen < 32)
    (h.base.hdr (oOut, p.op) (by simp [CandidateP.headers]))
    (h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers]))
    (by omega_using [h.base.widths.1]) (by omega_using [h.base.widths.2]) h.base.out)
    fun t ⟨hv, hf, k⟩ => ?_
  obtain ⟨ht, hs, hfr⟩ := h.after_bytes hf k (by decide)
  refine ⟨ht, (k.gpr (by decide)).trans hdi, ?_, ?_, hs, hfr, k.mono (by decide)⟩
  · refine List.eq_replicate_iff.mpr ⟨bytesAt_length _ _ _, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hv i (List.mem_range.mp hi)
  · intro j hj
    exact words_outside_bytes h.base.size64 hf h.base.out.sep _ (by omega_using [hj, h.base.header_room])

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.FinishTail`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.WriteUsed`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: write the public consumed count -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem writeWord_frame (m : Mem) (p : Addr) (v : BitVec 64) :
    ∀ a, (∀ i < 8, a ≠ off p i) → (m.writeW p v) a = m a := by
  intro a ha
  have hfar : 8 ≤ ofs p a := by
    by_contra hn
    have he : off p (ofs p a) = a := by
      simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm]
      exact BitVec.sub_add_cancel _ _
    exact ha _ (by omega_using [hn]) he.symm
  have hf := writeW_outside m p (d := 0) v (by decide)
  simpa only [off, BitVec.add_zero] using hf a (Or.inr hfar)

theorem writeUsed_ok {p : CandidateP} {used status : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hs : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 status) (hstatus : status < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr oStatus)), .mov .rdx (.mem (hdr oUsedP)),
      .mov .rcx (.mem (hdr oUsed)), .alu .test .rax (.reg .rax), .cmov .e .rcx (.reg .rax), .store (at0 .rdx) .rcx]) s
      fun t => t.gpr .rax = BitVec.ofNat 64 status ∧ t.gpr .rdi = p.B ∧
        word t.mem p.up 0 = BitVec.ofNat 64 (if status = 0 then 0 else used) ∧
        Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k ∧
        (∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j)) ∧
        Keep [.rax, .rdx, .rcx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hup := h.base.hdr (oUsedP, p.up) (by simp [CandidateP.headers])
  have hst : InRegions s.wr p.up 8 := by simpa [off] using h.base.used.st (d := 0) (by decide)
  have hzero : (BitVec.ofNat 64 status == 0) = decide (status = 0) := ofNat64_beq_zero hstatus
  have hv : (if decide (status = 0) then BitVec.ofNat 64 status else BitVec.ofNat 64 used) =
      BitVec.ofNat 64 (if status = 0 then 0 else used) := by
    by_cases hz : status = 0 <;> simp [hz]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 status ∧
    t.mem = s.mem.writeW p.up (BitVec.ofNat 64 (if status = 0 then 0 else used)))
    (by xrun [State.ea, hdr, at0, hdrOff, hdi, hs, hup, h.usedWord,
      hrd oStatus (by decide), hrd oUsedP (by decide), hrd oUsed (by decide), hst,
      BitVec.ofInt_ofNat, BitVec.add_zero, BitVec.and_self, hzero, cmov_reg_value, eval, hv]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ?_
  have hf : ∀ a, (∀ i < 8, a ≠ off p.up i) → t.mem a = s.mem a := by
    rw [hm]; exact writeWord_frame _ _ _
  refine ⟨hax, (k.gpr (by decide)).trans hdi, ?_, ?_, ?_, k⟩
  · rw [hm]; simpa [off] using word_writeW_self s.mem p.up 0 (BitVec.ofNat 64 (if status = 0 then 0 else used))
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf _ (fun j hj he => h.base.outUsed i (List.mem_range.mp hi) j hj he)
  · intro j hj
    exact words_outside_bytes h.base.size64 hf h.base.usedOut.sep _ (by omega_using [hj, h.base.header_room])

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: the callable's final store and ABI return -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem finishTail_ok {p : CandidateP} {used status : Nat} {s₀ s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hs : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 status) (hstatus : status < 2 ^ 64)
    (hsaved : ∀ i < 6, word s.mem p.B (8 * i) = s₀.gpr (saved.getD i .rax)) :
    WP isa (.block (([.mov .rax (.mem (hdr oStatus)), .mov .rdx (.mem (hdr oUsedP)), .mov .rcx (.mem (hdr oUsed)),
      .alu .test .rax (.reg .rax), .cmov .e .rcx (.reg .rax), .store (at0 .rdx) .rcx] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = BitVec.ofNat 64 status ∧
        word t.mem p.up 0 = BitVec.ofNat 64 (if status = 0 then 0 else used) ∧
        Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k ∧
        (∀ r ∈ saved, t.gpr r = s₀.gpr r) ∧
        Keep (saved ++ ([.rax, .rdx, .rcx] : List Reg)) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (writeUsed_ok h hdi hs hstatus)
    fun u ⟨hax, hdu, hused, hout, hwords, ku⟩ => ?_
  refine WP.mono (VG.Proof.Ffdh.X86_64.exit_ok (h.base.scr.congr ku.2.2) hdu
    (by omega_using [h.base.header_room])
    (fun i hi => (hwords i (by omega_using [hi])).trans (hsaved i hi)))
    fun t ⟨hregs, hm, kt⟩ => ?_
  exact ⟨(kt.gpr (by decide)).trans hax, by rw [hm]; exact hused,
    by rw [hm]; exact hout, hregs, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: complete output handling -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem finish_ok {p : CandidateP} {used status : Nat} {s₀ s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hs : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 status) (hstatus : status < 2 ^ 64)
    (hsaved : ∀ i < 6, word s.mem p.B (8 * i) = s₀.gpr (saved.getD i .rax)) :
    WP isa finish s fun t => t.gpr .rax = BitVec.ofNat 64 status ∧
      word t.mem p.up 0 = BitVec.ofNat 64 (if status = 0 then 0 else used) ∧
      Spec.Rsa.bytesAt t.mem p.op p.k =
        (if status = 1 then Spec.Rsa.bytesAt s.mem p.op p.k else List.replicate p.k 0) ∧
      (∀ r ∈ saved, t.gpr r = s₀.gpr r) ∧ Keep (.rdi :: mmRegs) s t := by
  have hrd := h.base.scr.ld (show 8 * oStatus + 8 ≤ p.Z by
    change 160 ≤ p.Z; omega_using [h.base.header_room])
  have heq : (BitVec.ofNat 64 status == 1) = decide (status = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstatus]
    rfl
  unfold finish
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
    u.zf = some (decide (status = 1)) ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdrOff, hdi, hs, hrd, sub_beq_zero, heq]) rfl)
    fun u ⟨⟨hz, hm⟩, ku⟩ => ?_)
  obtain ⟨hu, hsu, hfu⟩ := h.same_mem hm ku (by decide)
  have hdu : u.gpr .rdi = p.B := (ku.gpr (by decide)).trans hdi
  have hsu' : word u.mem p.B (8 * oStatus) = BitVec.ofNat 64 status := by rw [hm]; exact hs
  have hsavedu := fun i hi => (show word u.mem p.B (8 * i) = word s.mem p.B (8 * i) by rw [hm]).trans (hsaved i hi)
  refine WP.seq (WP.ite (decide (status = 1)) (by simp [eval, hz]) ?_ ?_)
  · intro hy
    have hy' := of_decide_eq_true hy
    refine WP.block_nil ?_
    refine WP.mono (finishTail_ok hu hdu hsu' hstatus hsavedu)
      fun t ⟨hax, hused, hout, hregs, kt⟩ => ?_
    exact ⟨hax, hused, by simpa only [hy', ite_true, hm] using hout,
      hregs, (ku.trans kt).mono (by decide)⟩
  · intro hn
    have hn' := of_decide_eq_false hn
    refine WP.mono (clearOutput_ok hu hdu) fun v ⟨hv, hdv, hzv, hw, _, _, kv⟩ => ?_
    refine WP.mono (finishTail_ok hv hdv ((hw _ (by decide)).trans hsu') hstatus
      (fun i hi => (hw i (by omega_using [hi])).trans (hsavedu i hi)))
      fun t ⟨hax, hused, hout, hregs, kt⟩ => ?_
    exact ⟨hax, hused, by simpa only [hn', ite_false] using hout.trans hzv,
      hregs, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: preserve the complete System V ABI -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/Correct.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: functional correctness of the callable -/

section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

def FinalResult (p : CandidateP) (t : State) : Prop :=
  let r := Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand
  ((t.gpr .rax).setWidth 32).toNat = Proof.Ffdh.candidateStatus r ∧
    Spec.Rsa.bytesAt t.mem p.op p.k =
      (match r with | some (some n, _) => Spec.Rsa.i2osp n p.k | _ => List.replicate p.k 0) ∧
    word t.mem p.up 0 = BitVec.ofNat 64
      (match r with | some (_, rest) => p.rand.length - rest.length | none => 0)

private theorem finish_result {p : CandidateP} {used : Nat} {s t : State}
    (hbound : used ≤ p.rand.length) (hr : NativeResult p used s.mem)
    (hout : word s.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P)
    (hax : t.gpr .rax = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand)))
    (hused : word t.mem p.up 0 = BitVec.ofNat 64
      (if Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand) = 0 then 0 else used))
    (hbytes : Spec.Rsa.bytesAt t.mem p.op p.k =
      (if Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand) = 1 then
        Spec.Rsa.bytesAt s.mem p.op p.k else List.replicate p.k 0)) : FinalResult p t := by
  unfold FinalResult
  cases he : Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand with
  | none => simpa [he, Proof.Ffdh.candidateStatus, hax] using And.intro hbytes hused
  | some ar =>
    obtain ⟨value, rest⟩ := ar
    have hrest : rest = p.rand.drop used := by simpa only [NativeResult, he] using hr.2.1
    have hcount : p.rand.length - rest.length = used := by
      rw [hrest, List.length_drop]
      omega
    cases value with
    | none =>
      refine ⟨?_, ?_, ?_⟩
      · simp [hax, he, Proof.Ffdh.candidateStatus]
      · simpa only [he, Proof.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false] using hbytes
      · simpa only [he, Proof.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false, hcount] using hused
    | some n =>
      have hn : n = p.P := hr.2.2 n rest he
      have hstatus : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 1 := by
        simpa only [he, Proof.Ffdh.candidateStatus] using hr.1
      have hval := hout hstatus
      have hi := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt s.mem p.op p.k)
      rw [bytesAt_length, hval, ← hn] at hi
      refine ⟨?_, ?_, ?_⟩
      · simp [hax, he, Proof.Ffdh.candidateStatus]
      · simpa only [he, Proof.Ffdh.candidateStatus, ite_true, hi] using hbytes
      · simpa only [he, Proof.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false, hcount] using hused

theorem correct_ok (M : Mont) (R : R2Impl M) (K : Kernel) {s : State} (c : PcCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) s fun t => pcPost s t ∧
      (∀ r ∈ saved, t.gpr r = s.gpr r) ∧ Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.ParameterCandidate.code
  refine WP.seq (WP.mono (body_ok M R K c) fun u ⟨used, hu, hdu, hr, hout, hsaved, ku⟩ => ?_)
  let p := candidateOfState s
  have hsmall : Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand) < 2 ^ 64 := by
    cases Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand with
    | none => decide
    | some ar => obtain ⟨value, rest⟩ := ar; cases value <;> dsimp only [Proof.Ffdh.candidateStatus] <;> decide
  refine WP.mono (finish_ok hu hdu hr.1 hsmall hsaved)
    fun t ⟨hax, hused, hbytes, hregs, kt⟩ => ?_
  have hfinal := finish_result hu.bound hr hout hax hused hbytes
  refine ⟨?_, hregs, (ku.trans kt).mono (by decide)⟩
  change pcPost s t
  unfold pcPost
  refine ⟨hfinal.1, hfinal.2.1, ?_⟩
  have hw := hfinal.2.2
  change VG.Proof.Bignum.word t.mem (s.gpr .rdx) 0 = BitVec.ofNat 64
    (match pcResult s with | some (_, rest) => (pcRand s).length - rest.length | none => 0) at hw
  have hlen : (pcRand s).length = (stackArg s 0).toNat := bytesAt_length _ _ _
  rw [hlen] at hw
  change [VG.Proof.Bignum.word t.mem (s.gpr .rdx) 0] = _
  exact congrArg (fun x : BitVec 64 => [x]) hw

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 (saved)
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

private theorem ret_frame {c : Prog isa} {s t : State} {tr : List Leak}
    (h : pcPre s) (hs : SpSafe c) (hd : c.x86_64Depth ≤ 128) (he : Exec isa c s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h
  have hf := Exec.stackFrame hs he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hro, hru, hrs]
  · simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem pc_correct (M : Mont) (R : R2Impl M) (K : Kernel)
    (hs : SpSafe (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run))
    (hd : (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run).x86_64Depth ≤ 128)
    (hmx : ctlOk (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) = true)
    (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) s tr t ∧
      abiPreserved s t ∧ pcContract.post s t := by
  obtain ⟨tr, t, he, hp, hregs, k⟩ := correct_ok M R K (pcCtx_of h)
  have hg : gprPreserved s t := by
    refine ⟨?_, ret_frame h hs hd he⟩
    intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact k.gpr (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
  exact ⟨tr, t, he, abiPreserved_of_ctl hmx he hg, hp⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
