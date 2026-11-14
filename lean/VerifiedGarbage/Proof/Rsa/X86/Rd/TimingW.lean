module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Abi
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SizedW
public import VerifiedGarbage.Proof.Rsa.X86.Rd.DetTimeW
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # Prime recovery by Appendix C.2 on i686 leaks only the modulus's and exponents' lengths

Its traces depend on the arguments alone: past the modulus check, which reads
the modulus (public: the contract's leak is the modulus and the public
exponent), every piece is checked by the taint analysis or runs a public count
of times (`det_relCT`). The pieces' checks take the arguments public, which needs the writable regions apart from
them: `sizedD_relCT` from states whose writable regions are narrowed to the
working space and the outputs, and `sizedNarrowD_relCT` from the states
themselves.
-/
/-! ## The narrowed regions and the GCD's timing

The writable regions the pieces' checks narrow to, and the GCD's timing
from a stage.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.X86.Keys

/-- What the body writes but the stack: the working space and the outputs. -/
def narrowW (g : CallGeometry) : List Region := [⟨g.B, g.Z⟩, g.buffer 0, g.buffer 2]

/-- The geometry with its writable regions narrowed to `narrowW`. -/
def narrowG (g : CallGeometry) : CallGeometry := ⟨{ g.toGeo with wr := narrowW g }⟩

theorem inputs_agree {g : CallGeometry} {s t : State} (pg : PubG g.toGeo) (h : Inputs g s) (j : Inputs g t) :
    VG.X86.Taint.Agree τA s t := by
  have a₁ : ArgsOk s := by unfold ArgsOk; rw [h.esp, h.wrEq]; exact pg
  have a₂ : ArgsOk t := by unfold ArgsOk; rw [j.esp, j.wrEq]; exact pg
  have f₁ := a₁.1
  have f₂ := a₂.1
  have sp : s.gpr .esp = t.gpr .esp := h.esp.trans j.esp.symm
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf a₁, τA_wf a₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.ws.workspace.edi_toNat.trans j.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τA] at hk
    have C₁ := h.arguments ((k - 4) / 4) (by omega_using [hk])
    have C₂ := j.arguments ((k - 4) / 4) (by omega_using [hk])
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s _ = arg t _ from C₁.value.trans C₂.value.symm)

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs (narrowG g) (s.withRegions (s.rd ++ s.wr) (narrowW g)) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, narrowW, narrowG], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper, h.esp, h.room, h.top,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j => ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit,
    fun j => ?_, h.outputScratch, h.outputSeparate, rfl⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · refine ⟨g.buffer (2 * j.val), ?_, Region.contains_self _ _⟩
    show _ ∈ narrowW g
    match j with
    | ⟨0, _⟩ => simp [narrowW]
    | ⟨1, _⟩ => simp [narrowW]

end VG.Proof.Rsa.X86.Recover
end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys

theorem loadsPubW : PubA VG.Impl.Rsa.X86.RecoverRt.loads := ⟨_, by taint_decide⟩
theorem prodPubW : PubA VG.Impl.Rsa.X86.RecoverRt.prod := ⟨_, by taint_decide⟩
theorem storesPubW : PubA VG.Impl.Rsa.X86.RecoverRt.stores := ⟨_, by taint_decide⟩

/-- From the inputs to `det`'s stage: the modulus, and `d e` (wide). -/
theorem pre_stepW {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true) :
    WP isa (seqs [VG.Impl.Rsa.X86.RecoverRt.loads, VG.Impl.Rsa.X86.RecoverRt.prod]) s (D0W g.toGeo (inputValue g s.mem 0)) := by
  have facts := valid
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at facts
  have odd : inputValue g s.mem 0 % 2 = 1 := facts.1.1.1
  have large : 3 ≤ inputValue g s.mem 0 := by
    have lower := facts.1.1.2
    have power (k : Nat) (hk : 2 ≤ k) : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (by decide) hk
    have bigger := power 511 (by decide)
    omega_using [facts]
  have up := h.upper
  have nb : inputValue g s.mem 0 < 2 ^ (64 * g.n) := by
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    omega_using [this]
  have small : inputValue g s.mem 0 < 2 ^ (32 * g.toGeo.w) :=
    Nat.lt_of_lt_of_le nb (Nat.pow_le_pow_right (by decide) (by change 64 * g.n ≤ 32 * (2 * g.n + 2); omega_using []))
  simp only [seqs]
  refine WP.seq (WP.mono (loads_ok h len) fun s1 h1 => ?_)
  have arg : VG.Proof.Bignum.X86.CallArgument s1 g.B g.Z 7 (BitVec.ofNat 32 ((g.args 7).toNat)) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      h1.argument (h.arguments 7 (by decide)) (h.stageApart (by decide))
  refine WP.mono (prod_ok h1 arg (h.inputPositive 1) (h.inputBound 1) (h.inputBound 2)
    (inputValue_lt g s.mem 1) (inputValue_lt g s.mem 2)) fun s2 h2 => ?_
  have h2' := h2.mono (liveW' := [VG.Impl.Rsa.X86.Recover.wM, VG.Impl.Rsa.X86.Recover.wZ])
    (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  exact ⟨_, _, _, _, h2', by simp [AWp, AW1, upd, VG.Impl.Rsa.X86.Recover.wZ, VG.Impl.Rsa.X86.Recover.wM,
    VG.Impl.Rsa.X86.Recover.wMod, VG.Impl.Rsa.X86.Recover.wE, VG.Impl.Rsa.X86.Recover.wD], rfl⟩

end VG.Proof.Rsa.X86.Recover
end


@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem abiD_of {s : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pre s) :
    ABI s ∧ (arg s 7).toNat ≤ 8 := by
  sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  have rd : s.rd = [(caller s).buffer 4, (caller s).buffer 6, (caller s).buffer 8] := by
    dsimp only [caller, CallGeometry.buffer, byteAddr]
    with_reducible assumption
  have lengths : Spec.Rsa.lenValid (arg s 5).toNat := by with_reducible assumption
  have lo := lengths.1
  have hi := lengths.2
  refine ⟨?_, by omega_arith⟩
  constructor
  all_goals try simp only [rd, bodyRegions, lowR, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)

theorem calculatedD_entry {s t : State} (a : ABI s)
    (o : Outside (caller s).B 0 (caller s).Z s.mem t.mem) :
    calculatedD (caller s) t.mem = calculatedD (caller s) s.mem := by
  have same (i : Fin 3) : inputBytes (caller s) t.mem i = inputBytes (caller s) s.mem i := by
    exact scratch_bytes o (by have := (a.inputLength i).2; have := a.width.2.1; omega_arith)
      (a.inApart _ (a.inputMember i) _ (by simp))
  unfold calculatedD
  rw [same 0, same 1, same 2]

theorem satisfiableD : ∃ s, (Spec.Rsa.recoverPrimesDetContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 16384 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 20480 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 24576 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 65536 := by decide
  have a11 : arg satState 11 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argSlots, argVal, argBytes,
    stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e, esp, satState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using satState

end VG.Proof.Rsa.X86.Recover

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem bodyD_ok [VG.Proof.Rsa.X86.Recover.G.GcdDone] {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.body s fun t => Inputs g t ∧ WrittenD g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.RecoverDetRt.body VG.Impl.Rsa.X86.CrtValues.inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 4 (by decide)).readSrc (h.arguments 5 (by decide)).readSrc)
    fun u ⟨p, c, m, k⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u len.lower len.upper
    (by rw [p]; exact h.inputFit 0)
    (by rw [p, k.2.1, k.2.2]; exact h.inputRead 0)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun v ⟨z, mv, kv⟩ => ?_)
  rw [p, m] at z
  have mem : v.mem = s.mem := mv.trans m
  have keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (k.mono (by decide)).trans (kv.mono (by decide))
  have hv := h.after keeps (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 5).toNat) z ?_ ?_
  · intro accepted
    have modulus : Spec.Rsa.modulusValid (inputValue g v.mem 0)
        (inputBytes g v.mem 0).length = true := by
      rw [mem]
      simp only [inputValue, inputBytes, bytesAt_length, CallGeometry.buffer]
      exact accepted
    have pLen : (g.buffer 0).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.pLen
    have qLen : (g.buffer 2).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.qLen
    refine WP.mono (sizedW_ok hv len modulus pLen qLen eSmall)
      fun t ⟨ht, result, frame, rest⟩ => ?_
    exact ⟨ht, mem ▸ result, mem ▸ frame, keeps.trans rest⟩
  · intro rejected
    have failed : calculatedD g s.mem = none := by
      unfold calculatedD Spec.Rsa.primesKeyDet
      dsimp only
      have ln : (inputBytes g s.mem 0).length = (g.args 5).toNat := bytesAt_length _ _ _
      rw [ln, rejected]
      rfl
    refine WP.mono (failure_ok hv) fun t ⟨ht, p, q, status, frame, rest⟩ => ?_
    exact ⟨ht, writtenD_failure failed p q status, mem ▸ frame, keeps.trans (rest.mono (by decide))⟩

theorem operationD_ok [VG.Proof.Rsa.X86.Recover.G.GcdDone] {s : State} (a : ABI s) (eSmall : (arg s 7).toNat ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.code s fun t => WrittenD (caller s) s.mem t ∧ abiPreserved s t := by
  have low : 16 ≤ (caller s).Z := by have := a.used; omega_using [this]
  have high : (caller s).Z ≤ 2 ^ 64 := by have := a.scratchBound; omega_using [this]
  unfold VG.Impl.Rsa.X86.RecoverDetRt.code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, k, o⟩ => ?_)
  refine WP.seq (WP.mono (bodyD_ok inputs a.lengths_ok eSmall) fun v ⟨iv, written, frame, kv⟩ => ?_)
  have saveV := bodyFrame_saved inputs frame saved
  have whole : Frame (caller s).writes s.mem v.mem := by
    have start := outside_frame o (by omega_using [high])
    simp only [off, BitVec.add_zero] at start
    exact (start.mono (by simp [CallGeometry.writes])).trans (bodyFrame_full low frame)
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) a.retApartW (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (k.1 _ (by decide))) ret⟩
  unfold WrittenD at written ⊢
  rw [calculatedD_entry a o] at written
  rw [restored.mem, restored.other .eax (by decide)]
  exact written

theorem correctD [VG.Proof.Rsa.X86.Recover.G.GcdDone] (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pre s) :
    ∃ trace t, Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.recoverPrimesDetContract abi 96).post s t := by
  obtain ⟨a, eSmall⟩ := abiD_of h
  obtain ⟨trace, t, run, written, preserved⟩ := operationD_ok a eSmall
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold WrittenD outputBuffersD calculatedD inputBytes CallGeometry.buffer caller at written
  change Spec.Rsa.writtenAll t.mem
    [(VG.Proof.Dsa.X86.argumentPointer s 0, (arg s 1).toNat),
      (VG.Proof.Dsa.X86.argumentPointer s 2, (arg s 3).toNat)] (t.gpr .eax) _ at written
  rw [a.pLen, a.qLen] at written
  exact written

end VG.Proof.Rsa.X86.Recover
end


@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

theorem argumentsD_eq {s t : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 12, arg s i = arg t i := by
  sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argSlots, argVal, argBytes] at h
  sig_split h
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem modulusD_eq {s t : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pub s t) :
    inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0 := by
  have args := (argumentsD_eq h).2
  have leak : (inputBytes (caller s) s.mem 0 ++ inputBytes (caller s) s.mem 1).map (·.toNat) =
      (inputBytes (caller t) t.mem 0 ++ inputBytes (caller t) t.mem 1).map (·.toNat) := by
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argSlots, argVal, argBytes] at h
    exact h.2.1
  have lenN : (inputBytes (caller s) s.mem 0).length = (inputBytes (caller t) t.mem 0).length := by
    simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, caller, CallGeometry.buffer]
    exact congrArg BitVec.toNat (args 5 (by decide))
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp leak
  exact (List.append_inj both lenN).1

end VG.Proof.Rsa.X86.Recover
end

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (relCT_narrow)

/-- Two runs of `sized` over the same geometry, its writable regions apart from the arguments. -/
def SizedPairD (g : CallGeometry) (s t : State) : Prop :=
  Inputs g s ∧ Inputs g t ∧ PubG g.toGeo ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true ∧
  inputValue g s.mem 0 = inputValue g t.mem 0

theorem sizedD_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (SizedPairD g) VG.Impl.Rsa.X86.RecoverDetRt.sized (fun _ _ => True) := by
  have shape : VG.Impl.Rsa.X86.RecoverDetRt.sized = VG.Impl.Rsa.X86.Keys.seqs
      (VG.Impl.Rsa.X86.RecoverRt.loads :: [VG.Impl.Rsa.X86.RecoverRt.prod] ++
        [.seq VG.Impl.Rsa.X86.RecoverDetRt.det VG.Impl.Rsa.X86.RecoverRt.stores]) := rfl
  rw [shape]
  intro s t tr ur sf tf ⟨hs, ht, pg, vs, vt, same⟩ es et
  obtain ⟨_, three, small, ha, ha0, ha1, haw, hn0, hn'⟩ := det_facts hs len vs
  have rel := pubs_relCT (VG.RelCT.seq (det_relCT pg (inputValue g s.mem 0) (g.args 5).toNat three small ha ha0 ha1
    haw hn0 hn') storesPubW.relCT') loadsPubW
    (fun d hd => by rw [List.mem_singleton.mp hd]; exact prodPubW)
  have pt := pre_stepW ht len vt
  rw [← same] at pt
  exact ⟨(rel _ _ _ _ _ _ ⟨inputs_agree pg hs ht, pre_stepW hs len vs, pt⟩ es et).1, trivial⟩

/-- Two runs of `sized` from the states themselves: the arguments apart from the working space and the
outputs. -/
def SizedAtD (g : CallGeometry) (s t : State) : Prop :=
  Inputs g s ∧ Inputs g t ∧ (∀ r ∈ narrowW g, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r) ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true ∧
  inputValue g s.mem 0 = inputValue g t.mem 0

theorem sizedNarrowD_relCT [VG.Proof.Rsa.X86.Recover.G.GcdDone] (g : CallGeometry) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    RelCT isa (SizedAtD g) VG.Impl.Rsa.X86.RecoverDetRt.sized (fun _ _ => True) := by
  have len' : Lengths (narrowG g) :=
    ⟨len.lower, len.upper, len.width, len.scratch, len.bytes, len.pLen, len.qLen⟩
  refine relCT_narrow (Pn := SizedPairD (narrowG g)) (fun s => s.rd ++ s.wr)
    (fun _ => narrowW g) (fun s₁ s₂ ⟨h₁, h₂, apart, v₁, v₂, same⟩ => ?_)
    (sizedD_relCT (narrowG g) len')
  have cov : ∀ {s : State}, Inputs g s → Covers (narrowW g) s.wr := by
    intro s h
    refine Covers.cons (Covers.of_mem fun r hr => ?_) (Covers.cons (Covers.one (h.outputWrite 0))
      (Covers.cons (Covers.one (h.outputWrite 1)) Covers.nil))
    rw [List.mem_singleton.mp hr]
    exact h.ws.workspace.wr
  have pLen : (g.buffer 0).len = (g.args 5).toNat := congrArg BitVec.toNat len.pLen
  have qLen : (g.buffer 2).len = (g.args 5).toNat := congrArg BitVec.toNat len.qLen
  have wp : ∀ {s : State}, Inputs g s →
      Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true →
      ∃ F, WP isa VG.Impl.Rsa.X86.RecoverDetRt.sized (s.withRegions (s.rd ++ s.wr) (narrowW g)) F :=
    fun h v => ⟨_, sizedW_ok (narrow_inputs h) len' v
      (by simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer] at pLen ⊢; exact pLen)
      (by simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer] at qLen ⊢; exact qLen)
      eSmall⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov h₁)), cov h₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov h₂)), cov h₂, wp h₁ v₁, wp h₂ v₂,
    narrow_inputs h₁, narrow_inputs h₂, ⟨h₁.top, apart⟩, v₁, v₂, same⟩

/-- Recovery needs only the public modulus bytes. -/
def BodyPairD (g : CallGeometry) (s t : State) : Prop :=
  Pair g s t ∧ (∀ r ∈ narrowW g, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r) ∧
    inputBytes g s.mem 0 = inputBytes g t.mem 0

theorem bodyD_relCT [VG.Proof.Rsa.X86.Recover.G.GcdDone] (g : CallGeometry) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    RelCT isa (BodyPairD g) VG.Impl.Rsa.X86.RecoverDetRt.body (fun _ _ => True) := by
  let r := fun s t => BodyPairD g s t ∧
    s.zf = some (Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length) ∧
    t.zf = some (Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length)
  have branch : RelCT isa r (.ite .e VG.Impl.Rsa.X86.RecoverDetRt.sized VG.Impl.Rsa.X86.Recover.failure)
      (fun _ _ => True) := by
    have flags : ∀ s t, r s t → isa.eval .e s = isa.eval .e t := by
      intro s t h
      change s.zf = t.zf
      rw [h.2.1, h.2.2]
      unfold inputValue
      rw [h.1.2.2]
    apply VG.RelCT.ite (M := isa) (c := .e) (P := r) flags
    · apply (sizedNarrowD_relCT g len eSmall).mono
      · intro s t ⟨h, cond⟩
        have vs := Option.some.inj (h.2.1.symm.trans cond)
        have vt := Option.some.inj (h.2.2.symm.trans ((flags s t h).symm.trans cond))
        exact ⟨h.1.1.left, h.1.1.right, h.1.2.1, vs, vt, by unfold inputValue; rw [h.1.2.2]⟩
      · intro s t h; exact h
    · exact (failure_relCT g).mono (fun _ _ h => h.1.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨pair, apart, modulus⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (modulus_relCT g _ _ _ _ _ _ pair e1 f1).1
      obtain ⟨zs, ms, ks⟩ := wp_result (modulus_ok pair.left len) e1
      obtain ⟨zt, mt, kt⟩ := wp_result (modulus_ok pair.right len) f1
      have next : BodyPairD g u v := by
        refine ⟨pair.keepMem ks kt (by decide) (by decide) ms mt, ?_⟩
        rw [ms, mt]
        exact ⟨apart, modulus⟩
      have vs : u.zf = some (Spec.Rsa.modulusValid (inputValue g u.mem 0) (inputBytes g u.mem 0).length) := by
        rw [ms]
        simp only [inputValue, inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer]
        exact zs
      have vt : v.zf = some (Spec.Rsa.modulusValid (inputValue g v.mem 0) (inputBytes g v.mem 0).length) := by
        rw [mt]
        simp only [inputValue, inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer]
        exact zt
      have eq2 := (branch _ _ _ _ _ _ ⟨next, vs, vt⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩

theorem operationD_trace [VG.Proof.Rsa.X86.Recover.G.GcdDone] {s t : State} (a : ABI s) (b : ABI t) (eSmall : (arg s 7).toNat ≤ 8)
    (args : ∀ i < 12, arg s i = arg t i) (sp : s.gpr .esp = t.gpr .esp)
    (modulus : inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code s tr sf)
    (et : Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code t ur tf) :
    tr = ur := by
  have a4 := args 4 (by decide)
  have a5 := args 5 (by decide)
  have a10 := args 10 (by decide)
  have a11 := args 11 (by decide)
  have a0 := args 0 (by decide)
  have a1 := args 1 (by decide)
  have a2 := args 2 (by decide)
  have a3 := args 3 (by decide)
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (entry_relCT _ _ _ _ _ _
        ⟨sp, a10, (a.stackArgument (by decide : 10 < 12)).readSrc,
          (b.stackArgument (by decide : 10 < 12)).readSrc⟩ e1 f1).1
      obtain ⟨hs, _, ks, os⟩ := wp_result (installed_ok a) e1
      obtain ⟨ht, _, kt, ot⟩ := wp_result (installed_ok b) f1
      have hv : Inputs (caller s) v := by
        refine ht.geoEq (by simp only [caller, argumentPointer, a10]) (by simp only [caller, a11])
          (by simp only [caller, a5]) sp ?_ fun i hi => args i hi
        change s.wr = t.wr
        rw [a.wr, b.wr]
        simp only [caller, CallGeometry.buffer, argumentPointer, argAddr, a0, a1, a2, a3, a10, a11, sp]
      have pair : Pair (caller s) u v :=
        ⟨hs, hv, (ks.1 _ (by decide)).trans (sp.trans (kt.1 _ (by decide)).symm)⟩
      have same : inputBytes (caller s) u.mem 0 = inputBytes (caller s) v.mem 0 := by
        have ns := VG.Proof.Bignum.scratch_bytes os (by have := a.lengths.2; change (arg s 5).toNat ≤ _; omega_using [])
          (a.inApart _ (a.inputMember 0) _ (by simp))
        have nt := VG.Proof.Bignum.scratch_bytes ot (by have := b.lengths.2; change (arg t 5).toNat ≤ _; omega_using [])
          (b.inApart _ (b.inputMember 0) _ (by simp))
        change inputBytes (caller s) u.mem 0 = inputBytes (caller s) s.mem 0 at ns
        change inputBytes (caller t) v.mem 0 = inputBytes (caller t) t.mem 0 at nt
        have align : inputBytes (caller s) v.mem 0 = inputBytes (caller t) v.mem 0 := by
          simp only [inputBytes, caller, CallGeometry.buffer]
          change Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat =
            Spec.Rsa.bytesAt v.mem (byteAddr (arg t 4)) (arg t 5).toNat
          rw [a4, a5]
        exact ns.trans (modulus.trans (align.trans nt).symm)
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have apart : ∀ r ∈ narrowW (caller s),
              Region.Disjoint ⟨(caller s).sp.setWidth 64, 52⟩ r := fun r hr =>
            VG.X86.Taint.frame_disjoint (n := 48)
              (by change (s.gpr .esp).toNat + 4 + 48 ≤ _; have := a.stackBound; omega_using [this]) (a.retApart r hr)
              (a.argsApart r hr)
          have eq2 := (bodyD_relCT (caller s) a.lengths_ok eSmall _ _ _ _ _ _ ⟨pair, apart, same⟩ e2 f2).1
          obtain ⟨hx, _, _, kx⟩ := wp_result (bodyD_ok hs a.lengths_ok eSmall) e2
          obtain ⟨hy, _, _, ky⟩ := wp_result (bodyD_ok hv a.lengths_ok eSmall) f2
          have next := pair.after hx hy kx ky (by decide)
          have eq3 := (publicRestore_relCT _ _ _ _ _ _ next.workspace e3 f3).1
          rw [eq1, eq2, eq3]

theorem constantTimeD [VG.Proof.Rsa.X86.Recover.G.GcdDone] : ConstantTime isa (Spec.Rsa.recoverPrimesDetContract abi 96).pre
    (Spec.Rsa.recoverPrimesDetContract abi 96).pub VG.Impl.Rsa.X86.RecoverDetRt.code := by
  intro s t tr ur sf tf hs ht h es et
  have args := argumentsD_eq h
  obtain ⟨a, eSmall⟩ := abiD_of hs
  exact operationD_trace a (abiD_of ht).1 eSmall args.2 args.1 (modulusD_eq h) es et

theorem verifiedD [VG.Proof.Rsa.X86.Recover.G.GcdDone] : Verified target VG.Impl.Rsa.X86.RecoverDetRt.code (Spec.Rsa.recoverPrimesDetContract abi 96) :=
  ⟨correctD, constantTimeD, satisfiableD⟩

end VG.Proof.Rsa.X86.Recover
end
